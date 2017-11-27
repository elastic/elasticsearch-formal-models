section \<open>Implementation\<close>

text \<open>This section presents the implementation of the algorithm.\<close>

theory Implementation
  imports Preliminaries
begin

subsection \<open>Protocol messages\<close>

text \<open>The
proven-safe core of the protocol works by sending messages as described here. The remainder of the
protocol may send other messages too, and may drop, reorder or duplicate any of these messages, but
must not send these messages itself to ensure safety. Another way of thinking of these messages is
to consider them as ``fire-and-forget'' RPC invocations that, on receipt, call some local method, maybe
update the receiving node's state, and maybe yield some further messages. The @{type nat} parameter to each
message refers to a slot number.\<close>


datatype Message
  = StartJoin Term
  | JoinRequest Slot Term "Term option"
  | ClientValue Value
  | PublishRequest Slot Term Value
  | PublishResponse Slot Term
  | ApplyCommit Slot Term
  | CatchUpRequest
  | CatchUpResponse Slot "Node set" ClusterState
  | Reboot

text \<open>Some prose descriptions of these messages follows, in order to give a bit more of an
intuitive understanding of their purposes.\<close>

text \<open>The message @{term "StartJoin t"} may be sent by any node to attempt to start a master
election in the given term @{term t}.\<close>

text \<open>The message @{term "JoinRequest i t a"} may be sent by a node in response
to a @{term StartJoin} message. It indicates that the sender knows all committed values for slots
strictly below @{term i}, and that the sender will no longer vote (i.e. send an @{term
PublishResponse}) in any term prior to @{term t}. The field @{term a} is either @{term
None} or @{term "Some t'"}. In the former case this indicates that
the node has not yet sent any @{term PublishResponse} message in slot @{term i}, and in the latter
case it indicates that the largest term in which it has previously sent an @{term PublishResponse}
message is @{term t'}.  All
nodes must avoid sending a @{term JoinRequest} message to two different masters in the same term.\<close>

text \<open>The message @{term "ClientValue x"} may be sent by any node and indicates an attempt to
reach consensus on the value @{term x}.\<close>

text \<open>The message @{term "PublishRequest i t v"} may be sent by the elected master of term
@{term t} to request the other master-eligible nodes to vote for value @{term v} to be committed in
slot @{term i}.\<close>

text \<open>The message @{term "PublishResponse i t"} may be sent by node in response to
the corresponding @{term PublishRequest} message, indicating that the sender votes for the value
proposed by the master of term @{term t} to be committed in slot @{term i}.\<close>

text \<open>The message @{term "ApplyCommit i t"} indicates that the value proposed by the master of
term @{term t} in slot @{term i} received a quorum of votes and is therefore committed.\<close>

text \<open>The message @{term Reboot} may be sent by any node to represent the restart of a node, which
loses any ephemeral state.\<close>

text \<open>The abstract model of Zen keeps track of the set of all messages that have ever been
sent, and asserts that this set obeys certain invariants, listed below. Further below, it will be
shown that these invariants imply that each slot obeys the @{term oneSlot} invariants above and
hence that each slot cannot see inconsistent committed values.\<close>

datatype Destination = Broadcast | OneNode Node

record RoutedMessage =
  sender :: Node
  destination :: Destination
  payload :: Message

text \<open>It will be useful to be able to choose the optional term with the greater term,
so here is a function that does that.\<close>

fun maxTermOption :: "Term option \<Rightarrow> Term option \<Rightarrow> Term option"
  where
    "maxTermOption None None = None"
  | "maxTermOption None (Some t) = Some t"
  | "maxTermOption (Some t) None = Some t"
  | "maxTermOption (Some t\<^sub>1) (Some t\<^sub>2) = Some (max t\<^sub>1 t\<^sub>2)"

lemma maxTermOption_t_None[simp]: "maxTermOption mt None = mt" by (cases mt, auto)
lemma maxTermOption_None_t[simp]: "maxTermOption None mt = mt" by (cases mt, auto)
lemma maxTermOption_diagonal[simp]: "maxTermOption p p = p" by (cases p, simp_all)

lemma
  assumes "maxTermOption p1 p2 = None"
  shows maxTermOption_eq_None_1:"p1 = None"
    and maxTermOption_eq_None_2:"p2 = None"
  using assms maxTermOption.elims by auto

lemma maxTermOption_range: "maxTermOption p1 p2 \<in> {p1, p2}"
  by (cases p1, simp, cases p2, simp_all add: max_def)

subsection \<open>Node implementation\<close>

text \<open>Each node holds the following local data.\<close>

record LastAcceptedData =
  ladSlot :: Slot
  ladTerm :: Term
  ladValue :: Value

record NodeData =
  currentNode :: Node (* identity of this node *)
  firstUncommittedSlot :: Slot (* all slots strictly below this one are committed *)
  currentTerm :: Term (* greatest term for which a promise was sent, and term of votes being collected *)
  currentVotingNodes :: "Node set" (* configuration of the currentEra - the set of voting nodes *)
  currentClusterState :: ClusterState (* last-committed cluster state *)
  (* acceptor data *)
  lastAcceptedData :: "LastAcceptedData option"
  (* election data *)
  joinVotes :: "Node set" (* set of nodes that have sent a JoinRequest for the current currentTerm *)
  electionWon :: bool
  electionValueForced :: bool (* if True, must propose lastAcceptedValue for this slot on winning an election; if False, can propose anything *)
  (* learner data *)
  publishPermitted :: bool (* if True, may publish a value for this slot/term pair; if False, must not: either there is definitely a PublishRequest in flight, or we've just rebooted. *)
  publishVotes :: "Node set"

definition lastAcceptedSlot :: "NodeData \<Rightarrow> Slot"
  where "lastAcceptedSlot nd \<equiv> ladSlot (THE lad. lastAcceptedData nd = Some lad)"

definition lastAcceptedValue :: "NodeData \<Rightarrow> Value"
  where "lastAcceptedValue nd \<equiv> ladValue (THE lad. lastAcceptedData nd = Some lad)"

definition lastAcceptedTerm :: "NodeData \<Rightarrow> Term option"
  where "lastAcceptedTerm nd \<equiv> case lastAcceptedData nd of None \<Rightarrow> None | Some lad \<Rightarrow> Some (ladTerm lad)"

definition isQuorum :: "NodeData \<Rightarrow> Node set \<Rightarrow> bool"
  where "isQuorum nd q \<equiv> q \<in> majorities (currentVotingNodes nd)"

definition lastAcceptedTermInSlot :: "NodeData \<Rightarrow> Term option"
  where "lastAcceptedTermInSlot nd \<equiv> if firstUncommittedSlot nd = lastAcceptedSlot nd then lastAcceptedTerm nd else None"

text \<open>This method publishes a value via a @{term PublishRequest} message.\<close>

definition publishValue :: "Value \<Rightarrow> NodeData \<Rightarrow> (NodeData * Message option)"
  where
    "publishValue x nd \<equiv>
        if electionWon nd \<and> publishPermitted nd
              then ( nd \<lparr> publishPermitted := False \<rparr>
                   , Some (PublishRequest
                             (firstUncommittedSlot nd)
                             (currentTerm nd) x) )
              else (nd, None)"

text \<open>This method updates the node's current term (if necessary) and discards any data associated
with the previous term.\<close>

definition ensureCurrentTerm :: "Term \<Rightarrow> NodeData \<Rightarrow> NodeData"
  where
    "ensureCurrentTerm t nd \<equiv>
        if t \<le> currentTerm nd
            then nd
            else nd
              \<lparr> joinVotes := {}
              , currentTerm := t
              , electionWon := False
              , electionValueForced := False
              , publishPermitted := True
              , publishVotes := {} \<rparr>"

text \<open>This method updates the node's state on receipt of a vote (a @{term JoinRequest}) in an election.\<close>

definition addElectionVote :: "Node \<Rightarrow> Slot => Term option \<Rightarrow> NodeData \<Rightarrow> NodeData"
  where
    "addElectionVote s i a nd \<equiv> let newVotes = insert s (joinVotes nd)
      in nd \<lparr> joinVotes := newVotes
            , electionValueForced := electionValueForced nd \<or> (a \<noteq> None \<and> i = firstUncommittedSlot nd)
            , electionWon := isQuorum nd newVotes \<rparr>"

text \<open>Clients request the cluster to achieve consensus on certain values using the @{term ClientValue}
message which is handled as follows.\<close>

definition handleClientValue :: "Value \<Rightarrow> NodeData \<Rightarrow> (NodeData * Message option)"
  where
    "handleClientValue x nd \<equiv> if electionValueForced nd then (nd, None) else publishValue x nd"

text \<open>A @{term StartJoin} message is checked for acceptability and then handled by updating the
node's term and yielding a @{term JoinRequest} message as follows.\<close>

definition handleStartJoin :: "Term \<Rightarrow> NodeData \<Rightarrow> (NodeData * Message option)"
  where
    "handleStartJoin t nd \<equiv>
        if currentTerm nd < t
          then ( ensureCurrentTerm t nd
               , Some (JoinRequest (firstUncommittedSlot nd)
                                     t
                                    (lastAcceptedTermInSlot nd)))
          else (nd, None)"

text \<open>A @{term JoinRequest} message is checked for acceptability and then handled as follows, perhaps
yielding a @{term PublishRequest} message.\<close>

definition handleJoinRequest :: "Node \<Rightarrow> Slot \<Rightarrow> Term \<Rightarrow> Term option \<Rightarrow> NodeData \<Rightarrow> (NodeData * Message option)"
  where
    "handleJoinRequest s i t a nd \<equiv>
         if t = currentTerm nd
             \<and> (i < firstUncommittedSlot nd
                \<or> (i = firstUncommittedSlot nd
                    \<and> (a = None
                        \<or> a = lastAcceptedTermInSlot nd
                        \<or> (maxTermOption a (lastAcceptedTermInSlot nd) = lastAcceptedTermInSlot nd
                              \<and> electionValueForced nd))))
          then let nd1 = addElectionVote s i a nd
               in (if electionValueForced nd1 then publishValue (lastAcceptedValue nd1) nd1 else (nd1, None))
          else (nd, None)"

text \<open>A @{term PublishRequest} message is checked for acceptability and then handled as follows,
yielding a @{term PublishResponse} message.\<close>

definition handlePublishRequest :: "Slot \<Rightarrow> Term \<Rightarrow> Value \<Rightarrow> NodeData \<Rightarrow> (NodeData * Message option)"
  where
    "handlePublishRequest i t x nd \<equiv>
          if i = firstUncommittedSlot nd
                \<and> t = currentTerm nd
          then ( nd \<lparr> lastAcceptedData := Some \<lparr> ladSlot = i, ladTerm = t, ladValue = x \<rparr> \<rparr>
               , Some (PublishResponse i t))
          else (nd, None)"

text \<open>This method sends an @{term ApplyCommit} message if a quorum of votes has been received.\<close>

definition commitIfQuorate :: "NodeData \<Rightarrow> (NodeData * Message option)"
  where
    "commitIfQuorate nd = (nd, if 2 * card (publishVotes nd) > card (currentVotingNodes nd)
                                  then Some (ApplyCommit (firstUncommittedSlot nd) (currentTerm nd)) else None)"

text \<open>A @{term PublishResponse} message is checked for acceptability and handled as follows. If
this message, together with the previously-received messages, forms a quorum of votes then the
value is committed, yielding an @{term ApplyCommit} message.\<close>

definition handlePublishResponse :: "Node \<Rightarrow> Slot \<Rightarrow> Term \<Rightarrow> NodeData \<Rightarrow> (NodeData * Message option)"
  where
    "handlePublishResponse s i t nd \<equiv>
        if i = firstUncommittedSlot nd \<and> t = currentTerm nd \<and> s \<in> currentVotingNodes nd
        then commitIfQuorate (nd \<lparr> publishVotes := insert s (publishVotes nd) \<rparr>)
        else (nd, None)"

text \<open>This method updates the node's state when a value is committed.\<close>

definition applyAcceptedValue :: "NodeData \<Rightarrow> NodeData"
  where
    "applyAcceptedValue nd \<equiv> case lastAcceptedValue nd of
        NoOp \<Rightarrow> nd
      | Reconfigure votingNodes \<Rightarrow> nd
          \<lparr> currentVotingNodes := set votingNodes
          , electionWon := joinVotes nd \<in> majorities (set votingNodes) \<rparr>
      | ClusterStateDiff diff \<Rightarrow> nd \<lparr> currentClusterState := diff (currentClusterState nd) \<rparr>"

text \<open>An @{term ApplyCommit} message is applied to the current node's state, updating its configuration
and \texttt{ClusterState} via the @{term applyValue} method. It yields no messages.\<close>

definition handleApplyCommit :: "Slot \<Rightarrow> Term \<Rightarrow> NodeData \<Rightarrow> NodeData"
  where
    "handleApplyCommit i t nd \<equiv>
        if i = firstUncommittedSlot nd \<and> lastAcceptedTermInSlot nd = Some t
          then (applyAcceptedValue nd)
                     \<lparr> firstUncommittedSlot := i + 1
                     , publishPermitted := True
                     , electionValueForced := False
                     , publishVotes := {} \<rparr>
          else nd"

definition handleCatchUpRequest :: "NodeData \<Rightarrow> (NodeData * Message option)"
  where
    "handleCatchUpRequest nd = (nd, Some (CatchUpResponse (firstUncommittedSlot nd)
                                              (currentVotingNodes nd) (currentClusterState nd)))"

definition handleCatchUpResponse :: "Slot \<Rightarrow> Node set \<Rightarrow> ClusterState \<Rightarrow> NodeData \<Rightarrow> NodeData"
  where
    "handleCatchUpResponse i conf cs nd \<equiv>
      if firstUncommittedSlot nd < i
        then nd \<lparr> firstUncommittedSlot := i
                , publishPermitted := False
                , electionValueForced := False
                , publishVotes := {}
                , currentVotingNodes := conf
                , currentClusterState := cs
                , joinVotes := {}
                , electionWon := False \<rparr>
        else nd"

text \<open>A @{term Reboot} message simulates the effect of a reboot, discarding any ephemeral state but
preserving the persistent state. It yields no messages.\<close>

definition handleReboot :: "NodeData \<Rightarrow> NodeData"
  where
    "handleReboot nd \<equiv>
      \<lparr> currentNode = currentNode nd
      , firstUncommittedSlot = firstUncommittedSlot nd
      , currentTerm = currentTerm nd
      , currentVotingNodes = currentVotingNodes nd
      , currentClusterState = currentClusterState nd
      , lastAcceptedData = lastAcceptedData nd
      , joinVotes = {}
      , electionWon = False
      , electionValueForced = False
      , publishPermitted = False
      , publishVotes = {} \<rparr>"

text \<open>This function dispatches incoming messages to the appropriate handler method, and
routes any responses to the appropriate places. In particular, @{term JoinRequest} messages
(sent by the @{term handleStartJoin} method) and
@{term PublishResponse} messages (sent by the @{term handlePublishRequest} method) are
only sent to a single node, whereas all other responses are broadcast to all nodes.\<close>

definition ProcessMessage :: "NodeData \<Rightarrow> RoutedMessage \<Rightarrow> (NodeData * RoutedMessage option)"
  where
    "ProcessMessage nd msg \<equiv>
      let respondTo =
          (\<lambda> d (nd, mmsg). case mmsg of
               None \<Rightarrow> (nd, None)
             | Some msg \<Rightarrow> (nd,
                 Some \<lparr> sender = currentNode nd, destination = d,
                             payload = msg \<rparr>));
          respondToSender = respondTo (OneNode (sender msg));
          respondToAll    = respondTo Broadcast
      in
        if destination msg \<in> { Broadcast, OneNode (currentNode nd) }
        then case payload msg of
          StartJoin t
              \<Rightarrow> respondToSender (handleStartJoin t nd)
          | JoinRequest i t a
              \<Rightarrow> respondToAll (handleJoinRequest (sender msg) i t a nd)
          | ClientValue x
              \<Rightarrow> respondToAll (handleClientValue x nd)
          | PublishRequest i t x
              \<Rightarrow> respondToSender (handlePublishRequest i t x nd)
          | PublishResponse i t
              \<Rightarrow> respondToAll (handlePublishResponse (sender msg) i t nd)
          | ApplyCommit i t
              \<Rightarrow> (handleApplyCommit i t nd, None)
          | CatchUpRequest
              \<Rightarrow> respondToSender (handleCatchUpRequest nd)
          | CatchUpResponse i conf cs
              \<Rightarrow> (handleCatchUpResponse i conf cs nd, None)
          | Reboot
              \<Rightarrow> (handleReboot nd, None)
        else (nd, None)"

text \<open>Nodes are initialised to this state. The data required is the initial configuration, @{term Q\<^sub>0}
and the initial \texttt{ClusterState}, here shown as @{term "ClusterState 0"}.\<close>

definition initialNodeState :: "Node \<Rightarrow> NodeData"
  where "initialNodeState n =
      \<lparr> currentNode = n
      , firstUncommittedSlot = 0
      , currentTerm = 0
      , currentVotingNodes = V\<^sub>0
      , currentClusterState = CS\<^sub>0
      , lastAcceptedData = None
      , joinVotes = {}
      , electionWon = False
      , electionValueForced = False
      , publishPermitted = False
      , publishVotes = {} \<rparr>"

end
