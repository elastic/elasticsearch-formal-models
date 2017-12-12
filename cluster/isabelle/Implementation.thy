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

datatype TermOption = NO_TERM | SomeTerm Term

instantiation TermOption :: linorder
begin

fun less_TermOption :: "TermOption \<Rightarrow> TermOption \<Rightarrow> bool"
  where "t < NO_TERM = False"
  | "NO_TERM < SomeTerm t = True"
  | "SomeTerm t\<^sub>1 < SomeTerm t\<^sub>2 = (t\<^sub>1 < t\<^sub>2)"

definition less_eq_TermOption :: "TermOption \<Rightarrow> TermOption \<Rightarrow> bool"
  where "(t\<^sub>1 :: TermOption) \<le> t\<^sub>2 \<equiv> t\<^sub>1 = t\<^sub>2 \<or> t\<^sub>1 < t\<^sub>2"

instance proof
  fix x y z :: TermOption
  show "(x < y) = (x \<le> y \<and> \<not> y \<le> x)" unfolding less_eq_TermOption_def apply auto
    using less_TermOption.elims apply fastforce
    by (metis less_TermOption.elims(2) less_TermOption.simps(3) less_not_sym)

  show "x \<le> x" by (simp add: less_eq_TermOption_def)

  show "x \<le> y \<Longrightarrow> y \<le> z \<Longrightarrow> x \<le> z" unfolding less_eq_TermOption_def apply auto
    by (metis TermOption.distinct(1) TermOption.inject dual_order.strict_trans less_TermOption.elims(2) less_TermOption.elims(3))

  show "x \<le> y \<Longrightarrow> y \<le> x \<Longrightarrow> x = y" unfolding less_eq_TermOption_def apply auto
    using \<open>(x < y) = (x \<le> y \<and> \<not> y \<le> x)\<close> less_eq_TermOption_def by blast

  show "x \<le> y \<or> y \<le> x" unfolding less_eq_TermOption_def apply auto
    by (metis TermOption.distinct(1) TermOption.inject less_TermOption.elims(3) neqE)
qed

end

lemma NO_TERM_le [simp]: "NO_TERM \<le> t" by (cases t, simp_all add: less_eq_TermOption_def)
lemma le_NO_TERM [simp]: "(t \<le> NO_TERM) = (t = NO_TERM)" by (cases t, simp_all add: less_eq_TermOption_def)
lemma le_SomeTerm [simp]: "(SomeTerm t\<^sub>1 \<le> SomeTerm t\<^sub>2) = (t\<^sub>1 \<le> t\<^sub>2)" by (auto simp add: less_eq_TermOption_def)

datatype Message
  = StartJoin Term
  | Vote Slot Term TermOption
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

text \<open>The message @{term "Vote i t a"} may be sent by a node in response
to a @{term StartJoin} message. It indicates that the sender knows all committed values for slots
strictly below @{term i}, and that the sender will no longer vote (i.e. send an @{term
PublishResponse}) in any term prior to @{term t}. The field @{term a} is either @{term
None} or @{term "Some t'"}. In the former case this indicates that
the node has not yet sent any @{term PublishResponse} message in slot @{term i}, and in the latter
case it indicates that the largest term in which it has previously sent an @{term PublishResponse}
message is @{term t'}.  All
nodes must avoid sending a @{term Vote} message to two different masters in the same term.\<close>

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

subsection \<open>Node implementation\<close>

text \<open>Each node holds the following local data.\<close>

record TermValue =
  tvTerm :: Term
  tvValue :: Value

record NodeData =
  currentNode :: Node
  currentTerm :: Term
  (* committed state *)
  firstUncommittedSlot :: Slot
  currentVotingNodes :: "Node set"
  currentClusterState :: ClusterState
  (* accepted state *)
  lastAcceptedData :: "TermValue option"
  (* election state *)
  joinVotes :: "Node set"
  electionWon :: bool
  (* publish state *)
  publishPermitted :: bool
  publishVotes :: "Node set"

definition lastAcceptedValue :: "NodeData \<Rightarrow> Value"
  where "lastAcceptedValue nd \<equiv> tvValue (THE lad. lastAcceptedData nd = Some lad)"

definition lastAcceptedTerm :: "NodeData \<Rightarrow> TermOption"
  where "lastAcceptedTerm nd \<equiv> case lastAcceptedData nd of None \<Rightarrow> NO_TERM | Some lad \<Rightarrow> SomeTerm (tvTerm lad)"

definition isQuorum :: "NodeData \<Rightarrow> Node set \<Rightarrow> bool"
  where "isQuorum nd q \<equiv> q \<in> majorities (currentVotingNodes nd)"

lemma lastAcceptedValue_joinVotes_update[simp]: "lastAcceptedValue (joinVotes_update f nd) = lastAcceptedValue nd" by (simp add: lastAcceptedValue_def)
lemma lastAcceptedTerm_joinVotes_update[simp]: "lastAcceptedTerm (joinVotes_update f nd) = lastAcceptedTerm nd" by (simp add: lastAcceptedTerm_def)

lemma lastAcceptedValue_electionWon_update[simp]: "lastAcceptedValue (electionWon_update f nd) = lastAcceptedValue nd" by (simp add: lastAcceptedValue_def)
lemma lastAcceptedTerm_electionWon_update[simp]: "lastAcceptedTerm (electionWon_update f nd) = lastAcceptedTerm nd" by (simp add: lastAcceptedTerm_def)

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
              , publishPermitted := True
              , publishVotes := {} \<rparr>"

text \<open>This method updates the node's state on receipt of a vote (a @{term Vote}) in an election.\<close>

definition addElectionVote :: "Node \<Rightarrow> Slot => TermOption \<Rightarrow> NodeData \<Rightarrow> NodeData"
  where
    "addElectionVote s i a nd \<equiv> let newVotes = insert s (joinVotes nd)
      in nd \<lparr> joinVotes := newVotes
            , electionWon := isQuorum nd newVotes \<rparr>"

text \<open>Clients request the cluster to achieve consensus on certain values using the @{term ClientValue}
message which is handled as follows.\<close>

definition handleClientValue :: "Value \<Rightarrow> NodeData \<Rightarrow> (NodeData * Message option)"
  where
    "handleClientValue x nd \<equiv> if lastAcceptedTerm nd = NO_TERM then publishValue x nd else (nd, None)"

text \<open>A @{term StartJoin} message is checked for acceptability and then handled by updating the
node's term and yielding a @{term Vote} message as follows.\<close>

definition handleStartJoin :: "Term \<Rightarrow> NodeData \<Rightarrow> (NodeData * Message option)"
  where
    "handleStartJoin t nd \<equiv>
        if currentTerm nd < t
          then ( ensureCurrentTerm t nd
               , Some (Vote (firstUncommittedSlot nd)
                                     t
                                    (lastAcceptedTerm nd)))
          else (nd, None)"

text \<open>A @{term Vote} message is checked for acceptability and then handled as follows, perhaps
yielding a @{term PublishRequest} message.\<close>

definition handleVote :: "Node \<Rightarrow> Slot \<Rightarrow> Term \<Rightarrow> TermOption \<Rightarrow> NodeData \<Rightarrow> (NodeData * Message option)"
  where
    "handleVote s i t a nd \<equiv>
         if t = currentTerm nd
             \<and> (i < firstUncommittedSlot nd
                \<or> (i = firstUncommittedSlot nd \<and> a \<le> lastAcceptedTerm nd))
          then let nd1 = addElectionVote s i a nd
               in (if lastAcceptedTerm nd = NO_TERM then (nd1, None) else publishValue (lastAcceptedValue nd1) nd1)
          else (nd, None)"

text \<open>A @{term PublishRequest} message is checked for acceptability and then handled as follows,
yielding a @{term PublishResponse} message.\<close>

definition handlePublishRequest :: "Slot \<Rightarrow> Term \<Rightarrow> Value \<Rightarrow> NodeData \<Rightarrow> (NodeData * Message option)"
  where
    "handlePublishRequest i t x nd \<equiv>
          if i = firstUncommittedSlot nd
                \<and> t = currentTerm nd
          then ( nd \<lparr> lastAcceptedData := Some \<lparr> tvTerm = t, tvValue = x \<rparr> \<rparr>
               , Some (PublishResponse i t))
          else (nd, None)"

text \<open>This method sends an @{term ApplyCommit} message if a quorum of votes has been received.\<close>

definition commitIfQuorate :: "NodeData \<Rightarrow> (NodeData * Message option)"
  where
    "commitIfQuorate nd = (nd, if isQuorum nd (publishVotes nd)
                                  then Some (ApplyCommit (firstUncommittedSlot nd) (currentTerm nd)) else None)"

text \<open>A @{term PublishResponse} message is checked for acceptability and handled as follows. If
this message, together with the previously-received messages, forms a quorum of votes then the
value is committed, yielding an @{term ApplyCommit} message.\<close>

definition handlePublishResponse :: "Node \<Rightarrow> Slot \<Rightarrow> Term \<Rightarrow> NodeData \<Rightarrow> (NodeData * Message option)"
  where
    "handlePublishResponse s i t nd \<equiv>
        if i = firstUncommittedSlot nd \<and> t = currentTerm nd
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
        if i = firstUncommittedSlot nd \<and> lastAcceptedTerm nd = SomeTerm t
          then (applyAcceptedValue nd)
                     \<lparr> firstUncommittedSlot := i + 1
                     , lastAcceptedData := None
                     , publishPermitted := True
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
                , publishPermitted := True
                , publishVotes := {}
                , currentVotingNodes := conf
                , currentClusterState := cs
                , lastAcceptedData := None
                , joinVotes := {}
                , electionWon := False \<rparr>
        else nd"

text \<open>A @{term Reboot} message simulates the effect of a reboot, discarding any ephemeral state but
preserving the persistent state. It yields no messages.\<close>

definition handleReboot :: "NodeData \<Rightarrow> NodeData"
  where
    "handleReboot nd \<equiv>
      \<lparr> currentNode = currentNode nd
      , currentTerm = currentTerm nd
      , firstUncommittedSlot = firstUncommittedSlot nd
      , currentVotingNodes = currentVotingNodes nd
      , currentClusterState = currentClusterState nd
      , lastAcceptedData = lastAcceptedData nd
      , joinVotes = {}
      , electionWon = False
      , publishPermitted = False
      , publishVotes = {} \<rparr>"

text \<open>This function dispatches incoming messages to the appropriate handler method, and
routes any responses to the appropriate places. In particular, @{term Vote} messages
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
          | Vote i t a
              \<Rightarrow> respondToAll (handleVote (sender msg) i t a nd)
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
      , currentTerm = 0
      , firstUncommittedSlot = 0
      , currentVotingNodes = V\<^sub>0
      , currentClusterState = CS\<^sub>0
      , lastAcceptedData = None
      , joinVotes = {}
      , electionWon = False
      , publishPermitted = True
      , publishVotes = {} \<rparr>"

end
