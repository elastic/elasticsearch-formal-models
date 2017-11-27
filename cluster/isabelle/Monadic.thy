theory Monadic
  imports Implementation "~~/src/HOL/Library/Monad_Syntax"
begin

datatype 'a Action = Action "NodeData \<Rightarrow> (NodeData * RoutedMessage list * 'a)"

definition return :: "'a \<Rightarrow> 'a Action" where "return a \<equiv> Action (\<lambda> nd. (nd, [], a))"

definition Action_bind :: "'a Action \<Rightarrow> ('a \<Rightarrow> 'b Action) \<Rightarrow> 'b Action"
  where "Action_bind ma mf \<equiv> case ma of
    Action unwrapped_ma \<Rightarrow> Action (\<lambda> nd0. case unwrapped_ma nd0 of
      (nd1, msgs0, a) \<Rightarrow> case mf a of
        Action unwrapped_mb \<Rightarrow> case unwrapped_mb nd1 of
          (nd2, msgs1, b) \<Rightarrow> (nd2, msgs0 @ msgs1, b))"

adhoc_overloading bind Action_bind

definition runM :: "'a Action \<Rightarrow> NodeData \<Rightarrow> (NodeData * RoutedMessage list * 'a)"
  where "runM ma \<equiv> case ma of Action unwrapped_ma \<Rightarrow> unwrapped_ma"

lemma runM_action[simp]: "runM (Action f) = f" by (simp add: runM_def)
lemma runM_inject[intro]: "(\<And>nd. runM ma nd = runM mb nd) \<Longrightarrow> ma = mb" by (cases ma, cases mb, auto simp add: runM_def)

lemma runM_return[simp]: "runM (return a) nd = (nd, [], a)" unfolding runM_def return_def by simp
lemma runM_bind: "runM (a \<bind> f) nd0 = (case runM a nd0 of (nd1, msgs1, b) \<Rightarrow> case runM (f b) nd1 of (nd2, msgs2, c) \<Rightarrow> (nd2, msgs1@msgs2, c))"
  unfolding runM_def Action_bind_def apply (cases "a", auto)
  by (metis (no_types, lifting) Action.case Action.exhaust case_prod_conv old.prod.exhaust)

lemma return_bind[simp]: "do { a' <- return a; f a' } = f a"
  apply (intro runM_inject) by (simp add: runM_bind return_def)
lemma bind_return[simp]: "do { a' <- f; return a' } = f"
  apply (intro runM_inject) by (simp add: runM_bind return_def)

lemma bind_bind_assoc[simp]:
  fixes f :: "'a Action"
  shows "do { b <- do { a <- f; g a }; h b } = do { a <- f; b <- g a; h b }" (is "?LHS = ?RHS")
proof (intro runM_inject)
  fix nd0
  show "runM ?LHS nd0 = runM ?RHS nd0"
  proof (cases "runM f nd0")
    case fields1: (fields nd1 msgs1 b)
    show ?thesis
    proof (cases "runM (g b) nd1")
      case fields2: (fields nd2 msgs2 c)
      show ?thesis by (cases "runM (h c) nd2", simp add: runM_bind fields1 fields2)
    qed
  qed
qed

definition getNodeData :: "NodeData Action" where "getNodeData \<equiv> Action (\<lambda>nd. (nd, [], nd))"
definition setNodeData :: "NodeData \<Rightarrow> unit Action" where "setNodeData nd \<equiv> Action (\<lambda>_. (nd, [], ()))"

lemma runM_getNodeData[simp]: "runM  getNodeData      nd = (nd,  [], nd)" by (simp add: runM_def getNodeData_def)
lemma runM_setNodeData[simp]: "runM (setNodeData nd') nd = (nd', [], ())" by (simp add: runM_def setNodeData_def)

lemma runM_getNodeData_continue[simp]: "runM (do { nd' <- getNodeData; f nd' }) nd = runM (f nd) nd" by (simp add: runM_bind)
lemma runM_setNodeData_continue[simp]: "runM (do { setNodeData nd'; f }) nd = runM f nd'" by (simp add: runM_bind)

definition modifyNodeData :: "(NodeData \<Rightarrow> NodeData) \<Rightarrow> unit Action" where "modifyNodeData f = getNodeData \<bind> (setNodeData \<circ> f)"

lemma runM_modifyNodeData[simp]: "runM (modifyNodeData f) nd = (f nd, [], ())" by (simp add: modifyNodeData_def runM_bind)
lemma runM_modifyNodeData_continue[simp]: "runM (do { modifyNodeData f; a }) nd = runM a (f nd)" by (simp add: runM_bind)

definition tell :: "RoutedMessage list \<Rightarrow> unit Action" where "tell rms \<equiv> Action (\<lambda>nd. (nd, rms, ()))"
lemma runM_tell[simp]: "runM (tell rms) nd = (nd, rms, ())" by (simp add: runM_def tell_def)
lemma runM_tell_contiue[simp]: "runM (do { tell rms; a }) nd = (let (nd, rms', x) = runM a nd in (nd, rms@rms', x))" by (simp add: runM_bind tell_def)

definition send :: "RoutedMessage \<Rightarrow> unit Action" where "send rm = tell [rm]"

definition gets :: "(NodeData \<Rightarrow> 'a) \<Rightarrow> 'a Action" where "gets f \<equiv> do { nd <- getNodeData; return (f nd) }"
definition getCurrentClusterState where "getCurrentClusterState = gets currentClusterState"
definition getCurrentNode where "getCurrentNode = gets currentNode"
definition getCurrentTerm where "getCurrentTerm = gets currentTerm"
definition getCurrentVotingNodes where "getCurrentVotingNodes = gets currentVotingNodes"
definition getElectionValueForced where "getElectionValueForced = gets electionValueForced"
definition getElectionWon where "getElectionWon = gets electionWon"
definition getFirstUncommittedSlot where "getFirstUncommittedSlot = gets firstUncommittedSlot"
definition getJoinVotes where "getJoinVotes = gets joinVotes"
definition getLastAcceptedSlot where "getLastAcceptedSlot = gets lastAcceptedSlot"
definition getLastAcceptedTerm where "getLastAcceptedTerm = gets lastAcceptedTerm"
definition getLastAcceptedValue where "getLastAcceptedValue = gets lastAcceptedValue"
definition getPublishPermitted where "getPublishPermitted = gets publishPermitted"
definition getPublishVotes where "getPublishVotes = gets publishVotes"

definition sets where "sets f x = modifyNodeData (f (\<lambda>_. x))"
definition setCurrentClusterState where "setCurrentClusterState = sets currentClusterState_update"
definition setCurrentNode where "setCurrentNode = sets currentNode_update"
definition setCurrentTerm where "setCurrentTerm = sets currentTerm_update"
definition setCurrentVotingNodes where "setCurrentVotingNodes = sets currentVotingNodes_update"
definition setElectionValueForced where "setElectionValueForced = sets electionValueForced_update"
definition setElectionWon where "setElectionWon = sets electionWon_update"
definition setFirstUncommittedSlot where "setFirstUncommittedSlot = sets firstUncommittedSlot_update"
definition setJoinVotes where "setJoinVotes = sets joinVotes_update"
definition setLastAcceptedSlot where "setLastAcceptedSlot = sets lastAcceptedSlot_update"
definition setLastAcceptedTerm where "setLastAcceptedTerm = sets lastAcceptedTerm_update"
definition setLastAcceptedValue where "setLastAcceptedValue = sets lastAcceptedValue_update"
definition setPublishPermitted where "setPublishPermitted = sets publishPermitted_update"
definition setPublishVotes where "setPublishVotes = sets publishVotes_update"

definition modifies where "modifies f g = modifyNodeData (f g)"
definition modifyJoinVotes where "modifyJoinVotes = modifies joinVotes_update"
definition modifyPublishVotes where "modifyPublishVotes = modifies publishVotes_update"
definition modifyCurrentClusterState where "modifyCurrentClusterState = modifies currentClusterState_update"

definition "when" :: "bool \<Rightarrow> unit Action \<Rightarrow> unit Action" where "when c a \<equiv> if c then a else return ()"
definition unless :: "bool \<Rightarrow> unit Action \<Rightarrow> unit Action" where "unless \<equiv> when \<circ> Not"

lemma runM_when: "runM (when c a) nd = (if c then runM a nd else (nd, [], ()))"
  by (auto simp add: when_def)
lemma runM_unless: "runM (unless c a) nd = (if c then (nd, [], ()) else runM a nd)"
  by (auto simp add: unless_def when_def)

lemma runM_when_continue: "runM (do { when c a; b }) nd = (if c then runM (do {a;b}) nd else runM b nd)"
  by (auto simp add: when_def)
lemma runM_unless_continue: "runM (do { unless c a; b }) nd = (if c then runM b nd else runM (do {a;b}) nd)"
  by (auto simp add: unless_def when_def)

definition whenCorrectDestination :: "Destination \<Rightarrow> unit Action \<Rightarrow> unit Action"
  where "whenCorrectDestination d go \<equiv> do {
    n <- getCurrentNode;
    when (d \<in> { Broadcast, OneNode n }) go
  }"

lemma runM_whenCorrectDestination:
  "runM (whenCorrectDestination d go) nd = (if d \<in> { Broadcast, OneNode (currentNode nd) } then runM go nd else (nd, [], ()))"
  by (simp add: whenCorrectDestination_def getCurrentNode_def gets_def runM_when)

definition broadcast :: "Message \<Rightarrow> unit Action"
  where "broadcast msg \<equiv> do {
       n <- getCurrentNode;
       send \<lparr> sender = n, destination = Broadcast, payload = msg \<rparr>
    }"

lemma runM_broadcast[simp]: "runM (broadcast msg) nd = (nd, [\<lparr> sender = currentNode nd, destination = Broadcast, payload = msg \<rparr>], ())"
  by (simp add: broadcast_def getCurrentNode_def gets_def send_def)

definition sendTo :: "Node \<Rightarrow> Message \<Rightarrow> unit Action"
  where "sendTo d msg \<equiv> do {
       n <- getCurrentNode;
       send \<lparr> sender = n, destination = OneNode d, payload = msg \<rparr>
    }"

lemma runM_sendTo[simp]: "runM (sendTo d msg) nd = (nd, [\<lparr> sender = currentNode nd, destination = OneNode d, payload = msg \<rparr>], ())"
  by (simp add: sendTo_def getCurrentNode_def gets_def send_def)

definition getLastAcceptedTermInSlot where "getLastAcceptedTermInSlot \<equiv> do {
    lastAcceptedSlot <- getLastAcceptedSlot;
    firstUncommittedSlot <- getFirstUncommittedSlot;
    if lastAcceptedSlot = firstUncommittedSlot
      then getLastAcceptedTerm
      else return None
  }"

definition doStartJoin :: "Node \<Rightarrow> Term \<Rightarrow> unit Action"
  where
    "doStartJoin newMaster newTerm \<equiv> do {
        currentTerm <- getCurrentTerm;
        unless (newTerm \<le> currentTerm) (do {

          setJoinVotes {};
          setElectionWon False;
          setCurrentTerm newTerm;
          setElectionValueForced False;
          setPublishPermitted True;
          setPublishVotes {};

          firstUncommittedSlot <- getFirstUncommittedSlot;
          lastAcceptedTerm <- getLastAcceptedTermInSlot;
          sendTo newMaster (JoinRequest firstUncommittedSlot newTerm lastAcceptedTerm)

        })
      }"

definition doJoinRequestCurrentSlot :: "Node \<Rightarrow> Term option \<Rightarrow> unit Action"
  where
    "doJoinRequestCurrentSlot requestSender requestLastAcceptedTerm \<equiv> do {

        lastAcceptedTerm <- getLastAcceptedTermInSlot;
        electionValueForced <- getElectionValueForced;

        when (requestLastAcceptedTerm = None
               \<or> requestLastAcceptedTerm = lastAcceptedTerm
               \<or> (maxTermOption requestLastAcceptedTerm lastAcceptedTerm = lastAcceptedTerm \<and> electionValueForced)) (do {

          modifyJoinVotes (insert requestSender);
          when (requestLastAcceptedTerm \<noteq> None) (setElectionValueForced True);

          joinVotes <- getJoinVotes;
          currentVotingNodes <- getCurrentVotingNodes;

          let electionWon' = card (joinVotes \<inter> currentVotingNodes) * 2 > card currentVotingNodes;
          setElectionWon electionWon';
          when electionWon' (do {

            publishPermitted <- getPublishPermitted;
            when publishPermitted (do {
              setPublishPermitted False;

              firstUncommittedSlot <- getFirstUncommittedSlot;
              currentTerm <- getCurrentTerm;
              lastAcceptedValue <- getLastAcceptedValue;
              broadcast (PublishRequest firstUncommittedSlot currentTerm lastAcceptedValue)
            })
          })
        })
      }"

definition doJoinRequest :: "Node \<Rightarrow> Slot \<Rightarrow> Term \<Rightarrow> Term option \<Rightarrow> unit Action"
  where
    "doJoinRequest s i t a \<equiv> do {

      firstUncommittedSlot <- getFirstUncommittedSlot;
      unless (firstUncommittedSlot < i) (do {

        currentTerm <- getCurrentTerm;
        when (t = currentTerm) (do {

          if i = firstUncommittedSlot
            then doJoinRequestCurrentSlot s a
            else doJoinRequestCurrentSlot s None
        })
      })
    }"

definition doClientValue :: "Value \<Rightarrow> unit Action"
  where
    "doClientValue x \<equiv> do {

      electionWon <- getElectionWon;
      when electionWon (do {

        publishPermitted <- getPublishPermitted;
        when publishPermitted (do {

          electionValueForced <- getElectionValueForced;
          unless electionValueForced (do {

            setPublishPermitted False;

            currentTerm <- getCurrentTerm;
            firstUncommittedSlot <- getFirstUncommittedSlot;
            broadcast (PublishRequest firstUncommittedSlot currentTerm x)
          })
        })
      })
    }"

definition doPublishRequest :: "Node \<Rightarrow> Slot \<Rightarrow> Term \<Rightarrow> Value \<Rightarrow> unit Action"
  where
    "doPublishRequest s i t x \<equiv> do {

      firstUncommittedSlot <- getFirstUncommittedSlot;
      when (i = firstUncommittedSlot) (do {

        currentTerm <- getCurrentTerm;
        when (t = currentTerm) (do {

          setLastAcceptedSlot i;
          setLastAcceptedTerm (Some t);
          setLastAcceptedValue x;
          sendTo s (PublishResponse i t)
        })
      })
    }"

definition doPublishResponse :: "Node \<Rightarrow> Slot \<Rightarrow> Term \<Rightarrow> unit Action"
  where
    "doPublishResponse s i t \<equiv> do {

      firstUncommittedSlot <- getFirstUncommittedSlot;
      when (i = firstUncommittedSlot) (do {

        currentTerm <- getCurrentTerm;
        when (t = currentTerm) (do {

          currentVotingNodes <- getCurrentVotingNodes;
          when (s \<in> currentVotingNodes) (do {

            modifyPublishVotes (insert s);
            publishVotes <- getPublishVotes;
            currentVotingNodes <- getCurrentVotingNodes;
            when (card publishVotes * 2 > card currentVotingNodes)
              (broadcast (ApplyCommit i t))
          })
        })
      })
    }"

definition doApplyCommit :: "Slot \<Rightarrow> Term \<Rightarrow> unit Action"
  where
    "doApplyCommit i t \<equiv> do {

      firstUncommittedSlot <- getFirstUncommittedSlot;
      when (i = firstUncommittedSlot) (do {

        lastAcceptedTerm <- getLastAcceptedTermInSlot;
        when (Some t = lastAcceptedTerm) (do {

          lastAcceptedValue <- getLastAcceptedValue;
          (case lastAcceptedValue of
            ClusterStateDiff diff
                \<Rightarrow> modifyCurrentClusterState diff
            | Reconfigure votingNodes \<Rightarrow> do {
                   setCurrentVotingNodes (set votingNodes);
                   joinVotes <- getJoinVotes;
                   setElectionWon (card (joinVotes \<inter> (set votingNodes)) * 2 > card (set votingNodes))
                 }
            | NoOp \<Rightarrow> return ());

          setFirstUncommittedSlot (i + 1);
          setPublishPermitted True;
          setElectionValueForced False;
          setPublishVotes {}
        })
      })
    }"

definition doCatchUpRequest :: "Node \<Rightarrow> unit Action"
  where
    "doCatchUpRequest s \<equiv> do {

      firstUncommittedSlot <- getFirstUncommittedSlot;
      currentVotingNodes <- getCurrentVotingNodes;
      currentClusterState <- getCurrentClusterState;

      sendTo s (CatchUpResponse firstUncommittedSlot currentVotingNodes currentClusterState)
    }"

definition doCatchUpResponse :: "Slot \<Rightarrow> Node set \<Rightarrow> ClusterState \<Rightarrow> unit Action"
  where
    "doCatchUpResponse i conf cs \<equiv> do {

      firstUncommittedSlot <- getFirstUncommittedSlot;
      unless (i \<le> firstUncommittedSlot) (do {

        setFirstUncommittedSlot i;
        setPublishPermitted False;
        setElectionValueForced False;
        setPublishVotes {};
        setCurrentVotingNodes conf;
        setCurrentClusterState cs;
        setJoinVotes {};
        setElectionWon False
      })
    }"

definition doReboot :: "unit Action"
  where
    "doReboot \<equiv> modifyNodeData (\<lambda>nd.
                  \<lparr> currentNode = currentNode nd
                  , firstUncommittedSlot = firstUncommittedSlot nd
                  , currentTerm = currentTerm nd
                  , currentVotingNodes = currentVotingNodes nd
                  , currentClusterState = currentClusterState nd
                  , lastAcceptedSlot = lastAcceptedSlot nd
                  , lastAcceptedTerm = lastAcceptedTerm nd
                  , lastAcceptedValue = lastAcceptedValue nd
                  , joinVotes = {}
                  , electionWon = False
                  , electionValueForced = False
                  , publishPermitted = False
                  , publishVotes = {} \<rparr>)"

definition ProcessMessageAction :: "RoutedMessage \<Rightarrow> unit Action"
  where "ProcessMessageAction rm \<equiv> Action (\<lambda>nd. case ProcessMessage nd rm of (nd', messageOption) \<Rightarrow> (nd', case messageOption of None \<Rightarrow> [] | Some m \<Rightarrow> [m], ()))"

definition dispatchMessage :: "RoutedMessage \<Rightarrow> unit Action"
  where "dispatchMessage m \<equiv> whenCorrectDestination (destination m) (case payload m of
          StartJoin t \<Rightarrow> doStartJoin (sender m) t
          | JoinRequest i t a \<Rightarrow> doJoinRequest (sender m) i t a
          | ClientValue x \<Rightarrow> doClientValue x
          | PublishRequest i t x \<Rightarrow> doPublishRequest (sender m) i t x
          | PublishResponse i t \<Rightarrow> doPublishResponse (sender m) i t
          | ApplyCommit i t \<Rightarrow> doApplyCommit i t
          | CatchUpRequest \<Rightarrow> doCatchUpRequest (sender m)
          | CatchUpResponse i conf cs \<Rightarrow> doCatchUpResponse i conf cs
          | Reboot \<Rightarrow> doReboot)"

lemma getLastAcceptedTermInSlot_gets[simp]: "getLastAcceptedTermInSlot = gets lastAcceptedTermInSlot"
  by (intro runM_inject, simp add: gets_def getLastAcceptedTermInSlot_def getLastAcceptedSlot_def
      getFirstUncommittedSlot_def getLastAcceptedTerm_def lastAcceptedTermInSlot_def)

lemma monadic_implementation_is_faithful:
  "dispatchMessage = ProcessMessageAction"
proof (intro ext runM_inject)
  fix rm nd
  show "runM (dispatchMessage rm) nd = runM (ProcessMessageAction rm) nd" (is "?LHS = ?RHS")
  proof (cases "destination rm \<in> {Broadcast, OneNode (currentNode nd)}")
    case False
    thus ?thesis
      unfolding ProcessMessageAction_def dispatchMessage_def whenCorrectDestination_def getCurrentNode_def gets_def ProcessMessage_def Let_def
      by (simp add: runM_when)
  next
    case dest_ok: True

    show ?thesis
    proof (cases "payload rm")
      case (StartJoin t)

      consider
        (a) "t \<le> currentTerm nd"
        | (b) "currentTerm nd < t" "case lastAcceptedTerm nd of None \<Rightarrow> False | Some x \<Rightarrow> t \<le> x"
        | (c) "currentTerm nd < t" "case lastAcceptedTerm nd of None \<Rightarrow> True | Some x \<Rightarrow> x < t"
      proof (cases "t \<le> currentTerm nd")
        case True thus ?thesis by (intro a)
      next
        case 1: False
        with b c show ?thesis
          by (cases "case lastAcceptedTerm nd of None \<Rightarrow> False | Some x \<Rightarrow> t \<le> x", auto, cases "lastAcceptedTerm nd", auto)
      qed

      thus ?thesis
      proof cases
        case a
        with StartJoin dest_ok show ?thesis
          by (simp add: ProcessMessageAction_def dispatchMessage_def runM_whenCorrectDestination ProcessMessage_def Let_def runM_unless
              doStartJoin_def getCurrentTerm_def gets_def getLastAcceptedTerm_def setJoinVotes_def sets_def setCurrentTerm_def setElectionValueForced_def
              setPublishPermitted_def setPublishVotes_def getFirstUncommittedSlot_def handleStartJoin_def ensureCurrentTerm_def setElectionWon_def)
      next
        case b
        with StartJoin dest_ok show ?thesis
          by (cases "lastAcceptedTerm nd ", simp_all add: ProcessMessageAction_def dispatchMessage_def runM_whenCorrectDestination ProcessMessage_def Let_def
              doStartJoin_def getCurrentTerm_def gets_def getLastAcceptedTerm_def setJoinVotes_def sets_def setCurrentTerm_def setElectionValueForced_def runM_unless
              setPublishPermitted_def setPublishVotes_def getFirstUncommittedSlot_def handleStartJoin_def ensureCurrentTerm_def setElectionWon_def lastAcceptedTermInSlot_def)
      next
        case c with StartJoin dest_ok show ?thesis
          by (cases "lastAcceptedTerm nd", simp_all add: ProcessMessageAction_def dispatchMessage_def runM_whenCorrectDestination ProcessMessage_def Let_def
              doStartJoin_def getCurrentTerm_def gets_def getLastAcceptedTerm_def setJoinVotes_def sets_def setCurrentTerm_def setElectionValueForced_def runM_unless
              setPublishPermitted_def setPublishVotes_def getFirstUncommittedSlot_def handleStartJoin_def ensureCurrentTerm_def setElectionWon_def lastAcceptedTermInSlot_def)
      qed

    next
      case (JoinRequest i t a)

      show ?thesis
      proof (cases "firstUncommittedSlot nd < i")
        case True
        with JoinRequest dest_ok show ?thesis
          by (simp add: dispatchMessage_def runM_whenCorrectDestination runM_unless
              doJoinRequest_def gets_def getFirstUncommittedSlot_def ProcessMessage_def
              ProcessMessageAction_def handleJoinRequest_def)
      next
        case False hence le: "i \<le> firstUncommittedSlot nd" by simp

        show ?thesis
        proof (cases "t = currentTerm nd")
          case False
          with JoinRequest dest_ok le show ?thesis
            by (simp add: dispatchMessage_def runM_whenCorrectDestination runM_when runM_unless
                doJoinRequest_def gets_def getFirstUncommittedSlot_def getCurrentTerm_def
                ProcessMessage_def ProcessMessageAction_def handleJoinRequest_def)

        next
          case t: True

          show ?thesis
          proof (cases "i = firstUncommittedSlot nd")
            case False
            with JoinRequest dest_ok le t show ?thesis
              by (simp add: dispatchMessage_def runM_whenCorrectDestination Let_def runM_when_continue
                doJoinRequest_def doJoinRequestCurrentSlot_def runM_when runM_unless
                gets_def getFirstUncommittedSlot_def getCurrentTerm_def getLastAcceptedTerm_def
                getElectionValueForced_def getJoinVotes_def getCurrentVotingNodes_def
                getPublishPermitted_def getLastAcceptedValue_def
                modifies_def modifyJoinVotes_def
                sets_def setElectionWon_def setPublishPermitted_def
                ProcessMessage_def ProcessMessageAction_def handleJoinRequest_def
                addElectionVote_def publishValue_def isQuorum_def majorities_def)
          next
            case True
            with JoinRequest dest_ok le t show ?thesis
              by (simp add: dispatchMessage_def runM_whenCorrectDestination Let_def
                  doJoinRequest_def doJoinRequestCurrentSlot_def
                  runM_unless runM_when runM_when_continue
                  gets_def getFirstUncommittedSlot_def getCurrentTerm_def getLastAcceptedTerm_def
                  getElectionValueForced_def getJoinVotes_def getCurrentVotingNodes_def
                  getPublishPermitted_def getLastAcceptedValue_def
                  modifies_def modifyJoinVotes_def
                  sets_def setElectionWon_def setPublishPermitted_def setElectionValueForced_def
                  ProcessMessage_def ProcessMessageAction_def handleJoinRequest_def
                  addElectionVote_def publishValue_def isQuorum_def majorities_def)
          qed
        qed
      qed

    next
      case (ClientValue x) with dest_ok show ?thesis
        by (simp add: ProcessMessageAction_def dispatchMessage_def runM_whenCorrectDestination
            doClientValue_def gets_def getElectionValueForced_def getElectionWon_def
            runM_unless getPublishPermitted_def setPublishPermitted_def sets_def
            getCurrentTerm_def getFirstUncommittedSlot_def ProcessMessage_def handleClientValue_def
            publishValue_def runM_when)

    next
      case (PublishRequest i t x) with dest_ok show ?thesis
        by (simp add: ProcessMessageAction_def dispatchMessage_def runM_whenCorrectDestination
          doPublishRequest_def gets_def getCurrentTerm_def getFirstUncommittedSlot_def
          sets_def setLastAcceptedTerm_def setLastAcceptedSlot_def setLastAcceptedValue_def
          getCurrentNode_def runM_unless send_def
          ProcessMessage_def handlePublishRequest_def runM_when)

    next
      case (PublishResponse i t) with dest_ok show ?thesis
        by (simp add: ProcessMessageAction_def dispatchMessage_def runM_whenCorrectDestination
          doPublishResponse_def gets_def getCurrentTerm_def getFirstUncommittedSlot_def
          broadcast_def getCurrentNode_def runM_unless send_def
          modifyPublishVotes_def modifies_def getPublishVotes_def getCurrentVotingNodes_def
          runM_when
          ProcessMessage_def handlePublishResponse_def commitIfQuorate_def isQuorum_def majorities_def)

    next
      case (ApplyCommit i t)

      show ?thesis
      proof (cases "lastAcceptedValue nd")
        case NoOp
        with ApplyCommit dest_ok show ?thesis
          by (simp add: ProcessMessageAction_def dispatchMessage_def runM_whenCorrectDestination
            doApplyCommit_def runM_unless runM_when
            gets_def getFirstUncommittedSlot_def getLastAcceptedTerm_def getLastAcceptedValue_def
            sets_def setFirstUncommittedSlot_def setLastAcceptedValue_def setLastAcceptedTerm_def
            setPublishPermitted_def setElectionValueForced_def setPublishVotes_def
            ProcessMessage_def handleApplyCommit_def applyAcceptedValue_def)
      next
        case Reconfigure
        with ApplyCommit dest_ok show ?thesis
          by (simp add: ProcessMessageAction_def dispatchMessage_def runM_whenCorrectDestination
            doApplyCommit_def runM_unless runM_when
            gets_def getFirstUncommittedSlot_def getLastAcceptedTerm_def getLastAcceptedValue_def
            getJoinVotes_def
            sets_def setFirstUncommittedSlot_def setLastAcceptedValue_def setLastAcceptedTerm_def
            setPublishPermitted_def setElectionValueForced_def setPublishVotes_def
            setCurrentVotingNodes_def setElectionWon_def
            ProcessMessage_def handleApplyCommit_def applyAcceptedValue_def majorities_def)
      next
        case ClusterStateDiff
        with ApplyCommit dest_ok show ?thesis
          by (simp add: ProcessMessageAction_def dispatchMessage_def runM_whenCorrectDestination
            doApplyCommit_def runM_unless runM_when
            gets_def getFirstUncommittedSlot_def getLastAcceptedTerm_def getLastAcceptedValue_def
            sets_def setFirstUncommittedSlot_def setLastAcceptedValue_def setLastAcceptedTerm_def
            modifies_def modifyCurrentClusterState_def
            setPublishPermitted_def setElectionValueForced_def setPublishVotes_def
            ProcessMessage_def handleApplyCommit_def applyAcceptedValue_def)
      qed

    next
      case CatchUpRequest
      with dest_ok show ?thesis
        by (simp add: ProcessMessageAction_def dispatchMessage_def runM_whenCorrectDestination
          doCatchUpRequest_def
          gets_def getFirstUncommittedSlot_def getCurrentVotingNodes_def getCurrentClusterState_def
          ProcessMessage_def handleCatchUpRequest_def)

    next
      case (CatchUpResponse i conf cs)
      with dest_ok show ?thesis
        by (simp add: ProcessMessageAction_def dispatchMessage_def runM_whenCorrectDestination
            doCatchUpResponse_def gets_def getFirstUncommittedSlot_def
            sets_def setFirstUncommittedSlot_def setLastAcceptedValue_def setLastAcceptedTerm_def
            setPublishPermitted_def setElectionValueForced_def setPublishVotes_def
            setCurrentVotingNodes_def setCurrentClusterState_def setJoinVotes_def
            setElectionWon_def runM_unless
            ProcessMessage_def handleCatchUpResponse_def)

    next
      case Reboot
      with dest_ok show ?thesis
        by (simp add: ProcessMessageAction_def dispatchMessage_def runM_whenCorrectDestination
          doReboot_def ProcessMessage_def handleReboot_def)
    qed
  qed
qed

end
