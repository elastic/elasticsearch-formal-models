theory Monadic
  imports Implementation "~~/src/HOL/Library/Monad_Syntax"
begin

datatype Exception = IllegalArgumentException

datatype ('e,'a) Result = Success 'a | Exception 'e

datatype 'a Action = Action "NodeData \<Rightarrow> (NodeData * RoutedMessage list * (Exception,'a) Result)"

definition runM :: "'a Action \<Rightarrow> NodeData \<Rightarrow> (NodeData * RoutedMessage list * (Exception,'a) Result)"
  where "runM ma \<equiv> case ma of Action unwrapped_ma \<Rightarrow> unwrapped_ma"

lemma runM_Action[simp]: "runM (Action f) = f" by (simp add: runM_def)
lemma runM_inject[intro]: "(\<And>nd. runM ma nd = runM mb nd) \<Longrightarrow> ma = mb" by (cases ma, cases mb, auto simp add: runM_def)

definition return :: "'a \<Rightarrow> 'a Action" where "return a \<equiv> Action (\<lambda> nd. (nd, [], Success a))"

lemma runM_return[simp]: "runM (return a) nd = (nd, [], Success a)" unfolding runM_def return_def by simp

definition Action_bind :: "'a Action \<Rightarrow> ('a \<Rightarrow> 'b Action) \<Rightarrow> 'b Action"
  where "Action_bind ma mf \<equiv> Action (\<lambda> nd0. case runM ma nd0 of
      (nd1, msgs1, result1) \<Rightarrow> (case result1 of
          Exception e \<Rightarrow> (nd1, msgs1, Exception e)
        | Success a \<Rightarrow> (case runM (mf a) nd1 of
             (nd2, msgs2, result2) \<Rightarrow> (nd2, msgs1 @ msgs2, result2))))"

adhoc_overloading bind Action_bind

lemma runM_bind: "runM (a \<bind> f) nd0 = (case runM a nd0 of (nd1, msgs1, result1) \<Rightarrow> (case result1 of Exception e \<Rightarrow> (nd1, msgs1, Exception e) | Success b \<Rightarrow> (case runM (f b) nd1 of (nd2, msgs2, c) \<Rightarrow> (nd2, msgs1@msgs2, c))))"
  unfolding Action_bind_def by auto

lemma return_bind[simp]: "do { a' <- return a; f a' } = f a"
  apply (intro runM_inject) by (simp add: runM_bind)
lemma bind_return[simp]: "do { a' <- f; return a' } = f"
proof (intro runM_inject)
  fix nd
  obtain nd1 msgs1 result1 where result1: "runM f nd = (nd1, msgs1, result1)" by (cases "runM f nd", blast)
  show "runM (f \<bind> return) nd = runM f nd"
    by (cases result1, simp_all add: runM_bind result1)
qed

lemma bind_bind_assoc[simp]:
  fixes f :: "'a Action"
  shows "do { b <- do { a <- f; g a }; h b } = do { a <- f; b <- g a; h b }" (is "?LHS = ?RHS")
proof (intro runM_inject)
  fix nd0
  show "runM ?LHS nd0 = runM ?RHS nd0"
  proof (cases "runM f nd0")
    case fields1: (fields nd1 msgs1 result1)
    show ?thesis
    proof (cases result1)
      case Exception show ?thesis by (simp add: runM_bind fields1 Exception)
    next
      case Success1: (Success b)
      show ?thesis
      proof (cases "runM (g b) nd1")
        case fields2: (fields nd2 msgs2 result2)
        show ?thesis
        proof (cases result2)
          case Exception show ?thesis by (simp add: runM_bind fields1 fields2 Success1 Exception)
        next
          case Success2: (Success c)
          show ?thesis
            by (cases "runM (h c) nd2", simp add: runM_bind fields1 Success1 fields2 Success2)
        qed
      qed
    qed
  qed
qed

definition getNodeData :: "NodeData Action" where "getNodeData \<equiv> Action (\<lambda>nd. (nd, [], Success nd))"
definition setNodeData :: "NodeData \<Rightarrow> unit Action" where "setNodeData nd \<equiv> Action (\<lambda>_. (nd, [], Success ()))"

lemma runM_getNodeData[simp]: "runM  getNodeData      nd = (nd,  [], Success nd)" by (simp add: runM_def getNodeData_def)
lemma runM_setNodeData[simp]: "runM (setNodeData nd') nd = (nd', [], Success ())" by (simp add: runM_def setNodeData_def)

lemma runM_getNodeData_continue[simp]: "runM (do { nd' <- getNodeData; f nd' }) nd = runM (f nd) nd" by (simp add: runM_bind)
lemma runM_setNodeData_continue[simp]: "runM (do { setNodeData nd'; f }) nd = runM f nd'" by (simp add: runM_bind)

definition modifyNodeData :: "(NodeData \<Rightarrow> NodeData) \<Rightarrow> unit Action" where "modifyNodeData f = getNodeData \<bind> (setNodeData \<circ> f)"

lemma runM_modifyNodeData[simp]: "runM (modifyNodeData f) nd = (f nd, [], Success ())" by (simp add: modifyNodeData_def runM_bind)
lemma runM_modifyNodeData_continue[simp]: "runM (do { modifyNodeData f; a }) nd = runM a (f nd)" by (simp add: runM_bind)

definition tell :: "RoutedMessage list \<Rightarrow> unit Action" where "tell rms \<equiv> Action (\<lambda>nd. (nd, rms, Success ()))"
lemma runM_tell[simp]: "runM (tell rms) nd = (nd, rms, Success ())" by (simp add: runM_def tell_def)
lemma runM_tell_contiue[simp]: "runM (do { tell rms; a }) nd = (let (nd, rms', x) = runM a nd in (nd, rms@rms', x))" by (simp add: runM_bind tell_def)

definition send :: "RoutedMessage \<Rightarrow> unit Action" where "send rm = tell [rm]"

definition throw :: "Exception \<Rightarrow> 'a Action" where "throw e = Action (\<lambda>nd. (nd, [], Exception e))"
lemma runM_throw[simp]: "runM (throw e) nd = (nd, [], Exception e)" by (simp add: runM_def throw_def)
lemma throw_continue[simp]: "do { throw e; a } = throw e" by (intro runM_inject, simp add: runM_bind)

definition catch :: "'a Action \<Rightarrow> (Exception \<Rightarrow> 'a Action) \<Rightarrow> 'a Action"
  where "catch go onException = Action (\<lambda>nd0. case runM go nd0 of (nd1, rms1, result1) \<Rightarrow> (case result1 of Success _ \<Rightarrow> (nd1, rms1, result1) | Exception e \<Rightarrow> runM (tell rms1 \<then> onException e) nd1))"
lemma catch_throw[simp]: "catch (throw e) handle = handle e" by (intro runM_inject, simp add: catch_def)
lemma catch_return[simp]: "catch (return a) handle = return a" by (intro runM_inject, simp add: catch_def)

lemma catch_getNodeData[simp]: "catch getNodeData handle = getNodeData" by (intro runM_inject, simp add: catch_def)
lemma catch_getNodeData_continue[simp]: "catch (do { nd <- getNodeData; f nd }) handle = do { nd <- getNodeData; catch (f nd) handle }" by (intro runM_inject, simp add: catch_def)
lemma catch_setNodeData[simp]: "catch (setNodeData nd) handle = setNodeData nd" by (intro runM_inject, simp add: catch_def)
lemma catch_setNodeData_continue[simp]: "catch (do { setNodeData nd; f }) handle = do { setNodeData nd; catch f handle }" by (intro runM_inject, simp add: catch_def)
lemma catch_modifyNodeData[simp]: "catch (modifyNodeData f) handle = modifyNodeData f" by (intro runM_inject, simp add: catch_def)
lemma catch_modifyNodeData_continue[simp]: "catch (do { modifyNodeData f; g }) handle = do { modifyNodeData f; catch g handle }" by (intro runM_inject, simp add: catch_def)
lemma catch_tell[simp]: "catch (tell rms) handle = tell rms" by (intro runM_inject, simp add: catch_def)
lemma catch_tell_continue[simp]: "catch (do { tell rms; f }) handle = do { tell rms; catch f handle }"
proof (intro runM_inject)
  fix nd0
  show "runM (catch (do { tell rms; f }) handle) nd0 = runM (do { tell rms; catch f handle }) nd0"
  proof (cases "runM f nd0")
    case fields1: (fields nd1 msgs1 result1)
    show ?thesis
    proof (cases result1)
      case (Exception e) show ?thesis by (cases "runM (handle e) nd1", simp add: catch_def fields1 Exception)
    next
      case Success1: (Success b)
      show ?thesis
        by (simp add: catch_def fields1 Success1)
    qed
  qed
qed
lemma catch_send[simp]: "catch (send rm) handle = send rm" by (simp add: send_def)
lemma catch_send_continue[simp]: "catch (do { send rm; f }) handle = do { send rm; catch f handle }" by (simp add: send_def)

definition gets :: "(NodeData \<Rightarrow> 'a) \<Rightarrow> 'a Action" where "gets f \<equiv> do { nd <- getNodeData; return (f nd) }"
definition getCurrentClusterState where "getCurrentClusterState = gets currentClusterState"
definition getCurrentNode where "getCurrentNode = gets currentNode"
definition getCurrentTerm where "getCurrentTerm = gets currentTerm"
definition getCurrentVotingNodes where "getCurrentVotingNodes = gets currentVotingNodes"
definition getElectionValueForced where "getElectionValueForced = gets electionValueForced"
definition getElectionWon where "getElectionWon = gets electionWon"
definition getFirstUncommittedSlot where "getFirstUncommittedSlot = gets firstUncommittedSlot"
definition getJoinVotes where "getJoinVotes = gets joinVotes"
definition getLastAcceptedData where "getLastAcceptedData = gets lastAcceptedData"
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
definition setLastAcceptedData where "setLastAcceptedData = sets lastAcceptedData_update"
definition setPublishPermitted where "setPublishPermitted = sets publishPermitted_update"
definition setPublishVotes where "setPublishVotes = sets publishVotes_update"

definition modifies where "modifies f g = modifyNodeData (f g)"
definition modifyJoinVotes where "modifyJoinVotes = modifies joinVotes_update"
definition modifyPublishVotes where "modifyPublishVotes = modifies publishVotes_update"
definition modifyCurrentClusterState where "modifyCurrentClusterState = modifies currentClusterState_update"

definition "when" :: "bool \<Rightarrow> unit Action \<Rightarrow> unit Action" where "when c a \<equiv> if c then a else return ()"
definition unless :: "bool \<Rightarrow> unit Action \<Rightarrow> unit Action" where "unless \<equiv> when \<circ> Not"

lemma runM_when: "runM (when c a) nd = (if c then runM a nd else (nd, [], Success ()))"
  by (auto simp add: when_def)
lemma runM_unless: "runM (unless c a) nd = (if c then (nd, [], Success ()) else runM a nd)"
  by (auto simp add: unless_def when_def)

lemma runM_when_continue: "runM (do { when c a; b }) nd = (if c then runM (do {a;b}) nd else runM b nd)"
  by (auto simp add: when_def)
lemma runM_unless_continue: "runM (do { unless c a; b }) nd = (if c then runM b nd else runM (do {a;b}) nd)"
  by (auto simp add: unless_def when_def)

lemma catch_when[simp]: "catch (when c a) onException = when c (catch a onException)"
  by (intro runM_inject, simp add: catch_def runM_when)
lemma catch_unless[simp]: "catch (unless c a) onException = unless c (catch a onException)"
  by (intro runM_inject, simp add: catch_def runM_unless)

lemma catch_when_continue[simp]: "catch (do { when c a; b }) onException = (if c then catch (do {a;b}) onException else catch b onException)"
  by (intro runM_inject, simp add: catch_def runM_when_continue)
lemma catch_unless_continue[simp]: "catch (do { unless c a; b }) onException = (if c then catch b onException else catch (do {a;b}) onException)"
  by (intro runM_inject, simp add: catch_def runM_unless_continue)

definition ensureCorrectDestination :: "Destination \<Rightarrow> unit Action"
  where "ensureCorrectDestination d \<equiv> do {
    n <- getCurrentNode;
    when (d \<notin> { Broadcast, OneNode n }) (throw IllegalArgumentException)
  }"

lemma runM_ensureCorrectDestination_continue:
  "runM (do { ensureCorrectDestination d; go }) nd = (if d \<in> { Broadcast, OneNode (currentNode nd) } then runM go nd else (nd, [], Exception IllegalArgumentException))"
  by (simp add: ensureCorrectDestination_def getCurrentNode_def gets_def runM_when_continue)

definition broadcast :: "Message \<Rightarrow> unit Action"
  where "broadcast msg \<equiv> do {
       n <- getCurrentNode;
       send \<lparr> sender = n, destination = Broadcast, payload = msg \<rparr>
    }"

lemma runM_broadcast[simp]: "runM (broadcast msg) nd = (nd, [\<lparr> sender = currentNode nd, destination = Broadcast, payload = msg \<rparr>], Success ())"
  by (simp add: broadcast_def getCurrentNode_def gets_def send_def)

definition sendTo :: "Node \<Rightarrow> Message \<Rightarrow> unit Action"
  where "sendTo d msg \<equiv> do {
       n <- getCurrentNode;
       send \<lparr> sender = n, destination = OneNode d, payload = msg \<rparr>
    }"

lemma runM_sendTo[simp]: "runM (sendTo d msg) nd = (nd, [\<lparr> sender = currentNode nd, destination = OneNode d, payload = msg \<rparr>], Success ())"
  by (simp add: sendTo_def getCurrentNode_def gets_def send_def)

definition ignoringExceptions :: "unit Action \<Rightarrow> unit Action" where "ignoringExceptions go \<equiv> catch go (\<lambda>_. return ())"

definition lt_term_option :: "Term option \<Rightarrow> Term option \<Rightarrow> bool" (infix "<\<^sup>+" 50)
  where "t\<^sub>1 <\<^sup>+ t\<^sub>2 \<equiv> t\<^sub>1 \<noteq> t\<^sub>2 \<and> maxTermOption t\<^sub>1 t\<^sub>2 = t\<^sub>2"

definition gt_term_option :: "Term option \<Rightarrow> Term option \<Rightarrow> bool" (infix ">\<^sup>+" 50)
  where "t\<^sub>1 >\<^sup>+ t\<^sub>2 \<equiv> t\<^sub>2 <\<^sup>+ t\<^sub>1"

lemma lt_None[simp]: "t <\<^sup>+ None = False" by (cases t, simp_all add: lt_term_option_def)
lemma None_lt[simp]: "None <\<^sup>+ t = (t \<noteq> None)" by (cases t, simp_all add: lt_term_option_def)
lemma Some_lt_Some[simp]: "(Some t\<^sub>1 <\<^sup>+ Some t\<^sub>2) = (t\<^sub>1 < t\<^sub>2)" by (auto simp add: lt_term_option_def max_def)

lemma None_gt[simp]: "None >\<^sup>+ t = False"
  and gt_None[simp]: "t >\<^sup>+ None = (t \<noteq> None)"
  and Some_gt_Some[simp]: "(Some t\<^sub>1 >\<^sup>+ Some t\<^sub>2) = (t\<^sub>1 > t\<^sub>2)"
  by (simp_all add: gt_term_option_def)

definition getLastAcceptedTermInSlot :: "Term option Action"
  where
    "getLastAcceptedTermInSlot \<equiv> do {
      lastAcceptedData <- getLastAcceptedData;
      case lastAcceptedData of
          None \<Rightarrow> return None
        | Some lad \<Rightarrow> do {
      firstUncommittedSlot <- getFirstUncommittedSlot;
      return (if ladSlot lad = firstUncommittedSlot
        then Some (ladTerm lad)
        else None)
    }}"

definition doStartJoin :: "Node \<Rightarrow> Term \<Rightarrow> unit Action"
  where
    "doStartJoin newMaster newTerm \<equiv> do {
        currentTerm <- getCurrentTerm;

        when (newTerm \<le> currentTerm) (throw IllegalArgumentException);

        setCurrentTerm newTerm;
        setJoinVotes {};
        setElectionWon False;
        setElectionValueForced False;
        setPublishPermitted True;
        setPublishVotes {};

        firstUncommittedSlot <- getFirstUncommittedSlot;
        lastAcceptedTerm <- getLastAcceptedTermInSlot;
        sendTo newMaster (JoinRequest firstUncommittedSlot newTerm lastAcceptedTerm)

      }"

definition doVote :: "Node \<Rightarrow> Slot \<Rightarrow> Term \<Rightarrow> Term option \<Rightarrow> unit Action"
  where
    "doVote sourceNode voteFirstUncommittedSlot voteTerm voteLastAcceptedTerm \<equiv> do {

      currentTerm <- getCurrentTerm;
      when (voteTerm \<noteq> currentTerm) (throw IllegalArgumentException);

      firstUncommittedSlot <- getFirstUncommittedSlot;
      when (voteFirstUncommittedSlot > firstUncommittedSlot) (throw IllegalArgumentException);

      when (voteFirstUncommittedSlot = firstUncommittedSlot \<and> voteLastAcceptedTerm \<noteq> None) (do {
        lastAcceptedTermInSlot <- getLastAcceptedTermInSlot;
        when (voteLastAcceptedTerm >\<^sup>+ lastAcceptedTermInSlot)
          (throw IllegalArgumentException);
        electionValueForced <- getElectionValueForced;
        when (voteLastAcceptedTerm <\<^sup>+ lastAcceptedTermInSlot \<and> \<not> electionValueForced)
          (throw IllegalArgumentException);
        setElectionValueForced True
      });

      modifyJoinVotes (insert sourceNode);

      joinVotes <- getJoinVotes;
      currentVotingNodes <- getCurrentVotingNodes;

      let electionWon' = card (joinVotes \<inter> currentVotingNodes) * 2 > card currentVotingNodes;
      setElectionWon electionWon';
      when electionWon' (do {
        electionValueForced <- getElectionValueForced;
        publishPermitted <- getPublishPermitted;
        when (publishPermitted \<and> electionValueForced) (do {
          setPublishPermitted False;

          lastAcceptedValue <- gets lastAcceptedValue; (* NB must be present since electionValueForced *)
          broadcast (PublishRequest firstUncommittedSlot currentTerm lastAcceptedValue)
        })
      })
    }"

definition doPublishRequest :: "Node \<Rightarrow> LastAcceptedData \<Rightarrow> unit Action"
  where
    "doPublishRequest sourceNode newAcceptedState \<equiv> do {

      currentTerm <- getCurrentTerm;
      when (ladTerm newAcceptedState \<noteq> currentTerm) (throw IllegalArgumentException);

      firstUncommittedSlot <- getFirstUncommittedSlot;
      when (ladSlot newAcceptedState \<noteq> firstUncommittedSlot) (throw IllegalArgumentException);

      setLastAcceptedData (Some newAcceptedState);
      sendTo sourceNode (PublishResponse (ladSlot newAcceptedState) (ladTerm newAcceptedState))
    }"

record SlotTerm =
  stSlot :: Slot
  stTerm :: Term

definition ApplyCommitFromSlotTerm :: "SlotTerm \<Rightarrow> Message"
  where "ApplyCommitFromSlotTerm st = ApplyCommit (stSlot st) (stTerm st)"

definition doPublishResponse :: "Node \<Rightarrow> SlotTerm \<Rightarrow> unit Action"
  where
    "doPublishResponse sourceNode slotTerm \<equiv> do {

      currentTerm <- getCurrentTerm;
      when (stTerm slotTerm \<noteq> currentTerm) (throw IllegalArgumentException);

      firstUncommittedSlot <- getFirstUncommittedSlot;
      when (stSlot slotTerm \<noteq> firstUncommittedSlot) (throw IllegalArgumentException);

      modifyPublishVotes (insert sourceNode);
      publishVotes <- getPublishVotes;
      currentVotingNodes <- getCurrentVotingNodes;
      when (card (publishVotes \<inter> currentVotingNodes) * 2 > card currentVotingNodes)
        (broadcast (ApplyCommitFromSlotTerm slotTerm))
    }"

definition doCommit :: "SlotTerm \<Rightarrow> unit Action"
  where
    "doCommit slotTerm \<equiv> do {

      lastAcceptedTermInSlot <- getLastAcceptedTermInSlot;
      when (Some (stTerm slotTerm) \<noteq> lastAcceptedTermInSlot) (throw IllegalArgumentException);

      firstUncommittedSlot <- getFirstUncommittedSlot;
      when (stSlot slotTerm \<noteq> firstUncommittedSlot) (throw IllegalArgumentException);

      lastAcceptedValue <- gets lastAcceptedValue;  (* NB must be not None since lastAcceptedTerm = Some t *)
      (case lastAcceptedValue of
        ClusterStateDiff diff
            \<Rightarrow> modifyCurrentClusterState diff
        | Reconfigure votingNodes \<Rightarrow> do {
               setCurrentVotingNodes (set votingNodes);
               joinVotes <- getJoinVotes;
               setElectionWon (card (joinVotes \<inter> (set votingNodes)) * 2 > card (set votingNodes))
             }
        | NoOp \<Rightarrow> return ());

      setFirstUncommittedSlot (firstUncommittedSlot + 1);
      setPublishPermitted True;
      setElectionValueForced False;
      setPublishVotes {}
    }"

definition generateCatchup :: "Node \<Rightarrow> unit Action"
  where
    "generateCatchup sourceNode \<equiv> do {

      firstUncommittedSlot <- getFirstUncommittedSlot;
      currentVotingNodes <- getCurrentVotingNodes;
      currentClusterState <- getCurrentClusterState;

      sendTo sourceNode (CatchUpResponse firstUncommittedSlot currentVotingNodes currentClusterState)
    }"

definition applyCatchup :: "Slot \<Rightarrow> Node set \<Rightarrow> ClusterState \<Rightarrow> unit Action"
  where
    "applyCatchup catchUpSlot catchUpConfiguration catchUpState \<equiv> do {

      firstUncommittedSlot <- getFirstUncommittedSlot;
      when (catchUpSlot \<le> firstUncommittedSlot) (throw IllegalArgumentException);

      setFirstUncommittedSlot catchUpSlot;
      setCurrentVotingNodes catchUpConfiguration;
      setCurrentClusterState catchUpState;

      setElectionValueForced False;
      setJoinVotes {};
      setElectionWon False;

      setPublishVotes {};
      setPublishPermitted False
    }"

definition doClientValue :: "Value \<Rightarrow> unit Action"
  where
    "doClientValue x \<equiv> do {

      electionWon <- getElectionWon;
      when (\<not> electionWon) (throw IllegalArgumentException);

      publishPermitted <- getPublishPermitted;
      when (\<not> publishPermitted) (throw IllegalArgumentException);

      electionValueForced <- getElectionValueForced;
      when electionValueForced (throw IllegalArgumentException);

      setPublishPermitted False;

      currentTerm <- getCurrentTerm;
      firstUncommittedSlot <- getFirstUncommittedSlot;
      broadcast (PublishRequest firstUncommittedSlot currentTerm x)
    }"

definition doReboot :: "unit Action"
  where
    "doReboot \<equiv> modifyNodeData (\<lambda>nd.
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
                  , publishVotes = {} \<rparr>)"

definition ProcessMessageAction :: "RoutedMessage \<Rightarrow> unit Action"
  where "ProcessMessageAction rm \<equiv> Action (\<lambda>nd. case ProcessMessage nd rm of (nd', messageOption) \<Rightarrow> (nd', case messageOption of None \<Rightarrow> [] | Some m \<Rightarrow> [m], Success ()))"

definition dispatchMessageInner :: "RoutedMessage \<Rightarrow> unit Action"
  where "dispatchMessageInner m \<equiv> case payload m of
          StartJoin t \<Rightarrow> doStartJoin (sender m) t
          | JoinRequest i t a \<Rightarrow> doVote (sender m) i t a
          | ClientValue x \<Rightarrow> doClientValue x
          | PublishRequest i t x \<Rightarrow> doPublishRequest (sender m) \<lparr> ladSlot = i, ladTerm = t, ladValue = x \<rparr>
          | PublishResponse i t \<Rightarrow> doPublishResponse (sender m) \<lparr> stSlot = i, stTerm = t \<rparr>
          | ApplyCommit i t \<Rightarrow> doCommit \<lparr> stSlot = i, stTerm = t \<rparr>
          | CatchUpRequest \<Rightarrow> generateCatchup (sender m)
          | CatchUpResponse i conf cs \<Rightarrow> applyCatchup i conf cs
          | Reboot \<Rightarrow> doReboot"

definition dispatchMessage :: "RoutedMessage \<Rightarrow> unit Action"
  where "dispatchMessage m \<equiv> ignoringExceptions (do {
      ensureCorrectDestination (destination m);
      dispatchMessageInner m
    })"

lemma getLastAcceptedTermInSlot_gets[simp]: "getLastAcceptedTermInSlot = gets lastAcceptedTermInSlot"
proof (intro runM_inject)
  fix nd
  show "runM getLastAcceptedTermInSlot nd = runM (gets lastAcceptedTermInSlot) nd"
    by (cases "lastAcceptedData nd", simp_all add: gets_def getLastAcceptedTermInSlot_def getLastAcceptedData_def
        getFirstUncommittedSlot_def lastAcceptedTermInSlot_def lastAcceptedTerm_def lastAcceptedSlot_def)
qed

lemma monadic_implementation_is_faithful:
  "dispatchMessage = ProcessMessageAction"
proof (intro ext runM_inject)
  fix rm nd
  show "runM (dispatchMessage rm) nd = runM (ProcessMessageAction rm) nd" (is "?LHS = ?RHS")
  proof (cases "destination rm \<in> {Broadcast, OneNode (currentNode nd)}")
    case False

    hence 1: "\<And>f. runM (do { ensureCorrectDestination (destination rm); f }) nd = (nd, [], Exception IllegalArgumentException)"
      by (simp add: runM_ensureCorrectDestination_continue)

    from False
    show ?thesis
      unfolding ProcessMessageAction_def dispatchMessage_def
      by (simp add: ignoringExceptions_def catch_def 1 ProcessMessage_def)
  next
    case dest_ok: True

    hence 1: "runM (dispatchMessage rm) nd = runM (ignoringExceptions (dispatchMessageInner rm)) nd"
      by (simp add: dispatchMessage_def ignoringExceptions_def catch_def runM_ensureCorrectDestination_continue)

    also have "... = runM (ProcessMessageAction rm) nd" (is "?LHS = ?RHS")
    proof (cases "payload rm")
      case (StartJoin t)

      have "?LHS = runM (ignoringExceptions (doStartJoin (sender rm) t)) nd" (is "_ = ?STEP")
        by (simp add: dispatchMessageInner_def StartJoin)

      also consider
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

      hence "?STEP = ?RHS"
      proof cases
        case a
        thus ?thesis
          by (simp add: StartJoin ProcessMessageAction_def dispatchMessage_def ProcessMessage_def Let_def runM_unless
              doStartJoin_def getCurrentTerm_def gets_def setJoinVotes_def sets_def setCurrentTerm_def setElectionValueForced_def
              setPublishPermitted_def setPublishVotes_def getFirstUncommittedSlot_def handleStartJoin_def ensureCurrentTerm_def setElectionWon_def
              ignoringExceptions_def catch_def runM_when_continue)
      next
        case b
        with StartJoin dest_ok show ?thesis
          by (cases "lastAcceptedTerm nd ", simp_all add: ProcessMessageAction_def dispatchMessage_def ProcessMessage_def Let_def
              doStartJoin_def getCurrentTerm_def gets_def setJoinVotes_def sets_def setCurrentTerm_def setElectionValueForced_def runM_unless lastAcceptedTerm_def lastAcceptedSlot_def
              setPublishPermitted_def setPublishVotes_def getFirstUncommittedSlot_def handleStartJoin_def ensureCurrentTerm_def setElectionWon_def lastAcceptedTermInSlot_def
              ignoringExceptions_def catch_def runM_when_continue)
      next
        case c with StartJoin dest_ok show ?thesis
          by (cases "lastAcceptedTerm nd", simp_all add: ProcessMessageAction_def dispatchMessage_def ProcessMessage_def Let_def
              doStartJoin_def getCurrentTerm_def gets_def setJoinVotes_def sets_def setCurrentTerm_def setElectionValueForced_def runM_unless lastAcceptedTerm_def lastAcceptedSlot_def
              setPublishPermitted_def setPublishVotes_def getFirstUncommittedSlot_def handleStartJoin_def ensureCurrentTerm_def setElectionWon_def lastAcceptedTermInSlot_def
              ignoringExceptions_def catch_def runM_when_continue)
      qed

      finally show ?thesis by simp

    next
      case (JoinRequest i t a)

      have "?LHS = runM (ignoringExceptions (doVote (sender rm) i t a)) nd" (is "_ = ?STEP")
        by (simp add: dispatchMessageInner_def JoinRequest)

      also have "... = ?RHS"
      proof (cases "firstUncommittedSlot nd < i")
        case True
        with JoinRequest dest_ok show ?thesis
          by (simp add: dispatchMessage_def runM_unless
              doVote_def gets_def getFirstUncommittedSlot_def ProcessMessage_def
              ProcessMessageAction_def handleJoinRequest_def ignoringExceptions_def getCurrentTerm_def)
      next
        case False hence le: "i \<le> firstUncommittedSlot nd" by simp

        show ?thesis
        proof (cases "t = currentTerm nd")
          case False
          with JoinRequest dest_ok le show ?thesis
            by (simp add: dispatchMessage_def runM_when runM_unless
                doVote_def gets_def getFirstUncommittedSlot_def getCurrentTerm_def
                ProcessMessage_def ProcessMessageAction_def handleJoinRequest_def ignoringExceptions_def)

        next
          case t: True

          show ?thesis
          proof (cases "i = firstUncommittedSlot nd")
            case False
            with JoinRequest dest_ok le t show ?thesis
              by (simp add: dispatchMessage_def Let_def runM_when_continue
                  doVote_def runM_when runM_unless
                  gets_def getFirstUncommittedSlot_def getCurrentTerm_def
                  getElectionValueForced_def getJoinVotes_def getCurrentVotingNodes_def
                  getPublishPermitted_def ignoringExceptions_def broadcast_def getCurrentNode_def
                  modifies_def modifyJoinVotes_def send_def
                  sets_def setElectionWon_def setPublishPermitted_def lastAcceptedValue_def
                  ProcessMessage_def ProcessMessageAction_def handleJoinRequest_def
                  addElectionVote_def publishValue_def isQuorum_def majorities_def)
          next
            case i: True
            show ?thesis
            proof (cases a)
              case a: None

              show ?thesis
              proof (cases "isQuorum nd (insert (sender rm) (joinVotes nd))")
                case not_quorum: False
                hence not_quorum_card: "\<not> card (currentVotingNodes nd) < card (insert (sender rm) (joinVotes nd) \<inter> currentVotingNodes nd) * 2"
                  by (simp add: isQuorum_def majorities_def)

                have "?STEP = (nd\<lparr>electionWon := False, joinVotes := insert (sender rm) (joinVotes nd)\<rparr>, [], Success ())"
                  by (simp add: ignoringExceptions_def i t a doVote_def catch_def
                      gets_def getCurrentTerm_def runM_when_continue getFirstUncommittedSlot_def
                      getElectionValueForced_def modifyJoinVotes_def modifies_def getJoinVotes_def
                      getCurrentVotingNodes_def Let_def setElectionWon_def sets_def runM_when
                      not_quorum_card)

                also from dest_ok have "... = ?RHS"
                  by (simp add: ProcessMessageAction_def ProcessMessage_def JoinRequest handleJoinRequest_def
                      i t a addElectionVote_def not_quorum publishValue_def Let_def)

                finally show ?thesis .

              next
                case quorum: True
                hence quorum_card: "card (currentVotingNodes nd) < card (insert (sender rm) (joinVotes nd) \<inter> currentVotingNodes nd) * 2"
                  by (simp add: isQuorum_def majorities_def)

                show ?thesis
                proof (cases "publishPermitted nd \<and> electionValueForced nd")
                  case False

                  hence "?STEP = (nd\<lparr>electionWon := True, joinVotes := insert (sender rm) (joinVotes nd)\<rparr>, [], Success ())"
                    by (auto simp add: ignoringExceptions_def i t a doVote_def catch_def
                        gets_def getCurrentTerm_def runM_when_continue getFirstUncommittedSlot_def
                        getElectionValueForced_def modifyJoinVotes_def modifies_def getJoinVotes_def
                        getCurrentVotingNodes_def Let_def setElectionWon_def sets_def runM_when
                        quorum_card getPublishPermitted_def)

                  also from False dest_ok have "... = ?RHS"
                    by (simp add: ProcessMessageAction_def ProcessMessage_def JoinRequest handleJoinRequest_def
                        i t a addElectionVote_def quorum publishValue_def Let_def)

                  finally show ?thesis .

                next
                  case True

                  hence "?STEP = (nd\<lparr>electionWon := True, publishPermitted := False,
                                    joinVotes := insert (sender rm) (joinVotes nd)\<rparr>,
                                [\<lparr>sender = currentNode nd, destination = Broadcast,
                                  payload = PublishRequest (firstUncommittedSlot nd) (currentTerm nd)
                                                           (lastAcceptedValue nd) \<rparr>], Success ())"
                    by (auto simp add: ignoringExceptions_def i t a doVote_def catch_def
                        gets_def getCurrentTerm_def runM_when_continue getFirstUncommittedSlot_def
                        getElectionValueForced_def modifyJoinVotes_def modifies_def getJoinVotes_def
                        getCurrentVotingNodes_def Let_def setElectionWon_def sets_def runM_when
                        quorum_card getPublishPermitted_def setPublishPermitted_def lastAcceptedValue_def)

                  also from True dest_ok have "... = ?RHS"
                    by (simp add: ProcessMessageAction_def ProcessMessage_def JoinRequest handleJoinRequest_def
                        i t a addElectionVote_def quorum publishValue_def Let_def lastAcceptedValue_def)

                  finally show ?thesis .

                qed
              qed

            next
              case a: (Some voteLastAcceptedTerm)

              show ?thesis
              proof (cases "lastAcceptedTermInSlot nd")
                case lat: None

                have "?STEP = (nd, [], Success ())"
                  by (auto simp add: ignoringExceptions_def i t a lat doVote_def catch_def
                      gets_def getCurrentTerm_def runM_when_continue getFirstUncommittedSlot_def)

                also from dest_ok have "... = ?RHS"
                  by (simp add: ProcessMessageAction_def ProcessMessage_def JoinRequest handleJoinRequest_def
                      i t a lat)

                finally show ?thesis .

              next
                case lat: (Some nodeLastAcceptedTerm)

                consider (voteTooNew) "voteLastAcceptedTerm > nodeLastAcceptedTerm"
                  | (voteOlderButNotForced) "voteLastAcceptedTerm < nodeLastAcceptedTerm" "\<not> electionValueForced nd"
                  | (voteMatchesNode) "voteLastAcceptedTerm = nodeLastAcceptedTerm"
                  | (voteOlderAndForced) "voteLastAcceptedTerm < nodeLastAcceptedTerm" "electionValueForced nd"
                  using nat_neq_iff by blast

                then show ?thesis
                proof cases
                  case voteTooNew

                  hence "?STEP = (nd, [], Success ())"
                    by (simp add: ignoringExceptions_def i t a lat doVote_def catch_def
                        gets_def getCurrentTerm_def runM_when_continue getFirstUncommittedSlot_def)

                  also from voteTooNew dest_ok have "... = ?RHS"
                    by (simp add: ProcessMessageAction_def ProcessMessage_def JoinRequest handleJoinRequest_def
                        i t a lat max_def)

                  finally show ?thesis .

                next
                  case voteOlderButNotForced

                  hence "?STEP = (nd, [], Success ())"
                    by (simp add: ignoringExceptions_def i t a lat doVote_def catch_def
                        gets_def getCurrentTerm_def runM_when_continue getFirstUncommittedSlot_def
                        getElectionValueForced_def)

                  also from voteOlderButNotForced dest_ok have "... = ?RHS"
                    by (simp add: ProcessMessageAction_def ProcessMessage_def JoinRequest handleJoinRequest_def
                        i t a lat max_def)

                  finally show ?thesis .

                next
                  case voteMatchesNode

                  show ?thesis
                  proof (cases "isQuorum nd (insert (sender rm) (joinVotes nd))")
                    case not_quorum: False
                    hence not_quorum_card: "\<not> card (currentVotingNodes nd) < card (insert (sender rm) (joinVotes nd) \<inter> currentVotingNodes nd) * 2"
                      by (simp add: isQuorum_def majorities_def)

                    from voteMatchesNode
                    have "?STEP = (nd\<lparr>electionWon := False, electionValueForced := True,
                                    joinVotes := insert (sender rm) (joinVotes nd)\<rparr>, [], Success ())"
                      by (simp add: ignoringExceptions_def i t a lat doVote_def catch_def
                          gets_def getCurrentTerm_def runM_when_continue getFirstUncommittedSlot_def
                          getElectionValueForced_def modifyJoinVotes_def modifies_def getJoinVotes_def
                          getCurrentVotingNodes_def Let_def setElectionWon_def sets_def runM_when
                          not_quorum_card setElectionValueForced_def)

                    also from dest_ok voteMatchesNode have "... = ?RHS"
                      by (simp add: ProcessMessageAction_def ProcessMessage_def JoinRequest handleJoinRequest_def
                          i t a lat max_def addElectionVote_def not_quorum publishValue_def Let_def)

                    finally show ?thesis .

                  next
                    case quorum: True
                    hence quorum_card: "card (currentVotingNodes nd) < card (insert (sender rm) (joinVotes nd) \<inter> currentVotingNodes nd) * 2"
                      by (simp add: isQuorum_def majorities_def)

                    show ?thesis
                    proof (cases "publishPermitted nd")
                      case False

                      with voteMatchesNode
                      have "?STEP = (nd\<lparr>electionWon := True, electionValueForced := True,
                                    joinVotes := insert (sender rm) (joinVotes nd)\<rparr>, [], Success ())"
                        by (simp add: ignoringExceptions_def i t a lat doVote_def catch_def
                            gets_def getCurrentTerm_def runM_when_continue getFirstUncommittedSlot_def
                            getElectionValueForced_def modifyJoinVotes_def modifies_def getJoinVotes_def
                            getCurrentVotingNodes_def Let_def setElectionWon_def sets_def runM_when
                            quorum_card getPublishPermitted_def setElectionValueForced_def setPublishPermitted_def)

                      also from False dest_ok have "... = ?RHS"
                        by (simp add: ProcessMessageAction_def ProcessMessage_def JoinRequest handleJoinRequest_def
                            i t a lat voteMatchesNode addElectionVote_def quorum publishValue_def Let_def)

                      finally show ?thesis .

                    next
                      case True

                      hence "?STEP = (nd\<lparr>electionWon := True, publishPermitted := False, electionValueForced := True,
                                    joinVotes := insert (sender rm) (joinVotes nd)\<rparr>,
                                [\<lparr>sender = currentNode nd, destination = Broadcast,
                                  payload = PublishRequest (firstUncommittedSlot nd) (currentTerm nd)
                                                           (lastAcceptedValue nd) \<rparr>], Success ())"
                        by (auto simp add: ignoringExceptions_def i t a lat voteMatchesNode doVote_def catch_def
                            gets_def getCurrentTerm_def runM_when_continue getFirstUncommittedSlot_def
                            getElectionValueForced_def modifyJoinVotes_def modifies_def getJoinVotes_def
                            getCurrentVotingNodes_def Let_def setElectionWon_def sets_def runM_when
                            quorum_card getPublishPermitted_def setPublishPermitted_def lastAcceptedValue_def
                            setElectionValueForced_def)

                      also from True dest_ok have "... = ?RHS"
                        by (simp add: ProcessMessageAction_def ProcessMessage_def JoinRequest handleJoinRequest_def
                            i t a lat voteMatchesNode addElectionVote_def quorum publishValue_def Let_def lastAcceptedValue_def)

                      finally show ?thesis .

                    qed
                  qed

                next
                  case voteOlderAndForced

                  show ?thesis
                  proof (cases "isQuorum nd (insert (sender rm) (joinVotes nd))")
                    case not_quorum: False
                    hence not_quorum_card: "\<not> card (currentVotingNodes nd) < card (insert (sender rm) (joinVotes nd) \<inter> currentVotingNodes nd) * 2"
                      by (simp add: isQuorum_def majorities_def)

                    from voteOlderAndForced
                    have "?STEP = (nd\<lparr>electionWon := False, electionValueForced := True,
                                    joinVotes := insert (sender rm) (joinVotes nd)\<rparr>, [], Success ())"
                      by (simp add: ignoringExceptions_def i t a lat doVote_def catch_def
                          gets_def getCurrentTerm_def runM_when_continue getFirstUncommittedSlot_def
                          getElectionValueForced_def modifyJoinVotes_def modifies_def getJoinVotes_def
                          getCurrentVotingNodes_def Let_def setElectionWon_def sets_def runM_when
                          not_quorum_card setElectionValueForced_def)

                    also from dest_ok voteOlderAndForced have "... = ?RHS"
                      by (simp add: ProcessMessageAction_def ProcessMessage_def JoinRequest handleJoinRequest_def
                          i t a lat max_def addElectionVote_def not_quorum publishValue_def Let_def)

                    finally show ?thesis .

                  next
                    case quorum: True
                    hence quorum_card: "card (currentVotingNodes nd) < card (insert (sender rm) (joinVotes nd) \<inter> currentVotingNodes nd) * 2"
                      by (simp add: isQuorum_def majorities_def)

                    show ?thesis
                    proof (cases "publishPermitted nd")
                      case False

                      with voteOlderAndForced
                      have "?STEP = (nd\<lparr>electionWon := True, electionValueForced := True,
                                    joinVotes := insert (sender rm) (joinVotes nd)\<rparr>, [], Success ())"
                        by (simp add: ignoringExceptions_def i t a lat doVote_def catch_def
                            gets_def getCurrentTerm_def runM_when_continue getFirstUncommittedSlot_def
                            getElectionValueForced_def modifyJoinVotes_def modifies_def getJoinVotes_def
                            getCurrentVotingNodes_def Let_def setElectionWon_def sets_def runM_when
                            quorum_card getPublishPermitted_def setElectionValueForced_def setPublishPermitted_def)

                      also from False dest_ok voteOlderAndForced have "... = ?RHS"
                        by (simp add: ProcessMessageAction_def ProcessMessage_def JoinRequest handleJoinRequest_def
                          i t a lat addElectionVote_def quorum publishValue_def Let_def)

                      finally show ?thesis .

                    next
                      case True

                      with voteOlderAndForced
                      have "?STEP = (nd\<lparr>electionWon := True, publishPermitted := False, electionValueForced := True,
                                    joinVotes := insert (sender rm) (joinVotes nd)\<rparr>,
                                [\<lparr>sender = currentNode nd, destination = Broadcast,
                                  payload = PublishRequest (firstUncommittedSlot nd) (currentTerm nd)
                                                           (lastAcceptedValue nd) \<rparr>], Success ())"
                        by (auto simp add: ignoringExceptions_def i t a lat doVote_def catch_def
                            gets_def getCurrentTerm_def runM_when_continue getFirstUncommittedSlot_def
                            getElectionValueForced_def modifyJoinVotes_def modifies_def getJoinVotes_def
                            getCurrentVotingNodes_def Let_def setElectionWon_def sets_def runM_when
                            quorum_card getPublishPermitted_def setPublishPermitted_def lastAcceptedValue_def
                            setElectionValueForced_def)

                      also from True voteOlderAndForced dest_ok have "... = ?RHS"
                        by (simp add: ProcessMessageAction_def ProcessMessage_def JoinRequest handleJoinRequest_def
                            i t a lat addElectionVote_def quorum publishValue_def Let_def lastAcceptedValue_def)

                      finally show ?thesis .

                    qed
                  qed
                qed
              qed
            qed
          qed
        qed
      qed

      finally show ?thesis .

    next
      case (ClientValue x)

      with dest_ok show ?thesis
        by (simp add: ProcessMessageAction_def dispatchMessageInner_def
            doClientValue_def gets_def getElectionValueForced_def getElectionWon_def
            runM_unless getPublishPermitted_def setPublishPermitted_def sets_def
            getCurrentTerm_def getFirstUncommittedSlot_def ProcessMessage_def handleClientValue_def
            publishValue_def runM_when ignoringExceptions_def ClientValue catch_def runM_when_continue)

    next
      case (PublishRequest i t x) with dest_ok show ?thesis
        by (simp add: ProcessMessageAction_def dispatchMessageInner_def
          doPublishRequest_def gets_def getCurrentTerm_def getFirstUncommittedSlot_def
          sets_def setLastAcceptedData_def ignoringExceptions_def catch_def runM_when_continue
          getCurrentNode_def runM_unless send_def
          ProcessMessage_def handlePublishRequest_def runM_when)

    next
      case (PublishResponse i t) with dest_ok show ?thesis
        by (simp add: ProcessMessageAction_def dispatchMessageInner_def
          doPublishResponse_def gets_def getCurrentTerm_def getFirstUncommittedSlot_def
          broadcast_def getCurrentNode_def runM_unless send_def
          modifyPublishVotes_def modifies_def getPublishVotes_def getCurrentVotingNodes_def
          runM_when ignoringExceptions_def catch_def runM_when_continue
          ProcessMessage_def handlePublishResponse_def commitIfQuorate_def isQuorum_def majorities_def
          ApplyCommitFromSlotTerm_def)

    next
      case (ApplyCommit i t)

      show ?thesis
      proof (cases "lastAcceptedValue nd")
        case NoOp
        with ApplyCommit dest_ok show ?thesis
          by (simp add: ProcessMessageAction_def dispatchMessageInner_def
            doCommit_def runM_unless runM_when
            gets_def getFirstUncommittedSlot_def
            sets_def setFirstUncommittedSlot_def
            setPublishPermitted_def setElectionValueForced_def setPublishVotes_def
            ProcessMessage_def handleApplyCommit_def applyAcceptedValue_def
            ignoringExceptions_def catch_def runM_when_continue)
      next
        case Reconfigure
        with ApplyCommit dest_ok show ?thesis
          by (simp add: ProcessMessageAction_def dispatchMessageInner_def
            doCommit_def runM_unless runM_when
            gets_def getFirstUncommittedSlot_def
            getJoinVotes_def
            sets_def setFirstUncommittedSlot_def
            setPublishPermitted_def setElectionValueForced_def setPublishVotes_def
            setCurrentVotingNodes_def setElectionWon_def
            ProcessMessage_def handleApplyCommit_def applyAcceptedValue_def majorities_def
            ignoringExceptions_def catch_def runM_when_continue)
      next
        case ClusterStateDiff
        with ApplyCommit dest_ok show ?thesis
          by (simp add: ProcessMessageAction_def dispatchMessageInner_def
            doCommit_def runM_unless runM_when
            gets_def getFirstUncommittedSlot_def
            sets_def setFirstUncommittedSlot_def
            modifies_def modifyCurrentClusterState_def
            setPublishPermitted_def setElectionValueForced_def setPublishVotes_def
            ProcessMessage_def handleApplyCommit_def applyAcceptedValue_def
            ignoringExceptions_def catch_def runM_when_continue)
      qed

    next
      case CatchUpRequest
      with dest_ok show ?thesis
        by (simp add: ProcessMessageAction_def dispatchMessageInner_def
          generateCatchup_def
          gets_def getFirstUncommittedSlot_def getCurrentVotingNodes_def getCurrentClusterState_def
          ProcessMessage_def handleCatchUpRequest_def ignoringExceptions_def catch_def runM_when_continue)

    next
      case (CatchUpResponse i conf cs)
      with dest_ok show ?thesis
        by (simp add: ProcessMessageAction_def dispatchMessageInner_def
            applyCatchup_def gets_def getFirstUncommittedSlot_def
            sets_def setFirstUncommittedSlot_def
            setPublishPermitted_def setElectionValueForced_def setPublishVotes_def
            setCurrentVotingNodes_def setCurrentClusterState_def setJoinVotes_def
            setElectionWon_def runM_unless
            ProcessMessage_def handleCatchUpResponse_def
            ignoringExceptions_def catch_def runM_when_continue)

    next
      case Reboot
      with dest_ok show ?thesis
        by (simp add: ProcessMessageAction_def dispatchMessageInner_def
            doReboot_def ProcessMessage_def handleReboot_def ignoringExceptions_def catch_def runM_when_continue)
    qed

    finally show ?thesis .
  qed
qed

end
