section \<open>Safety Properties\<close>

text \<open>This section describes the invariants that hold in the system, shows that the implementation
preserves the invariants, and shows that the invariants imply the required safety properties.\<close>

theory Zen
  imports Implementation OneSlot
begin

subsection \<open>Invariants on messages\<close>

text \<open>Firstly, a set of invariants that hold on the set of messages that
have ever been sent, without considering the state of any individual
node.\<close>

fun nat_inductive_def :: "'a \<Rightarrow> (nat \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> nat \<Rightarrow> 'a"
  where
    "nat_inductive_def zeroCase sucCase 0 = zeroCase"
  | "nat_inductive_def zeroCase sucCase (Suc i) = sucCase i (nat_inductive_def zeroCase sucCase i)"

locale zenMessages =
  fixes messages :: "RoutedMessage set"
  fixes isMessageFromTo :: "Node \<Rightarrow> Message \<Rightarrow> Destination \<Rightarrow> bool" ("(_) \<midarrow>\<langle> _ \<rangle>\<rightarrow> (_)" [1000,55,1000])
  defines "s \<midarrow>\<langle> m \<rangle>\<rightarrow> d \<equiv> \<lparr> sender = s, destination = d, payload = m \<rparr> \<in> messages"
  fixes isMessageFrom :: "Node \<Rightarrow> Message \<Rightarrow> bool" ("(_) \<midarrow>\<langle> _ \<rangle>\<leadsto>" [1000,55])
  defines "s \<midarrow>\<langle> m \<rangle>\<leadsto> \<equiv> \<exists> d. s \<midarrow>\<langle> m \<rangle>\<rightarrow> d"
  fixes isMessageTo :: "Message \<Rightarrow> Destination \<Rightarrow> bool" ("\<langle> _ \<rangle>\<rightarrow> (_)" [55,1000])
  defines "\<langle> m \<rangle>\<rightarrow> d \<equiv> \<exists> s. s \<midarrow>\<langle> m \<rangle>\<rightarrow> d"
  fixes isMessage :: "Message \<Rightarrow> bool" ("\<langle> _ \<rangle>\<leadsto>" [55])
  defines "\<langle> m \<rangle>\<leadsto> \<equiv> \<exists> s. s \<midarrow>\<langle> m \<rangle>\<leadsto>"
    (* value proposed in a slot & a term *)
  fixes v :: "Slot \<Rightarrow> Term \<Rightarrow> Value"
  defines "v i t \<equiv> THE x. \<langle> PublishRequest i t x \<rangle>\<leadsto>"
    (* whether a slot is committed *)
  fixes isCommitted :: "Slot \<Rightarrow> bool"
  defines "isCommitted i \<equiv> \<exists> t. \<langle> ApplyCommit i t \<rangle>\<leadsto>"
    (* whether all preceding slots are committed *)
  fixes committedTo :: "Slot \<Rightarrow> bool" ("committed\<^sub><")
  defines "committed\<^sub>< i \<equiv> \<forall> j < i. isCommitted j"
    (* the committed value in a slot *)
  fixes v\<^sub>c :: "Slot \<Rightarrow> Value"
  defines "v\<^sub>c i \<equiv> v i (SOME t. \<langle> ApplyCommit i t \<rangle>\<leadsto>)"
    (* the configuration of a slot *)
  fixes V :: "Slot \<Rightarrow> Node set"
  defines "V \<equiv> nat_inductive_def V\<^sub>0 (\<lambda>i Vi. if isReconfiguration (v\<^sub>c i) then getConf (v\<^sub>c i) else Vi)"
    (* predicate to say whether an applicable Vote has been sent *)
  fixes promised :: "Slot \<Rightarrow> Node \<Rightarrow> Node \<Rightarrow> Term \<Rightarrow> bool"
  defines "promised i s dn t \<equiv> \<exists> i' \<le> i. \<exists> a. s \<midarrow>\<langle> Vote i' t a \<rangle>\<rightarrow> (OneNode dn)"
    (* set of previously-accepted terms *)
  fixes prevAccepted :: "Slot \<Rightarrow> Term \<Rightarrow> Node set \<Rightarrow> Term set"
  defines "prevAccepted i t senders
      \<equiv> {t'. \<exists> s \<in> senders. s \<midarrow>\<langle> Vote i t (SomeTerm t') \<rangle>\<leadsto> }"
  fixes lastCommittedClusterStateBefore :: "Slot \<Rightarrow> ClusterState"
  defines "lastCommittedClusterStateBefore \<equiv> nat_inductive_def CS\<^sub>0
      (\<lambda>i CSi. case v\<^sub>c i of ClusterStateDiff diff \<Rightarrow> diff CSi | _ \<Rightarrow> CSi)"

(* ASSUMPTIONS *)
assumes Vote_future:
  "\<And>i i' s t t' a.
        \<lbrakk> s \<midarrow>\<langle> Vote i t a \<rangle>\<leadsto>; i < i'; t' < t \<rbrakk>
            \<Longrightarrow> \<not> s \<midarrow>\<langle> PublishResponse i' t' \<rangle>\<leadsto>"
assumes Vote_None:
  "\<And>i s t t'.
        \<lbrakk> s \<midarrow>\<langle> Vote i t NO_TERM \<rangle>\<leadsto>; t' < t \<rbrakk>
            \<Longrightarrow> \<not> s \<midarrow>\<langle> PublishResponse i t' \<rangle>\<leadsto>"
assumes Vote_Some_lt:
  "\<And>i s t t'. s \<midarrow>\<langle> Vote i t (SomeTerm t') \<rangle>\<leadsto>
      \<Longrightarrow> t' < t"
assumes Vote_Some_PublishResponse:
  "\<And>i s t t'. s \<midarrow>\<langle> Vote i t (SomeTerm t') \<rangle>\<leadsto>
      \<Longrightarrow> s \<midarrow>\<langle> PublishResponse i t' \<rangle>\<leadsto>"
assumes Vote_Some_max:
  "\<And>i s t t' t''. \<lbrakk> s \<midarrow>\<langle> Vote i t (SomeTerm t') \<rangle>\<leadsto>; t' < t''; t'' < t \<rbrakk>
      \<Longrightarrow> \<not> s \<midarrow>\<langle> PublishResponse i t'' \<rangle>\<leadsto>"
assumes Vote_not_broadcast:
  "\<And>i t a d. \<langle> Vote i t a \<rangle>\<rightarrow> d \<Longrightarrow> d \<noteq> Broadcast"
assumes Vote_unique_destination:
  "\<And>i s t a a' d d'. \<lbrakk> s \<midarrow>\<langle> Vote i t a \<rangle>\<rightarrow> d; s \<midarrow>\<langle> Vote i' t a' \<rangle>\<rightarrow> d' \<rbrakk>
      \<Longrightarrow> d = d'"
assumes PublishRequest_committedTo:
  "\<And>i t x. \<langle> PublishRequest i t x \<rangle>\<leadsto> \<Longrightarrow> committedTo i"
assumes PublishRequest_quorum:
  "\<And>i s t x. s \<midarrow>\<langle> PublishRequest i t x \<rangle>\<leadsto>
      \<Longrightarrow> \<exists> q \<in> majorities (V i). (\<forall> n \<in> q. promised i n s t) \<and>
            (prevAccepted i t q = {}
                \<or> (\<exists> t'. v i t = v i t' \<and> maxTerm (prevAccepted i t q) \<le> t'
                                        \<and> \<langle> PublishResponse i t' \<rangle>\<leadsto> \<and> t' < t))"
assumes PublishRequest_function:
  "\<And>i t x x'. \<lbrakk> \<langle> PublishRequest i t x \<rangle>\<leadsto>; \<langle> PublishRequest i t x' \<rangle>\<leadsto> \<rbrakk>
       \<Longrightarrow> x = x'"
assumes finite_messages:
  "finite messages"
assumes PublishResponse_PublishRequest:
  "\<And>i s t. s \<midarrow>\<langle> PublishResponse i t \<rangle>\<leadsto> \<Longrightarrow> \<exists> x. \<langle> PublishRequest i t x \<rangle>\<leadsto>"
assumes ApplyCommit_quorum:
  "\<And>i t. \<langle> ApplyCommit i t \<rangle>\<leadsto>
                        \<Longrightarrow> \<exists> q \<in> majorities (V i). \<forall> s \<in> q. s \<midarrow>\<langle> PublishResponse i t \<rangle>\<leadsto>"
assumes CatchUpResponse_committedTo:
  "\<And>i conf cs. \<langle> CatchUpResponse i conf cs \<rangle>\<leadsto> \<Longrightarrow> committed\<^sub>< i"
assumes CatchUpResponse_V:
  "\<And>i conf cs. \<langle> CatchUpResponse i conf cs \<rangle>\<leadsto> \<Longrightarrow> V i = conf"
assumes CatchUpResponse_lastCommittedClusterStateBefore:
  "\<And>i conf cs. \<langle> CatchUpResponse i conf cs \<rangle>\<leadsto> \<Longrightarrow> lastCommittedClusterStateBefore i = cs"

definition (in zenMessages) votedFor :: "Node \<Rightarrow> Node \<Rightarrow> Term \<Rightarrow> bool"
  where "votedFor n\<^sub>1 n\<^sub>2 t \<equiv> \<exists> i. promised i n\<^sub>1 n\<^sub>2 t"

lemma (in zenMessages) votedFor_unique:
  assumes "votedFor n n\<^sub>1 t"
  assumes "votedFor n n\<^sub>2 t"
  shows "n\<^sub>1 = n\<^sub>2"
  using assms unfolding votedFor_def by (meson Destination.inject Vote_unique_destination promised_def)

lemma (in zenMessages) V_simps[simp]:
  "V 0 = V\<^sub>0"
  "V (Suc i) = (if isReconfiguration (v\<^sub>c i) then getConf (v\<^sub>c i) else V i)"
  unfolding V_def by simp_all

lemma (in zenMessages) lastCommittedClusterStateBefore_simps[simp]:
  "lastCommittedClusterStateBefore 0 = CS\<^sub>0"
  "lastCommittedClusterStateBefore (Suc i) = (case v\<^sub>c i of ClusterStateDiff diff \<Rightarrow> diff | _ \<Rightarrow> id) (lastCommittedClusterStateBefore i)"
  unfolding lastCommittedClusterStateBefore_def by (simp, cases "v\<^sub>c i", auto)

declare [[goals_limit = 40]]

subsubsection \<open>Utility lemmas\<close>

text \<open>Some results that are useful later:\<close>

lemma (in zenMessages) V_finite: "finite (V i)"
  by (induct i, simp_all add: finite_V\<^sub>0 getConf_finite)

lemma (in zenMessages) V_intersects: "majorities (V i) \<frown> majorities (V i)"
  using V_finite majorities_intersect by simp

lemma (in zenMessages) ApplyCommit_PublishResponse:
  assumes "\<langle> ApplyCommit i t \<rangle>\<leadsto>"
  obtains s where "s \<midarrow>\<langle> PublishResponse i t \<rangle>\<leadsto>"
  by (meson ApplyCommit_quorum majorities_member assms)

lemma (in zenMessages) ApplyCommit_PublishRequest:
  assumes "\<langle> ApplyCommit i t \<rangle>\<leadsto>"
  shows "\<langle> PublishRequest i t (v i t) \<rangle>\<leadsto>"
  by (metis ApplyCommit_PublishResponse PublishResponse_PublishRequest assms the_equality v_def PublishRequest_function)

lemma (in zenMessages) PublishRequest_Vote:
  assumes "s \<midarrow>\<langle> PublishRequest i t x \<rangle>\<leadsto>"
  obtains i' n a where "i' \<le> i" "n \<midarrow>\<langle> Vote i' t a \<rangle>\<rightarrow> (OneNode s)"
  by (meson PublishRequest_quorum majorities_member assms isMessage_def promised_def)

lemma (in zenMessages) finite_prevAccepted: "finite (prevAccepted i t ns)"
proof -
  fix t\<^sub>0
  define f :: "RoutedMessage \<Rightarrow> Term" where "f \<equiv> \<lambda> m. case payload m of Vote _ _ (SomeTerm t') \<Rightarrow> t' | _ \<Rightarrow> t\<^sub>0"
  have "prevAccepted i t ns \<subseteq> f ` messages"
    apply (simp add: prevAccepted_def f_def isMessageFrom_def isMessageFromTo_def, intro subsetI)
    using image_iff by fastforce
  with finite_messages show ?thesis using finite_surj by auto
qed

lemma (in zenMessages) promised_long_def: "\<exists>d. promised i s d t
     \<equiv> (s \<midarrow>\<langle> Vote i t NO_TERM \<rangle>\<leadsto>
           \<or> (\<exists>i'<i. \<exists>a. s \<midarrow>\<langle> Vote i' t a \<rangle>\<leadsto>))
           \<or> (\<exists>t'. s \<midarrow>\<langle> Vote i t (SomeTerm t') \<rangle>\<leadsto>)"
  (is "?LHS == ?RHS")
proof -
  have "?LHS = ?RHS"
    apply (intro iffI)
    apply (metis TermOption.exhaust isMessageFrom_def nat_less_le promised_def)
    by (metis Destination.exhaust Vote_not_broadcast isMessageFrom_def isMessageTo_def nat_less_le not_le promised_def)
  thus "?LHS == ?RHS" by simp
qed

lemma (in zenMessages) Vote_value_function:
  assumes "s \<midarrow>\<langle> Vote i t a\<^sub>1 \<rangle>\<leadsto>" and "s \<midarrow>\<langle> Vote i t a\<^sub>2 \<rangle>\<leadsto>"
  shows "a\<^sub>1 = a\<^sub>2"
proof (cases a\<^sub>1)
  case NO_TERM
  with assms show ?thesis
    by (metis TermOption.exhaust Vote_None Vote_Some_PublishResponse Vote_Some_lt)
next
  case (SomeTerm t\<^sub>1)
  with assms obtain t\<^sub>2 where a\<^sub>2: "a\<^sub>2 = SomeTerm t\<^sub>2"
    using Vote_None Vote_Some_PublishResponse Vote_Some_lt TermOption.exhaust by metis

  from SomeTerm a\<^sub>2 assms show ?thesis
    by (metis Vote_Some_PublishResponse Vote_Some_lt less_linear Vote_Some_max)
qed

lemma (in zenMessages) shows finite_messages_insert: "finite (insert m messages)"
  using finite_messages by auto

lemma (in zenMessages) isCommitted_committedTo:
  assumes "isCommitted i"
  shows "committed\<^sub>< i"
  using ApplyCommit_PublishRequest PublishRequest_committedTo assms isCommitted_def by blast

lemma (in zenMessages) isCommitted_committedTo_Suc:
  assumes "isCommitted i"
  shows "committed\<^sub>< (Suc i)"
  using assms committedTo_def isCommitted_committedTo less_antisym by blast

lemma (in zenMessages) promised_unique:
  assumes "promised i s d t" and "promised i' s d' t"
  shows "d = d'"
  by (meson Destination.inject Vote_unique_destination assms promised_def)

lemma (in zenMessages) PublishResponse_PublishRequest_v:
  assumes "\<langle> PublishResponse i t \<rangle>\<leadsto>"
  shows "\<langle> PublishRequest i t (v i t) \<rangle>\<leadsto>"
proof -
  from assms obtain s where "s \<midarrow>\<langle> PublishResponse i t \<rangle>\<leadsto>" unfolding isMessage_def by blast
  with PublishResponse_PublishRequest
  obtain x where x: "\<langle> PublishRequest i t x \<rangle>\<leadsto>" by blast
  have "v i t = x" unfolding v_def using x by (intro the_equality PublishRequest_function)
  with x show ?thesis by simp
qed

lemma (in zenMessages) Vote_PublishRequest_v:
  assumes "\<langle> Vote i t (SomeTerm t') \<rangle>\<leadsto>"
  shows "\<langle> PublishRequest i t' (v i t') \<rangle>\<leadsto>"
  using assms Vote_Some_PublishResponse PublishResponse_PublishRequest_v
  unfolding isMessage_def by metis

subsubsection \<open>Relationship to @{term oneSlot}\<close>

text \<open>This shows that each slot @{term i} in Zen satisfies the assumptions of the @{term
oneSlot} model above.\<close>

lemma (in zenMessages) zen_is_oneSlot:
  fixes i
  shows "oneSlot (majorities (V i)) (v i)
    (\<lambda> s t. s \<midarrow>\<langle> Vote i t NO_TERM \<rangle>\<leadsto>
        \<or> (\<exists> i' < i. \<exists> a. s \<midarrow>\<langle> Vote i' t a \<rangle>\<leadsto>))
    (\<lambda> s t t'. s \<midarrow>\<langle> Vote i t (SomeTerm t') \<rangle>\<leadsto>)
    (\<lambda> t. \<exists> x. \<langle> PublishRequest i t x \<rangle>\<leadsto>)
    (\<lambda> s t. s \<midarrow>\<langle> PublishResponse i t \<rangle>\<leadsto>)
    (\<lambda> t. \<langle> ApplyCommit i t \<rangle>\<leadsto>)"
proof (unfold_locales, fold prevAccepted_def promised_long_def)
  from V_intersects show "majorities (V i) \<frown> majorities (V i)".
next
  fix s t t'
  assume "t' < t" "s \<midarrow>\<langle> Vote i t NO_TERM \<rangle>\<leadsto> \<or> (\<exists>i'<i. \<exists>a. s \<midarrow>\<langle> Vote i' t a \<rangle>\<leadsto>)"
  thus "\<not> s \<midarrow>\<langle> PublishResponse i t' \<rangle>\<leadsto>"
    using Vote_None Vote_future by auto
next
  fix s t t'
  assume j: "s \<midarrow>\<langle> Vote i t (SomeTerm t') \<rangle>\<leadsto>"
  from j show "t' < t" using Vote_Some_lt by blast
  from j show "s \<midarrow>\<langle> PublishResponse i t' \<rangle>\<leadsto>" using Vote_Some_PublishResponse by blast

  fix t'' assume "t' < t''" "t'' < t"
  with j show "\<not> s \<midarrow>\<langle> PublishResponse i t'' \<rangle>\<leadsto>" using Vote_Some_max by blast
next
  fix t
  assume "\<exists>x. \<langle> PublishRequest i t x \<rangle>\<leadsto>"
  then obtain x s where "s \<midarrow>\<langle> PublishRequest i t x \<rangle>\<leadsto>" by (auto simp add: isMessage_def)
  from PublishRequest_quorum [OF this] PublishResponse_PublishRequest
  show "\<exists>q \<in> majorities (V i). (\<forall>n\<in>q. \<exists>d. promised i n d t) \<and> (prevAccepted i t q = {} \<or> (\<exists>t'. v i t = v i t' \<and> maxTerm (prevAccepted i t q) \<le> t' \<and> (\<exists>x. \<langle> PublishRequest i t' x \<rangle>\<leadsto>) \<and> t' < t))"
    unfolding isMessageFrom_def by (meson PublishResponse_PublishRequest_v)
next
  fix s t assume "s \<midarrow>\<langle> PublishResponse i t \<rangle>\<leadsto>"
  thus "\<exists>x. \<langle> PublishRequest i t x \<rangle>\<leadsto>"
    by (simp add: PublishResponse_PublishRequest)
next
  fix t assume "\<langle> ApplyCommit i t \<rangle>\<leadsto>"
  thus "\<exists>q \<in> majorities (V i). \<forall>s\<in>q. s \<midarrow>\<langle> PublishResponse i t \<rangle>\<leadsto>"
    by (simp add: ApplyCommit_quorum)
next
  fix t\<^sub>0
  define f :: "RoutedMessage \<Rightarrow> Term"
    where "f \<equiv> \<lambda> m. case payload m of PublishRequest i t x \<Rightarrow> t | _ \<Rightarrow> t\<^sub>0"

  have "{t. \<exists>x. \<langle> PublishRequest i t x \<rangle>\<leadsto>} \<subseteq> f ` messages"
    apply (unfold isMessage_def isMessageFrom_def isMessageFromTo_def)
    using f_def image_iff by fastforce

  moreover have "finite (f ` messages)"
    by (simp add: finite_messages)

  ultimately show "finite {t. \<exists>x. \<langle> PublishRequest i t x \<rangle>\<leadsto>}"
    using finite_subset by blast
qed

text \<open>From this it follows that all committed values are equal.\<close>

theorem (in zenMessages) consistent:
  assumes "\<langle> ApplyCommit  i t\<^sub>1 \<rangle>\<leadsto>"
  assumes "\<langle> ApplyCommit  i t\<^sub>2 \<rangle>\<leadsto>"
  assumes "\<langle> PublishRequest i t\<^sub>1 v\<^sub>1 \<rangle>\<leadsto>"
  assumes "\<langle> PublishRequest i t\<^sub>2 v\<^sub>2 \<rangle>\<leadsto>"
  shows "v\<^sub>1 = v\<^sub>2"
proof -
  from oneSlot.consistent [OF zen_is_oneSlot] assms
  have "v i t\<^sub>1 = v i t\<^sub>2" by blast
  moreover have "v\<^sub>1 = v i t\<^sub>1" using ApplyCommit_PublishRequest assms PublishRequest_function by blast
  moreover have "v\<^sub>2 = v i t\<^sub>2" using ApplyCommit_PublishRequest assms PublishRequest_function by blast
  ultimately show ?thesis by simp
qed

lemma (in zenMessages) ApplyCommit_v\<^sub>c:
  assumes "\<langle> ApplyCommit i t \<rangle>\<leadsto>"
  shows "v\<^sub>c i = v i t"
proof (unfold v\<^sub>c_def, intro someI2 [where Q = "\<lambda>t'. v i t' = v i t"])
  from assms show "\<langle> ApplyCommit i t \<rangle>\<leadsto>" .
  fix t' assume "\<langle> ApplyCommit i t' \<rangle>\<leadsto>"
  thus "v i t' = v i t" by (intro oneSlot.consistent [OF zen_is_oneSlot] assms)
qed

lemma (in zenMessages) ApplyCommit_PublishRequest_v\<^sub>c:
  assumes "\<langle> ApplyCommit i t \<rangle>\<leadsto>"
  shows "\<langle> PublishRequest i t (v\<^sub>c i) \<rangle>\<leadsto>"
  unfolding ApplyCommit_v\<^sub>c [OF assms]
  using ApplyCommit_PublishRequest assms .

subsection \<open>Invariants on node states\<close>

text \<open>A set of invariants which relate the states of the individual nodes to the set of messages sent.\<close>

locale zen = zenMessages +
  fixes nodeState :: "Node \<Rightarrow> NodeData"
  assumes currentNode_nodeState: "\<And>n. currentNode (nodeState n) = n"
  assumes committedTo_firstUncommittedSlot:
    "\<And>n. committed\<^sub>< (firstUncommittedSlot (nodeState n))"
  assumes currentVotingNodes_firstUncommittedSlot:
    "\<And>n. currentVotingNodes (nodeState n) = V (firstUncommittedSlot (nodeState n))"
  assumes firstUncommittedSlot_PublishRequest:
    "\<And>i n t x. firstUncommittedSlot (nodeState n) < i \<Longrightarrow> \<not> n \<midarrow>\<langle> PublishRequest i t x \<rangle>\<leadsto>"
  assumes firstUncommittedSlot_PublishResponse:
    "\<And>i n t. firstUncommittedSlot (nodeState n) < i \<Longrightarrow> \<not> n \<midarrow>\<langle> PublishResponse i t \<rangle>\<leadsto>"
  assumes lastAcceptedTerm_None: "\<And>n t. lastAcceptedTerm (nodeState n) = NO_TERM
    \<Longrightarrow> \<not> n \<midarrow>\<langle> PublishResponse (firstUncommittedSlot (nodeState n)) t \<rangle>\<leadsto>"
  assumes lastAcceptedTerm_Some_sent: "\<And>n t. lastAcceptedTerm (nodeState n) = SomeTerm t
    \<Longrightarrow> n \<midarrow>\<langle> PublishResponse (firstUncommittedSlot (nodeState n)) t \<rangle>\<leadsto>"
  assumes lastAcceptedTerm_Some_max: "\<And>n t t'. lastAcceptedTerm (nodeState n) = SomeTerm t
    \<Longrightarrow> n \<midarrow>\<langle> PublishResponse (firstUncommittedSlot (nodeState n)) t' \<rangle>\<leadsto>
    \<Longrightarrow> t' \<le> t"
  assumes lastAcceptedTerm_Some_currentTerm: "\<And>n t. lastAcceptedTerm (nodeState n) = SomeTerm t
    \<Longrightarrow> t \<le> currentTerm (nodeState n)"
  assumes lastAcceptedTerm_Some_value: "\<And>n t. lastAcceptedTerm (nodeState n) = SomeTerm t
    \<Longrightarrow> \<langle> PublishRequest (firstUncommittedSlot (nodeState n)) t (lastAcceptedValue (nodeState n)) \<rangle>\<leadsto>"
  assumes Vote_currentTerm:
    "\<And>n i t a. n \<midarrow>\<langle> Vote i t a \<rangle>\<leadsto> \<Longrightarrow> t \<le> currentTerm (nodeState n)"
  assumes Vote_slot_function:
    "\<And>n i i' t a a'. n \<midarrow>\<langle> Vote i t a \<rangle>\<leadsto> \<Longrightarrow> n \<midarrow>\<langle> Vote i' t a' \<rangle>\<leadsto> \<Longrightarrow> i = i'"
  assumes PublishRequest_currentTerm:
    "\<And>n t x. n \<midarrow>\<langle> PublishRequest (firstUncommittedSlot (nodeState n)) t x \<rangle>\<leadsto>
        \<Longrightarrow> t \<le> currentTerm (nodeState n)"
  assumes PublishRequest_publishPermitted_currentTerm:
    "\<And>n t x. n \<midarrow>\<langle> PublishRequest (firstUncommittedSlot (nodeState n)) t x \<rangle>\<leadsto>
        \<Longrightarrow> publishPermitted (nodeState n)
        \<Longrightarrow> t < currentTerm (nodeState n)"
  assumes joinVotes:
    "\<And> n n'. n' \<in> joinVotes (nodeState n)
      \<Longrightarrow> promised (firstUncommittedSlot (nodeState n)) n' n (currentTerm (nodeState n))"
  assumes electionWon_isQuorum:
    "\<And>n. electionWon (nodeState n) \<Longrightarrow> isQuorum (nodeState n) (joinVotes (nodeState n))"
  assumes joinVotes_max: "\<And>n n' a'.
    \<lbrakk> \<not> (\<exists> x. \<langle> PublishRequest (firstUncommittedSlot (nodeState n))
                               (currentTerm (nodeState n)) x \<rangle>\<leadsto>);
      n' \<in> joinVotes (nodeState n);
      n' \<midarrow>\<langle> Vote (firstUncommittedSlot (nodeState n))
                                (currentTerm (nodeState n))
                                a' \<rangle>\<rightarrow> (OneNode n) \<rbrakk>
    \<Longrightarrow> a' \<le> lastAcceptedTerm (nodeState n)"
  assumes publishVotes: "\<And>n n'. n' \<in> publishVotes (nodeState n)
    \<Longrightarrow> n' \<midarrow>\<langle> PublishResponse (firstUncommittedSlot (nodeState n))
                              (currentTerm (nodeState n)) \<rangle>\<leadsto>"
  assumes currentClusterState_lastCommittedClusterStateBefore:
    "\<And>n. currentClusterState (nodeState n)
              = lastCommittedClusterStateBefore (firstUncommittedSlot (nodeState n))"

lemma (in zen) joinVotes_votedFor:
  assumes "n' \<in> joinVotes (nodeState n)"
  shows "votedFor n' n (currentTerm (nodeState n))"
  using joinVotes assms unfolding votedFor_def by auto

locale zenStep = zen +
  fixes messages' :: "RoutedMessage set"
  fixes nodeState' :: "Node \<Rightarrow> NodeData"
  fixes n\<^sub>0 :: Node

assumes messages_subset: "messages \<subseteq> messages'"
fixes nd :: NodeData
defines "nd \<equiv> nodeState n\<^sub>0"
fixes nd' :: NodeData
defines "nd' \<equiv> nodeState' n\<^sub>0"
assumes nodeState_unchanged: "\<And>n. n \<noteq> n\<^sub>0 \<Longrightarrow> nodeState' n = nodeState n"
  (* updated definitions from zenMessages *)
fixes isMessageFromTo' :: "Node \<Rightarrow> Message \<Rightarrow> Destination \<Rightarrow> bool" ("(_) \<midarrow>\<langle> _ \<rangle>\<rightarrow>' (_)" [1000,55,1000])
defines "s \<midarrow>\<langle> m \<rangle>\<rightarrow>' d \<equiv> \<lparr> sender = s, destination = d, payload = m \<rparr> \<in> messages'"
fixes isMessageFrom' :: "Node \<Rightarrow> Message \<Rightarrow> bool" ("(_) \<midarrow>\<langle> _ \<rangle>\<leadsto>'" [1000,55])
defines "s \<midarrow>\<langle> m \<rangle>\<leadsto>' \<equiv> \<exists> d. s \<midarrow>\<langle> m \<rangle>\<rightarrow>' d"
fixes isMessageTo' :: "Message \<Rightarrow> Destination \<Rightarrow> bool" ("\<langle> _ \<rangle>\<rightarrow>' (_)" [55,1000])
defines "\<langle> m \<rangle>\<rightarrow>' d \<equiv> \<exists> s. s \<midarrow>\<langle> m \<rangle>\<rightarrow>' d"
fixes isMessage' :: "Message \<Rightarrow> bool" ("\<langle> _ \<rangle>\<leadsto>'" [55])
defines "\<langle> m \<rangle>\<leadsto>' \<equiv> \<exists> s. s \<midarrow>\<langle> m \<rangle>\<leadsto>'"
  (* value proposed in a slot & a term *)
fixes v' :: "nat \<Rightarrow> Term \<Rightarrow> Value"
defines "v' i t \<equiv> THE x. \<langle> PublishRequest i t x \<rangle>\<leadsto>'"
  (* whether a slot is committed *)
fixes isCommitted' :: "nat \<Rightarrow> bool"
defines "isCommitted' i \<equiv> \<exists> t. \<langle> ApplyCommit i t \<rangle>\<leadsto>'"
  (* whether all preceding slots are committed *)
fixes committedTo' :: "nat \<Rightarrow> bool" ("committed\<^sub><'")
defines "committed\<^sub><' i \<equiv> \<forall> j < i. isCommitted' j"
  (* the committed value in a slot *)
fixes v\<^sub>c' :: "nat \<Rightarrow> Value"
defines "v\<^sub>c' i \<equiv> v' i (SOME t. \<langle> ApplyCommit i t \<rangle>\<leadsto>')"
  (* the configuration of a slot *)
fixes V' :: "Slot \<Rightarrow> Node set"
defines "V' \<equiv> nat_inductive_def V\<^sub>0 (\<lambda>i Vi. if isReconfiguration (v\<^sub>c' i) then getConf (v\<^sub>c' i) else Vi)"
  (* predicate to say whether an applicable Vote has been sent *)
fixes promised' :: "nat \<Rightarrow> Node \<Rightarrow> Node \<Rightarrow> Term \<Rightarrow> bool"
defines "promised' i s dn t \<equiv> \<exists> i' \<le> i. \<exists> a. s \<midarrow>\<langle> Vote i' t a \<rangle>\<rightarrow>' (OneNode dn)"
  (* set of previously-accepted terms *)
fixes prevAccepted' :: "nat \<Rightarrow> Term \<Rightarrow> Node set \<Rightarrow> Term set"
defines "prevAccepted' i t senders
      \<equiv> {t'. \<exists> s \<in> senders. s \<midarrow>\<langle> Vote i t (SomeTerm t') \<rangle>\<leadsto>' }"
fixes lastCommittedClusterStateBefore' :: "nat \<Rightarrow> ClusterState"
defines "lastCommittedClusterStateBefore' \<equiv> nat_inductive_def CS\<^sub>0
      (\<lambda>i CSi. case v\<^sub>c' i of ClusterStateDiff diff \<Rightarrow> diff CSi | _ \<Rightarrow> CSi)"
fixes sendTo :: "Destination \<Rightarrow> (NodeData * Message option) \<Rightarrow> RoutedMessage set"
defines "sendTo d result \<equiv> case snd result of
    None \<Rightarrow> messages | Some m \<Rightarrow> insert \<lparr> sender = n\<^sub>0, destination = d, payload = m \<rparr> messages"

lemma (in zenStep) nodeState'_def: "nodeState' n \<equiv> if n = n\<^sub>0 then nd' else nodeState n"
  using nodeState_unchanged nd'_def by presburger

lemma (in zenStep) V'_simps[simp]:
  "V' 0 = V\<^sub>0"
  "V' (Suc i) = (if isReconfiguration (v\<^sub>c' i) then getConf (v\<^sub>c' i) else V' i)"
  unfolding V'_def by simp_all

lemma (in zenStep) lastCommittedClusterStateBefore'_simps[simp]:
  "lastCommittedClusterStateBefore' 0 = CS\<^sub>0"
  "lastCommittedClusterStateBefore' (Suc i) = (case v\<^sub>c' i of ClusterStateDiff diff \<Rightarrow> diff | _ \<Rightarrow> id) (lastCommittedClusterStateBefore' i)"
  unfolding lastCommittedClusterStateBefore'_def by (simp, cases "v\<^sub>c' i", auto)

lemma (in zenStep) sendTo_simps[simp]:
  "sendTo d (nd'', None) = messages"
  "sendTo d (nd'', Some m) = insert \<lparr> sender = n\<^sub>0, destination = d, payload = m \<rparr> messages"
  by (auto simp add: sendTo_def)

lemma currentTerm_ensureCurrentTerm[simp]: "currentTerm nd \<le> t \<Longrightarrow> currentTerm (ensureCurrentTerm t nd) = t"
  by (auto simp add: ensureCurrentTerm_def)

lemma (in zenStep)
  assumes "\<And>i i' s t t' a. s \<midarrow>\<langle> Vote i t a \<rangle>\<leadsto>' \<Longrightarrow> i < i' \<Longrightarrow> t' < t \<Longrightarrow> \<not> s \<midarrow>\<langle> PublishResponse i' t' \<rangle>\<leadsto>'"
  assumes "\<And>i s t t'. s \<midarrow>\<langle> Vote i t NO_TERM \<rangle>\<leadsto>' \<Longrightarrow> t' < t \<Longrightarrow> \<not> s \<midarrow>\<langle> PublishResponse i t' \<rangle>\<leadsto>'"
  assumes "\<And>i s t t'. s \<midarrow>\<langle> Vote i t (SomeTerm t') \<rangle>\<leadsto>' \<Longrightarrow> t' < t"
  assumes "\<And>i s t t'. s \<midarrow>\<langle> Vote i t (SomeTerm t') \<rangle>\<leadsto>' \<Longrightarrow> s \<midarrow>\<langle> PublishResponse i t' \<rangle>\<leadsto>'"
  assumes "\<And>i s t t' t''. s \<midarrow>\<langle> Vote i t (SomeTerm t') \<rangle>\<leadsto>' \<Longrightarrow> t' < t'' \<Longrightarrow> t'' < t \<Longrightarrow> \<not> s \<midarrow>\<langle> PublishResponse i t'' \<rangle>\<leadsto>'"
  assumes "\<And>i t a d. \<langle> Vote i t a \<rangle>\<rightarrow>' d \<Longrightarrow> d \<noteq> Broadcast"
  assumes "\<And>i' i s t a a' d d'. s \<midarrow>\<langle> Vote i t a \<rangle>\<rightarrow>' d \<Longrightarrow> s \<midarrow>\<langle> Vote i' t a' \<rangle>\<rightarrow>' d' \<Longrightarrow> d = d'"
  assumes "\<And>i t x. \<langle> PublishRequest i t x \<rangle>\<leadsto>' \<Longrightarrow> committed\<^sub><' i"
  assumes "\<And>i s t x. s \<midarrow>\<langle> PublishRequest i t x \<rangle>\<leadsto>' \<Longrightarrow> \<exists>q\<in>majorities (V' i). (\<forall>n\<in>q. promised' i n s t) \<and> (prevAccepted' i t q = {} \<or> (\<exists>t'. v' i t = v' i t' \<and> maxTerm (prevAccepted' i t q) \<le> t' \<and> \<langle> PublishResponse i t' \<rangle>\<leadsto>' \<and> t' < t))"
  assumes "\<And>i t x x'. \<langle> PublishRequest i t x \<rangle>\<leadsto>' \<Longrightarrow> \<langle> PublishRequest i t x' \<rangle>\<leadsto>' \<Longrightarrow> x = x'"
  assumes "finite messages'"
  assumes "\<And>i s t. s \<midarrow>\<langle> PublishResponse i t \<rangle>\<leadsto>' \<Longrightarrow> \<exists>x. \<langle> PublishRequest i t x \<rangle>\<leadsto>'"
  assumes "\<And>i t. \<langle> ApplyCommit i t \<rangle>\<leadsto>' \<Longrightarrow> \<exists>q\<in>majorities (V' i). \<forall>s\<in>q. s \<midarrow>\<langle> PublishResponse i t \<rangle>\<leadsto>'"
  assumes "\<And>n. currentNode (nodeState' n) = n"
  assumes "\<And>n. committed\<^sub><' (firstUncommittedSlot (nodeState' n))"
  assumes "\<And>n. currentVotingNodes (nodeState' n) = V' (firstUncommittedSlot (nodeState' n))"
  assumes "\<And>i n t x. firstUncommittedSlot (nodeState' n) < i \<Longrightarrow> \<not> n \<midarrow>\<langle> PublishRequest i t x \<rangle>\<leadsto>'"
  assumes "\<And>i n t. firstUncommittedSlot (nodeState' n) < i \<Longrightarrow> \<not> n \<midarrow>\<langle> PublishResponse i t \<rangle>\<leadsto>'"
  assumes "\<And>n t. lastAcceptedTerm (nodeState' n) = NO_TERM \<Longrightarrow> \<not> n \<midarrow>\<langle> PublishResponse (firstUncommittedSlot (nodeState' n)) t \<rangle>\<leadsto>'"
  assumes "\<And>n t. lastAcceptedTerm (nodeState' n) = SomeTerm t \<Longrightarrow> n \<midarrow>\<langle> PublishResponse (firstUncommittedSlot (nodeState' n)) t \<rangle>\<leadsto>'"
  assumes "\<And>n t t'. lastAcceptedTerm (nodeState' n) = SomeTerm t \<Longrightarrow> n \<midarrow>\<langle> PublishResponse (firstUncommittedSlot (nodeState' n)) t' \<rangle>\<leadsto>' \<Longrightarrow> t' \<le> t"
  assumes "\<And>n t. lastAcceptedTerm (nodeState' n) = SomeTerm t \<Longrightarrow> \<langle> PublishRequest (firstUncommittedSlot (nodeState' n)) t (lastAcceptedValue (nodeState' n)) \<rangle>\<leadsto>'"
  assumes "\<And>n t. lastAcceptedTerm (nodeState' n) = SomeTerm t \<Longrightarrow> t \<le> currentTerm (nodeState' n)"
  assumes "\<And>n i t a. n \<midarrow>\<langle> Vote i t a \<rangle>\<leadsto>' \<Longrightarrow> t \<le> currentTerm (nodeState' n)"
  assumes "\<And>n i i' t a a'. n \<midarrow>\<langle> Vote i t a \<rangle>\<leadsto>' \<Longrightarrow> n \<midarrow>\<langle> Vote i' t a' \<rangle>\<leadsto>' \<Longrightarrow> i = i'"
  assumes "\<And>n t x. n \<midarrow>\<langle> PublishRequest (firstUncommittedSlot (nodeState' n)) t x \<rangle>\<leadsto>' \<Longrightarrow> t \<le> currentTerm (nodeState' n)"
  assumes "\<And>n t x. n \<midarrow>\<langle> PublishRequest (firstUncommittedSlot (nodeState' n)) t x \<rangle>\<leadsto>' \<Longrightarrow> publishPermitted (nodeState' n) \<Longrightarrow> t < currentTerm (nodeState' n)"
  assumes "\<And>n n'. n' \<in> joinVotes (nodeState' n) \<Longrightarrow> promised' (firstUncommittedSlot (nodeState' n)) n' n (currentTerm (nodeState' n))"
  assumes "\<And>n. electionWon (nodeState' n) \<Longrightarrow> isQuorum (nodeState' n) (joinVotes (nodeState' n))"
  assumes "\<And>n n' a'. \<not> (\<exists>x. \<langle> PublishRequest (firstUncommittedSlot (nodeState' n)) (currentTerm (nodeState' n)) x \<rangle>\<leadsto>') \<Longrightarrow> n' \<in> joinVotes (nodeState' n) \<Longrightarrow> n' \<midarrow>\<langle> Vote (firstUncommittedSlot (nodeState' n)) (currentTerm (nodeState' n)) a' \<rangle>\<rightarrow>' (OneNode n) \<Longrightarrow> a' \<le> lastAcceptedTerm (nodeState' n)"
  assumes "\<And>n n'. n' \<in> publishVotes (nodeState' n) \<Longrightarrow> n' \<midarrow>\<langle> PublishResponse (firstUncommittedSlot (nodeState' n)) (currentTerm (nodeState' n)) \<rangle>\<leadsto>'"
  assumes "\<And>n. currentClusterState (nodeState' n) = lastCommittedClusterStateBefore' (firstUncommittedSlot (nodeState' n))"
  assumes "\<And>i conf cs. \<langle> CatchUpResponse i conf cs \<rangle>\<leadsto>' \<Longrightarrow> committed\<^sub><' i"
  assumes "\<And>i conf cs. \<langle> CatchUpResponse i conf cs \<rangle>\<leadsto>' \<Longrightarrow> V' i = conf"
  assumes "\<And>i conf cs. \<langle> CatchUpResponse i conf cs \<rangle>\<leadsto>' \<Longrightarrow> lastCommittedClusterStateBefore' i = cs"
  shows zenI: "zen messages' nodeState'"
  apply (unfold_locales)
                      apply (fold isMessageFromTo'_def)
                      apply (fold isMessageTo'_def)
                      apply (fold isMessageFrom'_def)
                      apply (fold isMessage'_def)
                      apply (fold v'_def)
                      apply (fold isCommitted'_def)
                      apply (fold committedTo'_def)
                      apply (fold v\<^sub>c'_def)
                      apply (fold V'_def)
                      apply (fold promised'_def)
                      apply (fold prevAccepted'_def)
                      apply (fold lastCommittedClusterStateBefore'_def)
  using assms proof - qed

lemma (in zenStep)
  assumes "zen messages' nodeState'" "messages' \<subseteq> messages''" "\<And>n. n \<noteq> n\<^sub>0 \<Longrightarrow> nodeState' n = nodeState'' n"
  shows zenStepI1: "zenStep messages' nodeState' messages'' nodeState'' n\<^sub>0"
proof (intro_locales)
  from `zen messages' nodeState'`
  show "zenMessages messages'" "zen_axioms messages' nodeState'"
    unfolding zen_def by simp_all

  from assms
  show "zenStep_axioms messages' nodeState' messages'' nodeState'' n\<^sub>0"
    by (intro zenStep_axioms.intro, auto)
qed

lemma (in zenStep)
  assumes "messages \<subseteq> messages''" "\<And>n. n \<noteq> n\<^sub>0 \<Longrightarrow> nodeState n = nodeState'' n"
  shows zenStepI2: "zenStep messages nodeState messages'' nodeState'' n\<^sub>0"
proof (intro_locales)
  from assms
  show "zenStep_axioms messages nodeState messages'' nodeState'' n\<^sub>0"
    by (intro zenStep_axioms.intro, auto)
qed

lemma (in zenStep) Broadcast_to_OneNode:
  fixes x
  assumes nodeState': "nodeState' = nodeState"
  assumes sent: "n\<^sub>0 \<midarrow>\<langle> m \<rangle>\<rightarrow> Broadcast"
  assumes messages': "messages' = sendTo (OneNode d) (nd'', Some m)"
  shows "zen messages' nodeState'"
proof -
  have messages': "messages' = insert \<lparr>sender = n\<^sub>0, destination = OneNode d, payload = m \<rparr> messages"
    by (simp add: messages')

  from Vote_not_broadcast sent have not_Vote: "\<And>i t a. m \<noteq> Vote i t a"
    unfolding isMessageTo_def by blast

  from sent not_Vote have message_simps:
    "\<And>s m'. (s \<midarrow>\<langle> m' \<rangle>\<leadsto>') = (s \<midarrow>\<langle> m' \<rangle>\<leadsto>)"
    "\<And>m'. (\<langle> m' \<rangle>\<leadsto>') = (\<langle> m' \<rangle>\<leadsto>)"
    "\<And>s d i t a. (s \<midarrow>\<langle> Vote i t a \<rangle>\<rightarrow>' d) = (s \<midarrow>\<langle> Vote i t a \<rangle>\<rightarrow> d)"
    "\<And>d i t a. (\<langle> Vote i t a \<rangle>\<rightarrow>' d) = (\<langle> Vote i t a \<rangle>\<rightarrow> d)"
    by (auto simp add: isMessageFromTo'_def isMessageTo'_def isMessage'_def isMessageFrom'_def,
        auto simp add: isMessageFromTo_def isMessageTo_def isMessage_def isMessageFrom_def messages')

  have property_simps[simp]:
    "\<And>n. currentNode (nodeState' n) = currentNode (nodeState n)"
    "\<And>n. firstUncommittedSlot (nodeState' n) = firstUncommittedSlot (nodeState n)"
    "\<And>n. currentVotingNodes (nodeState' n) = currentVotingNodes (nodeState n)"
    "\<And>n q. isQuorum (nodeState' n) q = isQuorum (nodeState n) q"
    "\<And>n. currentTerm (nodeState' n) = currentTerm (nodeState n)"
    "\<And>n. publishPermitted (nodeState' n) = publishPermitted (nodeState n)"
    "\<And>n. joinVotes (nodeState' n) = joinVotes (nodeState n)"
    "\<And>n. electionWon (nodeState' n) = electionWon (nodeState n)"
    "\<And>n. publishVotes (nodeState' n) = publishVotes (nodeState n)"
    "\<And>n. currentClusterState (nodeState' n) = currentClusterState (nodeState n)"
    "\<And>n. lastAcceptedTerm (nodeState' n) = lastAcceptedTerm (nodeState n)"
    "\<And>n. lastAcceptedValue (nodeState' n) = lastAcceptedValue (nodeState n)"
    by (unfold nodeState', auto)

  have v_eq[simp]: "v' = v" by (intro ext, auto simp add: v'_def v_def message_simps)
  have v\<^sub>c_eq[simp]: "v\<^sub>c' = v\<^sub>c" by (intro ext, auto simp add: v\<^sub>c'_def v\<^sub>c_def message_simps)
  have isCommitted_eq[simp]: "isCommitted' = isCommitted" by (intro ext, auto simp add: isCommitted'_def isCommitted_def message_simps)
  have committedTo_eq[simp]: "committed\<^sub><' = committed\<^sub><" by (intro ext, auto simp add: committedTo'_def committedTo_def)
  have V_eq[simp]: "V' = V" using v\<^sub>c_eq V'_def V_def by blast
  have lastCommittedClusterStateBefore_eq[simp]: "lastCommittedClusterStateBefore' = lastCommittedClusterStateBefore"
    unfolding lastCommittedClusterStateBefore_def lastCommittedClusterStateBefore'_def v\<^sub>c_eq ..
  have promised_eq[simp]: "promised' = promised" by (intro ext, auto simp add: promised'_def promised_def message_simps)
  have prevAccepted_eq[simp]: "prevAccepted' = prevAccepted" by (intro ext, auto simp add: prevAccepted'_def prevAccepted_def message_simps)

  show ?thesis
    apply (intro zenI)
                        apply (unfold message_simps committedTo_eq V_eq v_eq
        lastCommittedClusterStateBefore_eq property_simps promised_eq prevAccepted_eq)
  proof -
    from finite_messages show "finite messages'" by (simp add: messages')
    from Vote_future show "\<And>i i' s t t' a. s \<midarrow>\<langle> Vote i t a \<rangle>\<leadsto> \<Longrightarrow> i < i' \<Longrightarrow> t' < t \<Longrightarrow> \<not> s \<midarrow>\<langle> PublishResponse i' t' \<rangle>\<leadsto>".
    from Vote_None show "\<And>i s t t'. s \<midarrow>\<langle> Vote i t NO_TERM \<rangle>\<leadsto> \<Longrightarrow> t' < t \<Longrightarrow> \<not> s \<midarrow>\<langle> PublishResponse i t' \<rangle>\<leadsto>".
    from Vote_Some_lt show "\<And>i s t t'. s \<midarrow>\<langle> Vote i t (SomeTerm t') \<rangle>\<leadsto> \<Longrightarrow> t' < t".
    from Vote_Some_PublishResponse show "\<And>i s t t'. s \<midarrow>\<langle> Vote i t (SomeTerm t') \<rangle>\<leadsto> \<Longrightarrow> s \<midarrow>\<langle> PublishResponse i t' \<rangle>\<leadsto>".
    from Vote_Some_max show "\<And>i s t t' t''. s \<midarrow>\<langle> Vote i t (SomeTerm t') \<rangle>\<leadsto> \<Longrightarrow> t' < t'' \<Longrightarrow> t'' < t \<Longrightarrow> \<not> s \<midarrow>\<langle> PublishResponse i t'' \<rangle>\<leadsto>".
    from Vote_not_broadcast show "\<And>i t a d. \<langle> Vote i t a \<rangle>\<rightarrow> d \<Longrightarrow> d \<noteq> Broadcast".
    from Vote_unique_destination show "\<And>i' i s t a a' d d'. s \<midarrow>\<langle> Vote i t a \<rangle>\<rightarrow> d \<Longrightarrow> s \<midarrow>\<langle> Vote i' t a' \<rangle>\<rightarrow> d' \<Longrightarrow> d = d'".
    from currentNode_nodeState show "\<And>n. currentNode (nodeState n) = n" .
    from committedTo_firstUncommittedSlot show "\<And>n. committed\<^sub>< (firstUncommittedSlot (nodeState n))" .
    from firstUncommittedSlot_PublishResponse show "\<And>n i t. firstUncommittedSlot (nodeState n) < i \<Longrightarrow> \<not> n \<midarrow>\<langle> PublishResponse i t \<rangle>\<leadsto>" .
    from lastAcceptedTerm_None show "\<And>n i t. lastAcceptedTerm (nodeState n) = NO_TERM \<Longrightarrow> \<not> n \<midarrow>\<langle> PublishResponse (firstUncommittedSlot (nodeState n)) t \<rangle>\<leadsto>".
    from lastAcceptedTerm_Some_sent show "\<And>n t. lastAcceptedTerm (nodeState n) = SomeTerm t \<Longrightarrow> n \<midarrow>\<langle> PublishResponse (firstUncommittedSlot (nodeState n)) t \<rangle>\<leadsto>".
    from lastAcceptedTerm_Some_max show "\<And>n t t'. lastAcceptedTerm (nodeState n) = SomeTerm t \<Longrightarrow> n \<midarrow>\<langle> PublishResponse (firstUncommittedSlot (nodeState n)) t' \<rangle>\<leadsto> \<Longrightarrow> t' \<le> t".
    from Vote_currentTerm show "\<And>n i t a. n \<midarrow>\<langle> Vote i t a \<rangle>\<leadsto> \<Longrightarrow> t \<le> currentTerm (nodeState n)".
    from Vote_slot_function show "\<And>n i i' t a a'. n \<midarrow>\<langle> Vote i t a \<rangle>\<leadsto> \<Longrightarrow> n \<midarrow>\<langle> Vote i' t a' \<rangle>\<leadsto> \<Longrightarrow> i = i'".
    from electionWon_isQuorum show "\<And>n. electionWon (nodeState n) \<Longrightarrow> isQuorum (nodeState n) (joinVotes (nodeState n))".
    from joinVotes_max show " \<And>n n' a'. \<not> (\<exists>x. \<langle> PublishRequest (firstUncommittedSlot (nodeState n)) (currentTerm (nodeState n)) x \<rangle>\<leadsto>) \<Longrightarrow> n' \<in> joinVotes (nodeState n) \<Longrightarrow> n' \<midarrow>\<langle> Vote (firstUncommittedSlot (nodeState n)) (currentTerm (nodeState n)) a' \<rangle>\<rightarrow> (OneNode n) \<Longrightarrow> a' \<le> lastAcceptedTerm (nodeState n)".
    from publishVotes show "\<And>n n'. n' \<in> publishVotes (nodeState n) \<Longrightarrow> n' \<midarrow>\<langle> PublishResponse (firstUncommittedSlot (nodeState n)) (currentTerm (nodeState n)) \<rangle>\<leadsto>".
    from currentClusterState_lastCommittedClusterStateBefore show "\<And>n. currentClusterState (nodeState n) = lastCommittedClusterStateBefore (firstUncommittedSlot (nodeState n))".
    from joinVotes show "\<And>n n'. n' \<in> joinVotes (nodeState n) \<Longrightarrow> promised (firstUncommittedSlot (nodeState n)) n' n (currentTerm (nodeState n))".
    from PublishRequest_committedTo show "\<And>i t x. \<langle> PublishRequest i t x \<rangle>\<leadsto> \<Longrightarrow> committed\<^sub>< i".
    from PublishRequest_quorum show "\<And>i s t x. s \<midarrow>\<langle> PublishRequest i t x \<rangle>\<leadsto> \<Longrightarrow> \<exists>q\<in>majorities (V i). (\<forall>n\<in>q. promised i n s t) \<and> (prevAccepted i t q = {} \<or> (\<exists>t'. v i t = v i t' \<and> maxTerm (prevAccepted i t q) \<le> t' \<and> \<langle> PublishResponse i t' \<rangle>\<leadsto> \<and> t' < t))".
    from PublishRequest_function show "\<And>i t x x'. \<langle> PublishRequest i t x \<rangle>\<leadsto> \<Longrightarrow> \<langle> PublishRequest i t x' \<rangle>\<leadsto> \<Longrightarrow> x = x'".
    from PublishResponse_PublishRequest show "\<And>i s t. s \<midarrow>\<langle> PublishResponse i t \<rangle>\<leadsto> \<Longrightarrow> \<exists>x. \<langle> PublishRequest i t x \<rangle>\<leadsto>".
    from ApplyCommit_quorum show "\<And>i t. \<langle> ApplyCommit i t \<rangle>\<leadsto> \<Longrightarrow> \<exists>q\<in>majorities (V i). \<forall>s\<in>q. s \<midarrow>\<langle> PublishResponse i t \<rangle>\<leadsto>".
    from currentVotingNodes_firstUncommittedSlot show "\<And>n. currentVotingNodes (nodeState n) = V (firstUncommittedSlot (nodeState n))".
    from firstUncommittedSlot_PublishRequest show "\<And>i n t x. firstUncommittedSlot (nodeState n) < i \<Longrightarrow> \<not> n \<midarrow>\<langle> PublishRequest i t x \<rangle>\<leadsto>".
    from lastAcceptedTerm_Some_value show "\<And>n t. lastAcceptedTerm (nodeState n) = SomeTerm t \<Longrightarrow> \<langle> PublishRequest (firstUncommittedSlot (nodeState n)) t (lastAcceptedValue (nodeState n)) \<rangle>\<leadsto>".
    from PublishRequest_currentTerm show "\<And>n t x. n \<midarrow>\<langle> PublishRequest (firstUncommittedSlot (nodeState n)) t x \<rangle>\<leadsto> \<Longrightarrow> t \<le> currentTerm (nodeState n)".
    from PublishRequest_publishPermitted_currentTerm show "\<And>n t x. n \<midarrow>\<langle> PublishRequest (firstUncommittedSlot (nodeState n)) t x \<rangle>\<leadsto> \<Longrightarrow> publishPermitted (nodeState n) \<Longrightarrow> t < currentTerm (nodeState n)".
    from CatchUpResponse_committedTo show "\<And>i conf cs. \<langle> CatchUpResponse i conf cs \<rangle>\<leadsto> \<Longrightarrow> committed\<^sub>< i".
    from CatchUpResponse_V show "\<And>i conf cs. \<langle> CatchUpResponse i conf cs \<rangle>\<leadsto> \<Longrightarrow> V i = conf".
    from CatchUpResponse_lastCommittedClusterStateBefore show "\<And>i conf cs. \<langle> CatchUpResponse i conf cs \<rangle>\<leadsto> \<Longrightarrow> lastCommittedClusterStateBefore i = cs".
    from lastAcceptedTerm_Some_currentTerm show "\<And>n t. lastAcceptedTerm (nodeState n) = SomeTerm t \<Longrightarrow> t \<le> currentTerm (nodeState n)".
  qed
qed

lemma (in zenStep) send_spontaneous_message:
  assumes messages': "messages' = sendTo d\<^sub>0 (nd, Some m)"
  assumes spontaneous: "case m of StartJoin _ \<Rightarrow> True | ClientValue _ \<Rightarrow> True | Reboot \<Rightarrow> True | CatchUpRequest \<Rightarrow> True | _ \<Rightarrow> False"
  assumes nodeState': "nodeState' = nodeState"
  shows "zen messages' nodeState'"
proof -
  have messages': "messages' = insert \<lparr>sender = n\<^sub>0, destination = d\<^sub>0, payload = m \<rparr> messages"
    by (simp add: messages')

  from spontaneous
  have message_simps[simp]:
    "\<And>s d i t a. (s \<midarrow>\<langle> Vote i t a \<rangle>\<rightarrow>' d) = (s \<midarrow>\<langle> Vote i t a \<rangle>\<rightarrow> d)"
    "\<And>s d i t. (s \<midarrow>\<langle> PublishResponse i t \<rangle>\<rightarrow>' d) = (s \<midarrow>\<langle> PublishResponse i t \<rangle>\<rightarrow> d)"
    "\<And>s d i t x. (s \<midarrow>\<langle> PublishRequest i t x \<rangle>\<rightarrow>' d) = (s \<midarrow>\<langle> PublishRequest i t x \<rangle>\<rightarrow> d)"
    "\<And>s d i t. (s \<midarrow>\<langle> ApplyCommit i t \<rangle>\<rightarrow>' d) = (s \<midarrow>\<langle> ApplyCommit i t \<rangle>\<rightarrow> d)"
    "\<And>d i t a. (\<langle> Vote i t a \<rangle>\<rightarrow>' d) = (\<langle> Vote i t a \<rangle>\<rightarrow> d)"
    "\<And>d i t. (\<langle> PublishResponse i t \<rangle>\<rightarrow>' d) = (\<langle> PublishResponse i t \<rangle>\<rightarrow> d)"
    "\<And>d i t x. (\<langle> PublishRequest i t x \<rangle>\<rightarrow>' d) = (\<langle> PublishRequest i t x \<rangle>\<rightarrow> d)"
    "\<And>d i t. (\<langle> ApplyCommit i t \<rangle>\<rightarrow>' d) = (\<langle> ApplyCommit i t \<rangle>\<rightarrow> d)"
    "\<And>s i t a. (s \<midarrow>\<langle> Vote i t a \<rangle>\<leadsto>') = (s \<midarrow>\<langle> Vote i t a \<rangle>\<leadsto>)"
    "\<And>s i t. (s \<midarrow>\<langle> PublishResponse i t \<rangle>\<leadsto>') = (s \<midarrow>\<langle> PublishResponse i t \<rangle>\<leadsto>)"
    "\<And>s i t x. (s \<midarrow>\<langle> PublishRequest i t x \<rangle>\<leadsto>') = (s \<midarrow>\<langle> PublishRequest i t x \<rangle>\<leadsto>)"
    "\<And>s i t. (s \<midarrow>\<langle> ApplyCommit i t \<rangle>\<leadsto>') = (s \<midarrow>\<langle> ApplyCommit i t \<rangle>\<leadsto>)"
    "\<And>d i t a. (\<langle> Vote i t a \<rangle>\<leadsto>') = (\<langle> Vote i t a \<rangle>\<leadsto>)"
    "\<And>d i t. (\<langle> PublishResponse i t \<rangle>\<leadsto>') = (\<langle> PublishResponse i t \<rangle>\<leadsto>)"
    "\<And>d i t x. (\<langle> PublishRequest i t x \<rangle>\<leadsto>') = (\<langle> PublishRequest i t x \<rangle>\<leadsto>)"
    "\<And>d i t. (\<langle> ApplyCommit i t \<rangle>\<leadsto>') = (\<langle> ApplyCommit i t \<rangle>\<leadsto>)"
    "\<And>s d i conf cs. (s \<midarrow>\<langle> CatchUpResponse i conf cs \<rangle>\<rightarrow>' d) = (s \<midarrow>\<langle> CatchUpResponse i conf cs \<rangle>\<rightarrow> d)"
    "\<And>d i conf cs. (\<langle> CatchUpResponse i conf cs \<rangle>\<rightarrow>' d) = (\<langle> CatchUpResponse i conf cs \<rangle>\<rightarrow> d)"
    "\<And>s i conf cs. (s \<midarrow>\<langle> CatchUpResponse i conf cs \<rangle>\<leadsto>') = (s \<midarrow>\<langle> CatchUpResponse i conf cs \<rangle>\<leadsto>)"
    "\<And>d i conf cs. (\<langle> CatchUpResponse i conf cs \<rangle>\<leadsto>') = (\<langle> CatchUpResponse i conf cs \<rangle>\<leadsto>)"
    by (auto simp add: isMessageFromTo'_def isMessageTo'_def isMessage'_def isMessageFrom'_def,
        auto simp add: isMessageFromTo_def isMessageTo_def isMessage_def isMessageFrom_def messages')

  have property_simps[simp]:
    "\<And>n. currentNode (nodeState' n) = currentNode (nodeState n)"
    "\<And>n. firstUncommittedSlot (nodeState' n) = firstUncommittedSlot (nodeState n)"
    "\<And>n. currentVotingNodes (nodeState' n) = currentVotingNodes (nodeState n)"
    "\<And>n q. isQuorum (nodeState' n) q = isQuorum (nodeState n) q"
    "\<And>n. currentTerm (nodeState' n) = currentTerm (nodeState n)"
    "\<And>n. publishPermitted (nodeState' n) = publishPermitted (nodeState n)"
    "\<And>n. joinVotes (nodeState' n) = joinVotes (nodeState n)"
    "\<And>n. electionWon (nodeState' n) = electionWon (nodeState n)"
    "\<And>n. publishVotes (nodeState' n) = publishVotes (nodeState n)"
    "\<And>n. currentClusterState (nodeState' n) = currentClusterState (nodeState n)"
    "\<And>n. lastAcceptedTerm (nodeState' n) = lastAcceptedTerm (nodeState n)"
    "\<And>n. lastAcceptedValue (nodeState' n) = lastAcceptedValue (nodeState n)"
    by (unfold nodeState', auto)

  have v_eq[simp]: "v' = v" by (intro ext, auto simp add: v'_def v_def)
  have v\<^sub>c_eq[simp]: "v\<^sub>c' = v\<^sub>c" by (intro ext, auto simp add: v\<^sub>c'_def v\<^sub>c_def)
  have isCommitted_eq[simp]: "isCommitted' = isCommitted" by (intro ext, auto simp add: isCommitted'_def isCommitted_def)
  have committedTo_eq[simp]: "committed\<^sub><' = committed\<^sub><" by (intro ext, auto simp add: committedTo'_def committedTo_def)
  have V_eq[simp]: "V' = V" using v\<^sub>c_eq V'_def V_def by blast
  have lastCommittedClusterStateBefore_eq[simp]: "lastCommittedClusterStateBefore' = lastCommittedClusterStateBefore"
    unfolding lastCommittedClusterStateBefore_def lastCommittedClusterStateBefore'_def v\<^sub>c_eq ..
  have promised_eq[simp]: "promised' = promised" by (intro ext, auto simp add: promised'_def promised_def)
  have prevAccepted_eq[simp]: "prevAccepted' = prevAccepted" by (intro ext, auto simp add: prevAccepted'_def prevAccepted_def)

  show ?thesis
    apply (intro zenI)
                        apply (unfold message_simps committedTo_eq V_eq v_eq
        lastCommittedClusterStateBefore_eq property_simps promised_eq prevAccepted_eq)
  proof -
    from finite_messages show "finite messages'" by (simp add: messages')
    from Vote_future show "\<And>i i' s t t' a. s \<midarrow>\<langle> Vote i t a \<rangle>\<leadsto> \<Longrightarrow> i < i' \<Longrightarrow> t' < t \<Longrightarrow> \<not> s \<midarrow>\<langle> PublishResponse i' t' \<rangle>\<leadsto>".
    from Vote_None show "\<And>i s t t'. s \<midarrow>\<langle> Vote i t NO_TERM \<rangle>\<leadsto> \<Longrightarrow> t' < t \<Longrightarrow> \<not> s \<midarrow>\<langle> PublishResponse i t' \<rangle>\<leadsto>".
    from Vote_Some_lt show "\<And>i s t t'. s \<midarrow>\<langle> Vote i t (SomeTerm t') \<rangle>\<leadsto> \<Longrightarrow> t' < t".
    from Vote_Some_PublishResponse show "\<And>i s t t'. s \<midarrow>\<langle> Vote i t (SomeTerm t') \<rangle>\<leadsto> \<Longrightarrow> s \<midarrow>\<langle> PublishResponse i t' \<rangle>\<leadsto>".
    from Vote_Some_max show "\<And>i s t t' t''. s \<midarrow>\<langle> Vote i t (SomeTerm t') \<rangle>\<leadsto> \<Longrightarrow> t' < t'' \<Longrightarrow> t'' < t \<Longrightarrow> \<not> s \<midarrow>\<langle> PublishResponse i t'' \<rangle>\<leadsto>".
    from Vote_not_broadcast show "\<And>i t a d. \<langle> Vote i t a \<rangle>\<rightarrow> d \<Longrightarrow> d \<noteq> Broadcast".
    from Vote_unique_destination show "\<And>i' i s t a a' d d'. s \<midarrow>\<langle> Vote i t a \<rangle>\<rightarrow> d \<Longrightarrow> s \<midarrow>\<langle> Vote i' t a' \<rangle>\<rightarrow> d' \<Longrightarrow> d = d'".
    from currentNode_nodeState show "\<And>n. currentNode (nodeState n) = n" .
    from committedTo_firstUncommittedSlot show "\<And>n. committed\<^sub>< (firstUncommittedSlot (nodeState n))" .
    from firstUncommittedSlot_PublishResponse show "\<And>n i t. firstUncommittedSlot (nodeState n) < i \<Longrightarrow> \<not> n \<midarrow>\<langle> PublishResponse i t \<rangle>\<leadsto>" .
    from lastAcceptedTerm_None show "\<And>n i t. lastAcceptedTerm (nodeState n) = NO_TERM \<Longrightarrow> \<not> n \<midarrow>\<langle> PublishResponse (firstUncommittedSlot (nodeState n)) t \<rangle>\<leadsto>".
    from lastAcceptedTerm_Some_sent show "\<And>n t. lastAcceptedTerm (nodeState n) = SomeTerm t \<Longrightarrow> n \<midarrow>\<langle> PublishResponse (firstUncommittedSlot (nodeState n)) t \<rangle>\<leadsto>".
    from lastAcceptedTerm_Some_max show "\<And>n t t'. lastAcceptedTerm (nodeState n) = SomeTerm t \<Longrightarrow> n \<midarrow>\<langle> PublishResponse (firstUncommittedSlot (nodeState n)) t' \<rangle>\<leadsto> \<Longrightarrow> t' \<le> t".
    from Vote_currentTerm show "\<And>n i t a. n \<midarrow>\<langle> Vote i t a \<rangle>\<leadsto> \<Longrightarrow> t \<le> currentTerm (nodeState n)".
    from Vote_slot_function show "\<And>n i i' t a a'. n \<midarrow>\<langle> Vote i t a \<rangle>\<leadsto> \<Longrightarrow> n \<midarrow>\<langle> Vote i' t a' \<rangle>\<leadsto> \<Longrightarrow> i = i'".
    from electionWon_isQuorum show "\<And>n. electionWon (nodeState n) \<Longrightarrow> isQuorum (nodeState n) (joinVotes (nodeState n))".
    from joinVotes_max show " \<And>n n' a'. \<not> (\<exists>x. \<langle> PublishRequest (firstUncommittedSlot (nodeState n)) (currentTerm (nodeState n)) x \<rangle>\<leadsto>) \<Longrightarrow> n' \<in> joinVotes (nodeState n) \<Longrightarrow> n' \<midarrow>\<langle> Vote (firstUncommittedSlot (nodeState n)) (currentTerm (nodeState n)) a' \<rangle>\<rightarrow> (OneNode n) \<Longrightarrow> a' \<le> lastAcceptedTerm (nodeState n)".
    from publishVotes show "\<And>n n'. n' \<in> publishVotes (nodeState n) \<Longrightarrow> n' \<midarrow>\<langle> PublishResponse (firstUncommittedSlot (nodeState n)) (currentTerm (nodeState n)) \<rangle>\<leadsto>".
    from currentClusterState_lastCommittedClusterStateBefore show "\<And>n. currentClusterState (nodeState n) = lastCommittedClusterStateBefore (firstUncommittedSlot (nodeState n))".
    from joinVotes show "\<And>n n'. n' \<in> joinVotes (nodeState n) \<Longrightarrow> promised (firstUncommittedSlot (nodeState n)) n' n (currentTerm (nodeState n))".
    from PublishRequest_committedTo show "\<And>i t x. \<langle> PublishRequest i t x \<rangle>\<leadsto> \<Longrightarrow> committed\<^sub>< i".
    from PublishRequest_quorum show "\<And>i s t x. s \<midarrow>\<langle> PublishRequest i t x \<rangle>\<leadsto> \<Longrightarrow> \<exists>q\<in>majorities (V i). (\<forall>n\<in>q. promised i n s t) \<and> (prevAccepted i t q = {} \<or> (\<exists>t'. v i t = v i t' \<and> maxTerm (prevAccepted i t q) \<le> t' \<and> \<langle> PublishResponse i t' \<rangle>\<leadsto> \<and> t' < t))".
    from PublishRequest_function show "\<And>i t x x'. \<langle> PublishRequest i t x \<rangle>\<leadsto> \<Longrightarrow> \<langle> PublishRequest i t x' \<rangle>\<leadsto> \<Longrightarrow> x = x'".
    from PublishResponse_PublishRequest show "\<And>i s t. s \<midarrow>\<langle> PublishResponse i t \<rangle>\<leadsto> \<Longrightarrow> \<exists>x. \<langle> PublishRequest i t x \<rangle>\<leadsto>".
    from ApplyCommit_quorum show "\<And>i t. \<langle> ApplyCommit i t \<rangle>\<leadsto> \<Longrightarrow> \<exists>q\<in>majorities (V i). \<forall>s\<in>q. s \<midarrow>\<langle> PublishResponse i t \<rangle>\<leadsto>".
    from currentVotingNodes_firstUncommittedSlot show "\<And>n. currentVotingNodes (nodeState n) = V (firstUncommittedSlot (nodeState n))".
    from firstUncommittedSlot_PublishRequest show "\<And>i n t x. firstUncommittedSlot (nodeState n) < i \<Longrightarrow> \<not> n \<midarrow>\<langle> PublishRequest i t x \<rangle>\<leadsto>".
    from lastAcceptedTerm_Some_value show "\<And>n t. lastAcceptedTerm (nodeState n) = SomeTerm t \<Longrightarrow> \<langle> PublishRequest (firstUncommittedSlot (nodeState n)) t (lastAcceptedValue (nodeState n)) \<rangle>\<leadsto>".
    from PublishRequest_currentTerm show "\<And>n t x. n \<midarrow>\<langle> PublishRequest (firstUncommittedSlot (nodeState n)) t x \<rangle>\<leadsto> \<Longrightarrow> t \<le> currentTerm (nodeState n)".
    from PublishRequest_publishPermitted_currentTerm show "\<And>n t x. n \<midarrow>\<langle> PublishRequest (firstUncommittedSlot (nodeState n)) t x \<rangle>\<leadsto> \<Longrightarrow> publishPermitted (nodeState n) \<Longrightarrow> t < currentTerm (nodeState n)".
    from CatchUpResponse_committedTo show "\<And>i conf cs. \<langle> CatchUpResponse i conf cs \<rangle>\<leadsto> \<Longrightarrow> committed\<^sub>< i".
    from CatchUpResponse_V show "\<And>i conf cs. \<langle> CatchUpResponse i conf cs \<rangle>\<leadsto> \<Longrightarrow> V i = conf".
    from CatchUpResponse_lastCommittedClusterStateBefore show "\<And>i conf cs. \<langle> CatchUpResponse i conf cs \<rangle>\<leadsto> \<Longrightarrow> lastCommittedClusterStateBefore i = cs".
    from lastAcceptedTerm_Some_currentTerm show "\<And>n t. lastAcceptedTerm (nodeState n) = SomeTerm t \<Longrightarrow> t \<le> currentTerm (nodeState n)".
  qed
qed

lemma (in zenStep) send_StartJoin:
  assumes messages': "messages' = sendTo d\<^sub>0 (nd, Some (StartJoin t\<^sub>0))"
  assumes nodeState': "nodeState' = nodeState"
  shows "zen messages' nodeState'"
  using assms by (intro send_spontaneous_message, auto)

lemma (in zenStep) send_ClientValue:
  assumes messages': "messages' = sendTo d\<^sub>0 (nd, Some (ClientValue x\<^sub>0))"
  assumes nodeState': "nodeState' = nodeState"
  shows "zen messages' nodeState'"
  using assms by (intro send_spontaneous_message, auto)

lemma (in zenStep) send_CatchUpRequest:
  assumes messages': "messages' = sendTo d\<^sub>0 (nd, Some CatchUpRequest)"
  assumes nodeState': "nodeState' = nodeState"
  shows "zen messages' nodeState'"
  using assms by (intro send_spontaneous_message, auto)

lemma (in zenStep) send_Reboot:
  assumes messages': "messages' = sendTo d\<^sub>0 (nd, Some Reboot)"
  assumes nodeState': "nodeState' = nodeState"
  shows "zen messages' nodeState'"
  using assms by (intro send_spontaneous_message, auto)

lemma (in zenStep) ensureCurrentTerm_invariants:
  assumes nd': "nd' = ensureCurrentTerm t nd"
  assumes messages': "messages' = messages"
  shows "zen messages' nodeState'"
proof (cases "t \<le> currentTerm nd")
  case True
  hence "nodeState' = nodeState"
    by (intro ext, unfold nodeState'_def, auto simp add: nd' ensureCurrentTerm_def nd_def)
  with zen_axioms messages' show ?thesis by simp
next
  case False hence t: "currentTerm nd < t" by simp

  have message_simps[simp]:
    "\<And>s p d. (s \<midarrow>\<langle> p \<rangle>\<rightarrow>' d) = (s \<midarrow>\<langle> p \<rangle>\<rightarrow> d)"
    "\<And>p d. (\<langle> p \<rangle>\<rightarrow>' d) = (\<langle> p \<rangle>\<rightarrow> d)"
    "\<And>s p. (s \<midarrow>\<langle> p \<rangle>\<leadsto>') = (s \<midarrow>\<langle> p \<rangle>\<leadsto>)"
    "\<And>p. (\<langle> p \<rangle>\<leadsto>') = (\<langle> p \<rangle>\<leadsto>)"
    by (unfold isMessageFromTo'_def isMessageTo'_def isMessageFrom'_def isMessage'_def,
        auto simp add: messages' isMessageFromTo_def isMessageTo_def isMessageFrom_def isMessage_def)

  have property_simps[simp]:
    "\<And>n. currentNode (nodeState' n) = currentNode (nodeState n)"
    "\<And>n. firstUncommittedSlot (nodeState' n) = firstUncommittedSlot (nodeState n)"
    "\<And>n. currentClusterState (nodeState' n) = currentClusterState (nodeState n)"
    "\<And>n. currentVotingNodes (nodeState' n) = currentVotingNodes (nodeState n)"
    "\<And>n q. isQuorum (nodeState' n) q = isQuorum (nodeState n) q"
    "\<And>n. lastAcceptedTerm (nodeState' n) = lastAcceptedTerm (nodeState n)"
    "\<And>n. lastAcceptedValue (nodeState' n) = lastAcceptedValue (nodeState n)"
    "currentTerm (nodeState' n\<^sub>0) = t"
    "electionWon (nodeState' n\<^sub>0) = False"
    "joinVotes (nodeState' n\<^sub>0) = {}"
    "publishPermitted (nodeState' n\<^sub>0) = True"
    "publishVotes (nodeState' n\<^sub>0) = {}"
    using t
    by (unfold nodeState'_def, auto simp add: nd_def isQuorum_def nd' ensureCurrentTerm_def
        lastAcceptedTerm_def lastAcceptedValue_def)

  have currentTerm_increases: "\<And>n. currentTerm (nodeState n) \<le> currentTerm (nodeState' n)"
    using nd_def nodeState'_def property_simps t by auto

  have v_eq[simp]: "v' = v" by (intro ext, auto simp add: v'_def v_def)
  have v\<^sub>c_eq[simp]: "v\<^sub>c' = v\<^sub>c" by (intro ext, auto simp add: v\<^sub>c'_def v\<^sub>c_def)
  have isCommitted_eq[simp]: "isCommitted' = isCommitted" by (intro ext, auto simp add: isCommitted'_def isCommitted_def)
  have committedTo_eq[simp]: "committed\<^sub><' = committed\<^sub><" by (intro ext, auto simp add: committedTo'_def committedTo_def)
  have V_eq[simp]: "V' = V" using v\<^sub>c_eq V'_def V_def by blast
  have lastCommittedClusterStateBefore_eq[simp]: "lastCommittedClusterStateBefore' = lastCommittedClusterStateBefore"
    unfolding lastCommittedClusterStateBefore_def lastCommittedClusterStateBefore'_def v\<^sub>c_eq ..
  have promised_eq: "\<And>i n n' t. promised' i n n' t = promised i n n' t" by (simp add: promised_def promised'_def)
  have prevAccepted_eq: "\<And>i t q. prevAccepted' i t q  = prevAccepted i t q" by (simp add: prevAccepted_def prevAccepted'_def)

  show ?thesis
    apply (intro zenI)
                        apply (unfold message_simps committedTo_eq V_eq v_eq
        lastCommittedClusterStateBefore_eq property_simps promised_eq prevAccepted_eq)
  proof -
    from finite_messages show "finite messages'" by (simp add: messages')
    from Vote_future show "\<And>i i' s t t' a. s \<midarrow>\<langle> Vote i t a \<rangle>\<leadsto> \<Longrightarrow> i < i' \<Longrightarrow> t' < t \<Longrightarrow> \<not> s \<midarrow>\<langle> PublishResponse i' t' \<rangle>\<leadsto>".
    from Vote_None show "\<And>i s t t'. s \<midarrow>\<langle> Vote i t NO_TERM \<rangle>\<leadsto> \<Longrightarrow> t' < t \<Longrightarrow> \<not> s \<midarrow>\<langle> PublishResponse i t' \<rangle>\<leadsto>".
    from Vote_Some_lt show "\<And>i s t t'. s \<midarrow>\<langle> Vote i t (SomeTerm t') \<rangle>\<leadsto> \<Longrightarrow> t' < t".
    from Vote_Some_PublishResponse show "\<And>i s t t'. s \<midarrow>\<langle> Vote i t (SomeTerm t') \<rangle>\<leadsto> \<Longrightarrow> s \<midarrow>\<langle> PublishResponse i t' \<rangle>\<leadsto>".
    from Vote_Some_max show "\<And>i s t t' t''. s \<midarrow>\<langle> Vote i t (SomeTerm t') \<rangle>\<leadsto> \<Longrightarrow> t' < t'' \<Longrightarrow> t'' < t \<Longrightarrow> \<not> s \<midarrow>\<langle> PublishResponse i t'' \<rangle>\<leadsto>".
    from Vote_not_broadcast show "\<And>i t a d. \<langle> Vote i t a \<rangle>\<rightarrow> d \<Longrightarrow> d \<noteq> Broadcast".
    from Vote_unique_destination show "\<And>i' i s t a a' d d'. s \<midarrow>\<langle> Vote i t a \<rangle>\<rightarrow> d \<Longrightarrow> s \<midarrow>\<langle> Vote i' t a' \<rangle>\<rightarrow> d' \<Longrightarrow> d = d'".
    from currentNode_nodeState show "\<And>n. currentNode (nodeState n) = n" .
    from committedTo_firstUncommittedSlot show "\<And>n. committed\<^sub>< (firstUncommittedSlot (nodeState n))" .
    from firstUncommittedSlot_PublishResponse show "\<And>n i t. firstUncommittedSlot (nodeState n) < i \<Longrightarrow> \<not> n \<midarrow>\<langle> PublishResponse i t \<rangle>\<leadsto>" .
    from lastAcceptedTerm_None show "\<And>n i t. lastAcceptedTerm (nodeState n) = NO_TERM \<Longrightarrow> \<not> n \<midarrow>\<langle> PublishResponse (firstUncommittedSlot (nodeState n)) t \<rangle>\<leadsto>".
    from lastAcceptedTerm_Some_sent show "\<And>n t. lastAcceptedTerm (nodeState n) = SomeTerm t \<Longrightarrow> n \<midarrow>\<langle> PublishResponse (firstUncommittedSlot (nodeState n)) t \<rangle>\<leadsto>".
    from lastAcceptedTerm_Some_max show "\<And>n t t'. lastAcceptedTerm (nodeState n) = SomeTerm t \<Longrightarrow> n \<midarrow>\<langle> PublishResponse (firstUncommittedSlot (nodeState n)) t' \<rangle>\<leadsto> \<Longrightarrow> t' \<le> t".
    from Vote_slot_function show "\<And>n i i' t a a'. n \<midarrow>\<langle> Vote i t a \<rangle>\<leadsto> \<Longrightarrow> n \<midarrow>\<langle> Vote i' t a' \<rangle>\<leadsto> \<Longrightarrow> i = i'".
    from currentClusterState_lastCommittedClusterStateBefore show "\<And>n. currentClusterState (nodeState n) = lastCommittedClusterStateBefore (firstUncommittedSlot (nodeState n))".
    from PublishRequest_committedTo show "\<And>i t x. \<langle> PublishRequest i t x \<rangle>\<leadsto> \<Longrightarrow> committed\<^sub>< i".
    from PublishRequest_function show "\<And>i t x x'. \<langle> PublishRequest i t x \<rangle>\<leadsto> \<Longrightarrow> \<langle> PublishRequest i t x' \<rangle>\<leadsto> \<Longrightarrow> x = x'".
    from PublishResponse_PublishRequest show "\<And>i s t. s \<midarrow>\<langle> PublishResponse i t \<rangle>\<leadsto> \<Longrightarrow> \<exists>x. \<langle> PublishRequest i t x \<rangle>\<leadsto>".
    from ApplyCommit_quorum show "\<And>i t. \<langle> ApplyCommit i t \<rangle>\<leadsto> \<Longrightarrow> \<exists>q\<in>majorities (V i). \<forall>s\<in>q. s \<midarrow>\<langle> PublishResponse i t \<rangle>\<leadsto>".
    from currentVotingNodes_firstUncommittedSlot show "\<And>n. currentVotingNodes (nodeState n) = V (firstUncommittedSlot (nodeState n))".
    from firstUncommittedSlot_PublishRequest show "\<And>i n t x. firstUncommittedSlot (nodeState n) < i \<Longrightarrow> \<not> n \<midarrow>\<langle> PublishRequest i t x \<rangle>\<leadsto>".
    from lastAcceptedTerm_Some_value show "\<And>n t. lastAcceptedTerm (nodeState n) = SomeTerm t \<Longrightarrow> \<langle> PublishRequest (firstUncommittedSlot (nodeState n)) t (lastAcceptedValue (nodeState n)) \<rangle>\<leadsto>".
    from PublishRequest_quorum show "\<And>i s t x. s \<midarrow>\<langle> PublishRequest i t x \<rangle>\<leadsto> \<Longrightarrow> \<exists>q\<in>majorities (V i). (\<forall>n\<in>q. promised i n s t) \<and> (prevAccepted i t q = {} \<or> (\<exists>t'. v i t = v i t' \<and> maxTerm (prevAccepted i t q) \<le> t' \<and> \<langle> PublishResponse i t' \<rangle>\<leadsto> \<and> t' < t))".
    from CatchUpResponse_committedTo show "\<And>i conf cs. \<langle> CatchUpResponse i conf cs \<rangle>\<leadsto> \<Longrightarrow> committed\<^sub>< i".
    from CatchUpResponse_V show "\<And>i conf cs. \<langle> CatchUpResponse i conf cs \<rangle>\<leadsto> \<Longrightarrow> V i = conf".
    from CatchUpResponse_lastCommittedClusterStateBefore show "\<And>i conf cs. \<langle> CatchUpResponse i conf cs \<rangle>\<leadsto> \<Longrightarrow> lastCommittedClusterStateBefore i = cs".

    from Vote_currentTerm currentTerm_increases
    show "\<And>n i t a. n \<midarrow>\<langle> Vote i t a \<rangle>\<leadsto> \<Longrightarrow> t \<le> currentTerm (nodeState' n)"
      using dual_order.trans by blast

    from PublishRequest_publishPermitted_currentTerm currentTerm_increases property_simps
    show "\<And>n t x. n \<midarrow>\<langle> PublishRequest (firstUncommittedSlot (nodeState n)) t x \<rangle>\<leadsto> \<Longrightarrow> publishPermitted (nodeState' n) \<Longrightarrow> t < currentTerm (nodeState' n)"
      by (metis False PublishRequest_currentTerm dual_order.trans leI nd_def nodeState_unchanged)

    from joinVotes
    show "\<And>n n'. n' \<in> joinVotes (nodeState' n) \<Longrightarrow> promised (firstUncommittedSlot (nodeState n)) n' n (currentTerm (nodeState' n))"
      unfolding nodeState'_def by (auto simp add: nd'_def)

    from PublishRequest_currentTerm currentTerm_increases
    show "\<And>n t x. n \<midarrow>\<langle> PublishRequest (firstUncommittedSlot (nodeState n)) t x \<rangle>\<leadsto> \<Longrightarrow> t \<le> currentTerm (nodeState' n)"
      using dual_order.trans by blast

    from publishVotes
    show "\<And>n n'. n' \<in> publishVotes (nodeState' n) \<Longrightarrow> n' \<midarrow>\<langle> PublishResponse (firstUncommittedSlot (nodeState n)) (currentTerm (nodeState' n)) \<rangle>\<leadsto>"
      unfolding nodeState'_def by (auto simp add: nd'_def)

    from electionWon_isQuorum show "\<And>n. electionWon (nodeState' n) \<Longrightarrow> isQuorum (nodeState n) (joinVotes (nodeState' n))"
      unfolding nodeState'_def by (auto simp add: nd'_def)

    from lastAcceptedTerm_Some_currentTerm currentTerm_increases
    show "\<And>n t. lastAcceptedTerm (nodeState n) = SomeTerm t \<Longrightarrow> t \<le> currentTerm (nodeState' n)"
      using dual_order.trans by blast

    show "\<And>n n' a'. \<not> (\<exists>x. \<langle> PublishRequest (firstUncommittedSlot (nodeState n)) (currentTerm (nodeState' n)) x \<rangle>\<leadsto>) \<Longrightarrow> n' \<in> joinVotes (nodeState' n) \<Longrightarrow> n' \<midarrow>\<langle> Vote (firstUncommittedSlot (nodeState n)) (currentTerm (nodeState' n)) a' \<rangle>\<rightarrow> (OneNode n) \<Longrightarrow> a' \<le> lastAcceptedTerm (nodeState n)"
      by (metis ex_in_conv joinVotes_max nodeState_unchanged property_simps(10))
  qed
qed

lemma (in zenStep) sendVote_invariants:
  assumes messages': "messages' = sendTo (OneNode d\<^sub>0) (nd'',
    Some (Vote (firstUncommittedSlot nd) (currentTerm nd) (lastAcceptedTerm nd)))"
  assumes nd': "nd' = nd"
  assumes not_sent: "\<And>i a. \<not> n\<^sub>0 \<midarrow>\<langle> Vote i (currentTerm nd) a \<rangle>\<leadsto>"
  assumes not_accepted: "\<And>t'. lastAcceptedTerm nd = SomeTerm t' \<Longrightarrow> t' < currentTerm nd"
  shows "zen messages' nodeState'"
proof -
  have messages': "messages' = insert \<lparr>sender = n\<^sub>0, destination = OneNode d\<^sub>0,
                       payload = Vote (firstUncommittedSlot nd) (currentTerm nd) (lastAcceptedTerm nd)\<rparr> messages"
    by (simp add: messages')

  have nodeState'[simp]: "nodeState' = nodeState"
    by (intro ext, auto simp add: nodeState'_def nd' nd_def)

  have message_simps[simp]:
    "\<And>s d i t. (s \<midarrow>\<langle> ApplyCommit i t \<rangle>\<rightarrow>' d) = (s \<midarrow>\<langle> ApplyCommit i t \<rangle>\<rightarrow> d)"
    "\<And>s d i t x. (s \<midarrow>\<langle> PublishRequest i t x \<rangle>\<rightarrow>' d) = (s \<midarrow>\<langle> PublishRequest i t x \<rangle>\<rightarrow> d)"
    "\<And>s d i t. (s \<midarrow>\<langle> PublishResponse i t \<rangle>\<rightarrow>' d) = (s \<midarrow>\<langle> PublishResponse i t \<rangle>\<rightarrow> d)"
    "\<And>d i t. (\<langle> ApplyCommit i t \<rangle>\<rightarrow>' d) = (\<langle> ApplyCommit i t \<rangle>\<rightarrow> d)"
    "\<And>d i t x. (\<langle> PublishRequest i t x \<rangle>\<rightarrow>' d) = (\<langle> PublishRequest i t x \<rangle>\<rightarrow> d)"
    "\<And>d i t. (\<langle> PublishResponse i t \<rangle>\<rightarrow>' d) = (\<langle> PublishResponse i t \<rangle>\<rightarrow> d)"
    "\<And>s i t. (s \<midarrow>\<langle> ApplyCommit i t \<rangle>\<leadsto>') = (s \<midarrow>\<langle> ApplyCommit i t \<rangle>\<leadsto>)"
    "\<And>s i t x. (s \<midarrow>\<langle> PublishRequest i t x \<rangle>\<leadsto>') = (s \<midarrow>\<langle> PublishRequest i t x \<rangle>\<leadsto>)"
    "\<And>s i t. (s \<midarrow>\<langle> PublishResponse i t \<rangle>\<leadsto>') = (s \<midarrow>\<langle> PublishResponse i t \<rangle>\<leadsto>)"
    "\<And>i t. (\<langle> ApplyCommit i t \<rangle>\<leadsto>') = (\<langle> ApplyCommit i t \<rangle>\<leadsto>)"
    "\<And>i t x. (\<langle> PublishRequest i t x \<rangle>\<leadsto>') = (\<langle> PublishRequest i t x \<rangle>\<leadsto>)"
    "\<And>i t. (\<langle> PublishResponse i t \<rangle>\<leadsto>') = (\<langle> PublishResponse i t \<rangle>\<leadsto>)"
    "\<And>s d i conf cs. (s \<midarrow>\<langle> CatchUpResponse i conf cs \<rangle>\<rightarrow>' d) = (s \<midarrow>\<langle> CatchUpResponse i conf cs \<rangle>\<rightarrow> d)"
    "\<And>d i conf cs. (\<langle> CatchUpResponse i conf cs \<rangle>\<rightarrow>' d) = (\<langle> CatchUpResponse i conf cs \<rangle>\<rightarrow> d)"
    "\<And>s i conf cs. (s \<midarrow>\<langle> CatchUpResponse i conf cs \<rangle>\<leadsto>') = (s \<midarrow>\<langle> CatchUpResponse i conf cs \<rangle>\<leadsto>)"
    "\<And>d i conf cs. (\<langle> CatchUpResponse i conf cs \<rangle>\<leadsto>') = (\<langle> CatchUpResponse i conf cs \<rangle>\<leadsto>)"
    by (unfold isMessageFromTo'_def isMessageTo'_def isMessageFrom'_def isMessage'_def,
        auto simp add: messages' isMessageFromTo_def isMessageTo_def isMessageFrom_def isMessage_def)

  have Vote':
    "\<And>s d i t' a. (s \<midarrow>\<langle> Vote i t' a \<rangle>\<rightarrow>' d) =
    ((s \<midarrow>\<langle> Vote i t' a \<rangle>\<rightarrow> d)
      \<or> (s, i, t', a, d) = (n\<^sub>0, firstUncommittedSlot nd, currentTerm nd, lastAcceptedTerm nd, OneNode d\<^sub>0))"
    "\<And>d i t' a. (\<langle> Vote i t' a \<rangle>\<rightarrow>' d) =
    ((\<langle> Vote i t' a \<rangle>\<rightarrow> d)
      \<or> (i, t', a, d) = (firstUncommittedSlot nd, currentTerm nd, lastAcceptedTerm nd, OneNode d\<^sub>0))"
    "\<And>s i t' a. (s \<midarrow>\<langle> Vote i t' a \<rangle>\<leadsto>') =
    ((s \<midarrow>\<langle> Vote i t' a \<rangle>\<leadsto>)
      \<or> (s, i, t', a) = (n\<^sub>0, firstUncommittedSlot nd, currentTerm nd, lastAcceptedTerm nd))"
    "\<And>i t' a. (\<langle> Vote i t' a \<rangle>\<leadsto>') =
    ((\<langle> Vote i t' a \<rangle>\<leadsto>)
      \<or> (i, t', a) = (firstUncommittedSlot nd, currentTerm nd, lastAcceptedTerm nd))"
    by (unfold isMessageFromTo'_def isMessageFromTo_def isMessageTo'_def isMessageTo_def
        isMessageFrom'_def isMessageFrom_def isMessage'_def isMessage_def, auto simp add: messages')

  have v_eq[simp]: "v' = v" by (intro ext, auto simp add: v'_def v_def)
  have v\<^sub>c_eq[simp]: "v\<^sub>c' = v\<^sub>c" by (intro ext, auto simp add: v\<^sub>c'_def v\<^sub>c_def)
  have isCommitted_eq[simp]: "isCommitted' = isCommitted" by (intro ext, auto simp add: isCommitted'_def isCommitted_def)
  have committedTo_eq[simp]: "committed\<^sub><' = committed\<^sub><" by (intro ext, auto simp add: committedTo'_def committedTo_def)
  have V_eq[simp]: "V' = V" using v\<^sub>c_eq V'_def V_def by blast
  have lastCommittedClusterStateBefore_eq[simp]: "lastCommittedClusterStateBefore' = lastCommittedClusterStateBefore"
    unfolding lastCommittedClusterStateBefore_def lastCommittedClusterStateBefore'_def v\<^sub>c_eq ..

  have promised_eq: "\<And>i s dn t. promised' i s dn t = (promised i s dn t \<or> (firstUncommittedSlot nd \<le> i \<and> s = n\<^sub>0 \<and> dn = d\<^sub>0 \<and> t = currentTerm nd))"
    unfolding promised'_def promised_def Vote' by auto

  have prevAccepted_eq: "\<And>i t q. prevAccepted' i t q = prevAccepted i t q \<union> {t'. n\<^sub>0 \<in> q \<and> i = firstUncommittedSlot nd \<and> t = currentTerm nd \<and> lastAcceptedTerm nd = SomeTerm t'}"
    unfolding prevAccepted_def prevAccepted'_def Vote' by auto

  have property_simps[simp]:
    "\<And>n. currentNode (nodeState' n) = currentNode (nodeState n)"
    "\<And>n. firstUncommittedSlot (nodeState' n) = firstUncommittedSlot (nodeState n)"
    "\<And>n. currentVotingNodes (nodeState' n) = currentVotingNodes (nodeState n)"
    "\<And>n q. isQuorum (nodeState' n) q = isQuorum (nodeState n) q"
    "\<And>n. lastAcceptedTerm (nodeState' n) = lastAcceptedTerm (nodeState n)"
    "\<And>n. lastAcceptedValue (nodeState' n) = lastAcceptedValue (nodeState n)"
    "\<And>n. currentTerm (nodeState' n) = currentTerm (nodeState n)"
    "\<And>n. publishPermitted (nodeState' n) = publishPermitted (nodeState n)"
    "\<And>n. publishVotes (nodeState' n) = publishVotes (nodeState n)"
    "\<And>n. currentClusterState (nodeState' n) = currentClusterState (nodeState n)"
    "\<And>n. electionWon (nodeState' n) = electionWon (nodeState n)"
    "\<And>n. joinVotes (nodeState' n) = joinVotes (nodeState n)"
    by (unfold nodeState'_def, auto simp add: nd_def isQuorum_def nd' addElectionVote_def Let_def)

  show "zen messages' nodeState'"
    apply (intro zenI)
                        apply (unfold message_simps property_simps committedTo_eq V_eq lastCommittedClusterStateBefore_eq v_eq)
  proof -
    from finite_messages show "finite messages'" by (simp add: messages')
    from currentNode_nodeState show "\<And>n. currentNode (nodeState n) = n" .
    from committedTo_firstUncommittedSlot show "\<And>n. committed\<^sub>< (firstUncommittedSlot (nodeState n))" .
    from firstUncommittedSlot_PublishResponse show "\<And>n i t. firstUncommittedSlot (nodeState n) < i \<Longrightarrow> \<not> n \<midarrow>\<langle> PublishResponse i t \<rangle>\<leadsto>" .
    from lastAcceptedTerm_None show "\<And>n i t. lastAcceptedTerm (nodeState n) = NO_TERM \<Longrightarrow> \<not> n \<midarrow>\<langle> PublishResponse (firstUncommittedSlot (nodeState n)) t \<rangle>\<leadsto>".
    from lastAcceptedTerm_Some_sent show "\<And>n t. lastAcceptedTerm (nodeState n) = SomeTerm t \<Longrightarrow> n \<midarrow>\<langle> PublishResponse (firstUncommittedSlot (nodeState n)) t \<rangle>\<leadsto>".
    from lastAcceptedTerm_Some_max show "\<And>n t t'. lastAcceptedTerm (nodeState n) = SomeTerm t \<Longrightarrow> n \<midarrow>\<langle> PublishResponse (firstUncommittedSlot (nodeState n)) t' \<rangle>\<leadsto> \<Longrightarrow> t' \<le> t".
    from electionWon_isQuorum show "\<And>n. electionWon (nodeState n) \<Longrightarrow> isQuorum (nodeState n) (joinVotes (nodeState n))".
    from publishVotes show "\<And>n n'. n' \<in> publishVotes (nodeState n) \<Longrightarrow> n' \<midarrow>\<langle> PublishResponse (firstUncommittedSlot (nodeState n)) (currentTerm (nodeState n)) \<rangle>\<leadsto>".
    from currentClusterState_lastCommittedClusterStateBefore show "\<And>n. currentClusterState (nodeState n) = lastCommittedClusterStateBefore (firstUncommittedSlot (nodeState n))".
    from PublishRequest_committedTo show "\<And>i t x. \<langle> PublishRequest i t x \<rangle>\<leadsto> \<Longrightarrow> committed\<^sub>< i".
    from PublishRequest_function show "\<And>i t x x'. \<langle> PublishRequest i t x \<rangle>\<leadsto> \<Longrightarrow> \<langle> PublishRequest i t x' \<rangle>\<leadsto> \<Longrightarrow> x = x'".
    from PublishResponse_PublishRequest show "\<And>i s t. s \<midarrow>\<langle> PublishResponse i t \<rangle>\<leadsto> \<Longrightarrow> \<exists>x. \<langle> PublishRequest i t x \<rangle>\<leadsto>".
    from ApplyCommit_quorum show "\<And>i t. \<langle> ApplyCommit i t \<rangle>\<leadsto> \<Longrightarrow> \<exists>q\<in>majorities (V i). \<forall>s\<in>q. s \<midarrow>\<langle> PublishResponse i t \<rangle>\<leadsto>".
    from currentVotingNodes_firstUncommittedSlot show "\<And>n. currentVotingNodes (nodeState n) = V (firstUncommittedSlot (nodeState n))".
    from firstUncommittedSlot_PublishRequest show "\<And>i n t x. firstUncommittedSlot (nodeState n) < i \<Longrightarrow> \<not> n \<midarrow>\<langle> PublishRequest i t x \<rangle>\<leadsto>".
    from lastAcceptedTerm_Some_value show "\<And>n t. lastAcceptedTerm (nodeState n) = SomeTerm t \<Longrightarrow> \<langle> PublishRequest (firstUncommittedSlot (nodeState n)) t (lastAcceptedValue (nodeState n)) \<rangle>\<leadsto>".
    from PublishRequest_currentTerm show "\<And>n t x. n \<midarrow>\<langle> PublishRequest (firstUncommittedSlot (nodeState n)) t x \<rangle>\<leadsto> \<Longrightarrow> t \<le> currentTerm (nodeState n)".
    from PublishRequest_publishPermitted_currentTerm show "\<And>n t x. n \<midarrow>\<langle> PublishRequest (firstUncommittedSlot (nodeState n)) t x \<rangle>\<leadsto> \<Longrightarrow> publishPermitted (nodeState n) \<Longrightarrow> t < currentTerm (nodeState n)".
    from CatchUpResponse_committedTo show "\<And>i conf cs. \<langle> CatchUpResponse i conf cs \<rangle>\<leadsto> \<Longrightarrow> committed\<^sub>< i".
    from CatchUpResponse_V show "\<And>i conf cs. \<langle> CatchUpResponse i conf cs \<rangle>\<leadsto> \<Longrightarrow> V i = conf".
    from CatchUpResponse_lastCommittedClusterStateBefore show "\<And>i conf cs. \<langle> CatchUpResponse i conf cs \<rangle>\<leadsto> \<Longrightarrow> lastCommittedClusterStateBefore i = cs".
    from lastAcceptedTerm_Some_currentTerm show "\<And>n t. lastAcceptedTerm (nodeState n) = SomeTerm t \<Longrightarrow> t \<le> currentTerm (nodeState n)".

    from Vote_currentTerm show "\<And>n i t a. n \<midarrow>\<langle> Vote i t a \<rangle>\<leadsto>' \<Longrightarrow> t \<le> currentTerm (nodeState n)"
      unfolding Vote' by (auto simp add: nd_def)

    from joinVotes show "\<And>n n'. n' \<in> joinVotes (nodeState n) \<Longrightarrow> promised' (firstUncommittedSlot (nodeState n)) n' n (currentTerm (nodeState n))"
      unfolding promised_eq by simp

    from Vote_future firstUncommittedSlot_PublishResponse
    show "\<And>i i' s t t' a. s \<midarrow>\<langle> Vote i t a \<rangle>\<leadsto>' \<Longrightarrow> i < i' \<Longrightarrow> t' < t \<Longrightarrow> \<not> s \<midarrow>\<langle> PublishResponse i' t' \<rangle>\<leadsto>"
      unfolding Vote' nd_def by auto

    from Vote_None show "\<And>i s t t'. s \<midarrow>\<langle> Vote i t NO_TERM \<rangle>\<leadsto>' \<Longrightarrow> t' < t \<Longrightarrow> \<not> s \<midarrow>\<langle> PublishResponse i t' \<rangle>\<leadsto>"
      unfolding Vote' using Vote_future lastAcceptedTerm_None nd' nd'_def by auto

    from Vote_Some_lt show "\<And>i s t t'. s \<midarrow>\<langle> Vote i t (SomeTerm t') \<rangle>\<leadsto>' \<Longrightarrow> t' < t"
      unfolding Vote' using not_accepted lastAcceptedTerm_def
      by (smt fst_conv TermOption.distinct(1) snd_conv)

    from Vote_Some_PublishResponse show "\<And>i s t t'. s \<midarrow>\<langle> Vote i t (SomeTerm t') \<rangle>\<leadsto>' \<Longrightarrow> s \<midarrow>\<langle> PublishResponse i t' \<rangle>\<leadsto>"
      unfolding Vote' using lastAcceptedTerm_Some_sent nd' nd'_def nd_def
      by (smt Pair_inject TermOption.distinct(1))

    from Vote_Some_max show "\<And>i s t t' t''. s \<midarrow>\<langle> Vote i t (SomeTerm t') \<rangle>\<leadsto>' \<Longrightarrow> t' < t'' \<Longrightarrow> t'' < t \<Longrightarrow> \<not> s \<midarrow>\<langle> PublishResponse i t'' \<rangle>\<leadsto>"
      unfolding Vote' nd_def
      by (smt Pair_inject TermOption.distinct(1) \<open>\<And>t' t na. \<lbrakk>lastAcceptedTerm (nodeState na) = SomeTerm t; na \<midarrow>\<langle> PublishResponse (firstUncommittedSlot (nodeState na)) t' \<rangle>\<leadsto>\<rbrakk> \<Longrightarrow> t' \<le> t\<close> leD)

    from Vote_not_broadcast show "\<And>i t a d. \<langle> Vote i t a \<rangle>\<rightarrow>' d \<Longrightarrow> d \<noteq> Broadcast"
      unfolding Vote' by blast

    from Vote_unique_destination show "\<And>i' i s t a a' d d'. s \<midarrow>\<langle> Vote i t a \<rangle>\<rightarrow>' d \<Longrightarrow> s \<midarrow>\<langle> Vote i' t a' \<rangle>\<rightarrow>' d' \<Longrightarrow> d = d'"
      unfolding Vote'  using isMessageFrom_def not_sent by auto

    from Vote_slot_function show "\<And>n i i' t a a'. n \<midarrow>\<langle> Vote i t a \<rangle>\<leadsto>' \<Longrightarrow> n \<midarrow>\<langle> Vote i' t a' \<rangle>\<leadsto>' \<Longrightarrow> i = i'"
      unfolding Vote'
      by (metis Vote'(3) Message.inject(2) RoutedMessage.ext_inject insert_iff isMessageFrom'_def isMessageFromTo'_def isMessageFromTo_def isMessageFrom_def messages' not_sent)

    from joinVotes_max show "\<And>n n' a'. \<not> (\<exists>x. \<langle> PublishRequest (firstUncommittedSlot (nodeState n)) (currentTerm (nodeState n)) x \<rangle>\<leadsto>) \<Longrightarrow> n' \<in> joinVotes (nodeState n) \<Longrightarrow> n' \<midarrow>\<langle> Vote (firstUncommittedSlot (nodeState n)) (currentTerm (nodeState n)) a' \<rangle>\<rightarrow>' (OneNode n) \<Longrightarrow> a' \<le> lastAcceptedTerm (nodeState n)"
      unfolding Vote'
      by (smt Vote'(1) Message.inject(2) RoutedMessage.ext_inject insert_iff isMessageFromTo'_def isMessageFrom_def joinVotes messages' not_sent promised_def zen.Vote_slot_function zenMessages.Vote_value_function zenMessages_axioms zen_axioms)

    fix i s t x
    assume "s \<midarrow>\<langle> PublishRequest i t x \<rangle>\<leadsto>"
    from PublishRequest_quorum [OF this]
    obtain q where q_majority: "q \<in> majorities (V i)" 
      and q_promised: "\<And>n. n \<in> q \<Longrightarrow> promised i n s t"
      and q_value: "prevAccepted i t q = {} \<or> (\<exists>t'. v i t = v i t' \<and> maxTerm (prevAccepted i t q) \<le> t' \<and> \<langle> PublishResponse i t' \<rangle>\<leadsto> \<and> t' < t)" by blast

    from not_sent q_promised
    have no_new_terms: "{t'. n\<^sub>0 \<in> q \<and> i = firstUncommittedSlot nd \<and> t = currentTerm nd \<and> lastAcceptedTerm nd = SomeTerm t'} = {}"
      unfolding isMessageFrom_def promised_def by blast
    hence prevAccepted_eq: "prevAccepted' i t q = prevAccepted i t q"
      unfolding prevAccepted_eq by auto

    show "\<exists>q\<in>majorities (V i). (\<forall>n\<in>q. promised' i n s t) \<and> (prevAccepted' i t q = {} \<or> (\<exists>t'. v i t = v i t' \<and> maxTerm (prevAccepted' i t q) \<le> t' \<and> \<langle> PublishResponse i t' \<rangle>\<leadsto> \<and> t' < t))"
    proof (intro bexI conjI)
      from q_majority show "q \<in> majorities (V i)" .
      from q_promised show "\<forall>n\<in>q. promised' i n s t" unfolding promised_eq by simp

      from q_value show "prevAccepted' i t q = {} \<or> (\<exists>t'. v i t = v i t' \<and> maxTerm (prevAccepted' i t q) \<le> t' \<and> \<langle> PublishResponse i t' \<rangle>\<leadsto> \<and> t' < t)"
        unfolding prevAccepted_eq by simp
    qed
  qed
qed

lemma (in zenStep) handleStartJoin_invariants:
  fixes t
  defines "result \<equiv> handleStartJoin t nd"
  assumes nd': "nd' = fst result"
  assumes sent: "s \<midarrow>\<langle> StartJoin t \<rangle>\<leadsto>"
  assumes messages': "messages' = sendTo (OneNode s) result"
  shows "zen messages' nodeState'"
proof (cases "currentTerm nd < t")
  case False
  hence result: "result = (nd, None)" by (simp add: result_def handleStartJoin_def)
  have "messages' = messages" by (auto simp add: messages' result)
  moreover
  have "nodeState' = nodeState" by (intro ext, unfold nodeState'_def, simp add: nd' result nd_def)
  moreover note zen_axioms
  ultimately show ?thesis by simp
next
  case True
  hence new_term: "currentTerm nd < t" by simp

  have result: "result = (ensureCurrentTerm t nd, Some (Vote (firstUncommittedSlot nd) t (lastAcceptedTerm nd)))"
    by (simp add: result_def handleStartJoin_def True)

  have nd': "nd' = ensureCurrentTerm t nd" by (simp add: nd' result)

  have zen1: "zen messages nodeState'"
  proof (intro zenStep.ensureCurrentTerm_invariants)
    show "messages = messages" ..
    from nd' show "nodeState' n\<^sub>0 = ensureCurrentTerm t (nodeState n\<^sub>0)" by (simp add: nd'_def nd_def)
    show "zenStep messages nodeState messages nodeState' n\<^sub>0"
      by (intro_locales, intro zenStep_axioms.intro nodeState_unchanged, simp_all)
  qed

  with nodeState_unchanged messages_subset
  have zenStep1: "zenStep messages nodeState' messages' nodeState' n\<^sub>0"
    by (intro_locales, simp add: zen_def, intro zenStep_axioms.intro, auto)

  have nodeState': "nodeState' = (\<lambda> n. if n = n\<^sub>0 then nd' else nodeState' n)"
    by (auto simp add: nodeState'_def)

  have nd'_eq: "nodeState' n\<^sub>0 = nd'"
    by (simp add: nodeState'_def)

  from True
  have currentTerm_nd': "currentTerm nd' = t" by (auto simp add: nd')

  have [simp]: "firstUncommittedSlot nd' = firstUncommittedSlot nd"
    "lastAcceptedTerm nd' = lastAcceptedTerm nd"
    by (auto simp add: nd' ensureCurrentTerm_def lastAcceptedTerm_def
        lastAcceptedValue_def)

  show "zen messages' nodeState'"
  proof (intro zenStep.sendVote_invariants [OF zenStep1], unfold nd'_eq currentTerm_nd', simp_all add: messages' result)
    show "\<And>i a. \<forall>d. \<lparr>sender = n\<^sub>0, destination = d, payload = Vote i t a\<rparr> \<notin> messages"
      using nd_def new_term zen.Vote_currentTerm zen_axioms by fastforce
    show "\<And>t'. lastAcceptedTerm nd = SomeTerm t' \<Longrightarrow> t' < t" using True lastAcceptedTerm_Some_currentTerm unfolding nd_def by fastforce
  qed
qed

lemma (in zenStep) addElectionVote_invariants:
  assumes nd': "nd' = addElectionVote s i a nd"
  assumes messages': "messages' = messages"
  assumes sent: "s \<midarrow>\<langle> Vote i (currentTerm nd) a \<rangle>\<rightarrow> (OneNode n\<^sub>0)"
  assumes precondition:
    "i < firstUncommittedSlot nd \<or> (i = firstUncommittedSlot nd \<and> a \<le> lastAcceptedTerm nd)"
  shows "zen messages' nodeState'"
proof -
  from precondition have slot: "i \<le> firstUncommittedSlot nd" by auto

  have message_simps[simp]:
    "\<And>s p d. (s \<midarrow>\<langle> p \<rangle>\<rightarrow>' d) = (s \<midarrow>\<langle> p \<rangle>\<rightarrow> d)"
    "\<And>p d. (\<langle> p \<rangle>\<rightarrow>' d) = (\<langle> p \<rangle>\<rightarrow> d)"
    "\<And>s p. (s \<midarrow>\<langle> p \<rangle>\<leadsto>') = (s \<midarrow>\<langle> p \<rangle>\<leadsto>)"
    "\<And>p. (\<langle> p \<rangle>\<leadsto>') = (\<langle> p \<rangle>\<leadsto>)"
    by (unfold isMessageFromTo'_def isMessageTo'_def isMessageFrom'_def isMessage'_def,
        auto simp add: messages' isMessageFromTo_def isMessageTo_def isMessageFrom_def isMessage_def)

  have property_simps[simp]:
    "\<And>n. currentNode (nodeState' n) = currentNode (nodeState n)"
    "\<And>n. firstUncommittedSlot (nodeState' n) = firstUncommittedSlot (nodeState n)"
    "\<And>n. currentVotingNodes (nodeState' n) = currentVotingNodes (nodeState n)"
    "\<And>n q. isQuorum (nodeState' n) q = isQuorum (nodeState n) q"
    "\<And>n. lastAcceptedTerm (nodeState' n) = lastAcceptedTerm (nodeState n)"
    "\<And>n. lastAcceptedValue (nodeState' n) = lastAcceptedValue (nodeState n)"
    "\<And>n. currentTerm (nodeState' n) = currentTerm (nodeState n)"
    "\<And>n. publishPermitted (nodeState' n) = publishPermitted (nodeState n)"
    "\<And>n. publishVotes (nodeState' n) = publishVotes (nodeState n)"
    "\<And>n. currentClusterState (nodeState' n) = currentClusterState (nodeState n)"
    by (unfold nodeState'_def, auto simp add: nd_def isQuorum_def nd' addElectionVote_def Let_def
        lastAcceptedValue_def lastAcceptedTerm_def)

  have updated_properties:
    "\<And>n. joinVotes (nodeState' n) = joinVotes (nodeState n) \<union> (if n = n\<^sub>0 then {s} else {})"
    "\<And>n. electionWon (nodeState' n) = (if n = n\<^sub>0 then isQuorum nd (insert s (joinVotes nd)) else electionWon (nodeState n))"
    unfolding nodeState'_def by (auto simp add: nd' addElectionVote_def Let_def nd_def)

  have v_eq[simp]: "v' = v" by (intro ext, auto simp add: v'_def v_def)
  have v\<^sub>c_eq[simp]: "v\<^sub>c' = v\<^sub>c" by (intro ext, auto simp add: v\<^sub>c'_def v\<^sub>c_def)
  have isCommitted_eq[simp]: "isCommitted' = isCommitted" by (intro ext, auto simp add: isCommitted'_def isCommitted_def)
  have committedTo_eq[simp]: "committed\<^sub><' = committed\<^sub><" by (intro ext, auto simp add: committedTo'_def committedTo_def)
  have V_eq[simp]: "V' = V" using v\<^sub>c_eq V'_def V_def by blast
  have promised_eq[simp]: "promised' = promised" by (intro ext, auto simp add: promised'_def promised_def)
  have prevAccepted_eq[simp]: "prevAccepted' = prevAccepted" by (intro ext, auto simp add: prevAccepted'_def prevAccepted_def)
  have lastCommittedClusterStateBefore_eq[simp]: "lastCommittedClusterStateBefore' = lastCommittedClusterStateBefore"
    unfolding lastCommittedClusterStateBefore_def lastCommittedClusterStateBefore'_def v\<^sub>c_eq ..

  show "zen messages' nodeState'"
    apply (intro zenI)
                        apply (unfold message_simps property_simps committedTo_eq v_eq V_eq promised_eq lastCommittedClusterStateBefore_eq prevAccepted_eq)
  proof -
    from finite_messages show "finite messages'" by (simp add: messages')
    from Vote_future show "\<And>i i' s t t' a. s \<midarrow>\<langle> Vote i t a \<rangle>\<leadsto> \<Longrightarrow> i < i' \<Longrightarrow> t' < t \<Longrightarrow> \<not> s \<midarrow>\<langle> PublishResponse i' t' \<rangle>\<leadsto>".
    from Vote_None show "\<And>i s t t'. s \<midarrow>\<langle> Vote i t NO_TERM \<rangle>\<leadsto> \<Longrightarrow> t' < t \<Longrightarrow> \<not> s \<midarrow>\<langle> PublishResponse i t' \<rangle>\<leadsto>".
    from Vote_Some_lt show "\<And>i s t t'. s \<midarrow>\<langle> Vote i t (SomeTerm t') \<rangle>\<leadsto> \<Longrightarrow> t' < t".
    from Vote_Some_PublishResponse show "\<And>i s t t'. s \<midarrow>\<langle> Vote i t (SomeTerm t') \<rangle>\<leadsto> \<Longrightarrow> s \<midarrow>\<langle> PublishResponse i t' \<rangle>\<leadsto>".
    from Vote_Some_max show "\<And>i s t t' t''. s \<midarrow>\<langle> Vote i t (SomeTerm t') \<rangle>\<leadsto> \<Longrightarrow> t' < t'' \<Longrightarrow> t'' < t \<Longrightarrow> \<not> s \<midarrow>\<langle> PublishResponse i t'' \<rangle>\<leadsto>".
    from Vote_not_broadcast show "\<And>i t a d. \<langle> Vote i t a \<rangle>\<rightarrow> d \<Longrightarrow> d \<noteq> Broadcast".
    from Vote_unique_destination show "\<And>i' i s t a a' d d'. s \<midarrow>\<langle> Vote i t a \<rangle>\<rightarrow> d \<Longrightarrow> s \<midarrow>\<langle> Vote i' t a' \<rangle>\<rightarrow> d' \<Longrightarrow> d = d'".
    from currentNode_nodeState show "\<And>n. currentNode (nodeState n) = n" .
    from committedTo_firstUncommittedSlot show "\<And>n. committed\<^sub>< (firstUncommittedSlot (nodeState n))" .
    from firstUncommittedSlot_PublishResponse show "\<And>n i t. firstUncommittedSlot (nodeState n) < i \<Longrightarrow> \<not> n \<midarrow>\<langle> PublishResponse i t \<rangle>\<leadsto>" .
    from lastAcceptedTerm_None show "\<And>n i t. lastAcceptedTerm (nodeState n) = NO_TERM \<Longrightarrow> \<not> n \<midarrow>\<langle> PublishResponse (firstUncommittedSlot (nodeState n)) t \<rangle>\<leadsto>".
    from lastAcceptedTerm_Some_sent show "\<And>n t. lastAcceptedTerm (nodeState n) = SomeTerm t \<Longrightarrow> n \<midarrow>\<langle> PublishResponse (firstUncommittedSlot (nodeState n)) t \<rangle>\<leadsto>".
    from lastAcceptedTerm_Some_max show "\<And>n t t'. lastAcceptedTerm (nodeState n) = SomeTerm t \<Longrightarrow> n \<midarrow>\<langle> PublishResponse (firstUncommittedSlot (nodeState n)) t' \<rangle>\<leadsto> \<Longrightarrow> t' \<le> t".
    from Vote_currentTerm show "\<And>n i t a. n \<midarrow>\<langle> Vote i t a \<rangle>\<leadsto> \<Longrightarrow> t \<le> currentTerm (nodeState n)".
    from Vote_slot_function show "\<And>n i i' t a a'. n \<midarrow>\<langle> Vote i t a \<rangle>\<leadsto> \<Longrightarrow> n \<midarrow>\<langle> Vote i' t a' \<rangle>\<leadsto> \<Longrightarrow> i = i'".
    from publishVotes show "\<And>n n'. n' \<in> publishVotes (nodeState n) \<Longrightarrow> n' \<midarrow>\<langle> PublishResponse (firstUncommittedSlot (nodeState n)) (currentTerm (nodeState n)) \<rangle>\<leadsto>".
    from currentClusterState_lastCommittedClusterStateBefore show "\<And>n. currentClusterState (nodeState n) = lastCommittedClusterStateBefore (firstUncommittedSlot (nodeState n))".
    from PublishRequest_committedTo show "\<And>i t x. \<langle> PublishRequest i t x \<rangle>\<leadsto> \<Longrightarrow> committed\<^sub>< i".
    from PublishRequest_function show "\<And>i t x x'. \<langle> PublishRequest i t x \<rangle>\<leadsto> \<Longrightarrow> \<langle> PublishRequest i t x' \<rangle>\<leadsto> \<Longrightarrow> x = x'".
    from PublishResponse_PublishRequest show "\<And>i s t. s \<midarrow>\<langle> PublishResponse i t \<rangle>\<leadsto> \<Longrightarrow> \<exists>x. \<langle> PublishRequest i t x \<rangle>\<leadsto>".
    from ApplyCommit_quorum show "\<And>i t. \<langle> ApplyCommit i t \<rangle>\<leadsto> \<Longrightarrow> \<exists>q\<in>majorities (V i). \<forall>s\<in>q. s \<midarrow>\<langle> PublishResponse i t \<rangle>\<leadsto>".
    from currentVotingNodes_firstUncommittedSlot show "\<And>n. currentVotingNodes (nodeState n) = V (firstUncommittedSlot (nodeState n))".
    from firstUncommittedSlot_PublishRequest show "\<And>i n t x. firstUncommittedSlot (nodeState n) < i \<Longrightarrow> \<not> n \<midarrow>\<langle> PublishRequest i t x \<rangle>\<leadsto>".
    from lastAcceptedTerm_Some_value show "\<And>n t. lastAcceptedTerm (nodeState n) = SomeTerm t \<Longrightarrow> \<langle> PublishRequest (firstUncommittedSlot (nodeState n)) t (lastAcceptedValue (nodeState n)) \<rangle>\<leadsto>".
    from PublishRequest_currentTerm show "\<And>n t x. n \<midarrow>\<langle> PublishRequest (firstUncommittedSlot (nodeState n)) t x \<rangle>\<leadsto> \<Longrightarrow> t \<le> currentTerm (nodeState n)".
    from PublishRequest_publishPermitted_currentTerm show "\<And>n t x. n \<midarrow>\<langle> PublishRequest (firstUncommittedSlot (nodeState n)) t x \<rangle>\<leadsto> \<Longrightarrow> publishPermitted (nodeState n) \<Longrightarrow> t < currentTerm (nodeState n)".
    from PublishRequest_quorum show "\<And>i s t x. s \<midarrow>\<langle> PublishRequest i t x \<rangle>\<leadsto> \<Longrightarrow> \<exists>q\<in>majorities (V i). (\<forall>n\<in>q. promised i n s t) \<and> (prevAccepted i t q = {} \<or> (\<exists>t'. v i t = v i t' \<and> maxTerm (prevAccepted i t q) \<le> t' \<and> \<langle> PublishResponse i t' \<rangle>\<leadsto> \<and> t' < t))".
    from CatchUpResponse_committedTo show "\<And>i conf cs. \<langle> CatchUpResponse i conf cs \<rangle>\<leadsto> \<Longrightarrow> committed\<^sub>< i".
    from CatchUpResponse_V show "\<And>i conf cs. \<langle> CatchUpResponse i conf cs \<rangle>\<leadsto> \<Longrightarrow> V i = conf".
    from CatchUpResponse_lastCommittedClusterStateBefore show "\<And>i conf cs. \<langle> CatchUpResponse i conf cs \<rangle>\<leadsto> \<Longrightarrow> lastCommittedClusterStateBefore i = cs".
    from lastAcceptedTerm_Some_currentTerm show "\<And>n t. lastAcceptedTerm (nodeState n) = SomeTerm t \<Longrightarrow> t \<le> currentTerm (nodeState n)".

    from electionWon_isQuorum show "\<And>n. electionWon (nodeState' n) \<Longrightarrow> isQuorum (nodeState n) (joinVotes (nodeState' n))"
      unfolding updated_properties by (auto simp add: nd_def)

    fix n

    from joinVotes nd_def precondition sent
    show "\<And>n'. n' \<in> joinVotes (nodeState' n) \<Longrightarrow> promised (firstUncommittedSlot (nodeState n)) n' n (currentTerm (nodeState n))"
      using precondition sent unfolding updated_properties nd_def apply (cases "n = n\<^sub>0", simp_all)
      using nd_def promised_def slot by blast

    fix n' a'
    assume fresh_request: "\<not> (\<exists>x. \<langle> PublishRequest (firstUncommittedSlot (nodeState n)) (currentTerm (nodeState n)) x \<rangle>\<leadsto>)"
      and n'_joinVotes: "n' \<in> joinVotes (nodeState' n)"
      and n'_vote: "n' \<midarrow>\<langle> Vote (firstUncommittedSlot (nodeState n)) (currentTerm (nodeState n)) a' \<rangle>\<rightarrow> (OneNode n)"

    show "a' \<le> lastAcceptedTerm (nodeState n)"
    proof (cases "n = n\<^sub>0")
      case False
      with fresh_request n'_joinVotes n'_vote joinVotes_max
      show ?thesis by (simp add: updated_properties)
    next
      case n_eq: True

      show ?thesis
      proof (cases "n' = s")
        case n'_eq: True
        have i: "i = firstUncommittedSlot nd"
        proof (intro Vote_slot_function)
          from n'_vote show "n' \<midarrow>\<langle> Vote (firstUncommittedSlot nd) (currentTerm nd) a' \<rangle>\<leadsto>"
            unfolding isMessageFrom_def nd_def n_eq by auto
          from sent show "n' \<midarrow>\<langle> Vote i (currentTerm nd) a \<rangle>\<leadsto>"
            unfolding isMessageFrom_def nd_def n'_eq by auto
        qed

        have a: "a = a'"
        proof (intro Vote_value_function)
          from n'_vote show "n' \<midarrow>\<langle> Vote (firstUncommittedSlot nd) (currentTerm nd) a' \<rangle>\<leadsto>"
            unfolding isMessageFrom_def nd_def n_eq by auto
          from sent show "n' \<midarrow>\<langle> Vote (firstUncommittedSlot nd) (currentTerm nd) a \<rangle>\<leadsto>"
            unfolding isMessageFrom_def nd_def n'_eq i by auto
        qed

        from precondition show ?thesis by (auto simp add: i a n_eq nd_def)
      next
        case False with n'_joinVotes have n'_joinVotes: "n' \<in> joinVotes nd" by (simp add: nd_def n_eq updated_properties)
        with fresh_request n'_vote joinVotes_max show ?thesis unfolding nd_def n_eq by auto
      qed
    qed
  qed
qed

lemma (in zenStep) publishValue_invariants:
  fixes x
  defines "result \<equiv> publishValue x nd"
  assumes nd': "nd' = fst result"
  assumes messages': "messages' = sendTo Broadcast result"
  assumes x: "lastAcceptedTerm nd \<noteq> NO_TERM \<Longrightarrow> x = lastAcceptedValue nd"
  shows "zen messages' nodeState'"
proof (cases "electionWon nd \<and> publishPermitted nd")
  case False
  hence result: "result = (nd, None)" by (simp add: result_def publishValue_def)
  have "messages' = messages" by (auto simp add: messages' result)
  moreover
  have "nodeState' = nodeState" by (intro ext, unfold nodeState'_def, simp add: nd' result nd_def)
  moreover note zen_axioms
  ultimately show ?thesis by simp
next
  case won: True
  hence result: "result = (nd \<lparr> publishPermitted := False \<rparr>,
                           Some (PublishRequest (firstUncommittedSlot nd) (currentTerm nd) x))"
    by (simp add: result_def publishValue_def)

  have messages': "messages' = insert \<lparr>sender = n\<^sub>0, destination = Broadcast, payload = PublishRequest (firstUncommittedSlot nd) (currentTerm nd) x\<rparr> messages"
    by (simp add: messages' result)

  have message_simps:
    "\<And>s d i t a. (s \<midarrow>\<langle> Vote i t a \<rangle>\<rightarrow>' d) = (s \<midarrow>\<langle> Vote i t a \<rangle>\<rightarrow> d)"
    "\<And>s d i t. (s \<midarrow>\<langle> PublishResponse i t \<rangle>\<rightarrow>' d) = (s \<midarrow>\<langle> PublishResponse i t \<rangle>\<rightarrow> d)"
    "\<And>s d i t. (s \<midarrow>\<langle> ApplyCommit i t \<rangle>\<rightarrow>' d) = (s \<midarrow>\<langle> ApplyCommit i t \<rangle>\<rightarrow> d)"
    "\<And>d i t a. (\<langle> Vote i t a \<rangle>\<rightarrow>' d) = (\<langle> Vote i t a \<rangle>\<rightarrow> d)"
    "\<And>d i t. (\<langle> PublishResponse i t \<rangle>\<rightarrow>' d) = (\<langle> PublishResponse i t \<rangle>\<rightarrow> d)"
    "\<And>d i t. (\<langle> ApplyCommit i t \<rangle>\<rightarrow>' d) = (\<langle> ApplyCommit i t \<rangle>\<rightarrow> d)"
    "\<And>s i t a. (s \<midarrow>\<langle> Vote i t a \<rangle>\<leadsto>') = (s \<midarrow>\<langle> Vote i t a \<rangle>\<leadsto>)"
    "\<And>s i t. (s \<midarrow>\<langle> PublishResponse i t \<rangle>\<leadsto>') = (s \<midarrow>\<langle> PublishResponse i t \<rangle>\<leadsto>)"
    "\<And>s i t. (s \<midarrow>\<langle> ApplyCommit i t \<rangle>\<leadsto>') = (s \<midarrow>\<langle> ApplyCommit i t \<rangle>\<leadsto>)"
    "\<And>d i t a. (\<langle> Vote i t a \<rangle>\<leadsto>') = (\<langle> Vote i t a \<rangle>\<leadsto>)"
    "\<And>d i t. (\<langle> PublishResponse i t \<rangle>\<leadsto>') = (\<langle> PublishResponse i t \<rangle>\<leadsto>)"
    "\<And>d i t. (\<langle> ApplyCommit i t \<rangle>\<leadsto>') = (\<langle> ApplyCommit i t \<rangle>\<leadsto>)"
    "\<And>s d i conf cs. (s \<midarrow>\<langle> CatchUpResponse i conf cs \<rangle>\<rightarrow>' d) = (s \<midarrow>\<langle> CatchUpResponse i conf cs \<rangle>\<rightarrow> d)"
    "\<And>d i conf cs. (\<langle> CatchUpResponse i conf cs \<rangle>\<rightarrow>' d) = (\<langle> CatchUpResponse i conf cs \<rangle>\<rightarrow> d)"
    "\<And>s i conf cs. (s \<midarrow>\<langle> CatchUpResponse i conf cs \<rangle>\<leadsto>') = (s \<midarrow>\<langle> CatchUpResponse i conf cs \<rangle>\<leadsto>)"
    "\<And>d i conf cs. (\<langle> CatchUpResponse i conf cs \<rangle>\<leadsto>') = (\<langle> CatchUpResponse i conf cs \<rangle>\<leadsto>)"
    by (auto simp add: isMessageFromTo'_def isMessageTo'_def isMessage'_def isMessageFrom'_def,
        auto simp add: isMessageFromTo_def isMessageTo_def isMessage_def isMessageFrom_def messages')

  have PublishRequest': "\<And>s d i t x'. (s \<midarrow>\<langle> PublishRequest i t x' \<rangle>\<rightarrow>' d) = ((s \<midarrow>\<langle> PublishRequest i t x' \<rangle>\<rightarrow> d)
          \<or> (s, d, i, t, x') = (n\<^sub>0, Broadcast, firstUncommittedSlot nd, currentTerm nd, x))"
    "\<And>s i t x'. (s \<midarrow>\<langle> PublishRequest i t x' \<rangle>\<leadsto>') = ((s \<midarrow>\<langle> PublishRequest i t x' \<rangle>\<leadsto>)
          \<or> (s, i, t, x') = (n\<^sub>0, firstUncommittedSlot nd, currentTerm nd, x))"
    "\<And>d i t x'. (\<langle> PublishRequest i t x' \<rangle>\<rightarrow>' d) = ((\<langle> PublishRequest i t x' \<rangle>\<rightarrow> d)
          \<or> (d, i, t, x') = (Broadcast, firstUncommittedSlot nd, currentTerm nd, x))"
    "\<And>i t x'. (\<langle> PublishRequest i t x' \<rangle>\<leadsto>') = ((\<langle> PublishRequest i t x' \<rangle>\<leadsto>)
          \<or> (i, t, x') = (firstUncommittedSlot nd, currentTerm nd, x))"
    by (auto simp add: isMessageFromTo'_def isMessageFrom'_def isMessageTo'_def isMessage'_def,
        auto simp add: messages' isMessageFromTo_def isMessageFrom_def isMessageTo_def isMessage_def)

  have fresh_request: "\<And>x. \<not> \<langle> PublishRequest (firstUncommittedSlot nd) (currentTerm nd) x \<rangle>\<leadsto>"
  proof (intro notI)
    fix x'
    assume "\<langle> PublishRequest (firstUncommittedSlot nd) (currentTerm nd) x' \<rangle>\<leadsto>"
    with won obtain s d where
      s: "s \<midarrow>\<langle> PublishRequest (firstUncommittedSlot nd) (currentTerm nd) x' \<rangle>\<rightarrow> d"
      by (auto simp add: isMessage_def isMessageFrom_def)

    with PublishRequest_quorum [where s = s and i = "firstUncommittedSlot nd" and t = "currentTerm nd" and x = x']
    obtain q where q: "q \<in> majorities (V (firstUncommittedSlot nd))" and promised: "\<And>n. n \<in> q \<Longrightarrow> promised (firstUncommittedSlot nd) n s (currentTerm nd)"
      by (auto simp add: isMessageFrom_def, blast)

    from won have "isQuorum nd (joinVotes nd)"
      by (unfold nd_def, intro electionWon_isQuorum, simp)
    with currentVotingNodes_firstUncommittedSlot [of n\<^sub>0]
    have "joinVotes nd \<in> majorities (V (firstUncommittedSlot nd))" using nd_def isQuorum_def by auto

    from q this V_intersects have "q \<inter> joinVotes nd \<noteq> {}"
      by (auto simp add: intersects_def)
    then obtain n where n: "n \<in> q" "n \<in> joinVotes nd" by auto

    from promised [OF `n \<in> q`]
    obtain i' a' where "n \<midarrow>\<langle> Vote i' (currentTerm nd) a' \<rangle>\<rightarrow> (OneNode s)"
      by (auto simp add: promised_def)

    moreover from joinVotes n
    obtain i'' a'' where "n \<midarrow>\<langle> Vote i'' (currentTerm nd) a'' \<rangle>\<rightarrow> (OneNode n\<^sub>0)"
      by (auto simp add: nd_def promised_def, blast)

    ultimately have "OneNode s = OneNode n\<^sub>0"
      by (intro Vote_unique_destination)

    with s have "n\<^sub>0 \<midarrow>\<langle> PublishRequest (firstUncommittedSlot nd) (currentTerm nd) x' \<rangle>\<leadsto>"
      by (auto simp add: isMessageFrom_def)

    hence "currentTerm nd < currentTerm (nodeState n\<^sub>0)"
    proof (intro PublishRequest_publishPermitted_currentTerm, fold nd_def)
      from won show "publishPermitted nd" by (simp add: nd_def)
    qed
    thus False by (simp add: nd_def)
  qed

  have v_eq: "\<And>i t x. \<langle> PublishRequest i t x \<rangle>\<leadsto> \<Longrightarrow> v' i t = v i t"
  proof -
    fix i t x'

    assume "\<langle> PublishRequest i t x' \<rangle>\<leadsto>"
    with fresh_request have ne: "(i, t) \<noteq> (firstUncommittedSlot nd, currentTerm nd)" by auto

    have sent_eq: "\<And>x''. \<langle> PublishRequest i t x'' \<rangle>\<leadsto>' = \<langle> PublishRequest i t x'' \<rangle>\<leadsto>"
    proof (intro iffI)
      fix x''
      show "\<langle> PublishRequest i t x'' \<rangle>\<leadsto> \<Longrightarrow> \<langle> PublishRequest i t x'' \<rangle>\<leadsto>'" by (simp add: PublishRequest')
      assume "\<langle> PublishRequest i t x'' \<rangle>\<leadsto>'" with ne show "\<langle> PublishRequest i t x'' \<rangle>\<leadsto>"
        by (unfold PublishRequest', auto)
    qed

    show "v' i t = v i t"
      by (unfold v'_def v_def sent_eq, simp)
  qed

  have isCommitted_eq: "isCommitted' = isCommitted"
    by (intro ext, simp add: isCommitted_def isCommitted'_def message_simps)

  have committedTo_eq: "committed\<^sub><' = committed\<^sub><"
    by (intro ext, simp add: committedTo_def committedTo'_def isCommitted_eq)

  have v\<^sub>c_eq: "\<And>i. isCommitted i \<Longrightarrow> v\<^sub>c' i = v\<^sub>c i"
  proof -
    fix i assume i: "isCommitted i"
    define t where "t \<equiv> SOME t. \<langle> ApplyCommit i t \<rangle>\<leadsto>"
    have t: "\<langle> ApplyCommit i t \<rangle>\<leadsto>"
    proof -
      from i obtain t where t: "\<langle> ApplyCommit i t \<rangle>\<leadsto>" by (auto simp add: isCommitted_def)
      thus ?thesis by (unfold t_def, intro someI)
    qed
    hence v_eq: "v' i t = v i t" by (intro v_eq [OF ApplyCommit_PublishRequest])

    have "v\<^sub>c' i = v' i t" by (simp add: v\<^sub>c'_def t_def message_simps)
    also note v_eq
    also have "v i t = v\<^sub>c i" by (simp add: v\<^sub>c_def t_def)
    finally show "?thesis i" by simp
  qed

  have V_eq: "\<And>i. committed\<^sub>< i \<Longrightarrow> V' i = V i"
  proof -
    fix i assume i: "committed\<^sub>< i"
    thus "?thesis i"
    proof (induct i)
      case (Suc i')
      hence prems: "committed\<^sub>< i'" "isCommitted i'" unfolding committedTo_def by auto
      thus ?case using Suc v\<^sub>c_eq by simp
    qed simp
  qed

  have lastCommittedClusterStateBefore_eq: "\<And>i. committed\<^sub>< i \<Longrightarrow> lastCommittedClusterStateBefore' i = lastCommittedClusterStateBefore i"
  proof -
    fix i assume "committed\<^sub>< i"
    thus "?thesis i"
    proof (induct i)
      case (Suc i')
      hence prems: "committed\<^sub>< i'" "isCommitted i'" unfolding committedTo_def by auto
      thus ?case using Suc v\<^sub>c_eq by (cases "v\<^sub>c i'", simp_all)
    qed simp
  qed

  have promised_eq: "\<And>i n n' t. promised' i n n' t = promised i n n' t"
    by (simp add: promised_def promised'_def message_simps)

  have prevAccepted_eq: "\<And>i t q. prevAccepted' i t q  = prevAccepted i t q"
    by (simp add: prevAccepted_def prevAccepted'_def message_simps)

  from committedTo_firstUncommittedSlot V_eq
  have V_slot_eq: "\<And>n. V' (firstUncommittedSlot (nodeState n)) = V (firstUncommittedSlot (nodeState n))" by blast

  have lastCommittedClusterStateBefore_slot_eq: "\<And>n. lastCommittedClusterStateBefore' (firstUncommittedSlot (nodeState n)) = lastCommittedClusterStateBefore (firstUncommittedSlot (nodeState n))"
    by (intro lastCommittedClusterStateBefore_eq committedTo_firstUncommittedSlot)

  have v_prevAccepted_eq: "\<And>i t q. prevAccepted i t q \<noteq> {} \<Longrightarrow> v' i (maxTerm (prevAccepted i t q)) = v i (maxTerm (prevAccepted i t q))"
  proof -
    fix i t q
    assume nonempty: "prevAccepted i t q \<noteq> {}"
    have "maxTerm (prevAccepted i t q) \<in> prevAccepted i t q"
      by (intro maxTerm_mem finite_prevAccepted nonempty)
    hence "\<langle> Vote i t (SomeTerm (maxTerm (prevAccepted i t q))) \<rangle>\<leadsto>"
      by (auto simp add: prevAccepted_def isMessage_def)
    hence "\<langle> PublishResponse i (maxTerm (prevAccepted i t q)) \<rangle>\<leadsto>"
      using Vote_Some_PublishResponse unfolding isMessage_def by blast
    then obtain x' where "\<langle> PublishRequest i (maxTerm (prevAccepted i t q)) x' \<rangle>\<leadsto>"
      using PublishResponse_PublishRequest unfolding isMessage_def by blast
    thus "?thesis i t q" by (intro v_eq)
  qed

  have nd': "nd' = nd \<lparr> publishPermitted := False \<rparr>" by (simp add: nd' result)

  have property_simps[simp]:
    "\<And>n. currentNode (nodeState' n) = currentNode (nodeState n)"
    "\<And>n. firstUncommittedSlot (nodeState' n) = firstUncommittedSlot (nodeState n)"
    "\<And>n. currentVotingNodes (nodeState' n) = currentVotingNodes (nodeState n)"
    "\<And>n q. isQuorum (nodeState' n) q = isQuorum (nodeState n) q"
    "\<And>n. lastAcceptedValue (nodeState' n) = lastAcceptedValue (nodeState n)"
    "\<And>n. lastAcceptedTerm (nodeState' n) = lastAcceptedTerm (nodeState n)"
    "\<And>n. currentTerm (nodeState' n) = currentTerm (nodeState n)"
    "\<And>n. publishVotes (nodeState' n) = publishVotes (nodeState n)"
    "\<And>n. currentClusterState (nodeState' n) = currentClusterState (nodeState n)"
    "\<And>n. electionWon (nodeState' n) = electionWon (nodeState n)"
    "\<And>n. joinVotes (nodeState' n) = joinVotes (nodeState n)"
    by (unfold nodeState'_def, auto simp add: nd_def isQuorum_def nd' addElectionVote_def Let_def
        lastAcceptedTerm_def lastAcceptedValue_def)

  show ?thesis
    apply (intro zenI)
                        apply (unfold message_simps committedTo_eq V_slot_eq
        lastCommittedClusterStateBefore_slot_eq property_simps promised_eq prevAccepted_eq)
  proof -
    from Vote_future show "\<And>i i' s t t' a. s \<midarrow>\<langle> Vote i t a \<rangle>\<leadsto> \<Longrightarrow> i < i' \<Longrightarrow> t' < t \<Longrightarrow> \<not> s \<midarrow>\<langle> PublishResponse i' t' \<rangle>\<leadsto>".
    from Vote_None show "\<And>i s t t'. s \<midarrow>\<langle> Vote i t NO_TERM \<rangle>\<leadsto> \<Longrightarrow> t' < t \<Longrightarrow> \<not> s \<midarrow>\<langle> PublishResponse i t' \<rangle>\<leadsto>".
    from Vote_Some_lt show "\<And>i s t t'. s \<midarrow>\<langle> Vote i t (SomeTerm t') \<rangle>\<leadsto> \<Longrightarrow> t' < t".
    from Vote_Some_PublishResponse show "\<And>i s t t'. s \<midarrow>\<langle> Vote i t (SomeTerm t') \<rangle>\<leadsto> \<Longrightarrow> s \<midarrow>\<langle> PublishResponse i t' \<rangle>\<leadsto>".
    from Vote_Some_max show "\<And>i s t t' t''. s \<midarrow>\<langle> Vote i t (SomeTerm t') \<rangle>\<leadsto> \<Longrightarrow> t' < t'' \<Longrightarrow> t'' < t \<Longrightarrow> \<not> s \<midarrow>\<langle> PublishResponse i t'' \<rangle>\<leadsto>".
    from Vote_not_broadcast show "\<And>i t a d. \<langle> Vote i t a \<rangle>\<rightarrow> d \<Longrightarrow> d \<noteq> Broadcast".
    from Vote_unique_destination show "\<And>i' i s t a a' d d'. s \<midarrow>\<langle> Vote i t a \<rangle>\<rightarrow> d \<Longrightarrow> s \<midarrow>\<langle> Vote i' t a' \<rangle>\<rightarrow> d' \<Longrightarrow> d = d'".
    from currentNode_nodeState show "\<And>n. currentNode (nodeState n) = n" .
    from committedTo_firstUncommittedSlot show "\<And>n. committed\<^sub>< (firstUncommittedSlot (nodeState n))" .
    from firstUncommittedSlot_PublishResponse show "\<And>n i t. firstUncommittedSlot (nodeState n) < i \<Longrightarrow> \<not> n \<midarrow>\<langle> PublishResponse i t \<rangle>\<leadsto>" .
    from lastAcceptedTerm_None show "\<And>n i t. lastAcceptedTerm (nodeState n) = NO_TERM \<Longrightarrow> \<not> n \<midarrow>\<langle> PublishResponse (firstUncommittedSlot (nodeState n)) t \<rangle>\<leadsto>".
    from lastAcceptedTerm_Some_sent show "\<And>n t. lastAcceptedTerm (nodeState n) = SomeTerm t \<Longrightarrow> n \<midarrow>\<langle> PublishResponse (firstUncommittedSlot (nodeState n)) t \<rangle>\<leadsto>".
    from lastAcceptedTerm_Some_max show "\<And>n t t'. lastAcceptedTerm (nodeState n) = SomeTerm t \<Longrightarrow> n \<midarrow>\<langle> PublishResponse (firstUncommittedSlot (nodeState n)) t' \<rangle>\<leadsto> \<Longrightarrow> t' \<le> t".
    from Vote_currentTerm show "\<And>n i t a. n \<midarrow>\<langle> Vote i t a \<rangle>\<leadsto> \<Longrightarrow> t \<le> currentTerm (nodeState n)".
    from Vote_slot_function show "\<And>n i i' t a a'. n \<midarrow>\<langle> Vote i t a \<rangle>\<leadsto> \<Longrightarrow> n \<midarrow>\<langle> Vote i' t a' \<rangle>\<leadsto> \<Longrightarrow> i = i'".
    from electionWon_isQuorum show "\<And>n. electionWon (nodeState n) \<Longrightarrow> isQuorum (nodeState n) (joinVotes (nodeState n))".
    from publishVotes show "\<And>n n'. n' \<in> publishVotes (nodeState n) \<Longrightarrow> n' \<midarrow>\<langle> PublishResponse (firstUncommittedSlot (nodeState n)) (currentTerm (nodeState n)) \<rangle>\<leadsto>".
    from currentClusterState_lastCommittedClusterStateBefore show "\<And>n. currentClusterState (nodeState n) = lastCommittedClusterStateBefore (firstUncommittedSlot (nodeState n))".
    from joinVotes show "\<And>n n'. n' \<in> joinVotes (nodeState n) \<Longrightarrow> promised (firstUncommittedSlot (nodeState n)) n' n (currentTerm (nodeState n))".
    from currentVotingNodes_firstUncommittedSlot show "\<And>n. currentVotingNodes (nodeState n) = V (firstUncommittedSlot (nodeState n))".
    from lastAcceptedTerm_Some_currentTerm show "\<And>n t. lastAcceptedTerm (nodeState n) = SomeTerm t \<Longrightarrow> t \<le> currentTerm (nodeState n)".

    {
      fix i conf cs assume a: "\<langle> CatchUpResponse i conf cs \<rangle>\<leadsto>"
      with CatchUpResponse_committedTo show "committed\<^sub>< i" .
      with a V_eq lastCommittedClusterStateBefore_eq CatchUpResponse_V CatchUpResponse_lastCommittedClusterStateBefore
      show "V' i = conf" "lastCommittedClusterStateBefore' i = cs" by auto
    }

    from lastAcceptedTerm_Some_value  PublishRequest'
    show "\<And>n t. lastAcceptedTerm (nodeState n) = SomeTerm t \<Longrightarrow> \<langle> PublishRequest (firstUncommittedSlot (nodeState n)) t (lastAcceptedValue (nodeState n)) \<rangle>\<leadsto>'"
      by (meson isMessage'_def isMessageFrom'_def isMessageFrom_def isMessage_def)

    from PublishRequest_currentTerm
    show "\<And>n t x. n \<midarrow>\<langle> PublishRequest (firstUncommittedSlot (nodeState n)) t x \<rangle>\<leadsto>' \<Longrightarrow> t \<le> currentTerm (nodeState n)"
      using PublishRequest' isMessageFrom'_def isMessageFrom_def nd_def by fastforce

    from fresh_request PublishRequest_function
    show "\<And>i t x x'. \<langle> PublishRequest i t x \<rangle>\<leadsto>' \<Longrightarrow> \<langle> PublishRequest i t x' \<rangle>\<leadsto>' \<Longrightarrow> x = x'"
      unfolding PublishRequest' by auto

    from messages' finite_messages show "finite messages'" by simp

    from PublishResponse_PublishRequest show "\<And>i s t. s \<midarrow>\<langle> PublishResponse i t \<rangle>\<leadsto> \<Longrightarrow> \<exists>x. \<langle> PublishRequest i t x \<rangle>\<leadsto>'"
      unfolding PublishRequest' by blast

    from ApplyCommit_quorum V_eq isCommitted_committedTo
    show "\<And>i t. \<langle> ApplyCommit i t \<rangle>\<leadsto> \<Longrightarrow> \<exists>q\<in>majorities (V' i). \<forall>s\<in>q. s \<midarrow>\<langle> PublishResponse i t \<rangle>\<leadsto>"
      unfolding isCommitted_def by fastforce

    fix n

    from firstUncommittedSlot_PublishRequest
    show "\<And>i t x. firstUncommittedSlot (nodeState n) < i \<Longrightarrow> \<not> n \<midarrow>\<langle> PublishRequest i t x \<rangle>\<leadsto>'"
      by (cases "n = n\<^sub>0", unfold nodeState'_def PublishRequest' isMessageFrom'_def isMessageFrom_def, auto simp add: nd' nd_def)

    from PublishRequest_publishPermitted_currentTerm
    show "\<And>t x. n \<midarrow>\<langle> PublishRequest (firstUncommittedSlot (nodeState n)) t x \<rangle>\<leadsto>' \<Longrightarrow> publishPermitted (nodeState' n) \<Longrightarrow> t < currentTerm (nodeState n)"
      unfolding isMessageFrom'_def PublishRequest'
      by (cases "n = n\<^sub>0", auto simp add: nodeState'_def nd' isMessageFrom_def)

    show PublishRequest_committedTo': "\<And>i t x. \<langle> PublishRequest i t x \<rangle>\<leadsto>' \<Longrightarrow> committed\<^sub>< i"
      using PublishRequest_committedTo committedTo_firstUncommittedSlot
      by (auto simp add: committedTo_def PublishRequest' nd_def)

    from joinVotes_max
    show "\<And>n' a'. \<not> (\<exists>x. \<langle> PublishRequest (firstUncommittedSlot (nodeState n)) (currentTerm (nodeState n)) x \<rangle>\<leadsto>') \<Longrightarrow> n' \<in> joinVotes (nodeState n) \<Longrightarrow> n' \<midarrow>\<langle> Vote (firstUncommittedSlot (nodeState n)) (currentTerm (nodeState n)) a' \<rangle>\<rightarrow> (OneNode n) \<Longrightarrow> a' \<le> lastAcceptedTerm (nodeState n)"
      by (cases "n = n\<^sub>0", auto simp add: nodeState'_def nd' PublishRequest')

    {
      fix i s t x'
      assume "s \<midarrow>\<langle> PublishRequest i t x' \<rangle>\<leadsto>'"
      thus "\<exists>q\<in>majorities (V' i). (\<forall>n\<in>q. promised i n s t) \<and> (prevAccepted i t q = {} \<or> (\<exists>t'. v' i t = v' i t' \<and> maxTerm (prevAccepted i t q) \<le> t' \<and> \<langle> PublishResponse i t' \<rangle>\<leadsto> \<and> t' < t))"
        unfolding PublishRequest'
      proof (elim disjE)
        assume sent: "s \<midarrow>\<langle> PublishRequest i t x' \<rangle>\<leadsto>"
        from sent have [simp]: "V' i = V i" by (intro V_eq PublishRequest_committedTo, auto simp add: isMessage_def)
        from sent have [simp]: "v' i t = v i t" by (intro v_eq, auto simp add: isMessage_def)

        from PublishRequest_quorum [OF sent]
        obtain q where q_quorum: "q \<in> majorities (V i)"
          and q_promised: "\<And>n. n \<in> q \<Longrightarrow> promised i n s t"
          and q_value: "prevAccepted i t q = {} \<or> (\<exists>t'. v i t = v i t' \<and> maxTerm (prevAccepted i t q) \<le> t' \<and> \<langle> PublishResponse i t' \<rangle>\<leadsto> \<and> t' < t)"
          by blast

        show ?thesis
        proof (cases "prevAccepted i t q = {}")
          case True with q_quorum q_promised show ?thesis by auto
        next
          case False
          with q_value obtain t' where t': "v i t = v i t'" "maxTerm (prevAccepted i t q) \<le> t'" "\<langle> PublishResponse i t' \<rangle>\<leadsto>" "t' < t" by blast

          show ?thesis
          proof (intro bexI conjI disjI2 exI ballI)
            from q_promised show "\<And>n. n \<in> q \<Longrightarrow> promised i n s t" .
            from t' show "maxTerm (prevAccepted i t q) \<le> t'" "\<langle> PublishResponse i t' \<rangle>\<leadsto>" "t' < t" by simp_all
            from q_quorum show "q \<in> majorities (V' i)" by simp

            have "v' i t = v i t" by simp
            also have "... = v i t'" using t' by simp
            also have "... = v' i t'" unfolding v_def v'_def PublishRequest' using t'
              by (metis PublishResponse_PublishRequest_v fresh_request fst_conv snd_conv)
            finally show "v' i t = v' i t'" .
          qed
        qed
      next
        assume "(s, i, t, x') = (n\<^sub>0, firstUncommittedSlot nd, currentTerm nd, x)"
        hence [simp]: "s = n\<^sub>0" "i = firstUncommittedSlot nd" "t = currentTerm nd" "x' = x" by simp_all

        have Vi: "V' i = V i"
          using committedTo_firstUncommittedSlot by (intro V_eq, simp add: nd_def)
        define q where "q \<equiv> joinVotes nd"

        show ?thesis
        proof (intro bexI conjI ballI)
          from won have "isQuorum nd q" unfolding nd_def q_def by (intro electionWon_isQuorum, simp)
          with currentVotingNodes_firstUncommittedSlot Vi show "q \<in> majorities (V' i)" by (auto simp add: nd_def isQuorum_def)
          fix n assume "n \<in> q"
          with joinVotes show "promised i n s t" by (simp add: nd_def q_def)
        next
          show "prevAccepted i t q = {} \<or> (\<exists>t'. v' i t = v' i t' \<and> maxTerm (prevAccepted i t q) \<le> t' \<and> \<langle> PublishResponse i t' \<rangle>\<leadsto> \<and> t' < t)"
          proof (cases "prevAccepted i t q = {}")
            case True thus ?thesis by simp
          next
            case False
            then obtain t' n' where n'_vote: "n' \<in> q" and n'_sent: "n' \<midarrow>\<langle> Vote i t (SomeTerm t') \<rangle>\<leadsto>"
              unfolding prevAccepted_def by auto

            from n'_sent n'_vote
            have n'_sent: "n' \<midarrow>\<langle> Vote i t (SomeTerm t') \<rangle>\<rightarrow> (OneNode n\<^sub>0)" unfolding isMessageFrom_def q_def nd_def
              using \<open>t = currentTerm nd\<close> isMessageFromTo_def nd_def zen.joinVotes zenMessages.Vote_unique_destination zenMessages_axioms zen_axioms by blast

            have t'_latis: "SomeTerm t' \<le> lastAcceptedTerm nd"
              unfolding nd_def
            proof (intro joinVotes_max)
              from fresh_request
              show "\<not> (\<exists>x. \<langle> PublishRequest (firstUncommittedSlot (nodeState n\<^sub>0)) (currentTerm (nodeState n\<^sub>0)) x \<rangle>\<leadsto>)"
                unfolding nd_def by auto

              from n'_vote show "n' \<in> joinVotes (nodeState n\<^sub>0)" by (simp add: q_def nd_def)

              from n'_sent
              show "n' \<midarrow>\<langle> Vote (firstUncommittedSlot (nodeState n\<^sub>0)) (currentTerm (nodeState n\<^sub>0)) (SomeTerm t') \<rangle>\<rightarrow> (OneNode n\<^sub>0)"
                by (simp add: nd_def)
            qed

            then obtain t'' where t'': "lastAcceptedTerm nd = SomeTerm t''"
              by (cases "lastAcceptedTerm nd", auto)

            show ?thesis
            proof (intro disjI2 exI conjI)
              from t''
              have slots: "firstUncommittedSlot nd = firstUncommittedSlot nd"
                by (cases "firstUncommittedSlot nd = firstUncommittedSlot nd", simp_all add: lastAcceptedTerm_def)
              
              from t'' have lat: "lastAcceptedTerm nd = SomeTerm t''"
                by (cases "firstUncommittedSlot nd = firstUncommittedSlot nd", simp_all add: lastAcceptedTerm_def)
              
              from lastAcceptedTerm_Some_sent lat slots
              show accepted: "\<langle> PublishResponse i t'' \<rangle>\<leadsto>" by (auto simp add: nd_def isMessage_def)
              
              from fresh_request
              have "\<And>x'. \<langle> PublishRequest i t x' \<rangle>\<leadsto>' \<Longrightarrow> x' = x" unfolding PublishRequest' by simp
              hence "v' i t = x" unfolding v'_def using \<open>s \<midarrow>\<langle> PublishRequest i t x' \<rangle>\<leadsto>'\<close> isMessage'_def by blast
              
              also from x have "x = lastAcceptedValue nd" by (simp add: t'')
              
              also have "... = v i t''"
              proof (intro PublishRequest_function)
                from accepted PublishResponse_PublishRequest_v show "\<langle> PublishRequest i t'' (v i t'') \<rangle>\<leadsto>" by simp
              
                from lat lastAcceptedTerm_Some_value slots
                show "\<langle> PublishRequest i t'' (lastAcceptedValue nd) \<rangle>\<leadsto>"
                  by (simp add: nd_def)
              qed
              
              also have "... = v' i t''"
              proof (intro sym [OF v_eq])
                from accepted PublishResponse_PublishRequest_v show "\<langle> PublishRequest i t'' (v i t'') \<rangle>\<leadsto>" by simp
              qed
              
              finally show "v' i t = v' i t''" .
              
              show "maxTerm (prevAccepted i t q) \<le> t''"
              proof (intro maxTerm_le False finite_prevAccepted)
                fix t''' assume "t''' \<in> prevAccepted i t q"
                thus "t''' \<le> t''" unfolding prevAccepted_def apply auto
                  by (metis \<open>\<And>t s i' ia d' d a' a. \<lbrakk>s \<midarrow>\<langle> Vote ia t a \<rangle>\<rightarrow> d; s \<midarrow>\<langle> Vote i' t a' \<rangle>\<rightarrow> d'\<rbrakk> \<Longrightarrow> d = d'\<close> fresh_request isMessageFrom_def joinVotes joinVotes_max le_SomeTerm nd_def promised_def q_def t'')
              qed
              
              have "t'' \<le> t" using \<open>t = currentTerm nd\<close> lastAcceptedTerm_Some_currentTerm lat nd_def by blast
              moreover have "t'' \<noteq> t" apply (intro notI) using accepted fresh_request
                using lastAcceptedTerm_Some_value lat nd_def slots by auto
              ultimately show "t'' < t" by simp
            qed
          qed
        qed
      qed
    }
  qed
qed

lemma (in zenStep) handleVote_invariants:
  fixes s i t a
  defines "result \<equiv> handleVote s i t a nd"
  assumes nd': "nd' = fst result"
  assumes messages': "messages' = sendTo Broadcast result"
  assumes sent: "s \<midarrow>\<langle> Vote i t a \<rangle>\<rightarrow> (OneNode n\<^sub>0)"
  shows "zen messages' nodeState'"
proof (cases "t = currentTerm nd
             \<and> (i < firstUncommittedSlot nd
                \<or> (i = firstUncommittedSlot nd
                    \<and> (a \<le> lastAcceptedTerm nd)))")
  case False
  have [simp]: "result = (nd, None)" unfolding result_def handleVote_def by (simp add: False Let_def)
  have [simp]: "messages' = messages" by (simp add: messages')
  have [simp]: "nodeState' = nodeState" unfolding nodeState'_def by (intro ext, simp add: nd' nd_def)
  from zen_axioms show ?thesis by simp
next
  case True
  hence True': "i \<le> firstUncommittedSlot nd"
    "t = currentTerm nd"
    "i < firstUncommittedSlot nd \<or> (i = firstUncommittedSlot nd \<and> a \<le> lastAcceptedTerm nd)"
    by auto

  define nd1 where "nd1 \<equiv> addElectionVote s i a nd"
  define nodeState1 where "\<And>n. nodeState1 n \<equiv> if n = n\<^sub>0 then nd1 else nodeState n"

  have zenStep1: "zenStep messages nodeState messages nodeState1 n\<^sub>0"
    by (intro zenStepI2, auto simp add: nodeState1_def)

  have zenStep2: "zenStep messages nodeState1 messages' nodeState' n\<^sub>0"
  proof (intro zenStep.zenStepI1 [OF zenStep1] zenStep.addElectionVote_invariants [OF zenStep1] refl messages_subset,
      fold nd_def isMessageFromTo_def)
    show "nodeState1 n\<^sub>0 = addElectionVote s i a nd" by (simp add: nodeState1_def nd1_def)
    from True' sent show "s \<midarrow>\<langle> Vote i (currentTerm nd) a \<rangle>\<rightarrow> (OneNode n\<^sub>0)" by simp
    from True' show "i < firstUncommittedSlot nd \<or> (i = firstUncommittedSlot nd \<and> a \<le> lastAcceptedTerm nd)" by simp
    show "\<And>n. n \<noteq> n\<^sub>0 \<Longrightarrow> nodeState1 n = nodeState' n" unfolding nodeState1_def nodeState'_def by simp
  qed

  note zenStep.publishValue_invariants
  have latis_eq: "lastAcceptedTerm nd1 = lastAcceptedTerm nd"
    by (simp add: nd1_def addElectionVote_def Let_def)

  show ?thesis
  proof (cases "lastAcceptedTerm nd1")
    case (SomeTerm t')
    with True' latis_eq
    have handleVote_eq: "handleVote s i t a nd = publishValue (lastAcceptedValue nd1) nd1"
      unfolding handleVote_def nd1_def by (simp add: addElectionVote_def Let_def)

    show ?thesis
    proof (intro zenStep.publishValue_invariants [OF zenStep2])
      show "nodeState' n\<^sub>0 = fst (publishValue (lastAcceptedValue nd1) (nodeState1 n\<^sub>0))"
        by (simp add: nodeState1_def nd1_def nodeState'_def nd' result_def handleVote_eq)

      show "messages' = (case snd (publishValue (lastAcceptedValue nd1) (nodeState1 n\<^sub>0)) of None \<Rightarrow> messages | Some m \<Rightarrow> insert \<lparr>sender = n\<^sub>0, destination = Broadcast, payload = m\<rparr> messages)"
        by (cases "publishValue (lastAcceptedValue nd1) nd1", cases "snd (publishValue (lastAcceptedValue nd1) nd1)",
            simp_all add: nodeState1_def messages' result_def handleVote_eq)

      show "lastAcceptedValue nd1 = lastAcceptedValue (nodeState1 n\<^sub>0)" by (simp add: nodeState1_def)
    qed

  next
    case NO_TERM
    with True' latis_eq
    have handleVote_eq: "handleVote s i t a nd = (nd1, None)" unfolding handleVote_def nd1_def by simp
    have [simp]: "messages' = messages" by (simp add: messages' result_def handleVote_eq)
    have [simp]: "nodeState' = nodeState1" by (intro ext, simp add: nodeState'_def nodeState1_def nd' result_def handleVote_eq)
    from zenStep2 show ?thesis by (simp add: zenStep_def)
  qed
qed

lemma (in zenStep) handleClientValue_invariants:
  fixes x
  defines "result \<equiv> handleClientValue x nd"
  assumes nd': "nd' = fst result"
  assumes messages': "messages' = sendTo Broadcast result"
  shows "zen messages' nodeState'"
proof (cases "lastAcceptedTerm nd")
  case (SomeTerm t')
  hence "handleClientValue x nd = (nd, None)" by (auto simp add: handleClientValue_def)
  hence [simp]: "result = (nd, None)" by (simp add: result_def)
  have [simp]: "messages' = messages" by (simp add: messages')
  have [simp]: "nodeState' = nodeState" unfolding nodeState'_def by (intro ext, simp add: nd' nd_def)
  from zen_axioms show ?thesis by simp
next
  case NO_TERM
  hence handleClientValue_eq[simp]: "handleClientValue x nd = publishValue x nd"
    by (auto simp add: handleClientValue_def)

  have result: "result = publishValue x nd"
    unfolding result_def by simp

  show ?thesis
  proof (intro publishValue_invariants)
    show "nd' = fst (publishValue x nd)" by (simp add: result nd')
    show "messages' = sendTo Broadcast (publishValue x nd)" by (simp_all add: messages' result)
    from NO_TERM show "lastAcceptedTerm nd \<noteq> NO_TERM \<Longrightarrow> x = lastAcceptedValue nd"
      by simp
  qed
qed

lemma (in zenStep) handlePublishRequest_invariants:
  fixes i t x
  defines "result \<equiv> handlePublishRequest i t x nd"
  assumes nd': "nd' = fst result"
  assumes messages': "messages' = sendTo (OneNode s) result"
  assumes sent: "s \<midarrow>\<langle> PublishRequest i t x \<rangle>\<leadsto>"
  shows "zen messages' nodeState'"
proof (cases "i = firstUncommittedSlot nd \<and> t = currentTerm nd")
  case False
  hence [simp]: "result = (nd, None)"
    by (simp add: result_def handlePublishRequest_def)

  have [simp]: "messages' = messages"
    by (simp add: messages')

  have [simp]: "nodeState' = nodeState"
    unfolding nodeState'_def
    by (intro ext, simp add: nd' nd_def)

  from zen_axioms show ?thesis by simp

next
  case precondition: True

  hence result: "result = (nd\<lparr>lastAcceptedData := Some \<lparr> tvTerm = t, tvValue = x\<rparr> \<rparr>,
      Some (PublishResponse i t))"
    by (auto simp add: result_def handlePublishRequest_def)

  have messages': "messages' = insert \<lparr> sender = n\<^sub>0, destination = OneNode s, payload = PublishResponse i t \<rparr> messages"
    by (simp add: messages' result)

  have message_simps[simp]:
    "\<And>s d i t. (s \<midarrow>\<langle> ApplyCommit i t \<rangle>\<rightarrow>' d) = (s \<midarrow>\<langle> ApplyCommit i t \<rangle>\<rightarrow> d)"
    "\<And>s d i t x. (s \<midarrow>\<langle> PublishRequest i t x \<rangle>\<rightarrow>' d) = (s \<midarrow>\<langle> PublishRequest i t x \<rangle>\<rightarrow> d)"
    "\<And>s d i t a. (s \<midarrow>\<langle> Vote i t a \<rangle>\<rightarrow>' d) = (s \<midarrow>\<langle> Vote i t a \<rangle>\<rightarrow> d)"
    "\<And>d i t. (\<langle> ApplyCommit i t \<rangle>\<rightarrow>' d) = (\<langle> ApplyCommit i t \<rangle>\<rightarrow> d)"
    "\<And>d i t x. (\<langle> PublishRequest i t x \<rangle>\<rightarrow>' d) = (\<langle> PublishRequest i t x \<rangle>\<rightarrow> d)"
    "\<And>d i t a. (\<langle> Vote i t a \<rangle>\<rightarrow>' d) = (\<langle> Vote i t a \<rangle>\<rightarrow> d)"
    "\<And>s i t. (s \<midarrow>\<langle> ApplyCommit i t \<rangle>\<leadsto>') = (s \<midarrow>\<langle> ApplyCommit i t \<rangle>\<leadsto>)"
    "\<And>s i t x. (s \<midarrow>\<langle> PublishRequest i t x \<rangle>\<leadsto>') = (s \<midarrow>\<langle> PublishRequest i t x \<rangle>\<leadsto>)"
    "\<And>s i t a. (s \<midarrow>\<langle> Vote i t a \<rangle>\<leadsto>') = (s \<midarrow>\<langle> Vote i t a \<rangle>\<leadsto>)"
    "\<And>i t. (\<langle> ApplyCommit i t \<rangle>\<leadsto>') = (\<langle> ApplyCommit i t \<rangle>\<leadsto>)"
    "\<And>i t x. (\<langle> PublishRequest i t x \<rangle>\<leadsto>') = (\<langle> PublishRequest i t x \<rangle>\<leadsto>)"
    "\<And>i t a. (\<langle> Vote i t a \<rangle>\<leadsto>') = (\<langle> Vote i t a \<rangle>\<leadsto>)"
    "\<And>s d i conf cs. (s \<midarrow>\<langle> CatchUpResponse i conf cs \<rangle>\<rightarrow>' d) = (s \<midarrow>\<langle> CatchUpResponse i conf cs \<rangle>\<rightarrow> d)"
    "\<And>d i conf cs. (\<langle> CatchUpResponse i conf cs \<rangle>\<rightarrow>' d) = (\<langle> CatchUpResponse i conf cs \<rangle>\<rightarrow> d)"
    "\<And>s i conf cs. (s \<midarrow>\<langle> CatchUpResponse i conf cs \<rangle>\<leadsto>') = (s \<midarrow>\<langle> CatchUpResponse i conf cs \<rangle>\<leadsto>)"
    "\<And>d i conf cs. (\<langle> CatchUpResponse i conf cs \<rangle>\<leadsto>') = (\<langle> CatchUpResponse i conf cs \<rangle>\<leadsto>)"
    by (unfold isMessageFromTo'_def isMessageTo'_def isMessageFrom'_def isMessage'_def,
        auto simp add: messages' isMessageFromTo_def isMessageTo_def isMessageFrom_def isMessage_def)

  have property_simps[simp]:
    "\<And>n. currentNode (nodeState' n) = currentNode (nodeState n)"
    "\<And>n. firstUncommittedSlot (nodeState' n) = firstUncommittedSlot (nodeState n)"
    "\<And>n. currentVotingNodes (nodeState' n) = currentVotingNodes (nodeState n)"
    "\<And>n q. isQuorum (nodeState' n) q = isQuorum (nodeState n) q"
    "\<And>n. currentTerm (nodeState' n) = currentTerm (nodeState n)"
    "\<And>n. publishPermitted (nodeState' n) = publishPermitted (nodeState n)"
    "\<And>n. joinVotes (nodeState' n) = joinVotes (nodeState n)"
    "\<And>n. electionWon (nodeState' n) = electionWon (nodeState n)"
    "\<And>n. publishVotes (nodeState' n) = publishVotes (nodeState n)"
    "\<And>n. currentClusterState (nodeState' n) = currentClusterState (nodeState n)"
    "lastAcceptedTerm nd' = SomeTerm t"
    "lastAcceptedValue nd' = x"
    using precondition
    by (unfold nodeState'_def, auto simp add: result nd' nd_def isQuorum_def
        lastAcceptedTerm_def lastAcceptedValue_def)

  have updated_properties:
    "\<And>n. lastAcceptedTerm (nodeState' n) = (if n = n\<^sub>0 then SomeTerm t else lastAcceptedTerm (nodeState n))"
    "\<And>n. lastAcceptedValue (nodeState' n) = (if n = n\<^sub>0 then x else lastAcceptedValue (nodeState n))"
    by (unfold nodeState'_def, auto simp add: result nd' nd_def
        lastAcceptedTerm_def lastAcceptedValue_def)

  have PublishResponse': "\<And>s' d i t'. (s' \<midarrow>\<langle> PublishResponse i t' \<rangle>\<rightarrow>' d) =
    ((s' \<midarrow>\<langle> PublishResponse i t' \<rangle>\<rightarrow> d) \<or> (s', i, t', d) = (n\<^sub>0, firstUncommittedSlot nd, t, OneNode s))"
    "\<And>d i t'. (\<langle> PublishResponse i t' \<rangle>\<rightarrow>' d) =
    ((\<langle> PublishResponse i t' \<rangle>\<rightarrow> d) \<or> (i, t', d) = (firstUncommittedSlot nd, t, OneNode s))"
    "\<And>s' i t'. (s' \<midarrow>\<langle> PublishResponse i t' \<rangle>\<leadsto>') =
    ((s' \<midarrow>\<langle> PublishResponse i t' \<rangle>\<leadsto>) \<or> (s', i, t') = (n\<^sub>0, firstUncommittedSlot nd, t))"
    "\<And>i t'. (\<langle> PublishResponse i t' \<rangle>\<leadsto>') =
    ((\<langle> PublishResponse i t' \<rangle>\<leadsto>) \<or> (i, t') = (firstUncommittedSlot nd, t))"
    unfolding isMessageFromTo_def isMessageFromTo'_def isMessageFrom_def isMessageFrom'_def isMessageTo_def isMessageTo'_def isMessage_def isMessage'_def
    by (auto simp add: messages' precondition)

  have v_eq[simp]: "v' = v" by (intro ext, auto simp add: v'_def v_def)
  have v\<^sub>c_eq[simp]: "v\<^sub>c' = v\<^sub>c" by (intro ext, auto simp add: v\<^sub>c'_def v\<^sub>c_def)
  have isCommitted_eq[simp]: "isCommitted' = isCommitted" by (intro ext, auto simp add: isCommitted'_def isCommitted_def)
  have committedTo_eq[simp]: "committed\<^sub><' = committed\<^sub><" by (intro ext, auto simp add: committedTo'_def committedTo_def)
  have V_eq[simp]: "V' = V" using v\<^sub>c_eq V'_def V_def by blast
  have lastCommittedClusterStateBefore_eq[simp]: "lastCommittedClusterStateBefore' = lastCommittedClusterStateBefore"
    unfolding lastCommittedClusterStateBefore_def lastCommittedClusterStateBefore'_def v\<^sub>c_eq ..
  have promised_eq[simp]: "promised' = promised" by (intro ext, auto simp add: promised'_def promised_def)
  have prevAccepted_eq[simp]: "prevAccepted' = prevAccepted" by (intro ext, auto simp add: prevAccepted'_def prevAccepted_def)

  show ?thesis
    apply (intro zenI)
                        apply (unfold message_simps committedTo_eq V_eq v_eq
        lastCommittedClusterStateBefore_eq property_simps promised_eq prevAccepted_eq)
  proof -
    from finite_messages show "finite messages'" by (simp add: messages')
    from Vote_Some_lt show "\<And>i s t t'. s \<midarrow>\<langle> Vote i t (SomeTerm t') \<rangle>\<leadsto> \<Longrightarrow> t' < t".
    from Vote_not_broadcast show "\<And>i t a d. \<langle> Vote i t a \<rangle>\<rightarrow> d \<Longrightarrow> d \<noteq> Broadcast".
    from Vote_unique_destination show "\<And>i' i s t a a' d d'. s \<midarrow>\<langle> Vote i t a \<rangle>\<rightarrow> d \<Longrightarrow> s \<midarrow>\<langle> Vote i' t a' \<rangle>\<rightarrow> d' \<Longrightarrow> d = d'".
    from currentNode_nodeState show "\<And>n. currentNode (nodeState n) = n" .
    from committedTo_firstUncommittedSlot show "\<And>n. committed\<^sub>< (firstUncommittedSlot (nodeState n))" .
    from Vote_currentTerm show "\<And>n i t a. n \<midarrow>\<langle> Vote i t a \<rangle>\<leadsto> \<Longrightarrow> t \<le> currentTerm (nodeState n)".
    from Vote_slot_function show "\<And>n i i' t a a'. n \<midarrow>\<langle> Vote i t a \<rangle>\<leadsto> \<Longrightarrow> n \<midarrow>\<langle> Vote i' t a' \<rangle>\<leadsto> \<Longrightarrow> i = i'".
    from electionWon_isQuorum show "\<And>n. electionWon (nodeState n) \<Longrightarrow> isQuorum (nodeState n) (joinVotes (nodeState n))".
    from currentClusterState_lastCommittedClusterStateBefore show "\<And>n. currentClusterState (nodeState n) = lastCommittedClusterStateBefore (firstUncommittedSlot (nodeState n))".
    from joinVotes show "\<And>n n'. n' \<in> joinVotes (nodeState n) \<Longrightarrow> promised (firstUncommittedSlot (nodeState n)) n' n (currentTerm (nodeState n))".
    from PublishRequest_committedTo show "\<And>i t x. \<langle> PublishRequest i t x \<rangle>\<leadsto> \<Longrightarrow> committed\<^sub>< i".
    from PublishRequest_function show "\<And>i t x x'. \<langle> PublishRequest i t x \<rangle>\<leadsto> \<Longrightarrow> \<langle> PublishRequest i t x' \<rangle>\<leadsto> \<Longrightarrow> x = x'".
    from currentVotingNodes_firstUncommittedSlot show "\<And>n. currentVotingNodes (nodeState n) = V (firstUncommittedSlot (nodeState n))".
    from firstUncommittedSlot_PublishRequest show "\<And>i n t x. firstUncommittedSlot (nodeState n) < i \<Longrightarrow> \<not> n \<midarrow>\<langle> PublishRequest i t x \<rangle>\<leadsto>".
    from PublishRequest_currentTerm show "\<And>n t x. n \<midarrow>\<langle> PublishRequest (firstUncommittedSlot (nodeState n)) t x \<rangle>\<leadsto> \<Longrightarrow> t \<le> currentTerm (nodeState n)".
    from PublishRequest_publishPermitted_currentTerm show "\<And>n t x. n \<midarrow>\<langle> PublishRequest (firstUncommittedSlot (nodeState n)) t x \<rangle>\<leadsto> \<Longrightarrow> publishPermitted (nodeState n) \<Longrightarrow> t < currentTerm (nodeState n)".
    from CatchUpResponse_committedTo show "\<And>i conf cs. \<langle> CatchUpResponse i conf cs \<rangle>\<leadsto> \<Longrightarrow> committed\<^sub>< i".
    from CatchUpResponse_V show "\<And>i conf cs. \<langle> CatchUpResponse i conf cs \<rangle>\<leadsto> \<Longrightarrow> V i = conf".
    from CatchUpResponse_lastCommittedClusterStateBefore show "\<And>i conf cs. \<langle> CatchUpResponse i conf cs \<rangle>\<leadsto> \<Longrightarrow> lastCommittedClusterStateBefore i = cs".

    from Vote_future show "\<And>i i' s t t' a. s \<midarrow>\<langle> Vote i t a \<rangle>\<leadsto> \<Longrightarrow> i < i' \<Longrightarrow> t' < t \<Longrightarrow> \<not> s \<midarrow>\<langle> PublishResponse i' t' \<rangle>\<leadsto>'"
      using precondition unfolding PublishResponse' nd_def by (metis Vote_currentTerm Pair_inject leD)

    from Vote_None show "\<And>i s t t'. s \<midarrow>\<langle> Vote i t NO_TERM \<rangle>\<leadsto> \<Longrightarrow> t' < t \<Longrightarrow> \<not> s \<midarrow>\<langle> PublishResponse i t' \<rangle>\<leadsto>'"
      using precondition unfolding PublishResponse' nd_def by (metis Vote_currentTerm Pair_inject leD)

    from Vote_Some_PublishResponse show "\<And>i s t t'. s \<midarrow>\<langle> Vote i t (SomeTerm t') \<rangle>\<leadsto> \<Longrightarrow> s \<midarrow>\<langle> PublishResponse i t' \<rangle>\<leadsto>'"
      using precondition unfolding PublishResponse' nd_def by metis

    from Vote_Some_max show "\<And>i s t t' t''. s \<midarrow>\<langle> Vote i t (SomeTerm t') \<rangle>\<leadsto> \<Longrightarrow> t' < t'' \<Longrightarrow> t'' < t \<Longrightarrow> \<not> s \<midarrow>\<langle> PublishResponse i t'' \<rangle>\<leadsto>'"
      using precondition unfolding PublishResponse' nd_def using Vote_currentTerm by fastforce

    from PublishRequest_quorum show "\<And>i s t x. s \<midarrow>\<langle> PublishRequest i t x \<rangle>\<leadsto> \<Longrightarrow> \<exists>q\<in>majorities (V i). (\<forall>n\<in>q. promised i n s t) \<and> (prevAccepted i t q = {} \<or> (\<exists>t'. v i t = v i t' \<and> maxTerm (prevAccepted i t q) \<le> t' \<and> \<langle> PublishResponse i t' \<rangle>\<leadsto>' \<and> t' < t))" 
      unfolding PublishResponse' by meson

    fix n

    from firstUncommittedSlot_PublishResponse show "\<And>i t. firstUncommittedSlot (nodeState n) < i \<Longrightarrow> \<not> n \<midarrow>\<langle> PublishResponse i t \<rangle>\<leadsto>'" 
      using precondition property_simps unfolding PublishResponse' nd_def by (cases "n = n\<^sub>0", auto)

    from lastAcceptedTerm_None show "\<And>i t. lastAcceptedTerm (nodeState' n) = NO_TERM \<Longrightarrow> \<not> n \<midarrow>\<langle> PublishResponse (firstUncommittedSlot (nodeState n)) t \<rangle>\<leadsto>'"
      using precondition property_simps updated_properties unfolding PublishResponse' nd_def by (cases "n = n\<^sub>0", auto)

    from lastAcceptedTerm_Some_sent show "\<And>n t. lastAcceptedTerm (nodeState' n) = SomeTerm t \<Longrightarrow> n \<midarrow>\<langle> PublishResponse (firstUncommittedSlot (nodeState n)) t \<rangle>\<leadsto>'"
      using precondition property_simps unfolding PublishResponse' nd_def
      by (metis nd'_def nodeState_unchanged TermOption.inject)

    from lastAcceptedTerm_Some_max show "\<And>t t'. lastAcceptedTerm (nodeState' n) = SomeTerm t \<Longrightarrow> n \<midarrow>\<langle> PublishResponse (firstUncommittedSlot (nodeState n)) t' \<rangle>\<leadsto>' \<Longrightarrow> t' \<le> t"
      using precondition property_simps updated_properties unfolding PublishResponse' nd_def apply (cases "n = n\<^sub>0", auto)
      by (meson TermOption.exhaust lastAcceptedTerm_None lastAcceptedTerm_Some_currentTerm le_trans)
    
    from joinVotes_max show "\<And>n n' a'. \<not> (\<exists>x. \<langle> PublishRequest (firstUncommittedSlot (nodeState n)) (currentTerm (nodeState n)) x \<rangle>\<leadsto>) \<Longrightarrow> n' \<in> joinVotes (nodeState n) \<Longrightarrow> n' \<midarrow>\<langle> Vote (firstUncommittedSlot (nodeState n)) (currentTerm (nodeState n)) a' \<rangle>\<rightarrow> (OneNode n) \<Longrightarrow> a' \<le> lastAcceptedTerm (nodeState' n)"
      using precondition property_simps unfolding PublishResponse' nd_def
      by (metis isMessage_def nodeState_unchanged sent)

    from publishVotes show "\<And>n n'. n' \<in> publishVotes (nodeState n) \<Longrightarrow> n' \<midarrow>\<langle> PublishResponse (firstUncommittedSlot (nodeState n)) (currentTerm (nodeState n)) \<rangle>\<leadsto>'"
      using precondition property_simps unfolding PublishResponse' nd_def
      by blast

    from PublishResponse_PublishRequest show "\<And>i s t. s \<midarrow>\<langle> PublishResponse i t \<rangle>\<leadsto>' \<Longrightarrow> \<exists>x. \<langle> PublishRequest i t x \<rangle>\<leadsto>"
      using precondition property_simps unfolding PublishResponse' nd_def
      using isMessage_def sent by auto

    from ApplyCommit_quorum show "\<And>i t. \<langle> ApplyCommit i t \<rangle>\<leadsto> \<Longrightarrow> \<exists>q\<in>majorities (V i). \<forall>s\<in>q. s \<midarrow>\<langle> PublishResponse i t \<rangle>\<leadsto>'"
      using precondition property_simps unfolding PublishResponse' nd_def
      by meson

    from lastAcceptedTerm_Some_value show "\<And>n t. lastAcceptedTerm (nodeState' n) = SomeTerm t \<Longrightarrow> \<langle> PublishRequest (firstUncommittedSlot (nodeState n)) t (lastAcceptedValue (nodeState' n)) \<rangle>\<leadsto>"
      using precondition property_simps unfolding PublishResponse' nd_def
      by (metis isMessage_def nd'_def nodeState_unchanged TermOption.inject sent)

    from lastAcceptedTerm_Some_currentTerm show "\<And>n t. lastAcceptedTerm (nodeState' n) = SomeTerm t \<Longrightarrow> t \<le> currentTerm (nodeState n)"
      using precondition property_simps unfolding PublishResponse' nd_def
      by (metis eq_imp_le TermOption.inject updated_properties(1))
  qed
qed

lemma (in zenStep) addPublishVote_invariants:
  assumes nd': "nd' = nd \<lparr> publishVotes := insert s (publishVotes nd) \<rparr>"
  assumes messages': "messages' = messages"
  assumes sent: "s \<midarrow>\<langle> PublishResponse (firstUncommittedSlot nd) (currentTerm nd) \<rangle>\<leadsto>"
  shows "zen messages' nodeState'"
proof -
  have message_simps[simp]:
    "\<And>s p d. (s \<midarrow>\<langle> p \<rangle>\<rightarrow>' d) = (s \<midarrow>\<langle> p \<rangle>\<rightarrow> d)"
    "\<And>p d. (\<langle> p \<rangle>\<rightarrow>' d) = (\<langle> p \<rangle>\<rightarrow> d)"
    "\<And>s p. (s \<midarrow>\<langle> p \<rangle>\<leadsto>') = (s \<midarrow>\<langle> p \<rangle>\<leadsto>)"
    "\<And>p. (\<langle> p \<rangle>\<leadsto>') = (\<langle> p \<rangle>\<leadsto>)"
    by (unfold isMessageFromTo'_def isMessageTo'_def isMessageFrom'_def isMessage'_def,
        auto simp add: messages' isMessageFromTo_def isMessageTo_def isMessageFrom_def isMessage_def)

  have property_simps[simp]:
    "\<And>n. currentNode (nodeState' n) = currentNode (nodeState n)"
    "\<And>n. firstUncommittedSlot (nodeState' n) = firstUncommittedSlot (nodeState n)"
    "\<And>n. currentVotingNodes (nodeState' n) = currentVotingNodes (nodeState n)"
    "\<And>n q. isQuorum (nodeState' n) q = isQuorum (nodeState n) q"
    "\<And>n. lastAcceptedTerm (nodeState' n) = lastAcceptedTerm (nodeState n)"
    "\<And>n. lastAcceptedValue (nodeState' n) = lastAcceptedValue (nodeState n)"
    "\<And>n. currentTerm (nodeState' n) = currentTerm (nodeState n)"
    "\<And>n. publishPermitted (nodeState' n) = publishPermitted (nodeState n)"
    "\<And>n. joinVotes (nodeState' n) = joinVotes (nodeState n)"
    "\<And>n. electionWon (nodeState' n) = electionWon (nodeState n)"
    "\<And>n. currentClusterState (nodeState' n) = currentClusterState (nodeState n)"
    by (unfold nodeState'_def, auto simp add: nd_def isQuorum_def nd' addElectionVote_def Let_def
        lastAcceptedTerm_def lastAcceptedValue_def)

  have updated_properties[simp]:
    "\<And>n. publishVotes (nodeState' n) = publishVotes (nodeState n) \<union> (if n = n\<^sub>0 then {s} else {})"
    by (unfold nodeState'_def, auto simp add: nd' nd_def isQuorum_def)

  have v_eq[simp]: "v' = v" by (intro ext, auto simp add: v'_def v_def)
  have v\<^sub>c_eq[simp]: "v\<^sub>c' = v\<^sub>c" by (intro ext, auto simp add: v\<^sub>c'_def v\<^sub>c_def)
  have isCommitted_eq[simp]: "isCommitted' = isCommitted" by (intro ext, auto simp add: isCommitted'_def isCommitted_def)
  have committedTo_eq[simp]: "committed\<^sub><' = committed\<^sub><" by (intro ext, auto simp add: committedTo'_def committedTo_def)
  have V_eq[simp]: "V' = V" using v\<^sub>c_eq V'_def V_def by blast
  have promised_eq[simp]: "promised' = promised" by (intro ext, auto simp add: promised'_def promised_def)
  have lastCommittedClusterStateBefore_eq[simp]: "lastCommittedClusterStateBefore' = lastCommittedClusterStateBefore"
    unfolding lastCommittedClusterStateBefore_def lastCommittedClusterStateBefore'_def v\<^sub>c_eq ..
  have prevAccepted_eq[simp]: "prevAccepted' = prevAccepted" by (intro ext, auto simp add: prevAccepted'_def prevAccepted_def)

  show ?thesis
    apply (intro zenI)
                        apply (unfold message_simps committedTo_eq V_eq v_eq
        lastCommittedClusterStateBefore_eq property_simps promised_eq prevAccepted_eq)
  proof -
    from finite_messages show "finite messages'" by (simp add: messages')
    from Vote_future show "\<And>i i' s t t' a. s \<midarrow>\<langle> Vote i t a \<rangle>\<leadsto> \<Longrightarrow> i < i' \<Longrightarrow> t' < t \<Longrightarrow> \<not> s \<midarrow>\<langle> PublishResponse i' t' \<rangle>\<leadsto>".
    from Vote_None show "\<And>i s t t'. s \<midarrow>\<langle> Vote i t NO_TERM \<rangle>\<leadsto> \<Longrightarrow> t' < t \<Longrightarrow> \<not> s \<midarrow>\<langle> PublishResponse i t' \<rangle>\<leadsto>".
    from Vote_Some_lt show "\<And>i s t t'. s \<midarrow>\<langle> Vote i t (SomeTerm t') \<rangle>\<leadsto> \<Longrightarrow> t' < t".
    from Vote_Some_PublishResponse show "\<And>i s t t'. s \<midarrow>\<langle> Vote i t (SomeTerm t') \<rangle>\<leadsto> \<Longrightarrow> s \<midarrow>\<langle> PublishResponse i t' \<rangle>\<leadsto>".
    from Vote_Some_max show "\<And>i s t t' t''. s \<midarrow>\<langle> Vote i t (SomeTerm t') \<rangle>\<leadsto> \<Longrightarrow> t' < t'' \<Longrightarrow> t'' < t \<Longrightarrow> \<not> s \<midarrow>\<langle> PublishResponse i t'' \<rangle>\<leadsto>".
    from Vote_not_broadcast show "\<And>i t a d. \<langle> Vote i t a \<rangle>\<rightarrow> d \<Longrightarrow> d \<noteq> Broadcast".
    from Vote_unique_destination show "\<And>i' i s t a a' d d'. s \<midarrow>\<langle> Vote i t a \<rangle>\<rightarrow> d \<Longrightarrow> s \<midarrow>\<langle> Vote i' t a' \<rangle>\<rightarrow> d' \<Longrightarrow> d = d'".
    from currentNode_nodeState show "\<And>n. currentNode (nodeState n) = n" .
    from committedTo_firstUncommittedSlot show "\<And>n. committed\<^sub>< (firstUncommittedSlot (nodeState n))" .
    from firstUncommittedSlot_PublishResponse show "\<And>n i t. firstUncommittedSlot (nodeState n) < i \<Longrightarrow> \<not> n \<midarrow>\<langle> PublishResponse i t \<rangle>\<leadsto>" .
    from lastAcceptedTerm_None show "\<And>n i t. lastAcceptedTerm (nodeState n) = NO_TERM \<Longrightarrow> \<not> n \<midarrow>\<langle> PublishResponse (firstUncommittedSlot (nodeState n)) t \<rangle>\<leadsto>".
    from lastAcceptedTerm_Some_sent show "\<And>n t. lastAcceptedTerm (nodeState n) = SomeTerm t \<Longrightarrow> n \<midarrow>\<langle> PublishResponse (firstUncommittedSlot (nodeState n)) t \<rangle>\<leadsto>".
    from lastAcceptedTerm_Some_max show "\<And>n t t'. lastAcceptedTerm (nodeState n) = SomeTerm t \<Longrightarrow> n \<midarrow>\<langle> PublishResponse (firstUncommittedSlot (nodeState n)) t' \<rangle>\<leadsto> \<Longrightarrow> t' \<le> t".
    from Vote_currentTerm show "\<And>n i t a. n \<midarrow>\<langle> Vote i t a \<rangle>\<leadsto> \<Longrightarrow> t \<le> currentTerm (nodeState n)".
    from Vote_slot_function show "\<And>n i i' t a a'. n \<midarrow>\<langle> Vote i t a \<rangle>\<leadsto> \<Longrightarrow> n \<midarrow>\<langle> Vote i' t a' \<rangle>\<leadsto> \<Longrightarrow> i = i'".
    from electionWon_isQuorum show "\<And>n. electionWon (nodeState n) \<Longrightarrow> isQuorum (nodeState n) (joinVotes (nodeState n))".
    from joinVotes_max show "\<And>n n' a'. \<not> (\<exists>x. \<langle> PublishRequest (firstUncommittedSlot (nodeState n)) (currentTerm (nodeState n)) x \<rangle>\<leadsto>) \<Longrightarrow> n' \<in> joinVotes (nodeState n) \<Longrightarrow> n' \<midarrow>\<langle> Vote (firstUncommittedSlot (nodeState n)) (currentTerm (nodeState n)) a' \<rangle>\<rightarrow> (OneNode n) \<Longrightarrow> a' \<le> lastAcceptedTerm (nodeState n)".
    from currentClusterState_lastCommittedClusterStateBefore show "\<And>n. currentClusterState (nodeState n) = lastCommittedClusterStateBefore (firstUncommittedSlot (nodeState n))".
    from joinVotes show "\<And>n n'. n' \<in> joinVotes (nodeState n) \<Longrightarrow> promised (firstUncommittedSlot (nodeState n)) n' n (currentTerm (nodeState n))".
    from PublishRequest_committedTo show "\<And>i t x. \<langle> PublishRequest i t x \<rangle>\<leadsto> \<Longrightarrow> committed\<^sub>< i".
    from PublishRequest_quorum show "\<And>i s t x. s \<midarrow>\<langle> PublishRequest i t x \<rangle>\<leadsto> \<Longrightarrow> \<exists>q\<in>majorities (V i). (\<forall>n\<in>q. promised i n s t) \<and> (prevAccepted i t q = {} \<or> (\<exists>t'. v i t = v i t' \<and> maxTerm (prevAccepted i t q) \<le> t' \<and> \<langle> PublishResponse i t' \<rangle>\<leadsto> \<and> t' < t))".
    from PublishRequest_function show "\<And>i t x x'. \<langle> PublishRequest i t x \<rangle>\<leadsto> \<Longrightarrow> \<langle> PublishRequest i t x' \<rangle>\<leadsto> \<Longrightarrow> x = x'".
    from PublishResponse_PublishRequest show "\<And>i s t. s \<midarrow>\<langle> PublishResponse i t \<rangle>\<leadsto> \<Longrightarrow> \<exists>x. \<langle> PublishRequest i t x \<rangle>\<leadsto>".
    from ApplyCommit_quorum show "\<And>i t. \<langle> ApplyCommit i t \<rangle>\<leadsto> \<Longrightarrow> \<exists>q\<in>majorities (V i). \<forall>s\<in>q. s \<midarrow>\<langle> PublishResponse i t \<rangle>\<leadsto>".
    from currentVotingNodes_firstUncommittedSlot show "\<And>n. currentVotingNodes (nodeState n) = V (firstUncommittedSlot (nodeState n))".
    from firstUncommittedSlot_PublishRequest show "\<And>i n t x. firstUncommittedSlot (nodeState n) < i \<Longrightarrow> \<not> n \<midarrow>\<langle> PublishRequest i t x \<rangle>\<leadsto>".
    from lastAcceptedTerm_Some_value show "\<And>n t. lastAcceptedTerm (nodeState n) = SomeTerm t \<Longrightarrow> \<langle> PublishRequest (firstUncommittedSlot (nodeState n)) t (lastAcceptedValue (nodeState n)) \<rangle>\<leadsto>".
    from PublishRequest_currentTerm show "\<And>n t x. n \<midarrow>\<langle> PublishRequest (firstUncommittedSlot (nodeState n)) t x \<rangle>\<leadsto> \<Longrightarrow> t \<le> currentTerm (nodeState n)".
    from PublishRequest_publishPermitted_currentTerm show "\<And>n t x. n \<midarrow>\<langle> PublishRequest (firstUncommittedSlot (nodeState n)) t x \<rangle>\<leadsto> \<Longrightarrow> publishPermitted (nodeState n) \<Longrightarrow> t < currentTerm (nodeState n)".
    from CatchUpResponse_committedTo show "\<And>i conf cs. \<langle> CatchUpResponse i conf cs \<rangle>\<leadsto> \<Longrightarrow> committed\<^sub>< i".
    from CatchUpResponse_V show "\<And>i conf cs. \<langle> CatchUpResponse i conf cs \<rangle>\<leadsto> \<Longrightarrow> V i = conf".
    from CatchUpResponse_lastCommittedClusterStateBefore show "\<And>i conf cs. \<langle> CatchUpResponse i conf cs \<rangle>\<leadsto> \<Longrightarrow> lastCommittedClusterStateBefore i = cs".
    from lastAcceptedTerm_Some_currentTerm show "\<And>n t. lastAcceptedTerm (nodeState n) = SomeTerm t \<Longrightarrow> t \<le> currentTerm (nodeState n)".

    from publishVotes show "\<And>n n'. n' \<in> publishVotes (nodeState' n) \<Longrightarrow> n' \<midarrow>\<langle> PublishResponse (firstUncommittedSlot (nodeState n)) (currentTerm (nodeState n)) \<rangle>\<leadsto>"
      unfolding updated_properties using sent apply auto by (metis empty_iff nd_def singleton_iff)
  qed
qed

lemma (in zenStep) commitIfQuorate_invariants:
  fixes s i t
  defines "result \<equiv> commitIfQuorate nd"
  assumes nd': "nd' = fst result"
  assumes messages': "messages' = sendTo Broadcast result"
  shows "zen messages' nodeState'"
proof (cases "isQuorum nd (publishVotes nd)")
  case False
  hence [simp]: "result = (nd, None)"
    by (simp add: result_def commitIfQuorate_def)

  have [simp]: "messages' = messages"
    by (simp add: messages')

  have [simp]: "nodeState' = nodeState"
    unfolding nodeState'_def
    by (intro ext, simp add: nd' nd_def)

  from zen_axioms show ?thesis by simp

next
  case isQuorum: True
  hence result: "result = (nd, Some (ApplyCommit (firstUncommittedSlot nd) (currentTerm nd)))"
    by (simp add: result_def commitIfQuorate_def)

  have nodeState': "nodeState' = nodeState"
    unfolding nodeState'_def
    by (intro ext, simp add: nd' nd_def result)

  have messages': "messages' = insert \<lparr> sender = n\<^sub>0, destination = Broadcast, payload = ApplyCommit (firstUncommittedSlot nd) (currentTerm nd) \<rparr> messages"
    by (simp add: messages' result)

  have message_simps[simp]:
    "\<And>s d i t. (s \<midarrow>\<langle> PublishResponse i t \<rangle>\<rightarrow>' d) = (s \<midarrow>\<langle> PublishResponse i t \<rangle>\<rightarrow> d)"
    "\<And>s d i t x. (s \<midarrow>\<langle> PublishRequest i t x \<rangle>\<rightarrow>' d) = (s \<midarrow>\<langle> PublishRequest i t x \<rangle>\<rightarrow> d)"
    "\<And>s d i t a. (s \<midarrow>\<langle> Vote i t a \<rangle>\<rightarrow>' d) = (s \<midarrow>\<langle> Vote i t a \<rangle>\<rightarrow> d)"
    "\<And>d i t. (\<langle> PublishResponse i t \<rangle>\<rightarrow>' d) = (\<langle> PublishResponse i t \<rangle>\<rightarrow> d)"
    "\<And>d i t x. (\<langle> PublishRequest i t x \<rangle>\<rightarrow>' d) = (\<langle> PublishRequest i t x \<rangle>\<rightarrow> d)"
    "\<And>d i t a. (\<langle> Vote i t a \<rangle>\<rightarrow>' d) = (\<langle> Vote i t a \<rangle>\<rightarrow> d)"
    "\<And>s i t. (s \<midarrow>\<langle> PublishResponse i t \<rangle>\<leadsto>') = (s \<midarrow>\<langle> PublishResponse i t \<rangle>\<leadsto>)"
    "\<And>s i t x. (s \<midarrow>\<langle> PublishRequest i t x \<rangle>\<leadsto>') = (s \<midarrow>\<langle> PublishRequest i t x \<rangle>\<leadsto>)"
    "\<And>s i t a. (s \<midarrow>\<langle> Vote i t a \<rangle>\<leadsto>') = (s \<midarrow>\<langle> Vote i t a \<rangle>\<leadsto>)"
    "\<And>i t. (\<langle> PublishResponse i t \<rangle>\<leadsto>') = (\<langle> PublishResponse i t \<rangle>\<leadsto>)"
    "\<And>i t x. (\<langle> PublishRequest i t x \<rangle>\<leadsto>') = (\<langle> PublishRequest i t x \<rangle>\<leadsto>)"
    "\<And>i t a. (\<langle> Vote i t a \<rangle>\<leadsto>') = (\<langle> Vote i t a \<rangle>\<leadsto>)"
    "\<And>s d i conf cs. (s \<midarrow>\<langle> CatchUpResponse i conf cs \<rangle>\<rightarrow>' d) = (s \<midarrow>\<langle> CatchUpResponse i conf cs \<rangle>\<rightarrow> d)"
    "\<And>d i conf cs. (\<langle> CatchUpResponse i conf cs \<rangle>\<rightarrow>' d) = (\<langle> CatchUpResponse i conf cs \<rangle>\<rightarrow> d)"
    "\<And>s i conf cs. (s \<midarrow>\<langle> CatchUpResponse i conf cs \<rangle>\<leadsto>') = (s \<midarrow>\<langle> CatchUpResponse i conf cs \<rangle>\<leadsto>)"
    "\<And>d i conf cs. (\<langle> CatchUpResponse i conf cs \<rangle>\<leadsto>') = (\<langle> CatchUpResponse i conf cs \<rangle>\<leadsto>)"
    by (unfold isMessageFromTo'_def isMessageTo'_def isMessageFrom'_def isMessage'_def,
        auto simp add: messages' isMessageFromTo_def isMessageTo_def isMessageFrom_def isMessage_def)

  have ApplyCommit': "\<And>s d i t. (s \<midarrow>\<langle> ApplyCommit i t \<rangle>\<rightarrow>' d) = ((s \<midarrow>\<langle> ApplyCommit i t \<rangle>\<rightarrow> d)
      \<or> (s, i, t, d) = (n\<^sub>0, firstUncommittedSlot nd, currentTerm nd, Broadcast))"
    "\<And>s i t. (s \<midarrow>\<langle> ApplyCommit i t \<rangle>\<leadsto>') = ((s \<midarrow>\<langle> ApplyCommit i t \<rangle>\<leadsto>)
      \<or> (s, i, t) = (n\<^sub>0, firstUncommittedSlot nd, currentTerm nd))"
    "\<And>d i t. (\<langle> ApplyCommit i t \<rangle>\<rightarrow>' d) = ((\<langle> ApplyCommit i t \<rangle>\<rightarrow> d)
      \<or> (i, t, d) = (firstUncommittedSlot nd, currentTerm nd, Broadcast))"
    "\<And>i t. (\<langle> ApplyCommit i t \<rangle>\<leadsto>') = ((\<langle> ApplyCommit i t \<rangle>\<leadsto>)
      \<or> (i, t) = (firstUncommittedSlot nd, currentTerm nd))"
    unfolding isMessageFromTo_def isMessageFromTo'_def isMessageFrom_def isMessageFrom'_def isMessageTo_def isMessageTo'_def isMessage_def isMessage'_def
    by (auto simp add: messages')

  from committedTo_firstUncommittedSlot
  have committedTo_current: "committed\<^sub>< (firstUncommittedSlot nd)"
    by (simp add: nd_def)

  have isCommitted_eq: "\<And>i. isCommitted' i = (isCommitted i \<or> i = firstUncommittedSlot nd)"
    using isCommitted'_def isCommitted_def by (auto simp add: ApplyCommit')

  have committedTo_eq: "\<And>i. committed\<^sub><' i = ((committed\<^sub>< i) \<or> (i = Suc (firstUncommittedSlot nd)))"
  proof -
    fix i
    show "?thesis i"
    proof (cases "isCommitted (firstUncommittedSlot nd)")
      case True with isCommitted_eq have 1: "isCommitted' = isCommitted" by (intro ext, auto)
      from True isCommitted_committedTo_Suc have 2: "committed\<^sub>< (Suc (firstUncommittedSlot nd))" by simp
      from 1 2 show ?thesis by (simp add: committedTo'_def committedTo_def, blast)
    next
      case False
      with committedTo_current isCommitted_committedTo
      have isCommitted_lt[simp]: "\<And>j. isCommitted j = (j < firstUncommittedSlot nd)"
        using committedTo_def nat_neq_iff by blast
      have isCommitted'_le[simp]: "\<And>j. isCommitted' j = (j \<le> firstUncommittedSlot nd)"
        by (auto simp add: isCommitted_eq)
      show ?thesis
        by (simp add: committedTo'_def committedTo_def, auto, presburger)
    qed
  qed

  have v_eq[simp]: "v' = v" by (intro ext, auto simp add: v'_def v_def)

  note oneSlot.consistent [OF oneSlot.commit [OF zen_is_oneSlot]]

  have v\<^sub>c_eq: "\<And>i. isCommitted i \<Longrightarrow> v\<^sub>c' i = v\<^sub>c i"
  proof -
    fix i assume "isCommitted i" then obtain t where t: "\<langle> ApplyCommit i t \<rangle>\<leadsto>" unfolding isCommitted_def by blast
    show "?thesis i"
    proof (cases "i = firstUncommittedSlot nd")
      case False thus ?thesis unfolding v\<^sub>c_def v\<^sub>c'_def v_eq ApplyCommit' by simp
    next
      case i: True
      show "v\<^sub>c' i = v\<^sub>c i"
        unfolding v\<^sub>c_def v\<^sub>c'_def v_eq
      proof (intro oneSlot.consistent [OF oneSlot.commit [OF zen_is_oneSlot]])
        from isQuorum show "publishVotes nd \<in> majorities (V i)" unfolding nd_def i isQuorum_def using currentVotingNodes_firstUncommittedSlot by simp
        from publishVotes show "\<And>n. n \<in> publishVotes nd \<Longrightarrow> n \<midarrow>\<langle> PublishResponse i (currentTerm nd) \<rangle>\<leadsto>" unfolding nd_def i .
        from t have "\<langle> ApplyCommit i (SOME t. \<langle> ApplyCommit i t \<rangle>\<leadsto>) \<rangle>\<leadsto>" by (intro someI)
        thus "\<langle> ApplyCommit i (SOME t. \<langle> ApplyCommit i t \<rangle>\<leadsto>) \<rangle>\<leadsto> \<or> (SOME t. \<langle> ApplyCommit i t \<rangle>\<leadsto>) = currentTerm nd" by simp
        show "\<langle> ApplyCommit i (SOME t. \<langle> ApplyCommit i t \<rangle>\<leadsto>') \<rangle>\<leadsto> \<or> (SOME t. \<langle> ApplyCommit i t \<rangle>\<leadsto>') = currentTerm nd"
        proof (rule someI2)
          from t show "\<langle> ApplyCommit i t \<rangle>\<leadsto>'"
            "\<And>x. \<langle> ApplyCommit i x \<rangle>\<leadsto>' \<Longrightarrow> \<langle> ApplyCommit i x \<rangle>\<leadsto> \<or> x = currentTerm nd"
            by (simp_all add: ApplyCommit' i)
        qed
      qed
    qed
  qed

  have V_eq: "\<And>i. committed\<^sub>< i \<Longrightarrow> V' i = V i"
  proof -
    fix i assume i: "committed\<^sub>< i"
    thus "?thesis i"
    proof (induct i)
      case (Suc i')
      hence prems: "committed\<^sub>< i'" "isCommitted i'" unfolding committedTo_def by auto
      thus ?case using Suc v\<^sub>c_eq by simp
    qed simp
  qed
  hence V_era_eq: "\<And>n. V' (firstUncommittedSlot (nodeState n)) = V (firstUncommittedSlot (nodeState n))"
    using committedTo_firstUncommittedSlot by blast

  have lastCommittedClusterStateBefore_eq: "\<And>i. committed\<^sub>< i \<Longrightarrow> lastCommittedClusterStateBefore' i = lastCommittedClusterStateBefore i"
  proof -
    fix i assume "committed\<^sub>< i"
    thus "?thesis i"
    proof (induct i)
      case (Suc i')
      hence prems: "committed\<^sub>< i'" "isCommitted i'" unfolding committedTo_def by auto
      thus ?case using Suc v\<^sub>c_eq by (cases "v\<^sub>c i'", simp_all)
    qed simp
  qed
  hence lastCommittedClusterStateBefore_slot_eq:
    "\<And>n. lastCommittedClusterStateBefore' (firstUncommittedSlot (nodeState n))
        = lastCommittedClusterStateBefore (firstUncommittedSlot (nodeState n))"
    using committedTo_firstUncommittedSlot by blast

  have promised_eq[simp]: "promised' = promised" by (intro ext, auto simp add: promised'_def promised_def)
  have prevAccepted_eq[simp]: "prevAccepted' = prevAccepted" by (intro ext, auto simp add: prevAccepted'_def prevAccepted_def)

  show ?thesis
    apply (intro zenI)
                        apply (unfold nodeState' message_simps V_era_eq lastCommittedClusterStateBefore_slot_eq promised_eq prevAccepted_eq v_eq)
  proof -
    from finite_messages show "finite messages'" by (simp add: messages')
    from Vote_future show "\<And>i i' s t t' a. s \<midarrow>\<langle> Vote i t a \<rangle>\<leadsto> \<Longrightarrow> i < i' \<Longrightarrow> t' < t \<Longrightarrow> \<not> s \<midarrow>\<langle> PublishResponse i' t' \<rangle>\<leadsto>".
    from Vote_None show "\<And>i s t t'. s \<midarrow>\<langle> Vote i t NO_TERM \<rangle>\<leadsto> \<Longrightarrow> t' < t \<Longrightarrow> \<not> s \<midarrow>\<langle> PublishResponse i t' \<rangle>\<leadsto>".
    from Vote_Some_lt show "\<And>i s t t'. s \<midarrow>\<langle> Vote i t (SomeTerm t') \<rangle>\<leadsto> \<Longrightarrow> t' < t".
    from Vote_Some_PublishResponse show "\<And>i s t t'. s \<midarrow>\<langle> Vote i t (SomeTerm t') \<rangle>\<leadsto> \<Longrightarrow> s \<midarrow>\<langle> PublishResponse i t' \<rangle>\<leadsto>".
    from Vote_Some_max show "\<And>i s t t' t''. s \<midarrow>\<langle> Vote i t (SomeTerm t') \<rangle>\<leadsto> \<Longrightarrow> t' < t'' \<Longrightarrow> t'' < t \<Longrightarrow> \<not> s \<midarrow>\<langle> PublishResponse i t'' \<rangle>\<leadsto>".
    from Vote_not_broadcast show "\<And>i t a d. \<langle> Vote i t a \<rangle>\<rightarrow> d \<Longrightarrow> d \<noteq> Broadcast".
    from Vote_unique_destination show "\<And>i' i s t a a' d d'. s \<midarrow>\<langle> Vote i t a \<rangle>\<rightarrow> d \<Longrightarrow> s \<midarrow>\<langle> Vote i' t a' \<rangle>\<rightarrow> d' \<Longrightarrow> d = d'".
    from currentNode_nodeState show "\<And>n. currentNode (nodeState n) = n" .
    from firstUncommittedSlot_PublishResponse show "\<And>n i t. firstUncommittedSlot (nodeState n) < i \<Longrightarrow> \<not> n \<midarrow>\<langle> PublishResponse i t \<rangle>\<leadsto>" .
    from lastAcceptedTerm_None show "\<And>n i t. lastAcceptedTerm (nodeState n) = NO_TERM \<Longrightarrow> \<not> n \<midarrow>\<langle> PublishResponse (firstUncommittedSlot (nodeState n)) t \<rangle>\<leadsto>".
    from lastAcceptedTerm_Some_sent show "\<And>n t. lastAcceptedTerm (nodeState n) = SomeTerm t \<Longrightarrow> n \<midarrow>\<langle> PublishResponse (firstUncommittedSlot (nodeState n)) t \<rangle>\<leadsto>".
    from lastAcceptedTerm_Some_max show "\<And>n t t'. lastAcceptedTerm (nodeState n) = SomeTerm t \<Longrightarrow> n \<midarrow>\<langle> PublishResponse (firstUncommittedSlot (nodeState n)) t' \<rangle>\<leadsto> \<Longrightarrow> t' \<le> t".
    from Vote_currentTerm show "\<And>n i t a. n \<midarrow>\<langle> Vote i t a \<rangle>\<leadsto> \<Longrightarrow> t \<le> currentTerm (nodeState n)".
    from Vote_slot_function show "\<And>n i i' t a a'. n \<midarrow>\<langle> Vote i t a \<rangle>\<leadsto> \<Longrightarrow> n \<midarrow>\<langle> Vote i' t a' \<rangle>\<leadsto> \<Longrightarrow> i = i'".
    from electionWon_isQuorum show "\<And>n. electionWon (nodeState n) \<Longrightarrow> isQuorum (nodeState n) (joinVotes (nodeState n))".
    from joinVotes_max show "\<And>n n' a'. \<not> (\<exists>x. \<langle> PublishRequest (firstUncommittedSlot (nodeState n)) (currentTerm (nodeState n)) x \<rangle>\<leadsto>) \<Longrightarrow> n' \<in> joinVotes (nodeState n) \<Longrightarrow> n' \<midarrow>\<langle> Vote (firstUncommittedSlot (nodeState n)) (currentTerm (nodeState n)) a' \<rangle>\<rightarrow> (OneNode n) \<Longrightarrow> a' \<le> lastAcceptedTerm (nodeState n)".
    from publishVotes show "\<And>n n'. n' \<in> publishVotes (nodeState n) \<Longrightarrow> n' \<midarrow>\<langle> PublishResponse (firstUncommittedSlot (nodeState n)) (currentTerm (nodeState n)) \<rangle>\<leadsto>".
    from currentClusterState_lastCommittedClusterStateBefore show "\<And>n. currentClusterState (nodeState n) = lastCommittedClusterStateBefore (firstUncommittedSlot (nodeState n))".
    from joinVotes show "\<And>n n'. n' \<in> joinVotes (nodeState n) \<Longrightarrow> promised (firstUncommittedSlot (nodeState n)) n' n (currentTerm (nodeState n))".
    from PublishRequest_function show "\<And>i t x x'. \<langle> PublishRequest i t x \<rangle>\<leadsto> \<Longrightarrow> \<langle> PublishRequest i t x' \<rangle>\<leadsto> \<Longrightarrow> x = x'".
    from PublishResponse_PublishRequest show "\<And>i s t. s \<midarrow>\<langle> PublishResponse i t \<rangle>\<leadsto> \<Longrightarrow> \<exists>x. \<langle> PublishRequest i t x \<rangle>\<leadsto>".
    from currentVotingNodes_firstUncommittedSlot show "\<And>n. currentVotingNodes (nodeState n) = V (firstUncommittedSlot (nodeState n))".
    from firstUncommittedSlot_PublishRequest show "\<And>i n t x. firstUncommittedSlot (nodeState n) < i \<Longrightarrow> \<not> n \<midarrow>\<langle> PublishRequest i t x \<rangle>\<leadsto>".
    from lastAcceptedTerm_Some_value show "\<And>n t. lastAcceptedTerm (nodeState n) = SomeTerm t \<Longrightarrow> \<langle> PublishRequest (firstUncommittedSlot (nodeState n)) t (lastAcceptedValue (nodeState n)) \<rangle>\<leadsto>".
    from PublishRequest_currentTerm show "\<And>n t x. n \<midarrow>\<langle> PublishRequest (firstUncommittedSlot (nodeState n)) t x \<rangle>\<leadsto> \<Longrightarrow> t \<le> currentTerm (nodeState n)".
    from PublishRequest_publishPermitted_currentTerm show "\<And>n t x. n \<midarrow>\<langle> PublishRequest (firstUncommittedSlot (nodeState n)) t x \<rangle>\<leadsto> \<Longrightarrow> publishPermitted (nodeState n) \<Longrightarrow> t < currentTerm (nodeState n)".
    from lastAcceptedTerm_Some_currentTerm show "\<And>n t. lastAcceptedTerm (nodeState n) = SomeTerm t \<Longrightarrow> t \<le> currentTerm (nodeState n)".

    {
      fix i conf cs assume a: "\<langle> CatchUpResponse i conf cs \<rangle>\<leadsto>"
      with CatchUpResponse_committedTo have committedTo: "committed\<^sub>< i" .
      thus "committed\<^sub><' i" unfolding committedTo_eq by simp
      from a committedTo V_eq lastCommittedClusterStateBefore_eq CatchUpResponse_V CatchUpResponse_lastCommittedClusterStateBefore
      show "V' i = conf" "lastCommittedClusterStateBefore' i = cs" by auto
    }

    from committedTo_firstUncommittedSlot
    show "\<And>n. committed\<^sub><' (firstUncommittedSlot (nodeState n))"
      unfolding committedTo_eq by simp

    from PublishRequest_committedTo
    show "\<And>i t x. \<langle> PublishRequest i t x \<rangle>\<leadsto> \<Longrightarrow> committed\<^sub><' i"
      unfolding committedTo_eq by simp

    from PublishRequest_quorum
    show "\<And>i s t x. s \<midarrow>\<langle> PublishRequest i t x \<rangle>\<leadsto> \<Longrightarrow> \<exists>q\<in>majorities (V' i). (\<forall>n\<in>q. promised i n s t) \<and> (prevAccepted i t q = {} \<or> (\<exists>t'. v i t = v i t' \<and> maxTerm (prevAccepted i t q) \<le> t' \<and> \<langle> PublishResponse i t' \<rangle>\<leadsto> \<and> t' < t))"
      using V_eq PublishRequest_committedTo isMessage_def by metis

    from ApplyCommit_quorum
    show "\<And>i t. \<langle> ApplyCommit i t \<rangle>\<leadsto>' \<Longrightarrow> \<exists>q\<in>majorities (V' i). \<forall>s\<in>q. s \<midarrow>\<langle> PublishResponse i t \<rangle>\<leadsto>"
      using V_eq committedTo_firstUncommittedSlot unfolding ApplyCommit' committedTo_def isCommitted_def
      by (metis ApplyCommit_PublishRequest_v\<^sub>c PublishRequest_committedTo V_eq isQuorum currentVotingNodes_firstUncommittedSlot nd_def prod.inject publishVotes isQuorum_def)
  qed
qed

lemma (in zenStep) handlePublishResponse_invariants:
  fixes s i t
  defines "result \<equiv> handlePublishResponse s i t nd"
  assumes nd': "nd' = fst result"
  assumes messages': "messages' = sendTo Broadcast result"
  assumes sent: "s \<midarrow>\<langle> PublishResponse i t \<rangle>\<leadsto>"
  shows "zen messages' nodeState'"
proof (cases "i = firstUncommittedSlot nd \<and> t = currentTerm nd")
  case False
  hence [simp]: "result = (nd, None)"
    by (auto simp add: result_def handlePublishResponse_def Let_def)

  have [simp]: "messages' = messages"
    by (simp add: messages')

  have [simp]: "nodeState' = nodeState"
    unfolding nodeState'_def
    by (intro ext, simp add: nd' nd_def)

  from zen_axioms show ?thesis by simp

next
  case True
  hence i: "i = firstUncommittedSlot nd"
    and t: "t = currentTerm nd"
    by simp_all

  define nd1 where "nd1 \<equiv> nd \<lparr>publishVotes := insert s (publishVotes nd)\<rparr>"
  define nodeState1 where "nodeState1 \<equiv> \<lambda>n. if n = n\<^sub>0 then nd1 else nodeState n"

  have result: "result = commitIfQuorate nd1"
    by (simp add: result_def handlePublishResponse_def i t nd1_def)

  have zenStep1: "zenStep messages nodeState messages nodeState1 n\<^sub>0"
    by (intro zenStepI2, auto simp add: nodeState1_def)

  have zenStep2: "zenStep messages nodeState1 messages' nodeState' n\<^sub>0"
  proof (intro zenStep.zenStepI1 [OF zenStep1] zenStep.addPublishVote_invariants [OF zenStep1] refl messages_subset,
      fold isMessageFromTo_def isMessageFrom_def nd_def)
    show "nodeState1 n\<^sub>0 = nd\<lparr>publishVotes := insert s (publishVotes nd)\<rparr>"
      by (simp add: nodeState1_def nd1_def)
    from sent show "s \<midarrow>\<langle> PublishResponse (firstUncommittedSlot nd) (currentTerm nd) \<rangle>\<leadsto>" by (simp add: True)
    show "\<And>n. n \<noteq> n\<^sub>0 \<Longrightarrow> nodeState1 n = nodeState' n" unfolding nodeState1_def nodeState'_def by simp
  qed

  show ?thesis
  proof (intro zenStep.commitIfQuorate_invariants [OF zenStep2])
    show "nodeState' n\<^sub>0 = fst (commitIfQuorate (nodeState1 n\<^sub>0))"
      by (simp add: nodeState'_def nd' result nodeState1_def)
    show "messages' = (case snd (commitIfQuorate (nodeState1 n\<^sub>0)) of None \<Rightarrow> messages | Some m \<Rightarrow> insert \<lparr>sender = n\<^sub>0, destination = Broadcast, payload = m\<rparr> messages)"
      by (cases "commitIfQuorate (nodeState1 n\<^sub>0)", cases "snd (commitIfQuorate (nodeState1 n\<^sub>0))",
          simp_all add: nodeState1_def messages' result_def handlePublishResponse_def i t nd1_def)
  qed
qed

lemma (in zenStep) handleApplyCommit_invariants:
  assumes nd': "nd' = handleApplyCommit i t nd"
  assumes messages'[simp]: "messages' = messages"
  assumes sent: "\<langle> ApplyCommit i t \<rangle>\<leadsto>"
  shows "zen messages' nodeState'"
proof (cases "i = firstUncommittedSlot nd \<and> lastAcceptedTerm nd = SomeTerm t")
  case False
  hence nd'[simp]: "nd' = nd"
    by (auto simp add: nd' handleApplyCommit_def)

  have nodeState'[simp]: "nodeState' = nodeState" unfolding nodeState'_def by (intro ext, simp add: nd_def)

  from zen_axioms show ?thesis unfolding nodeState' by simp

next
  case True
  hence i: "i = firstUncommittedSlot nd"
    and t: "lastAcceptedTerm nd = SomeTerm t" by simp_all

  have message_simps[simp]:
    "\<And>s p d. (s \<midarrow>\<langle> p \<rangle>\<rightarrow>' d) = (s \<midarrow>\<langle> p \<rangle>\<rightarrow> d)"
    "\<And>p d. (\<langle> p \<rangle>\<rightarrow>' d) = (\<langle> p \<rangle>\<rightarrow> d)"
    "\<And>s p. (s \<midarrow>\<langle> p \<rangle>\<leadsto>') = (s \<midarrow>\<langle> p \<rangle>\<leadsto>)"
    "\<And>p. (\<langle> p \<rangle>\<leadsto>') = (\<langle> p \<rangle>\<leadsto>)"
    by (unfold isMessageFromTo'_def isMessageTo'_def isMessageFrom'_def isMessage'_def,
        auto simp add: isMessageFromTo_def isMessageTo_def isMessageFrom_def isMessage_def)

  have v_eq[simp]: "v' = v" by (intro ext, auto simp add: v'_def v_def)
  have v\<^sub>c_eq[simp]: "v\<^sub>c' = v\<^sub>c" by (intro ext, auto simp add: v\<^sub>c'_def v\<^sub>c_def)
  have isCommitted_eq[simp]: "isCommitted' = isCommitted" by (intro ext, auto simp add: isCommitted'_def isCommitted_def)
  have committedTo_eq[simp]: "committed\<^sub><' = committed\<^sub><" by (intro ext, auto simp add: committedTo'_def committedTo_def)
  have V_eq[simp]: "V' = V" using v\<^sub>c_eq V'_def V_def by blast
  have promised_eq[simp]: "promised' = promised" by (intro ext, auto simp add: promised'_def promised_def)
  have lastCommittedClusterStateBefore_eq[simp]: "lastCommittedClusterStateBefore' = lastCommittedClusterStateBefore"
    unfolding lastCommittedClusterStateBefore_def lastCommittedClusterStateBefore'_def v\<^sub>c_eq ..
  have prevAccepted_eq[simp]: "prevAccepted' = prevAccepted" by (intro ext, auto simp add: prevAccepted'_def prevAccepted_def)

  from sent t
  have lastAcceptedValue_eq: "v\<^sub>c i = lastAcceptedValue nd"
    unfolding i nd_def using lastAcceptedTerm_Some_value [of n\<^sub>0 t]
    by (intro PublishRequest_function [OF ApplyCommit_PublishRequest_v\<^sub>c])

  show ?thesis
  proof (cases "isReconfiguration (v\<^sub>c i)")
    case False

    have "\<And>n. currentNode (nodeState' n) = currentNode (nodeState n)
      \<and> currentTerm (nodeState' n) = currentTerm (nodeState n)
      \<and> currentVotingNodes (nodeState' n) = currentVotingNodes (nodeState n)
      \<and> joinVotes (nodeState' n) = joinVotes (nodeState n)
      \<and> electionWon (nodeState' n) = electionWon (nodeState n)
      \<and> isQuorum (nodeState' n) = isQuorum (nodeState n)"
    proof (cases "lastAcceptedValue nd")
      case NoOp thus "\<And>n. ?thesis n"
        unfolding nodeState'_def nd' handleApplyCommit_def i t applyAcceptedValue_def isQuorum_def nd_def
        by simp
    next
      case ClusterStateDiff thus "\<And>n. ?thesis n"
        unfolding nodeState'_def nd' handleApplyCommit_def i t applyAcceptedValue_def isQuorum_def nd_def
        by simp
    next
      case Reconfigure with False lastAcceptedValue_eq show "\<And>n. ?thesis n" by simp
    qed
    hence property_simps[simp]:
      "\<And>n. currentNode (nodeState' n) = currentNode (nodeState n)"
      "\<And>n. currentTerm (nodeState' n) = currentTerm (nodeState n)"
      "\<And>n. currentVotingNodes (nodeState' n) = currentVotingNodes (nodeState n)"
      "\<And>n. joinVotes (nodeState' n) = joinVotes (nodeState n)"
      "\<And>n. electionWon (nodeState' n) = electionWon (nodeState n)"
      "\<And>n. isQuorum (nodeState' n) = isQuorum (nodeState n)"
      by simp_all

    have "\<And>n. firstUncommittedSlot (nodeState' n) = (if n = n\<^sub>0 then Suc (firstUncommittedSlot (nodeState n)) else firstUncommittedSlot (nodeState n))
     \<and> publishPermitted (nodeState' n) = (publishPermitted (nodeState n) \<or> n = n\<^sub>0)
     \<and> publishVotes (nodeState' n) = (if n = n\<^sub>0 then {} else publishVotes (nodeState n))
     \<and> lastAcceptedTerm (nodeState' n) = (if n = n\<^sub>0 then NO_TERM else lastAcceptedTerm (nodeState n))"
    proof (cases "lastAcceptedValue nd")
      case NoOp
      with i t show "\<And>n. ?thesis n"
        by (unfold nodeState'_def, auto simp add: lastAcceptedValue_eq nd_def nd' applyAcceptedValue_def isQuorum_def handleApplyCommit_def lastAcceptedTerm_def)
    next
      case ClusterStateDiff
      with i t show "\<And>n. ?thesis n"
        by (unfold nodeState'_def, auto simp add: lastAcceptedValue_eq nd_def nd' applyAcceptedValue_def isQuorum_def handleApplyCommit_def lastAcceptedTerm_def)
    next
      case Reconfigure with False lastAcceptedValue_eq show "\<And>n. ?thesis n" by simp
    qed
    hence updated_properties:
      "\<And>n. firstUncommittedSlot (nodeState' n) = (if n = n\<^sub>0 then Suc (firstUncommittedSlot (nodeState n)) else firstUncommittedSlot (nodeState n)) "
      "\<And>n. publishPermitted (nodeState' n) = (publishPermitted (nodeState n) \<or> n = n\<^sub>0)"
      "\<And>n. publishVotes (nodeState' n) = (if n = n\<^sub>0 then {} else publishVotes (nodeState n))"
      "\<And>n. lastAcceptedTerm (nodeState' n) = (if n = n\<^sub>0 then NO_TERM else lastAcceptedTerm (nodeState n))"
      by simp_all

    show ?thesis
      apply (intro zenI)
                          apply (unfold messages' message_simps committedTo_eq V_eq v_eq
          lastCommittedClusterStateBefore_eq property_simps promised_eq prevAccepted_eq)
    proof -
      from finite_messages show "finite messages" .
      from Vote_future show "\<And>i i' s t t' a. s \<midarrow>\<langle> Vote i t a \<rangle>\<leadsto> \<Longrightarrow> i < i' \<Longrightarrow> t' < t \<Longrightarrow> \<not> s \<midarrow>\<langle> PublishResponse i' t' \<rangle>\<leadsto>".
      from Vote_None show "\<And>i s t t'. s \<midarrow>\<langle> Vote i t NO_TERM \<rangle>\<leadsto> \<Longrightarrow> t' < t \<Longrightarrow> \<not> s \<midarrow>\<langle> PublishResponse i t' \<rangle>\<leadsto>".
      from Vote_Some_lt show "\<And>i s t t'. s \<midarrow>\<langle> Vote i t (SomeTerm t') \<rangle>\<leadsto> \<Longrightarrow> t' < t".
      from Vote_Some_PublishResponse show "\<And>i s t t'. s \<midarrow>\<langle> Vote i t (SomeTerm t') \<rangle>\<leadsto> \<Longrightarrow> s \<midarrow>\<langle> PublishResponse i t' \<rangle>\<leadsto>".
      from Vote_Some_max show "\<And>i s t t' t''. s \<midarrow>\<langle> Vote i t (SomeTerm t') \<rangle>\<leadsto> \<Longrightarrow> t' < t'' \<Longrightarrow> t'' < t \<Longrightarrow> \<not> s \<midarrow>\<langle> PublishResponse i t'' \<rangle>\<leadsto>".
      from Vote_not_broadcast show "\<And>i t a d. \<langle> Vote i t a \<rangle>\<rightarrow> d \<Longrightarrow> d \<noteq> Broadcast".
      from Vote_unique_destination show "\<And>i' i s t a a' d d'. s \<midarrow>\<langle> Vote i t a \<rangle>\<rightarrow> d \<Longrightarrow> s \<midarrow>\<langle> Vote i' t a' \<rangle>\<rightarrow> d' \<Longrightarrow> d = d'".
      from currentNode_nodeState show "\<And>n. currentNode (nodeState n) = n" .
      from Vote_currentTerm show "\<And>n i t a. n \<midarrow>\<langle> Vote i t a \<rangle>\<leadsto> \<Longrightarrow> t \<le> currentTerm (nodeState n)".
      from Vote_slot_function show "\<And>n i i' t a a'. n \<midarrow>\<langle> Vote i t a \<rangle>\<leadsto> \<Longrightarrow> n \<midarrow>\<langle> Vote i' t a' \<rangle>\<leadsto> \<Longrightarrow> i = i'".
      from electionWon_isQuorum show "\<And>n. electionWon (nodeState n) \<Longrightarrow> isQuorum (nodeState n) (joinVotes (nodeState n))".
      from PublishRequest_committedTo show "\<And>i t x. \<langle> PublishRequest i t x \<rangle>\<leadsto> \<Longrightarrow> committed\<^sub>< i".
      from PublishRequest_quorum show "\<And>i s t x. s \<midarrow>\<langle> PublishRequest i t x \<rangle>\<leadsto> \<Longrightarrow> \<exists>q\<in>majorities (V i). (\<forall>n\<in>q. promised i n s t) \<and> (prevAccepted i t q = {} \<or> (\<exists>t'. v i t = v i t' \<and> maxTerm (prevAccepted i t q) \<le> t' \<and> \<langle> PublishResponse i t' \<rangle>\<leadsto> \<and> t' < t))".
      from PublishRequest_function show "\<And>i t x x'. \<langle> PublishRequest i t x \<rangle>\<leadsto> \<Longrightarrow> \<langle> PublishRequest i t x' \<rangle>\<leadsto> \<Longrightarrow> x = x'".
      from PublishResponse_PublishRequest show "\<And>i s t. s \<midarrow>\<langle> PublishResponse i t \<rangle>\<leadsto> \<Longrightarrow> \<exists>x. \<langle> PublishRequest i t x \<rangle>\<leadsto>".
      from ApplyCommit_quorum show "\<And>i t. \<langle> ApplyCommit i t \<rangle>\<leadsto> \<Longrightarrow> \<exists>q\<in>majorities (V i). \<forall>s\<in>q. s \<midarrow>\<langle> PublishResponse i t \<rangle>\<leadsto>".
      from CatchUpResponse_committedTo show "\<And>i conf cs. \<langle> CatchUpResponse i conf cs \<rangle>\<leadsto> \<Longrightarrow> committed\<^sub>< i".
      from CatchUpResponse_V show "\<And>i conf cs. \<langle> CatchUpResponse i conf cs \<rangle>\<leadsto> \<Longrightarrow> V i = conf".
      from CatchUpResponse_lastCommittedClusterStateBefore show "\<And>i conf cs. \<langle> CatchUpResponse i conf cs \<rangle>\<leadsto> \<Longrightarrow> lastCommittedClusterStateBefore i = cs".

      fix n

      from firstUncommittedSlot_PublishResponse show "\<And>i t. firstUncommittedSlot (nodeState' n) < i \<Longrightarrow> \<not> n \<midarrow>\<langle> PublishResponse i t \<rangle>\<leadsto>" 
        using updated_properties by (cases "n = n\<^sub>0", auto)

      from lastAcceptedTerm_None show "\<And>i t. lastAcceptedTerm (nodeState' n) = NO_TERM \<Longrightarrow> \<not> n \<midarrow>\<langle> PublishResponse (firstUncommittedSlot (nodeState' n)) t \<rangle>\<leadsto>"
        using updated_properties firstUncommittedSlot_PublishResponse by (cases "n = n\<^sub>0", auto)

      from lastAcceptedTerm_Some_sent show "\<And>t. lastAcceptedTerm (nodeState' n) = SomeTerm t \<Longrightarrow> n \<midarrow>\<langle> PublishResponse (firstUncommittedSlot (nodeState' n)) t \<rangle>\<leadsto>"
        using updated_properties by (cases "n = n\<^sub>0", auto)

      from lastAcceptedTerm_Some_max show "\<And>t t'. lastAcceptedTerm (nodeState' n) = SomeTerm t \<Longrightarrow> n \<midarrow>\<langle> PublishResponse (firstUncommittedSlot (nodeState' n)) t' \<rangle>\<leadsto> \<Longrightarrow> t' \<le> t"
        using updated_properties by (cases "n = n\<^sub>0", auto)

      from lastAcceptedTerm_Some_value show "\<And>t. lastAcceptedTerm (nodeState' n) = SomeTerm t \<Longrightarrow> \<langle> PublishRequest (firstUncommittedSlot (nodeState' n)) t (lastAcceptedValue (nodeState' n)) \<rangle>\<leadsto>"
        using updated_properties by (cases "n = n\<^sub>0", auto, simp add: nodeState'_def)

      from lastAcceptedTerm_Some_currentTerm show "\<And>t. lastAcceptedTerm (nodeState' n) = SomeTerm t \<Longrightarrow> t \<le> currentTerm (nodeState n)"
        using updated_properties by (cases "n = n\<^sub>0", auto)

      from committedTo_firstUncommittedSlot show "committed\<^sub>< (firstUncommittedSlot (nodeState' n))"
        unfolding updated_properties committedTo_def apply (cases "n = n\<^sub>0", auto)
        using i isCommitted_def less_antisym nd_def sent by blast

      from joinVotes_max show "\<And>n' a'. \<not> (\<exists>x. \<langle> PublishRequest (firstUncommittedSlot (nodeState' n)) (currentTerm (nodeState n)) x \<rangle>\<leadsto>) \<Longrightarrow> n' \<in> joinVotes (nodeState n) \<Longrightarrow> n' \<midarrow>\<langle> Vote (firstUncommittedSlot (nodeState' n)) (currentTerm (nodeState n)) a' \<rangle>\<rightarrow> (OneNode n) \<Longrightarrow> a' \<le> lastAcceptedTerm (nodeState' n)"
        unfolding updated_properties apply (cases "n = n\<^sub>0", auto)
        using isMessageFromTo_def zen.Vote_slot_function zen.joinVotes zen_axioms by fastforce

      from publishVotes show "\<And>n'. n' \<in> publishVotes (nodeState' n) \<Longrightarrow> n' \<midarrow>\<langle> PublishResponse (firstUncommittedSlot (nodeState' n)) (currentTerm (nodeState n)) \<rangle>\<leadsto>"
        unfolding updated_properties apply (cases "n = n\<^sub>0", auto) done

      from joinVotes show "\<And>n'. n' \<in> joinVotes (nodeState n) \<Longrightarrow> promised (firstUncommittedSlot (nodeState' n)) n' n (currentTerm (nodeState n))"
        unfolding updated_properties apply (cases "n = n\<^sub>0", auto)
        by (meson le_SucI promised_def)

      from currentVotingNodes_firstUncommittedSlot show "\<And>n. currentVotingNodes (nodeState n) = V (firstUncommittedSlot (nodeState' n))"
        unfolding updated_properties using False i nd_def by (cases "n = n\<^sub>0", auto)

      from firstUncommittedSlot_PublishRequest show "\<And>i t x. firstUncommittedSlot (nodeState' n) < i \<Longrightarrow> \<not> n \<midarrow>\<langle> PublishRequest i t x \<rangle>\<leadsto>"
        unfolding updated_properties apply (cases "n = n\<^sub>0", auto) done

      from PublishRequest_currentTerm show "\<And>t x. n \<midarrow>\<langle> PublishRequest (firstUncommittedSlot (nodeState' n)) t x \<rangle>\<leadsto> \<Longrightarrow> t \<le> currentTerm (nodeState n)"
        unfolding updated_properties apply (cases "n = n\<^sub>0", auto simp add: firstUncommittedSlot_PublishRequest) done

      from PublishRequest_publishPermitted_currentTerm show "\<And>t x. n \<midarrow>\<langle> PublishRequest (firstUncommittedSlot (nodeState' n)) t x \<rangle>\<leadsto> \<Longrightarrow> publishPermitted (nodeState' n) \<Longrightarrow> t < currentTerm (nodeState n)"
        unfolding updated_properties apply (cases "n = n\<^sub>0", auto simp add: firstUncommittedSlot_PublishRequest) done

      from currentClusterState_lastCommittedClusterStateBefore
      show "currentClusterState (nodeState' n) = lastCommittedClusterStateBefore (firstUncommittedSlot (nodeState' n))"
      proof (cases "n = n\<^sub>0")
        case False with currentClusterState_lastCommittedClusterStateBefore
        show ?thesis unfolding nodeState'_def by auto
      next
        case True
        show ?thesis
        proof (cases "v\<^sub>c i")
          case NoOp
          with currentClusterState_lastCommittedClusterStateBefore True lastAcceptedValue_eq i t
          show ?thesis
            unfolding nodeState'_def
            by (simp add: nd' nd_def applyAcceptedValue_def handleApplyCommit_def)
        next
          case Reconfigure with False show ?thesis by simp
        next
          case (ClusterStateDiff diff)
          with lastAcceptedValue_eq have "lastAcceptedValue nd = ClusterStateDiff diff" by simp
          with ClusterStateDiff True i t currentClusterState_lastCommittedClusterStateBefore
          show ?thesis
            unfolding nodeState'_def
            by (simp add: nd' nd_def applyAcceptedValue_def handleApplyCommit_def)
        qed
      qed
    qed

  next
    case True
    then obtain newConfig where Reconfigure: "v\<^sub>c i = Reconfigure newConfig" by (cases "v\<^sub>c i", auto)
    with lastAcceptedValue_eq have lastAcceptedValue_eq: "lastAcceptedValue nd = Reconfigure newConfig" by simp

    hence property_simps[simp]:
      "\<And>n. currentNode (nodeState' n) = currentNode (nodeState n)"
      "\<And>n. currentTerm (nodeState' n) = currentTerm (nodeState n)"
      "\<And>n. currentClusterState (nodeState' n) = currentClusterState (nodeState n)"
      "\<And>n. joinVotes (nodeState' n) = joinVotes (nodeState n)"
      unfolding nodeState'_def by (auto simp add: nd' handleApplyCommit_def applyAcceptedValue_def nd_def
          lastAcceptedTerm_def firstUncommittedSlot_def lastAcceptedValue_def)

    have updated_properties:
      "\<And>n. firstUncommittedSlot (nodeState' n) = (if n = n\<^sub>0 then Suc (firstUncommittedSlot (nodeState n)) else firstUncommittedSlot (nodeState n)) "
      "\<And>n. publishPermitted (nodeState' n) = (publishPermitted (nodeState n) \<or> n = n\<^sub>0)"
      "\<And>n. publishVotes (nodeState' n) = (if n = n\<^sub>0 then {} else publishVotes (nodeState n))"
      "\<And>n. currentVotingNodes (nodeState' n) = (if n = n\<^sub>0 then set newConfig else currentVotingNodes (nodeState n))"
      "\<And>n. electionWon (nodeState' n) = (if n = n\<^sub>0 then joinVotes nd \<in> majorities (set newConfig) else electionWon (nodeState n))"
      "\<And>n. isQuorum (nodeState' n) = (if n = n\<^sub>0 then (\<lambda>q. q \<in> majorities (set newConfig)) else isQuorum (nodeState n))"
      "\<And>n. currentVotingNodes (nodeState' n) = (if n = n\<^sub>0 then set newConfig else currentVotingNodes (nodeState n))"
      "\<And>n. lastAcceptedTerm (nodeState' n) = (if n = n\<^sub>0 then NO_TERM else lastAcceptedTerm (nodeState n))"
      "\<And>n. n \<noteq> n\<^sub>0 \<Longrightarrow> lastAcceptedValue (nodeState' n) = lastAcceptedValue (nodeState n)"
      unfolding nodeState'_def using i t lastAcceptedValue_eq
      by (auto simp add: nd' handleApplyCommit_def applyAcceptedValue_def nd_def isQuorum_def lastAcceptedTerm_def)

    show ?thesis
      apply (intro zenI)
                          apply (unfold messages' message_simps committedTo_eq V_eq v_eq
          lastCommittedClusterStateBefore_eq property_simps promised_eq prevAccepted_eq)
    proof -
      from finite_messages show "finite messages" .
      from Vote_future show "\<And>i i' s t t' a. s \<midarrow>\<langle> Vote i t a \<rangle>\<leadsto> \<Longrightarrow> i < i' \<Longrightarrow> t' < t \<Longrightarrow> \<not> s \<midarrow>\<langle> PublishResponse i' t' \<rangle>\<leadsto>".
      from Vote_None show "\<And>i s t t'. s \<midarrow>\<langle> Vote i t NO_TERM \<rangle>\<leadsto> \<Longrightarrow> t' < t \<Longrightarrow> \<not> s \<midarrow>\<langle> PublishResponse i t' \<rangle>\<leadsto>".
      from Vote_Some_lt show "\<And>i s t t'. s \<midarrow>\<langle> Vote i t (SomeTerm t') \<rangle>\<leadsto> \<Longrightarrow> t' < t".
      from Vote_Some_PublishResponse show "\<And>i s t t'. s \<midarrow>\<langle> Vote i t (SomeTerm t') \<rangle>\<leadsto> \<Longrightarrow> s \<midarrow>\<langle> PublishResponse i t' \<rangle>\<leadsto>".
      from Vote_Some_max show "\<And>i s t t' t''. s \<midarrow>\<langle> Vote i t (SomeTerm t') \<rangle>\<leadsto> \<Longrightarrow> t' < t'' \<Longrightarrow> t'' < t \<Longrightarrow> \<not> s \<midarrow>\<langle> PublishResponse i t'' \<rangle>\<leadsto>".
      from Vote_not_broadcast show "\<And>i t a d. \<langle> Vote i t a \<rangle>\<rightarrow> d \<Longrightarrow> d \<noteq> Broadcast".
      from Vote_unique_destination show "\<And>i' i s t a a' d d'. s \<midarrow>\<langle> Vote i t a \<rangle>\<rightarrow> d \<Longrightarrow> s \<midarrow>\<langle> Vote i' t a' \<rangle>\<rightarrow> d' \<Longrightarrow> d = d'".
      from currentNode_nodeState show "\<And>n. currentNode (nodeState n) = n" .
      from Vote_currentTerm show "\<And>n i t a. n \<midarrow>\<langle> Vote i t a \<rangle>\<leadsto> \<Longrightarrow> t \<le> currentTerm (nodeState n)".
      from Vote_slot_function show "\<And>n i i' t a a'. n \<midarrow>\<langle> Vote i t a \<rangle>\<leadsto> \<Longrightarrow> n \<midarrow>\<langle> Vote i' t a' \<rangle>\<leadsto> \<Longrightarrow> i = i'".
      from PublishRequest_committedTo show "\<And>i t x. \<langle> PublishRequest i t x \<rangle>\<leadsto> \<Longrightarrow> committed\<^sub>< i".
      from PublishRequest_quorum show "\<And>i s t x. s \<midarrow>\<langle> PublishRequest i t x \<rangle>\<leadsto> \<Longrightarrow> \<exists>q\<in>majorities (V i). (\<forall>n\<in>q. promised i n s t) \<and> (prevAccepted i t q = {} \<or> (\<exists>t'. v i t = v i t' \<and> maxTerm (prevAccepted i t q) \<le> t' \<and> \<langle> PublishResponse i t' \<rangle>\<leadsto> \<and> t' < t))".
      from PublishRequest_function show "\<And>i t x x'. \<langle> PublishRequest i t x \<rangle>\<leadsto> \<Longrightarrow> \<langle> PublishRequest i t x' \<rangle>\<leadsto> \<Longrightarrow> x = x'".
      from PublishResponse_PublishRequest show "\<And>i s t. s \<midarrow>\<langle> PublishResponse i t \<rangle>\<leadsto> \<Longrightarrow> \<exists>x. \<langle> PublishRequest i t x \<rangle>\<leadsto>".
      from ApplyCommit_quorum show "\<And>i t. \<langle> ApplyCommit i t \<rangle>\<leadsto> \<Longrightarrow> \<exists>q\<in>majorities (V i). \<forall>s\<in>q. s \<midarrow>\<langle> PublishResponse i t \<rangle>\<leadsto>".
      from CatchUpResponse_committedTo show "\<And>i conf cs. \<langle> CatchUpResponse i conf cs \<rangle>\<leadsto> \<Longrightarrow> committed\<^sub>< i".
      from CatchUpResponse_V show "\<And>i conf cs. \<langle> CatchUpResponse i conf cs \<rangle>\<leadsto> \<Longrightarrow> V i = conf".
      from CatchUpResponse_lastCommittedClusterStateBefore show "\<And>i conf cs. \<langle> CatchUpResponse i conf cs \<rangle>\<leadsto> \<Longrightarrow> lastCommittedClusterStateBefore i = cs".

      fix n

      from firstUncommittedSlot_PublishResponse show "\<And>i t. firstUncommittedSlot (nodeState' n) < i \<Longrightarrow> \<not> n \<midarrow>\<langle> PublishResponse i t \<rangle>\<leadsto>"
        using updated_properties by (cases "n = n\<^sub>0", auto)

      from lastAcceptedTerm_None show "\<And>i t. lastAcceptedTerm (nodeState' n) = NO_TERM \<Longrightarrow> \<not> n \<midarrow>\<langle> PublishResponse (firstUncommittedSlot (nodeState' n)) t \<rangle>\<leadsto>"
        using updated_properties firstUncommittedSlot_PublishResponse by (cases "n = n\<^sub>0", auto)

      from lastAcceptedTerm_Some_sent show "\<And>t. lastAcceptedTerm (nodeState' n) = SomeTerm t \<Longrightarrow> n \<midarrow>\<langle> PublishResponse (firstUncommittedSlot (nodeState' n)) t \<rangle>\<leadsto>"
        using updated_properties by (cases "n = n\<^sub>0", auto)

      from lastAcceptedTerm_Some_max show "\<And>t t'. lastAcceptedTerm (nodeState' n) = SomeTerm t \<Longrightarrow> n \<midarrow>\<langle> PublishResponse (firstUncommittedSlot (nodeState' n)) t' \<rangle>\<leadsto> \<Longrightarrow> t' \<le> t"
        using updated_properties by (cases "n = n\<^sub>0", auto)

      from lastAcceptedTerm_Some_value show "\<And>t. lastAcceptedTerm (nodeState' n) = SomeTerm t \<Longrightarrow> \<langle> PublishRequest (firstUncommittedSlot (nodeState' n)) t (lastAcceptedValue (nodeState' n)) \<rangle>\<leadsto>"
        using updated_properties by (cases "n = n\<^sub>0", auto)

      from committedTo_firstUncommittedSlot show "committed\<^sub>< (firstUncommittedSlot (nodeState' n))"
        unfolding updated_properties committedTo_def apply (cases "n = n\<^sub>0", auto)
        using i isCommitted_def less_antisym nd_def sent by blast

      from electionWon_isQuorum show "\<And>n. electionWon (nodeState' n) \<Longrightarrow> isQuorum (nodeState' n) (joinVotes (nodeState n))"
        unfolding updated_properties apply (cases "n = n\<^sub>0", auto simp add: nd_def) done

      from joinVotes_max show "\<And>n' a'. \<not> (\<exists>x. \<langle> PublishRequest (firstUncommittedSlot (nodeState' n)) (currentTerm (nodeState n)) x \<rangle>\<leadsto>) \<Longrightarrow> n' \<in> joinVotes (nodeState n) \<Longrightarrow> n' \<midarrow>\<langle> Vote (firstUncommittedSlot (nodeState' n)) (currentTerm (nodeState n)) a' \<rangle>\<rightarrow> (OneNode n) \<Longrightarrow> a' \<le> lastAcceptedTerm (nodeState' n)"
        unfolding updated_properties apply (cases "n = n\<^sub>0", auto)
        using isMessageFromTo_def zen.Vote_slot_function zen.joinVotes zen_axioms by fastforce

      from publishVotes show "\<And>n'. n' \<in> publishVotes (nodeState' n) \<Longrightarrow> n' \<midarrow>\<langle> PublishResponse (firstUncommittedSlot (nodeState' n)) (currentTerm (nodeState n)) \<rangle>\<leadsto>"
        unfolding updated_properties apply (cases "n = n\<^sub>0", auto) done

      from joinVotes show "\<And>n'. n' \<in> joinVotes (nodeState n) \<Longrightarrow> promised (firstUncommittedSlot (nodeState' n)) n' n (currentTerm (nodeState n))"
        unfolding updated_properties apply (cases "n = n\<^sub>0", auto)
        by (meson le_SucI promised_def)

      from firstUncommittedSlot_PublishRequest show "\<And>i t x. firstUncommittedSlot (nodeState' n) < i \<Longrightarrow> \<not> n \<midarrow>\<langle> PublishRequest i t x \<rangle>\<leadsto>"
        unfolding updated_properties apply (cases "n = n\<^sub>0", auto) done

      from PublishRequest_currentTerm show "\<And>t x. n \<midarrow>\<langle> PublishRequest (firstUncommittedSlot (nodeState' n)) t x \<rangle>\<leadsto> \<Longrightarrow> t \<le> currentTerm (nodeState n)"
        unfolding updated_properties apply (cases "n = n\<^sub>0", auto simp add: firstUncommittedSlot_PublishRequest) done

      from PublishRequest_publishPermitted_currentTerm show "\<And>t x. n \<midarrow>\<langle> PublishRequest (firstUncommittedSlot (nodeState' n)) t x \<rangle>\<leadsto> \<Longrightarrow> publishPermitted (nodeState' n) \<Longrightarrow> t < currentTerm (nodeState n)"
        unfolding updated_properties apply (cases "n = n\<^sub>0", auto simp add: firstUncommittedSlot_PublishRequest) done

      from currentClusterState_lastCommittedClusterStateBefore Reconfigure i nd_def
      show "currentClusterState (nodeState n) = lastCommittedClusterStateBefore (firstUncommittedSlot (nodeState' n))"
        unfolding updated_properties committedTo_def by (cases "n = n\<^sub>0", auto)

      from currentVotingNodes_firstUncommittedSlot show "\<And>n. currentVotingNodes (nodeState' n) = V (firstUncommittedSlot (nodeState' n))"
        unfolding updated_properties committedTo_def using Reconfigure i nd_def by (cases "n = n\<^sub>0", auto)

      from lastAcceptedTerm_Some_currentTerm show "\<And>t. lastAcceptedTerm (nodeState' n) = SomeTerm t \<Longrightarrow> t \<le> currentTerm (nodeState n)"
        unfolding updated_properties apply (cases "n = n\<^sub>0", auto) done
    qed
  qed
qed

lemma (in zenStep) handleCatchUpRequest_invariants:
  fixes s i t
  defines "result \<equiv> handleCatchUpRequest nd"
  assumes nd': "nd' = fst result"
  assumes messages': "messages' = sendTo d\<^sub>0 result"
  shows "zen messages' nodeState'"
proof -

  have result: "result = (nd, Some (CatchUpResponse (firstUncommittedSlot nd) (currentVotingNodes nd) (currentClusterState nd)))"
    by (simp add: result_def handleCatchUpRequest_def)

  have nd'[simp]: "nd' = nd" by (simp add: nd' result)
  have nodeState'[simp]: "nodeState' = nodeState" by (intro ext, simp add: nodeState'_def result nd_def)

  have messages': "messages' = insert \<lparr> sender = n\<^sub>0, destination = d\<^sub>0, payload = CatchUpResponse (firstUncommittedSlot nd) (currentVotingNodes nd) (currentClusterState nd) \<rparr> messages"
    by (simp add: messages' result)

  have message_simps[simp]:
    "\<And>s d i t. (s \<midarrow>\<langle> PublishResponse i t \<rangle>\<rightarrow>' d) = (s \<midarrow>\<langle> PublishResponse i t \<rangle>\<rightarrow> d)"
    "\<And>s d i t. (s \<midarrow>\<langle> ApplyCommit i t \<rangle>\<rightarrow>' d) = (s \<midarrow>\<langle> ApplyCommit i t \<rangle>\<rightarrow> d)"
    "\<And>s d i t x. (s \<midarrow>\<langle> PublishRequest i t x \<rangle>\<rightarrow>' d) = (s \<midarrow>\<langle> PublishRequest i t x \<rangle>\<rightarrow> d)"
    "\<And>s d i t a. (s \<midarrow>\<langle> Vote i t a \<rangle>\<rightarrow>' d) = (s \<midarrow>\<langle> Vote i t a \<rangle>\<rightarrow> d)"
    "\<And>d i t. (\<langle> PublishResponse i t \<rangle>\<rightarrow>' d) = (\<langle> PublishResponse i t \<rangle>\<rightarrow> d)"
    "\<And>d i t. (\<langle> ApplyCommit i t \<rangle>\<rightarrow>' d) = (\<langle> ApplyCommit i t \<rangle>\<rightarrow> d)"
    "\<And>d i t x. (\<langle> PublishRequest i t x \<rangle>\<rightarrow>' d) = (\<langle> PublishRequest i t x \<rangle>\<rightarrow> d)"
    "\<And>d i t a. (\<langle> Vote i t a \<rangle>\<rightarrow>' d) = (\<langle> Vote i t a \<rangle>\<rightarrow> d)"
    "\<And>s i t. (s \<midarrow>\<langle> PublishResponse i t \<rangle>\<leadsto>') = (s \<midarrow>\<langle> PublishResponse i t \<rangle>\<leadsto>)"
    "\<And>s i t. (s \<midarrow>\<langle> ApplyCommit i t \<rangle>\<leadsto>') = (s \<midarrow>\<langle> ApplyCommit i t \<rangle>\<leadsto>)"
    "\<And>s i t x. (s \<midarrow>\<langle> PublishRequest i t x \<rangle>\<leadsto>') = (s \<midarrow>\<langle> PublishRequest i t x \<rangle>\<leadsto>)"
    "\<And>s i t a. (s \<midarrow>\<langle> Vote i t a \<rangle>\<leadsto>') = (s \<midarrow>\<langle> Vote i t a \<rangle>\<leadsto>)"
    "\<And>i t. (\<langle> PublishResponse i t \<rangle>\<leadsto>') = (\<langle> PublishResponse i t \<rangle>\<leadsto>)"
    "\<And>i t. (\<langle> ApplyCommit i t \<rangle>\<leadsto>') = (\<langle> ApplyCommit i t \<rangle>\<leadsto>)"
    "\<And>i t x. (\<langle> PublishRequest i t x \<rangle>\<leadsto>') = (\<langle> PublishRequest i t x \<rangle>\<leadsto>)"
    "\<And>i t a. (\<langle> Vote i t a \<rangle>\<leadsto>') = (\<langle> Vote i t a \<rangle>\<leadsto>)"
    by (unfold isMessageFromTo'_def isMessageTo'_def isMessageFrom'_def isMessage'_def,
        auto simp add: messages' isMessageFromTo_def isMessageTo_def isMessageFrom_def isMessage_def)

  have CatchUpResponse':
    "\<And>s d i conf cs. (s \<midarrow>\<langle> CatchUpResponse i conf cs \<rangle>\<rightarrow>' d) = (s \<midarrow>\<langle> CatchUpResponse i conf cs \<rangle>\<rightarrow> d
      \<or> (s, i, conf, cs, d) = (n\<^sub>0, firstUncommittedSlot nd, currentVotingNodes nd, currentClusterState nd, d\<^sub>0))"
    "\<And>d i conf cs. (\<langle> CatchUpResponse i conf cs \<rangle>\<rightarrow>' d) = (\<langle> CatchUpResponse i conf cs \<rangle>\<rightarrow> d
      \<or> (i, conf, cs, d) = (firstUncommittedSlot nd, currentVotingNodes nd, currentClusterState nd, d\<^sub>0))"
    "\<And>s i conf cs. (s \<midarrow>\<langle> CatchUpResponse i conf cs \<rangle>\<leadsto>') = (s \<midarrow>\<langle> CatchUpResponse i conf cs \<rangle>\<leadsto>
      \<or> (s, i, conf, cs) = (n\<^sub>0, firstUncommittedSlot nd, currentVotingNodes nd, currentClusterState nd))"
    "\<And>i conf cs. (\<langle> CatchUpResponse i conf cs \<rangle>\<leadsto>') = (\<langle> CatchUpResponse i conf cs \<rangle>\<leadsto>
      \<or> (i, conf, cs) = (firstUncommittedSlot nd, currentVotingNodes nd, currentClusterState nd))"
    unfolding isMessageFromTo_def isMessageFromTo'_def isMessageFrom_def isMessageFrom'_def isMessageTo_def isMessageTo'_def isMessage_def isMessage'_def
    by (auto simp add: messages')

  have v_eq[simp]: "v' = v" by (intro ext, auto simp add: v'_def v_def)
  have v\<^sub>c_eq[simp]: "v\<^sub>c' = v\<^sub>c" by (intro ext, auto simp add: v\<^sub>c'_def v\<^sub>c_def)
  have isCommitted_eq[simp]: "isCommitted' = isCommitted" by (intro ext, auto simp add: isCommitted'_def isCommitted_def)
  have committedTo_eq[simp]: "committed\<^sub><' = committed\<^sub><" by (intro ext, auto simp add: committedTo'_def committedTo_def)
  have V_eq[simp]: "V' = V" using v\<^sub>c_eq V'_def V_def by blast
  have promised_eq[simp]: "promised' = promised" by (intro ext, auto simp add: promised'_def promised_def)
  have lastCommittedClusterStateBefore_eq[simp]: "lastCommittedClusterStateBefore' = lastCommittedClusterStateBefore"
    unfolding lastCommittedClusterStateBefore_def lastCommittedClusterStateBefore'_def v\<^sub>c_eq ..
  have prevAccepted_eq[simp]: "prevAccepted' = prevAccepted" by (intro ext, auto simp add: prevAccepted'_def prevAccepted_def)

  show ?thesis
    apply (intro zenI)
                        apply (unfold message_simps committedTo_eq V_eq v_eq
        lastCommittedClusterStateBefore_eq promised_eq prevAccepted_eq nodeState')
  proof -
    from finite_messages show "finite messages'" by (simp add: messages')
    from Vote_future show "\<And>i i' s t t' a. s \<midarrow>\<langle> Vote i t a \<rangle>\<leadsto> \<Longrightarrow> i < i' \<Longrightarrow> t' < t \<Longrightarrow> \<not> s \<midarrow>\<langle> PublishResponse i' t' \<rangle>\<leadsto>".
    from Vote_None show "\<And>i s t t'. s \<midarrow>\<langle> Vote i t NO_TERM \<rangle>\<leadsto> \<Longrightarrow> t' < t \<Longrightarrow> \<not> s \<midarrow>\<langle> PublishResponse i t' \<rangle>\<leadsto>".
    from Vote_Some_lt show "\<And>i s t t'. s \<midarrow>\<langle> Vote i t (SomeTerm t') \<rangle>\<leadsto> \<Longrightarrow> t' < t".
    from Vote_Some_PublishResponse show "\<And>i s t t'. s \<midarrow>\<langle> Vote i t (SomeTerm t') \<rangle>\<leadsto> \<Longrightarrow> s \<midarrow>\<langle> PublishResponse i t' \<rangle>\<leadsto>".
    from Vote_Some_max show "\<And>i s t t' t''. s \<midarrow>\<langle> Vote i t (SomeTerm t') \<rangle>\<leadsto> \<Longrightarrow> t' < t'' \<Longrightarrow> t'' < t \<Longrightarrow> \<not> s \<midarrow>\<langle> PublishResponse i t'' \<rangle>\<leadsto>".
    from Vote_not_broadcast show "\<And>i t a d. \<langle> Vote i t a \<rangle>\<rightarrow> d \<Longrightarrow> d \<noteq> Broadcast".
    from Vote_unique_destination show "\<And>i' i s t a a' d d'. s \<midarrow>\<langle> Vote i t a \<rangle>\<rightarrow> d \<Longrightarrow> s \<midarrow>\<langle> Vote i' t a' \<rangle>\<rightarrow> d' \<Longrightarrow> d = d'".
    from currentNode_nodeState show "\<And>n. currentNode (nodeState n) = n" .
    from committedTo_firstUncommittedSlot show "\<And>n. committed\<^sub>< (firstUncommittedSlot (nodeState n))" .
    from firstUncommittedSlot_PublishResponse show "\<And>n i t. firstUncommittedSlot (nodeState n) < i \<Longrightarrow> \<not> n \<midarrow>\<langle> PublishResponse i t \<rangle>\<leadsto>" .
    from lastAcceptedTerm_None show "\<And>n i t. lastAcceptedTerm (nodeState n) = NO_TERM \<Longrightarrow> \<not> n \<midarrow>\<langle> PublishResponse (firstUncommittedSlot (nodeState n)) t \<rangle>\<leadsto>".
    from lastAcceptedTerm_Some_sent show "\<And>n t. lastAcceptedTerm (nodeState n) = SomeTerm t \<Longrightarrow> n \<midarrow>\<langle> PublishResponse (firstUncommittedSlot (nodeState n)) t \<rangle>\<leadsto>".
    from lastAcceptedTerm_Some_max show "\<And>n t t'. lastAcceptedTerm (nodeState n) = SomeTerm t \<Longrightarrow> n \<midarrow>\<langle> PublishResponse (firstUncommittedSlot (nodeState n)) t' \<rangle>\<leadsto> \<Longrightarrow> t' \<le> t".
    from Vote_currentTerm show "\<And>n i t a. n \<midarrow>\<langle> Vote i t a \<rangle>\<leadsto> \<Longrightarrow> t \<le> currentTerm (nodeState n)".
    from Vote_slot_function show "\<And>n i i' t a a'. n \<midarrow>\<langle> Vote i t a \<rangle>\<leadsto> \<Longrightarrow> n \<midarrow>\<langle> Vote i' t a' \<rangle>\<leadsto> \<Longrightarrow> i = i'".
    from electionWon_isQuorum show "\<And>n. electionWon (nodeState n) \<Longrightarrow> isQuorum (nodeState n) (joinVotes (nodeState n))".
    from joinVotes_max show "\<And>n n' a'. \<not> (\<exists>x. \<langle> PublishRequest (firstUncommittedSlot (nodeState n)) (currentTerm (nodeState n)) x \<rangle>\<leadsto>) \<Longrightarrow> n' \<in> joinVotes (nodeState n) \<Longrightarrow> n' \<midarrow>\<langle> Vote (firstUncommittedSlot (nodeState n)) (currentTerm (nodeState n)) a' \<rangle>\<rightarrow> (OneNode n) \<Longrightarrow> a' \<le> lastAcceptedTerm (nodeState n)".
    from publishVotes show "\<And>n n'. n' \<in> publishVotes (nodeState n) \<Longrightarrow> n' \<midarrow>\<langle> PublishResponse (firstUncommittedSlot (nodeState n)) (currentTerm (nodeState n)) \<rangle>\<leadsto>".
    from currentClusterState_lastCommittedClusterStateBefore show "\<And>n. currentClusterState (nodeState n) = lastCommittedClusterStateBefore (firstUncommittedSlot (nodeState n))".
    from joinVotes show "\<And>n n'. n' \<in> joinVotes (nodeState n) \<Longrightarrow> promised (firstUncommittedSlot (nodeState n)) n' n (currentTerm (nodeState n))".
    from PublishRequest_committedTo show "\<And>i t x. \<langle> PublishRequest i t x \<rangle>\<leadsto> \<Longrightarrow> committed\<^sub>< i".
    from PublishRequest_quorum show "\<And>i s t x. s \<midarrow>\<langle> PublishRequest i t x \<rangle>\<leadsto> \<Longrightarrow> \<exists>q\<in>majorities (V i). (\<forall>n\<in>q. promised i n s t) \<and> (prevAccepted i t q = {} \<or> (\<exists>t'. v i t = v i t' \<and> maxTerm (prevAccepted i t q) \<le> t' \<and> \<langle> PublishResponse i t' \<rangle>\<leadsto> \<and> t' < t))".
    from PublishRequest_function show "\<And>i t x x'. \<langle> PublishRequest i t x \<rangle>\<leadsto> \<Longrightarrow> \<langle> PublishRequest i t x' \<rangle>\<leadsto> \<Longrightarrow> x = x'".
    from PublishResponse_PublishRequest show "\<And>i s t. s \<midarrow>\<langle> PublishResponse i t \<rangle>\<leadsto> \<Longrightarrow> \<exists>x. \<langle> PublishRequest i t x \<rangle>\<leadsto>".
    from ApplyCommit_quorum show "\<And>i t. \<langle> ApplyCommit i t \<rangle>\<leadsto> \<Longrightarrow> \<exists>q\<in>majorities (V i). \<forall>s\<in>q. s \<midarrow>\<langle> PublishResponse i t \<rangle>\<leadsto>".
    from currentVotingNodes_firstUncommittedSlot show "\<And>n. currentVotingNodes (nodeState n) = V (firstUncommittedSlot (nodeState n))".
    from firstUncommittedSlot_PublishRequest show "\<And>i n t x. firstUncommittedSlot (nodeState n) < i \<Longrightarrow> \<not> n \<midarrow>\<langle> PublishRequest i t x \<rangle>\<leadsto>".
    from lastAcceptedTerm_Some_value show "\<And>n t. lastAcceptedTerm (nodeState n) = SomeTerm t \<Longrightarrow> \<langle> PublishRequest (firstUncommittedSlot (nodeState n)) t (lastAcceptedValue (nodeState n)) \<rangle>\<leadsto>".
    from PublishRequest_currentTerm show "\<And>n t x. n \<midarrow>\<langle> PublishRequest (firstUncommittedSlot (nodeState n)) t x \<rangle>\<leadsto> \<Longrightarrow> t \<le> currentTerm (nodeState n)".
    from PublishRequest_publishPermitted_currentTerm show "\<And>n t x. n \<midarrow>\<langle> PublishRequest (firstUncommittedSlot (nodeState n)) t x \<rangle>\<leadsto> \<Longrightarrow> publishPermitted (nodeState n) \<Longrightarrow> t < currentTerm (nodeState n)".
    from lastAcceptedTerm_Some_currentTerm show "\<And>n t. lastAcceptedTerm (nodeState n) = SomeTerm t \<Longrightarrow> t \<le> currentTerm (nodeState n)".

    from CatchUpResponse_committedTo committedTo_firstUncommittedSlot
    show "\<And>i conf cs. \<langle> CatchUpResponse i conf cs \<rangle>\<leadsto>' \<Longrightarrow> committed\<^sub>< i"
      unfolding CatchUpResponse' nd_def by blast

    from CatchUpResponse_V currentVotingNodes_firstUncommittedSlot
    show "\<And>i conf cs. \<langle> CatchUpResponse i conf cs \<rangle>\<leadsto>' \<Longrightarrow> V i = conf"
      unfolding CatchUpResponse' nd_def isQuorum_def by auto

    from CatchUpResponse_lastCommittedClusterStateBefore currentClusterState_lastCommittedClusterStateBefore
    show "\<And>i conf cs. \<langle> CatchUpResponse i conf cs \<rangle>\<leadsto>' \<Longrightarrow> lastCommittedClusterStateBefore i = cs"
      unfolding CatchUpResponse' nd_def by auto
  qed
qed


lemma (in zenStep) handleCatchUpResponse_invariants:
  assumes nd': "nd' = handleCatchUpResponse i conf cs nd"
  assumes messages'[simp]: "messages' = messages"
  assumes sent: "\<langle> CatchUpResponse i conf cs \<rangle>\<leadsto>"
  shows "zen messages' nodeState'"
proof (cases "firstUncommittedSlot nd < i")
  case False
  hence nd'[simp]: "nd' = nd"
    by (auto simp add: nd' handleCatchUpResponse_def)

  have nodeState'[simp]: "nodeState' = nodeState" unfolding nodeState'_def by (intro ext, simp add: nd_def)

  from zen_axioms show ?thesis unfolding nodeState' by simp

next
  case True

  hence nd': "nd' = nd \<lparr> firstUncommittedSlot := i
                , publishPermitted := True
                , publishVotes := {}
                , currentVotingNodes := conf
                , currentClusterState := cs
                , joinVotes := {}
                , electionWon := False
                , lastAcceptedData := None \<rparr>"
    by (simp add: nd', simp add: handleCatchUpResponse_def)

  have message_simps[simp]:
    "\<And>s p d. (s \<midarrow>\<langle> p \<rangle>\<rightarrow>' d) = (s \<midarrow>\<langle> p \<rangle>\<rightarrow> d)"
    "\<And>p d. (\<langle> p \<rangle>\<rightarrow>' d) = (\<langle> p \<rangle>\<rightarrow> d)"
    "\<And>s p. (s \<midarrow>\<langle> p \<rangle>\<leadsto>') = (s \<midarrow>\<langle> p \<rangle>\<leadsto>)"
    "\<And>p. (\<langle> p \<rangle>\<leadsto>') = (\<langle> p \<rangle>\<leadsto>)"
    by (unfold isMessageFromTo'_def isMessageTo'_def isMessageFrom'_def isMessage'_def,
        auto simp add: isMessageFromTo_def isMessageTo_def isMessageFrom_def isMessage_def)

  have v_eq[simp]: "v' = v" by (intro ext, auto simp add: v'_def v_def)
  have v\<^sub>c_eq[simp]: "v\<^sub>c' = v\<^sub>c" by (intro ext, auto simp add: v\<^sub>c'_def v\<^sub>c_def)
  have isCommitted_eq[simp]: "isCommitted' = isCommitted" by (intro ext, auto simp add: isCommitted'_def isCommitted_def)
  have committedTo_eq[simp]: "committed\<^sub><' = committed\<^sub><" by (intro ext, auto simp add: committedTo'_def committedTo_def)
  have V_eq[simp]: "V' = V" using v\<^sub>c_eq V'_def V_def by blast
  have promised_eq[simp]: "promised' = promised" by (intro ext, auto simp add: promised'_def promised_def)
  have lastCommittedClusterStateBefore_eq[simp]: "lastCommittedClusterStateBefore' = lastCommittedClusterStateBefore"
    unfolding lastCommittedClusterStateBefore_def lastCommittedClusterStateBefore'_def v\<^sub>c_eq ..
  have prevAccepted_eq[simp]: "prevAccepted' = prevAccepted" by (intro ext, auto simp add: prevAccepted'_def prevAccepted_def)

  have property_simps[simp]:
    "\<And>n. currentNode (nodeState' n) = currentNode (nodeState n)"
    "\<And>n. currentTerm (nodeState' n) = currentTerm (nodeState n)"
    unfolding nodeState'_def by (auto simp add: nd' nd_def lastAcceptedTerm_def firstUncommittedSlot_def lastAcceptedValue_def)

  have updated_properties:
    "\<And>n. firstUncommittedSlot (nodeState' n) = (if n = n\<^sub>0 then i else firstUncommittedSlot (nodeState n)) "
    "\<And>n. publishPermitted (nodeState' n) = (publishPermitted (nodeState n) \<or> n = n\<^sub>0)"
    "\<And>n. publishVotes (nodeState' n) = (if n = n\<^sub>0 then {} else publishVotes (nodeState n))"
    "\<And>n. currentVotingNodes (nodeState' n) = (if n = n\<^sub>0 then conf else currentVotingNodes (nodeState n))"
    "\<And>n. joinVotes (nodeState' n) = (if n = n\<^sub>0 then {} else joinVotes (nodeState n))"
    "\<And>n. electionWon (nodeState' n) = (electionWon (nodeState n) \<and> n \<noteq> n\<^sub>0)"
    "\<And>n. currentVotingNodes (nodeState' n) = (if n = n\<^sub>0 then conf else currentVotingNodes (nodeState n))"
    "\<And>n. isQuorum (nodeState' n) = (if n = n\<^sub>0 then (\<lambda>q. q \<in> majorities conf) else isQuorum (nodeState n))"
    "\<And>n. currentClusterState (nodeState' n) = (if n = n\<^sub>0 then cs else currentClusterState (nodeState n))"
    unfolding nodeState'_def
    by (auto simp add: nd' nd_def isQuorum_def)

  have "\<And>n. lastAcceptedTerm (nodeState' n) = (if n = n\<^sub>0 then NO_TERM else lastAcceptedTerm (nodeState n))"
    using True unfolding lastAcceptedTerm_def updated_properties property_simps nd_def
    using not_le by (simp add: nodeState'_def nd')
  note updated_properties = updated_properties this

  show ?thesis
    apply (intro zenI)
                        apply (unfold messages' message_simps committedTo_eq V_eq v_eq
        lastCommittedClusterStateBefore_eq property_simps promised_eq prevAccepted_eq)
  proof -
    from finite_messages show "finite messages" .
    from Vote_future show "\<And>i i' s t t' a. s \<midarrow>\<langle> Vote i t a \<rangle>\<leadsto> \<Longrightarrow> i < i' \<Longrightarrow> t' < t \<Longrightarrow> \<not> s \<midarrow>\<langle> PublishResponse i' t' \<rangle>\<leadsto>".
    from Vote_None show "\<And>i s t t'. s \<midarrow>\<langle> Vote i t NO_TERM \<rangle>\<leadsto> \<Longrightarrow> t' < t \<Longrightarrow> \<not> s \<midarrow>\<langle> PublishResponse i t' \<rangle>\<leadsto>".
    from Vote_Some_lt show "\<And>i s t t'. s \<midarrow>\<langle> Vote i t (SomeTerm t') \<rangle>\<leadsto> \<Longrightarrow> t' < t".
    from Vote_Some_PublishResponse show "\<And>i s t t'. s \<midarrow>\<langle> Vote i t (SomeTerm t') \<rangle>\<leadsto> \<Longrightarrow> s \<midarrow>\<langle> PublishResponse i t' \<rangle>\<leadsto>".
    from Vote_Some_max show "\<And>i s t t' t''. s \<midarrow>\<langle> Vote i t (SomeTerm t') \<rangle>\<leadsto> \<Longrightarrow> t' < t'' \<Longrightarrow> t'' < t \<Longrightarrow> \<not> s \<midarrow>\<langle> PublishResponse i t'' \<rangle>\<leadsto>".
    from Vote_not_broadcast show "\<And>i t a d. \<langle> Vote i t a \<rangle>\<rightarrow> d \<Longrightarrow> d \<noteq> Broadcast".
    from Vote_unique_destination show "\<And>i' i s t a a' d d'. s \<midarrow>\<langle> Vote i t a \<rangle>\<rightarrow> d \<Longrightarrow> s \<midarrow>\<langle> Vote i' t a' \<rangle>\<rightarrow> d' \<Longrightarrow> d = d'".
    from currentNode_nodeState show "\<And>n. currentNode (nodeState n) = n" .
    from Vote_currentTerm show "\<And>n i t a. n \<midarrow>\<langle> Vote i t a \<rangle>\<leadsto> \<Longrightarrow> t \<le> currentTerm (nodeState n)".
    from Vote_slot_function show "\<And>n i i' t a a'. n \<midarrow>\<langle> Vote i t a \<rangle>\<leadsto> \<Longrightarrow> n \<midarrow>\<langle> Vote i' t a' \<rangle>\<leadsto> \<Longrightarrow> i = i'".
    from PublishRequest_committedTo show "\<And>i t x. \<langle> PublishRequest i t x \<rangle>\<leadsto> \<Longrightarrow> committed\<^sub>< i".
    from PublishRequest_quorum show "\<And>i s t x. s \<midarrow>\<langle> PublishRequest i t x \<rangle>\<leadsto> \<Longrightarrow> \<exists>q\<in>majorities (V i). (\<forall>n\<in>q. promised i n s t) \<and> (prevAccepted i t q = {} \<or> (\<exists>t'. v i t = v i t' \<and> maxTerm (prevAccepted i t q) \<le> t' \<and> \<langle> PublishResponse i t' \<rangle>\<leadsto> \<and> t' < t))".
    from PublishRequest_function show "\<And>i t x x'. \<langle> PublishRequest i t x \<rangle>\<leadsto> \<Longrightarrow> \<langle> PublishRequest i t x' \<rangle>\<leadsto> \<Longrightarrow> x = x'".
    from PublishResponse_PublishRequest show "\<And>i s t. s \<midarrow>\<langle> PublishResponse i t \<rangle>\<leadsto> \<Longrightarrow> \<exists>x. \<langle> PublishRequest i t x \<rangle>\<leadsto>".
    from ApplyCommit_quorum show "\<And>i t. \<langle> ApplyCommit i t \<rangle>\<leadsto> \<Longrightarrow> \<exists>q\<in>majorities (V i). \<forall>s\<in>q. s \<midarrow>\<langle> PublishResponse i t \<rangle>\<leadsto>".
    from CatchUpResponse_committedTo show "\<And>i conf cs. \<langle> CatchUpResponse i conf cs \<rangle>\<leadsto> \<Longrightarrow> committed\<^sub>< i".
    from CatchUpResponse_V show "\<And>i conf cs. \<langle> CatchUpResponse i conf cs \<rangle>\<leadsto> \<Longrightarrow> V i = conf".
    from CatchUpResponse_lastCommittedClusterStateBefore show "\<And>i conf cs. \<langle> CatchUpResponse i conf cs \<rangle>\<leadsto> \<Longrightarrow> lastCommittedClusterStateBefore i = cs".

    from committedTo_firstUncommittedSlot show "\<And>n. committed\<^sub>< (firstUncommittedSlot (nodeState' n))"
      unfolding updated_properties apply auto
      using CatchUpResponse_committedTo sent by blast

    from electionWon_isQuorum show "\<And>n. electionWon (nodeState' n) \<Longrightarrow> isQuorum (nodeState' n) (joinVotes (nodeState' n))"
      unfolding updated_properties apply auto done

    from joinVotes_max show "\<And>n n' a'. \<not> (\<exists>x. \<langle> PublishRequest (firstUncommittedSlot (nodeState' n)) (currentTerm (nodeState n)) x \<rangle>\<leadsto>) \<Longrightarrow> n' \<in> joinVotes (nodeState' n) \<Longrightarrow> n' \<midarrow>\<langle> Vote (firstUncommittedSlot (nodeState' n)) (currentTerm (nodeState n)) a' \<rangle>\<rightarrow> (OneNode n) \<Longrightarrow> a' \<le> lastAcceptedTerm (nodeState' n)"
      unfolding updated_properties apply auto done

    from publishVotes show "\<And>n n'. n' \<in> publishVotes (nodeState' n) \<Longrightarrow> n' \<midarrow>\<langle> PublishResponse (firstUncommittedSlot (nodeState' n)) (currentTerm (nodeState n)) \<rangle>\<leadsto>"
      unfolding updated_properties apply auto done

    from joinVotes show "\<And>n n'. n' \<in> joinVotes (nodeState' n) \<Longrightarrow> promised (firstUncommittedSlot (nodeState' n)) n' n (currentTerm (nodeState n))"
      unfolding updated_properties apply auto done

    fix n

    from firstUncommittedSlot_PublishRequest show "\<And>i t x. firstUncommittedSlot (nodeState' n) < i \<Longrightarrow> \<not> n \<midarrow>\<langle> PublishRequest i t x \<rangle>\<leadsto>"
      unfolding updated_properties using True nd_def by (cases "n = n\<^sub>0", auto)

    from PublishRequest_currentTerm show "\<And>t x. n \<midarrow>\<langle> PublishRequest (firstUncommittedSlot (nodeState' n)) t x \<rangle>\<leadsto> \<Longrightarrow> t \<le> currentTerm (nodeState n)"
      unfolding updated_properties apply (cases "n = n\<^sub>0", auto)
      using True firstUncommittedSlot_PublishRequest nd_def by blast

    from PublishRequest_publishPermitted_currentTerm show "\<And>t x. n \<midarrow>\<langle> PublishRequest (firstUncommittedSlot (nodeState' n)) t x \<rangle>\<leadsto> \<Longrightarrow> publishPermitted (nodeState' n) \<Longrightarrow> t < currentTerm (nodeState n)"
      unfolding updated_properties apply (cases "n = n\<^sub>0", auto)
      using True firstUncommittedSlot_PublishRequest nd_def by blast

    from currentClusterState_lastCommittedClusterStateBefore show "currentClusterState (nodeState' n) = lastCommittedClusterStateBefore (firstUncommittedSlot (nodeState' n))"
      unfolding updated_properties apply (cases "n = n\<^sub>0", auto)
      using CatchUpResponse_lastCommittedClusterStateBefore sent by blast

    from currentVotingNodes_firstUncommittedSlot show "\<And>n. currentVotingNodes (nodeState' n) = V (firstUncommittedSlot (nodeState' n))"
      unfolding updated_properties using CatchUpResponse_V sent by (cases "n = n\<^sub>0", auto)

    from firstUncommittedSlot_PublishResponse show "\<And>i t. firstUncommittedSlot (nodeState' n) < i \<Longrightarrow> \<not> n \<midarrow>\<langle> PublishResponse i t \<rangle>\<leadsto>" 
      unfolding updated_properties apply (cases "n = n\<^sub>0", auto)
      using True dual_order.strict_trans nd_def by blast

    from lastAcceptedTerm_None show "\<And>i t. lastAcceptedTerm (nodeState' n) = NO_TERM \<Longrightarrow> \<not> n \<midarrow>\<langle> PublishResponse (firstUncommittedSlot (nodeState' n)) t \<rangle>\<leadsto>"
      unfolding updated_properties apply (cases "n = n\<^sub>0", auto)
      using True firstUncommittedSlot_PublishResponse nd_def by blast

    from lastAcceptedTerm_Some_sent show "\<And>t. lastAcceptedTerm (nodeState' n) = SomeTerm t \<Longrightarrow> n \<midarrow>\<langle> PublishResponse (firstUncommittedSlot (nodeState' n)) t \<rangle>\<leadsto>"
      unfolding updated_properties by (cases "n = n\<^sub>0", auto)

    from lastAcceptedTerm_Some_max show "\<And>t t'. lastAcceptedTerm (nodeState' n) = SomeTerm t \<Longrightarrow> n \<midarrow>\<langle> PublishResponse (firstUncommittedSlot (nodeState' n)) t' \<rangle>\<leadsto> \<Longrightarrow> t' \<le> t" 
      unfolding updated_properties by (cases "n = n\<^sub>0", auto)

    from lastAcceptedTerm_Some_value show "\<And>t. lastAcceptedTerm (nodeState' n) = SomeTerm t \<Longrightarrow> \<langle> PublishRequest (firstUncommittedSlot (nodeState' n)) t (lastAcceptedValue (nodeState' n)) \<rangle>\<leadsto>" 
      unfolding updated_properties lastAcceptedValue_def by (cases "n = n\<^sub>0", auto simp add: nodeState'_def)

    from lastAcceptedTerm_Some_currentTerm show "\<And>t. lastAcceptedTerm (nodeState' n) = SomeTerm t \<Longrightarrow> t \<le> currentTerm (nodeState n)" 
      unfolding updated_properties by (cases "n = n\<^sub>0", auto)
  qed
qed

lemma (in zenStep) handleDiscardJoinVotes_invariants:
  assumes nd': "nd' = handleDiscardJoinVotes nd"
  assumes messages': "messages' = messages"
  shows "zen messages' nodeState'"
proof -
  have message_simps[simp]:
    "\<And>s p d. (s \<midarrow>\<langle> p \<rangle>\<rightarrow>' d) = (s \<midarrow>\<langle> p \<rangle>\<rightarrow> d)"
    "\<And>p d. (\<langle> p \<rangle>\<rightarrow>' d) = (\<langle> p \<rangle>\<rightarrow> d)"
    "\<And>s p. (s \<midarrow>\<langle> p \<rangle>\<leadsto>') = (s \<midarrow>\<langle> p \<rangle>\<leadsto>)"
    "\<And>p. (\<langle> p \<rangle>\<leadsto>') = (\<langle> p \<rangle>\<leadsto>)"
    by (unfold isMessageFromTo'_def isMessageTo'_def isMessageFrom'_def isMessage'_def,
        auto simp add: messages' isMessageFromTo_def isMessageTo_def isMessageFrom_def isMessage_def)

  have property_simps[simp]:
    "\<And>n. currentNode (nodeState' n) = currentNode (nodeState n)"
    "\<And>n. firstUncommittedSlot (nodeState' n) = firstUncommittedSlot (nodeState n)"
    "\<And>n. currentVotingNodes (nodeState' n) = currentVotingNodes (nodeState n)"
    "\<And>n q. isQuorum (nodeState' n) q = isQuorum (nodeState n) q"
    "\<And>n. lastAcceptedTerm (nodeState' n) = lastAcceptedTerm (nodeState n)"
    "\<And>n. lastAcceptedValue (nodeState' n) = lastAcceptedValue (nodeState n)"
    "\<And>n. currentTerm (nodeState' n) = currentTerm (nodeState n)"
    "\<And>n. currentClusterState (nodeState' n) = currentClusterState (nodeState n)"
    "\<And>n. publishPermitted (nodeState' n) = publishPermitted (nodeState n)"
    "\<And>n. publishVotes (nodeState' n) = publishVotes (nodeState n)"
    by (unfold nodeState'_def, auto simp add: nd_def isQuorum_def nd' handleDiscardJoinVotes_def Let_def
        lastAcceptedValue_def lastAcceptedTerm_def)

  have updated_properties:
    "\<And>n. joinVotes (nodeState' n) = (if n = n\<^sub>0 then {} else joinVotes (nodeState n))"
    "\<And>n. electionWon (nodeState' n) = (electionWon (nodeState n) \<and> n \<noteq> n\<^sub>0)"
    by (unfold nodeState'_def, auto simp add: nd' nd_def handleDiscardJoinVotes_def)

  have v_eq[simp]: "v' = v" by (intro ext, auto simp add: v'_def v_def)
  have v\<^sub>c_eq[simp]: "v\<^sub>c' = v\<^sub>c" by (intro ext, auto simp add: v\<^sub>c'_def v\<^sub>c_def)
  have isCommitted_eq[simp]: "isCommitted' = isCommitted" by (intro ext, auto simp add: isCommitted'_def isCommitted_def)
  have committedTo_eq[simp]: "committed\<^sub><' = committed\<^sub><" by (intro ext, auto simp add: committedTo'_def committedTo_def)
  have V_eq[simp]: "V' = V" using v\<^sub>c_eq V'_def V_def by blast
  have promised_eq[simp]: "promised' = promised" by (intro ext, auto simp add: promised'_def promised_def)
  have lastCommittedClusterStateBefore_eq[simp]: "lastCommittedClusterStateBefore' = lastCommittedClusterStateBefore"
    unfolding lastCommittedClusterStateBefore_def lastCommittedClusterStateBefore'_def v\<^sub>c_eq ..
  have prevAccepted_eq[simp]: "prevAccepted' = prevAccepted" by (intro ext, auto simp add: prevAccepted'_def prevAccepted_def)

  show ?thesis
    apply (intro zenI)
                        apply (unfold message_simps committedTo_eq V_eq v_eq
        lastCommittedClusterStateBefore_eq property_simps promised_eq prevAccepted_eq)
  proof -
    from finite_messages show "finite messages'" by (simp add: messages')
    from Vote_future show "\<And>i i' s t t' a. s \<midarrow>\<langle> Vote i t a \<rangle>\<leadsto> \<Longrightarrow> i < i' \<Longrightarrow> t' < t \<Longrightarrow> \<not> s \<midarrow>\<langle> PublishResponse i' t' \<rangle>\<leadsto>".
    from Vote_None show "\<And>i s t t'. s \<midarrow>\<langle> Vote i t NO_TERM \<rangle>\<leadsto> \<Longrightarrow> t' < t \<Longrightarrow> \<not> s \<midarrow>\<langle> PublishResponse i t' \<rangle>\<leadsto>".
    from Vote_Some_lt show "\<And>i s t t'. s \<midarrow>\<langle> Vote i t (SomeTerm t') \<rangle>\<leadsto> \<Longrightarrow> t' < t".
    from Vote_Some_PublishResponse show "\<And>i s t t'. s \<midarrow>\<langle> Vote i t (SomeTerm t') \<rangle>\<leadsto> \<Longrightarrow> s \<midarrow>\<langle> PublishResponse i t' \<rangle>\<leadsto>".
    from Vote_Some_max show "\<And>i s t t' t''. s \<midarrow>\<langle> Vote i t (SomeTerm t') \<rangle>\<leadsto> \<Longrightarrow> t' < t'' \<Longrightarrow> t'' < t \<Longrightarrow> \<not> s \<midarrow>\<langle> PublishResponse i t'' \<rangle>\<leadsto>".
    from Vote_not_broadcast show "\<And>i t a d. \<langle> Vote i t a \<rangle>\<rightarrow> d \<Longrightarrow> d \<noteq> Broadcast".
    from Vote_unique_destination show "\<And>i' i s t a a' d d'. s \<midarrow>\<langle> Vote i t a \<rangle>\<rightarrow> d \<Longrightarrow> s \<midarrow>\<langle> Vote i' t a' \<rangle>\<rightarrow> d' \<Longrightarrow> d = d'".
    from currentNode_nodeState show "\<And>n. currentNode (nodeState n) = n" .
    from committedTo_firstUncommittedSlot show "\<And>n. committed\<^sub>< (firstUncommittedSlot (nodeState n))" .
    from firstUncommittedSlot_PublishResponse show "\<And>n i t. firstUncommittedSlot (nodeState n) < i \<Longrightarrow> \<not> n \<midarrow>\<langle> PublishResponse i t \<rangle>\<leadsto>" .
    from lastAcceptedTerm_None show "\<And>n i t. lastAcceptedTerm (nodeState n) = NO_TERM \<Longrightarrow> \<not> n \<midarrow>\<langle> PublishResponse (firstUncommittedSlot (nodeState n)) t \<rangle>\<leadsto>".
    from lastAcceptedTerm_Some_sent show "\<And>n t. lastAcceptedTerm (nodeState n) = SomeTerm t \<Longrightarrow> n \<midarrow>\<langle> PublishResponse (firstUncommittedSlot (nodeState n)) t \<rangle>\<leadsto>" .
    from lastAcceptedTerm_Some_max show "\<And>n t t'. lastAcceptedTerm (nodeState n) = SomeTerm t \<Longrightarrow> n \<midarrow>\<langle> PublishResponse (firstUncommittedSlot (nodeState n)) t' \<rangle>\<leadsto> \<Longrightarrow> t' \<le> t" .
    from lastAcceptedTerm_Some_value show "\<And>n t. lastAcceptedTerm (nodeState n) = SomeTerm t \<Longrightarrow> \<langle> PublishRequest (firstUncommittedSlot (nodeState n)) t (lastAcceptedValue (nodeState n)) \<rangle>\<leadsto>" .
    from Vote_currentTerm show "\<And>n i t a. n \<midarrow>\<langle> Vote i t a \<rangle>\<leadsto> \<Longrightarrow> t \<le> currentTerm (nodeState n)".
    from Vote_slot_function show "\<And>n i i' t a a'. n \<midarrow>\<langle> Vote i t a \<rangle>\<leadsto> \<Longrightarrow> n \<midarrow>\<langle> Vote i' t a' \<rangle>\<leadsto> \<Longrightarrow> i = i'".
    from currentClusterState_lastCommittedClusterStateBefore show "\<And>n. currentClusterState (nodeState n) = lastCommittedClusterStateBefore (firstUncommittedSlot (nodeState n))".
    from PublishRequest_committedTo show "\<And>i t x. \<langle> PublishRequest i t x \<rangle>\<leadsto> \<Longrightarrow> committed\<^sub>< i".
    from PublishRequest_quorum show "\<And>i s t x. s \<midarrow>\<langle> PublishRequest i t x \<rangle>\<leadsto> \<Longrightarrow> \<exists>q\<in>majorities (V i). (\<forall>n\<in>q. promised i n s t) \<and> (prevAccepted i t q = {} \<or> (\<exists>t'. v i t = v i t' \<and> maxTerm (prevAccepted i t q) \<le> t' \<and> \<langle> PublishResponse i t' \<rangle>\<leadsto> \<and> t' < t))".
    from PublishRequest_function show "\<And>i t x x'. \<langle> PublishRequest i t x \<rangle>\<leadsto> \<Longrightarrow> \<langle> PublishRequest i t x' \<rangle>\<leadsto> \<Longrightarrow> x = x'".
    from PublishResponse_PublishRequest show "\<And>i s t. s \<midarrow>\<langle> PublishResponse i t \<rangle>\<leadsto> \<Longrightarrow> \<exists>x. \<langle> PublishRequest i t x \<rangle>\<leadsto>".
    from ApplyCommit_quorum show "\<And>i t. \<langle> ApplyCommit i t \<rangle>\<leadsto> \<Longrightarrow> \<exists>q\<in>majorities (V i). \<forall>s\<in>q. s \<midarrow>\<langle> PublishResponse i t \<rangle>\<leadsto>".
    from currentVotingNodes_firstUncommittedSlot show "\<And>n. currentVotingNodes (nodeState n) = V (firstUncommittedSlot (nodeState n))".
    from firstUncommittedSlot_PublishRequest show "\<And>i n t x. firstUncommittedSlot (nodeState n) < i \<Longrightarrow> \<not> n \<midarrow>\<langle> PublishRequest i t x \<rangle>\<leadsto>".
    from PublishRequest_currentTerm show "\<And>n t x. n \<midarrow>\<langle> PublishRequest (firstUncommittedSlot (nodeState n)) t x \<rangle>\<leadsto> \<Longrightarrow> t \<le> currentTerm (nodeState n)".
    from CatchUpResponse_committedTo show "\<And>i conf cs. \<langle> CatchUpResponse i conf cs \<rangle>\<leadsto> \<Longrightarrow> committed\<^sub>< i".
    from CatchUpResponse_V show "\<And>i conf cs. \<langle> CatchUpResponse i conf cs \<rangle>\<leadsto> \<Longrightarrow> V i = conf".
    from CatchUpResponse_lastCommittedClusterStateBefore show "\<And>i conf cs. \<langle> CatchUpResponse i conf cs \<rangle>\<leadsto> \<Longrightarrow> lastCommittedClusterStateBefore i = cs".
    from lastAcceptedTerm_Some_currentTerm show "\<And>n t. lastAcceptedTerm (nodeState n) = SomeTerm t \<Longrightarrow> t \<le> currentTerm (nodeState n)".
    from PublishRequest_publishPermitted_currentTerm show "\<And>n t x. n \<midarrow>\<langle> PublishRequest (firstUncommittedSlot (nodeState n)) t x \<rangle>\<leadsto> \<Longrightarrow> publishPermitted (nodeState n) \<Longrightarrow> t < currentTerm (nodeState n)".
    from publishVotes show "\<And>n n'. n' \<in> publishVotes (nodeState n) \<Longrightarrow> n' \<midarrow>\<langle> PublishResponse (firstUncommittedSlot (nodeState n)) (currentTerm (nodeState n)) \<rangle>\<leadsto>".

    from electionWon_isQuorum show "\<And>n. electionWon (nodeState' n) \<Longrightarrow> isQuorum (nodeState n) (joinVotes (nodeState' n))"
      unfolding updated_properties by simp

    fix n

    from joinVotes show "\<And>n'. n' \<in> joinVotes (nodeState' n) \<Longrightarrow> promised (firstUncommittedSlot (nodeState n)) n' n (currentTerm (nodeState n))"
      unfolding updated_properties by (cases "n = n\<^sub>0", simp_all)
    from joinVotes_max show "\<And>n' a'. \<not> (\<exists>x. \<langle> PublishRequest (firstUncommittedSlot (nodeState n)) (currentTerm (nodeState n)) x \<rangle>\<leadsto>) \<Longrightarrow> n' \<in> joinVotes (nodeState' n) \<Longrightarrow> n' \<midarrow>\<langle> Vote (firstUncommittedSlot (nodeState n)) (currentTerm (nodeState n)) a' \<rangle>\<rightarrow> (OneNode n) \<Longrightarrow> a' \<le> lastAcceptedTerm (nodeState n)"
      unfolding updated_properties by (cases "n = n\<^sub>0", simp_all)
  qed
qed

lemma (in zenStep) handleReboot_invariants:
  assumes nd': "nd' = handleReboot nd"
  assumes messages': "messages' = messages"
  shows "zen messages' nodeState'"
proof -
  have message_simps[simp]:
    "\<And>s p d. (s \<midarrow>\<langle> p \<rangle>\<rightarrow>' d) = (s \<midarrow>\<langle> p \<rangle>\<rightarrow> d)"
    "\<And>p d. (\<langle> p \<rangle>\<rightarrow>' d) = (\<langle> p \<rangle>\<rightarrow> d)"
    "\<And>s p. (s \<midarrow>\<langle> p \<rangle>\<leadsto>') = (s \<midarrow>\<langle> p \<rangle>\<leadsto>)"
    "\<And>p. (\<langle> p \<rangle>\<leadsto>') = (\<langle> p \<rangle>\<leadsto>)"
    by (unfold isMessageFromTo'_def isMessageTo'_def isMessageFrom'_def isMessage'_def,
        auto simp add: messages' isMessageFromTo_def isMessageTo_def isMessageFrom_def isMessage_def)

  have property_simps[simp]:
    "\<And>n. currentNode (nodeState' n) = currentNode (nodeState n)"
    "\<And>n. firstUncommittedSlot (nodeState' n) = firstUncommittedSlot (nodeState n)"
    "\<And>n. currentVotingNodes (nodeState' n) = currentVotingNodes (nodeState n)"
    "\<And>n q. isQuorum (nodeState' n) q = isQuorum (nodeState n) q"
    "\<And>n. lastAcceptedTerm (nodeState' n) = lastAcceptedTerm (nodeState n)"
    "\<And>n. lastAcceptedValue (nodeState' n) = lastAcceptedValue (nodeState n)"
    "\<And>n. currentTerm (nodeState' n) = currentTerm (nodeState n)"
    "\<And>n. currentClusterState (nodeState' n) = currentClusterState (nodeState n)"
    by (unfold nodeState'_def, auto simp add: nd_def isQuorum_def nd' handleReboot_def Let_def
        lastAcceptedValue_def lastAcceptedTerm_def)

  have updated_properties:
    "\<And>n. publishPermitted (nodeState' n) = (publishPermitted (nodeState n) \<and> n \<noteq> n\<^sub>0)"
    "\<And>n. joinVotes (nodeState' n) = (if n = n\<^sub>0 then {} else joinVotes (nodeState n))"
    "\<And>n. electionWon (nodeState' n) = (electionWon (nodeState n) \<and> n \<noteq> n\<^sub>0)"
    "\<And>n. publishVotes (nodeState' n) = (if n = n\<^sub>0 then {} else publishVotes (nodeState n))"
    by (unfold nodeState'_def, auto simp add: nd' nd_def handleReboot_def)

  have v_eq[simp]: "v' = v" by (intro ext, auto simp add: v'_def v_def)
  have v\<^sub>c_eq[simp]: "v\<^sub>c' = v\<^sub>c" by (intro ext, auto simp add: v\<^sub>c'_def v\<^sub>c_def)
  have isCommitted_eq[simp]: "isCommitted' = isCommitted" by (intro ext, auto simp add: isCommitted'_def isCommitted_def)
  have committedTo_eq[simp]: "committed\<^sub><' = committed\<^sub><" by (intro ext, auto simp add: committedTo'_def committedTo_def)
  have V_eq[simp]: "V' = V" using v\<^sub>c_eq V'_def V_def by blast
  have promised_eq[simp]: "promised' = promised" by (intro ext, auto simp add: promised'_def promised_def)
  have lastCommittedClusterStateBefore_eq[simp]: "lastCommittedClusterStateBefore' = lastCommittedClusterStateBefore"
    unfolding lastCommittedClusterStateBefore_def lastCommittedClusterStateBefore'_def v\<^sub>c_eq ..
  have prevAccepted_eq[simp]: "prevAccepted' = prevAccepted" by (intro ext, auto simp add: prevAccepted'_def prevAccepted_def)

  show ?thesis
    apply (intro zenI)
                        apply (unfold message_simps committedTo_eq V_eq v_eq
        lastCommittedClusterStateBefore_eq property_simps promised_eq prevAccepted_eq)
  proof -
    from finite_messages show "finite messages'" by (simp add: messages')
    from Vote_future show "\<And>i i' s t t' a. s \<midarrow>\<langle> Vote i t a \<rangle>\<leadsto> \<Longrightarrow> i < i' \<Longrightarrow> t' < t \<Longrightarrow> \<not> s \<midarrow>\<langle> PublishResponse i' t' \<rangle>\<leadsto>".
    from Vote_None show "\<And>i s t t'. s \<midarrow>\<langle> Vote i t NO_TERM \<rangle>\<leadsto> \<Longrightarrow> t' < t \<Longrightarrow> \<not> s \<midarrow>\<langle> PublishResponse i t' \<rangle>\<leadsto>".
    from Vote_Some_lt show "\<And>i s t t'. s \<midarrow>\<langle> Vote i t (SomeTerm t') \<rangle>\<leadsto> \<Longrightarrow> t' < t".
    from Vote_Some_PublishResponse show "\<And>i s t t'. s \<midarrow>\<langle> Vote i t (SomeTerm t') \<rangle>\<leadsto> \<Longrightarrow> s \<midarrow>\<langle> PublishResponse i t' \<rangle>\<leadsto>".
    from Vote_Some_max show "\<And>i s t t' t''. s \<midarrow>\<langle> Vote i t (SomeTerm t') \<rangle>\<leadsto> \<Longrightarrow> t' < t'' \<Longrightarrow> t'' < t \<Longrightarrow> \<not> s \<midarrow>\<langle> PublishResponse i t'' \<rangle>\<leadsto>".
    from Vote_not_broadcast show "\<And>i t a d. \<langle> Vote i t a \<rangle>\<rightarrow> d \<Longrightarrow> d \<noteq> Broadcast".
    from Vote_unique_destination show "\<And>i' i s t a a' d d'. s \<midarrow>\<langle> Vote i t a \<rangle>\<rightarrow> d \<Longrightarrow> s \<midarrow>\<langle> Vote i' t a' \<rangle>\<rightarrow> d' \<Longrightarrow> d = d'".
    from currentNode_nodeState show "\<And>n. currentNode (nodeState n) = n" .
    from committedTo_firstUncommittedSlot show "\<And>n. committed\<^sub>< (firstUncommittedSlot (nodeState n))" .
    from firstUncommittedSlot_PublishResponse show "\<And>n i t. firstUncommittedSlot (nodeState n) < i \<Longrightarrow> \<not> n \<midarrow>\<langle> PublishResponse i t \<rangle>\<leadsto>" .
    from lastAcceptedTerm_None show "\<And>n i t. lastAcceptedTerm (nodeState n) = NO_TERM \<Longrightarrow> \<not> n \<midarrow>\<langle> PublishResponse (firstUncommittedSlot (nodeState n)) t \<rangle>\<leadsto>".
    from lastAcceptedTerm_Some_sent show "\<And>n t. lastAcceptedTerm (nodeState n) = SomeTerm t \<Longrightarrow> n \<midarrow>\<langle> PublishResponse (firstUncommittedSlot (nodeState n)) t \<rangle>\<leadsto>" .
    from lastAcceptedTerm_Some_max show "\<And>n t t'. lastAcceptedTerm (nodeState n) = SomeTerm t \<Longrightarrow> n \<midarrow>\<langle> PublishResponse (firstUncommittedSlot (nodeState n)) t' \<rangle>\<leadsto> \<Longrightarrow> t' \<le> t" .
    from lastAcceptedTerm_Some_value show "\<And>n t. lastAcceptedTerm (nodeState n) = SomeTerm t \<Longrightarrow> \<langle> PublishRequest (firstUncommittedSlot (nodeState n)) t (lastAcceptedValue (nodeState n)) \<rangle>\<leadsto>" .
    from Vote_currentTerm show "\<And>n i t a. n \<midarrow>\<langle> Vote i t a \<rangle>\<leadsto> \<Longrightarrow> t \<le> currentTerm (nodeState n)".
    from Vote_slot_function show "\<And>n i i' t a a'. n \<midarrow>\<langle> Vote i t a \<rangle>\<leadsto> \<Longrightarrow> n \<midarrow>\<langle> Vote i' t a' \<rangle>\<leadsto> \<Longrightarrow> i = i'".
    from currentClusterState_lastCommittedClusterStateBefore show "\<And>n. currentClusterState (nodeState n) = lastCommittedClusterStateBefore (firstUncommittedSlot (nodeState n))".
    from PublishRequest_committedTo show "\<And>i t x. \<langle> PublishRequest i t x \<rangle>\<leadsto> \<Longrightarrow> committed\<^sub>< i".
    from PublishRequest_quorum show "\<And>i s t x. s \<midarrow>\<langle> PublishRequest i t x \<rangle>\<leadsto> \<Longrightarrow> \<exists>q\<in>majorities (V i). (\<forall>n\<in>q. promised i n s t) \<and> (prevAccepted i t q = {} \<or> (\<exists>t'. v i t = v i t' \<and> maxTerm (prevAccepted i t q) \<le> t' \<and> \<langle> PublishResponse i t' \<rangle>\<leadsto> \<and> t' < t))".
    from PublishRequest_function show "\<And>i t x x'. \<langle> PublishRequest i t x \<rangle>\<leadsto> \<Longrightarrow> \<langle> PublishRequest i t x' \<rangle>\<leadsto> \<Longrightarrow> x = x'".
    from PublishResponse_PublishRequest show "\<And>i s t. s \<midarrow>\<langle> PublishResponse i t \<rangle>\<leadsto> \<Longrightarrow> \<exists>x. \<langle> PublishRequest i t x \<rangle>\<leadsto>".
    from ApplyCommit_quorum show "\<And>i t. \<langle> ApplyCommit i t \<rangle>\<leadsto> \<Longrightarrow> \<exists>q\<in>majorities (V i). \<forall>s\<in>q. s \<midarrow>\<langle> PublishResponse i t \<rangle>\<leadsto>".
    from currentVotingNodes_firstUncommittedSlot show "\<And>n. currentVotingNodes (nodeState n) = V (firstUncommittedSlot (nodeState n))".
    from firstUncommittedSlot_PublishRequest show "\<And>i n t x. firstUncommittedSlot (nodeState n) < i \<Longrightarrow> \<not> n \<midarrow>\<langle> PublishRequest i t x \<rangle>\<leadsto>".
    from PublishRequest_currentTerm show "\<And>n t x. n \<midarrow>\<langle> PublishRequest (firstUncommittedSlot (nodeState n)) t x \<rangle>\<leadsto> \<Longrightarrow> t \<le> currentTerm (nodeState n)".
    from CatchUpResponse_committedTo show "\<And>i conf cs. \<langle> CatchUpResponse i conf cs \<rangle>\<leadsto> \<Longrightarrow> committed\<^sub>< i".
    from CatchUpResponse_V show "\<And>i conf cs. \<langle> CatchUpResponse i conf cs \<rangle>\<leadsto> \<Longrightarrow> V i = conf".
    from CatchUpResponse_lastCommittedClusterStateBefore show "\<And>i conf cs. \<langle> CatchUpResponse i conf cs \<rangle>\<leadsto> \<Longrightarrow> lastCommittedClusterStateBefore i = cs".
    from lastAcceptedTerm_Some_currentTerm show "\<And>n t. lastAcceptedTerm (nodeState n) = SomeTerm t \<Longrightarrow> t \<le> currentTerm (nodeState n)".

    from electionWon_isQuorum show "\<And>n. electionWon (nodeState' n) \<Longrightarrow> isQuorum (nodeState n) (joinVotes (nodeState' n))"
      unfolding updated_properties by simp
    from PublishRequest_publishPermitted_currentTerm show "\<And>n t x. n \<midarrow>\<langle> PublishRequest (firstUncommittedSlot (nodeState n)) t x \<rangle>\<leadsto> \<Longrightarrow> publishPermitted (nodeState' n) \<Longrightarrow> t < currentTerm (nodeState n)"
      unfolding updated_properties by simp

    fix n

    from joinVotes show "\<And>n'. n' \<in> joinVotes (nodeState' n) \<Longrightarrow> promised (firstUncommittedSlot (nodeState n)) n' n (currentTerm (nodeState n))"
      unfolding updated_properties by (cases "n = n\<^sub>0", simp_all)
    from publishVotes show "\<And>n'. n' \<in> publishVotes (nodeState' n) \<Longrightarrow> n' \<midarrow>\<langle> PublishResponse (firstUncommittedSlot (nodeState n)) (currentTerm (nodeState n)) \<rangle>\<leadsto>"
      unfolding updated_properties by (cases "n = n\<^sub>0", simp_all)
    from joinVotes_max show "\<And>n' a'. \<not> (\<exists>x. \<langle> PublishRequest (firstUncommittedSlot (nodeState n)) (currentTerm (nodeState n)) x \<rangle>\<leadsto>) \<Longrightarrow> n' \<in> joinVotes (nodeState' n) \<Longrightarrow> n' \<midarrow>\<langle> Vote (firstUncommittedSlot (nodeState n)) (currentTerm (nodeState n)) a' \<rangle>\<rightarrow> (OneNode n) \<Longrightarrow> a' \<le> lastAcceptedTerm (nodeState n)"
      unfolding updated_properties by (cases "n = n\<^sub>0", simp_all)
  qed
qed

fun insertOption :: "RoutedMessage option \<Rightarrow> RoutedMessage set \<Rightarrow> RoutedMessage set"
  where
    "insertOption None = id"
  | "insertOption (Some m) = insert m"

lemma currentNode_ensureCurrentTerm[simp]: "currentNode (ensureCurrentTerm t nd) = currentNode nd"
  by (auto simp add: ensureCurrentTerm_def)

lemma currentNode_publishValue[simp]: "currentNode (fst (publishValue x nd)) = currentNode nd"
  by (auto simp add: publishValue_def)

lemma currentNode_addElectionVote[simp]: "currentNode (addElectionVote s i a nd) = currentNode nd"
  by (auto simp add: addElectionVote_def Let_def)

lemma currentNode_handleVote[simp]: "currentNode (fst (handleVote s i t a nd)) = currentNode nd"
  by (auto simp add: handleVote_def Let_def)

text \<open>\pagebreak\<close>

lemma initial_state_satisfies_invariants:
  shows "zen {} initialNodeState"
  by (unfold_locales, simp_all add: initialNodeState_def isQuorum_def
      lastAcceptedTerm_def lastAcceptedValue_def)

lemma (in zen) invariants_preserved_by_ProcessMessage:
  fixes n\<^sub>0
  assumes "m \<in> messages"
  defines "nd \<equiv> nodeState n\<^sub>0"
  defines "result \<equiv> ProcessMessage nd m"
  defines "nodeState' \<equiv> \<lambda>n. if n = n\<^sub>0 then (fst result) else nodeState n"
  defines "messages' \<equiv> insertOption (snd result) messages"
  shows "zen messages' nodeState'"
proof -
  {
    assume r: "result = (nd, None)"
    from r have "nodeState' = nodeState"
      by (auto simp add: nodeState'_def nd_def)
    moreover from r have "messages' = messages" by (simp add: messages'_def)
    ultimately have "zen messages' nodeState'"
      using zen_axioms by blast
  }
  note noop = this

  from `m \<in> messages`
  have m: "(sender m) \<midarrow>\<langle> payload m \<rangle>\<rightarrow> (destination m)"
    by (cases m, auto simp add: isMessageFromTo_def)

  have currentNode[simp]: "currentNode nd = n\<^sub>0" "\<And>n. currentNode (nodeState n) = n"
    by (simp_all add: nd_def currentNode_nodeState)

  have zenStep: "zenStep messages nodeState messages' nodeState' n\<^sub>0"
  proof (intro_locales, intro zenStep_axioms.intro)
    show "messages \<subseteq> messages'"
      by (cases "snd result", auto simp add: messages'_def)
  qed (simp add: nodeState'_def)

  have [simp]: "nodeState n\<^sub>0 = nd" by (simp add: nd_def)

  define broadcast' :: "(NodeData * Message option) \<Rightarrow> (NodeData * RoutedMessage option)" where
    "\<And>p. broadcast' p \<equiv> case p of
            (nd, Some m') \<Rightarrow> (nd, Some \<lparr>sender = currentNode nd,
                                   destination = Broadcast,
                                   payload = m' \<rparr>)
            | (nd, None) \<Rightarrow> (nd, None)"

  define respond' :: "(NodeData * Message option) \<Rightarrow> (NodeData * RoutedMessage option)" where
    "\<And>p. respond' p \<equiv> case p of
            (nd, Some m') \<Rightarrow> (nd, Some \<lparr>sender = currentNode nd,
                                   destination = OneNode (sender m),
                                   payload = m' \<rparr>)
            | (nd, None) \<Rightarrow> (nd, None)"

  have fst_broadcast[simp]: "\<And>p. fst (broadcast' p) = fst p"
    unfolding broadcast'_def by (simp add: case_prod_unfold option.case_eq_if)

  have fst_respond[simp]: "\<And>p. fst (respond' p) = fst p"
    unfolding respond'_def by (simp add: case_prod_unfold option.case_eq_if)

  show ?thesis
  proof (cases "destination m = Broadcast \<or> destination m = OneNode (currentNode nd)")
    case False
    hence "result = (nd, None)"
      unfolding result_def ProcessMessage_def Let_def by simp
    thus ?thesis by (intro noop)
  next
    case dest_ok: True
    have dest_True: "destination m \<in> {Broadcast, OneNode (currentNode nd)} = True"
      using dest_ok by simp
    show ?thesis
    proof (cases "payload m")
      case (StartJoin t)

      have result: "result = respond' (handleStartJoin t nd)"
        unfolding result_def respond'_def ProcessMessage_def dest_True StartJoin by auto

      have currentNode_eq: "currentNode (nodeState' n\<^sub>0) = currentNode (nodeState n\<^sub>0)"
        unfolding nodeState'_def result by (auto simp add: handleStartJoin_def)

      show ?thesis
      proof (intro zenStep.handleStartJoin_invariants [OF zenStep])
        show "nodeState' n\<^sub>0 = fst (handleStartJoin t (nodeState n\<^sub>0))"
          by (simp add: result nodeState'_def)

        from currentNode_eq
        show "messages' = (case snd (handleStartJoin t (nodeState n\<^sub>0)) of None \<Rightarrow> messages | Some m' \<Rightarrow> insert \<lparr>sender = n\<^sub>0, destination = OneNode (sender m), payload = m'\<rparr> messages)"
          unfolding messages'_def result respond'_def nodeState'_def by (cases "handleStartJoin t nd", cases "snd (handleStartJoin t nd)", auto)

        from m show "\<exists>d. \<lparr>sender = sender m, destination = d, payload = StartJoin t\<rparr> \<in> messages"
          by (auto simp add: isMessageFromTo_def StartJoin)
      qed
    next
      case (Vote i t a)

      from Vote_not_broadcast m Vote dest_ok
      have dest_m: "destination m = OneNode n\<^sub>0"
        apply (cases "destination m")
        using isMessageTo_def apply fastforce
        by auto

      from Vote_not_broadcast m Vote dest_ok
      have m: "(sender m) \<midarrow>\<langle> Vote i t a \<rangle>\<rightarrow> (OneNode n\<^sub>0)"
        apply (cases "destination m")
        using isMessageTo_def apply fastforce
        by auto

      have result: "result = broadcast' (handleVote (sender m) i t a nd)"
        unfolding result_def ProcessMessage_def Vote dest_True broadcast'_def by simp

      have currentNode_eq: "currentNode (nodeState' n\<^sub>0) = currentNode (nodeState n\<^sub>0)"
        unfolding nodeState'_def result by simp

      show ?thesis
      proof (intro zenStep.handleVote_invariants [OF zenStep])
        show "nodeState' n\<^sub>0 = fst (handleVote (sender m) i t a (nodeState n\<^sub>0))"
          by (simp add: result nodeState'_def)

        from currentNode_eq
        show "messages' = (case snd (handleVote (sender m) i t a (nodeState n\<^sub>0)) of None \<Rightarrow> messages | Some m \<Rightarrow> insert \<lparr>sender = n\<^sub>0, destination = Broadcast, payload = m\<rparr> messages)"
          unfolding messages'_def result broadcast'_def nodeState'_def by (cases "handleVote (sender m) i t a nd", cases "snd (handleVote (sender m) i t a nd)", auto)

        from m
        show "\<lparr>sender = sender m, destination = OneNode n\<^sub>0, payload = Vote i t a\<rparr> \<in> messages"
          by (auto simp add: Vote isMessageFromTo_def)
      qed

    next
      case (ClientValue x)

      have result: "result = broadcast' (handleClientValue x nd)"
        unfolding result_def ProcessMessage_def ClientValue dest_True broadcast'_def by simp

      have currentNode_eq: "currentNode (nodeState' n\<^sub>0) = currentNode (nodeState n\<^sub>0)"
        unfolding nodeState'_def result by (simp add: handleClientValue_def)

      show ?thesis
      proof (intro zenStep.handleClientValue_invariants [OF zenStep])
        show "nodeState' n\<^sub>0 = fst (handleClientValue x (nodeState n\<^sub>0))"
          by (simp add: result nodeState'_def)

        from currentNode_eq
        show "messages' = (case snd (handleClientValue x (nodeState n\<^sub>0)) of None \<Rightarrow> messages | Some m \<Rightarrow> insert \<lparr>sender = n\<^sub>0, destination = Broadcast, payload = m\<rparr> messages)"
          unfolding messages'_def result broadcast'_def nodeState'_def by (cases "handleClientValue x (nodeState n\<^sub>0)", cases "snd (handleClientValue x (nodeState n\<^sub>0))", auto)
      qed

    next
      case (PublishRequest i t x)

      have result: "result = respond' (handlePublishRequest i t x nd)"
        unfolding result_def ProcessMessage_def PublishRequest dest_True by (simp add: respond'_def)

      have currentNode_eq: "currentNode (nodeState' n\<^sub>0) = currentNode (nodeState n\<^sub>0)"
        unfolding nodeState'_def result by (simp add: handlePublishRequest_def)

      show ?thesis
      proof (intro zenStep.handlePublishRequest_invariants [OF zenStep])
        show "nodeState' n\<^sub>0 = fst (handlePublishRequest i t x (nodeState n\<^sub>0))"
          by (simp add: nodeState'_def result)

        from currentNode_eq
        show "messages' = (case snd (handlePublishRequest i t x (nodeState n\<^sub>0)) of None \<Rightarrow> messages | Some m' \<Rightarrow> insert \<lparr>sender = n\<^sub>0, destination = OneNode (sender m), payload = m'\<rparr> messages)"
          unfolding messages'_def result respond'_def nodeState'_def by (cases "handlePublishRequest i t x (nodeState n\<^sub>0)", cases "snd (handlePublishRequest i t x (nodeState n\<^sub>0))", auto)

        from m
        show "\<exists>d. \<lparr>sender = sender m, destination = d, payload = PublishRequest i t x\<rparr> \<in> messages"
          by (auto simp add: PublishRequest isMessageFromTo_def)
      qed

    next
      case (PublishResponse i t)

      have result: "result = broadcast' (handlePublishResponse (sender m) i t nd)"
        unfolding result_def ProcessMessage_def PublishResponse dest_True by (simp add: broadcast'_def)

      show ?thesis
      proof (intro zenStep.handlePublishResponse_invariants [OF zenStep])
        show "nodeState' n\<^sub>0 = fst (handlePublishResponse (sender m) i t (nodeState n\<^sub>0))"
          by (simp add: result nodeState'_def)

        show "messages' = (case snd (handlePublishResponse (sender m) i t (nodeState n\<^sub>0)) of None \<Rightarrow> messages | Some m \<Rightarrow> insert \<lparr>sender = n\<^sub>0, destination = Broadcast, payload = m\<rparr> messages)"
          by (simp_all add: messages'_def result broadcast'_def handlePublishResponse_def commitIfQuorate_def)

        from m
        show "\<exists>d. \<lparr>sender = sender m, destination = d, payload = PublishResponse i t\<rparr> \<in> messages"
          by (auto simp add: PublishResponse isMessageFromTo_def)
      qed

    next
      case (ApplyCommit i t)

      have result: "result = (handleApplyCommit i t nd, None)"
        unfolding result_def ProcessMessage_def ApplyCommit dest_True by simp

      have currentNode_eq: "currentNode (nodeState' n\<^sub>0) = currentNode (nodeState n\<^sub>0)"
        unfolding nodeState'_def result by (cases "lastAcceptedValue nd", simp_all add: handleApplyCommit_def applyAcceptedValue_def)

      show ?thesis
      proof (intro zenStep.handleApplyCommit_invariants [OF zenStep])
        show "nodeState' n\<^sub>0 = handleApplyCommit i t (nodeState n\<^sub>0)"
          by (simp add: result nodeState'_def)
        show "messages' = messages"
          by (simp add: result messages'_def)
        from m show "\<exists>s d. \<lparr>sender = s, destination = d, payload = ApplyCommit i t\<rparr> \<in> messages"
          by (auto simp add: ApplyCommit isMessageFromTo_def)
      qed

    next
      case Reboot

      have result: "result = (handleReboot nd, None)"
        unfolding result_def ProcessMessage_def Reboot dest_True by simp

      show ?thesis
      proof (intro zenStep.handleReboot_invariants [OF zenStep])
        show "nodeState' n\<^sub>0 = handleReboot (nodeState n\<^sub>0)"
          by (simp add: nodeState'_def result)

        show "messages' = messages"
          by (simp add: result messages'_def)
      qed

    next
      case DiscardJoinVotes

      have result: "result = (handleDiscardJoinVotes nd, None)"
        unfolding result_def ProcessMessage_def DiscardJoinVotes dest_True by simp

      show ?thesis
      proof (intro zenStep.handleDiscardJoinVotes_invariants [OF zenStep])
        show "nodeState' n\<^sub>0 = handleDiscardJoinVotes (nodeState n\<^sub>0)"
          by (simp add: nodeState'_def result)

        show "messages' = messages"
          by (simp add: result messages'_def)
      qed

    next
      case CatchUpRequest

      have result: "result = respond' (handleCatchUpRequest nd)"
        unfolding result_def ProcessMessage_def CatchUpRequest dest_True by (simp add: respond'_def)

      have currentNode_eq: "currentNode (nodeState' n\<^sub>0) = currentNode (nodeState n\<^sub>0)"
        unfolding nodeState'_def result by (cases "lastAcceptedValue nd", simp_all add: handleCatchUpRequest_def)

      show ?thesis
      proof (intro zenStep.handleCatchUpRequest_invariants [OF zenStep])
        show "nodeState' n\<^sub>0 = fst (handleCatchUpRequest (nodeState n\<^sub>0))"
          by (simp add: nodeState'_def result)

        show "messages' = (case snd (handleCatchUpRequest (nodeState n\<^sub>0)) of None \<Rightarrow> messages | Some m' \<Rightarrow> insert \<lparr>sender = n\<^sub>0, destination = OneNode (sender m), payload = m'\<rparr> messages)"
          by (simp_all add: messages'_def result respond'_def handleCatchUpRequest_def)
      qed

    next
      case (CatchUpResponse i conf cs)

      have result: "result = (handleCatchUpResponse i conf cs nd, None)"
        unfolding result_def ProcessMessage_def CatchUpResponse dest_True by simp

      show ?thesis
      proof (intro zenStep.handleCatchUpResponse_invariants [OF zenStep])
        show "nodeState' n\<^sub>0 = handleCatchUpResponse i conf cs (nodeState n\<^sub>0)"
          by (simp add: nodeState'_def result)

        show "messages' = messages"
          by (simp add: result messages'_def)

        from m show "\<exists>s d. \<lparr>sender = s, destination = d, payload = CatchUpResponse i conf cs\<rparr> \<in> messages"
          unfolding CatchUpResponse isMessageFromTo_def by auto
      qed
    qed
  qed
qed

theorem (in zen) invariants_imply_consistent_states:
  assumes
    "firstUncommittedSlot (nodeState n\<^sub>1) = firstUncommittedSlot (nodeState n\<^sub>2)"
  shows
    "currentClusterState (nodeState n\<^sub>1) = currentClusterState (nodeState n\<^sub>2)"
proof -
  have "currentClusterState (nodeState n\<^sub>1) = lastCommittedClusterStateBefore (firstUncommittedSlot (nodeState n\<^sub>1))"
    using currentClusterState_lastCommittedClusterStateBefore .
  also have "... = lastCommittedClusterStateBefore (firstUncommittedSlot (nodeState n\<^sub>2))" using assms by simp
  also have "... = currentClusterState (nodeState n\<^sub>2)"
    using currentClusterState_lastCommittedClusterStateBefore ..
  finally show ?thesis .
qed

end
