section \<open>One-slot consistency\<close>

text \<open>The replicated state machine determines the values that are committed in each of a sequence
of \textit{slots}. Each slot runs a logically-separate consensus algorithm which is shown to be
consistent here. Further below, the protocol is shown to refine this slot-by-slot model correctly.\<close>

text \<open>Consistency is shown to follow from the invariants listed below. Further below, the protocol
is shown to preserve these invariants in each step, which means it is not enormously important
to understand these in detail.\<close>

theory OneSlot
  imports Preliminaries
begin

locale oneSlot =
  (* basic functions *)
  fixes Q :: "Node set set"
  fixes v :: "Term \<Rightarrow> Value"
    (* message-sent predicates *)
  fixes promised\<^sub>f :: "Node \<Rightarrow> Term \<Rightarrow> bool"
  fixes promised\<^sub>b :: "Node \<Rightarrow> Term \<Rightarrow> Term \<Rightarrow> bool"
  fixes proposed :: "Term \<Rightarrow> bool"
  fixes accepted :: "Node \<Rightarrow> Term \<Rightarrow> bool"
  fixes committed :: "Term \<Rightarrow> bool"
    (* other definitions *)
  fixes promised :: "Node \<Rightarrow> Term \<Rightarrow> bool"
  defines "promised n t \<equiv> promised\<^sub>f n t \<or> (\<exists> t'. promised\<^sub>b n t t')"
  fixes prevAccepted :: "Term \<Rightarrow> Node set \<Rightarrow> Term set"
  defines "prevAccepted t ns \<equiv> {t'. \<exists> n \<in> ns. promised\<^sub>b n t t'}"
    (* invariants *)
  assumes Q_intersects: "Q \<frown> Q"
  assumes promised\<^sub>f: "\<lbrakk> promised\<^sub>f n t; t' < t \<rbrakk> \<Longrightarrow> \<not> accepted n t'"
  assumes promised\<^sub>b_lt: "promised\<^sub>b n t t' \<Longrightarrow> t' < t"
  assumes promised\<^sub>b_accepted: "promised\<^sub>b n t t' \<Longrightarrow> accepted n t'"
  assumes promised\<^sub>b_max: "\<lbrakk> promised\<^sub>b n t t'; t' < t''; t'' < t \<rbrakk>
   \<Longrightarrow> \<not> accepted n t''"
  assumes proposed: "proposed t
     \<Longrightarrow> \<exists> q \<in> Q. (\<forall> n \<in> q. promised n t)
                     \<and> (prevAccepted t q = {}
                          \<or> v t = v (maxTerm (prevAccepted t q)))"
  assumes proposed_finite: "finite {t. proposed t}"
  assumes accepted: "accepted n t \<Longrightarrow> proposed t"
  assumes committed: "committed t \<Longrightarrow> \<exists> q \<in> Q. \<forall> n \<in> q. accepted n t"

lemma (in oneSlot) prevAccepted_proposed: "prevAccepted t ns \<subseteq> {t. proposed t}"
  using accepted prevAccepted_def promised\<^sub>b_accepted by fastforce

lemma (in oneSlot) prevAccepted_finite: "finite (prevAccepted p ns)"
  using prevAccepted_proposed proposed_finite by (meson rev_finite_subset)

lemma (in oneSlot) Q_nonempty: "\<And>q. q \<in> Q \<Longrightarrow> q \<noteq> {}"
  using Q_intersects by (auto simp add: intersects_def)

text \<open>The heart of the consistency proof is property P2b from \textit{Paxos made simple} by Lamport:\<close>

lemma (in oneSlot) p2b:
  assumes "proposed t\<^sub>1" and "committed t\<^sub>2" and "t\<^sub>2 < t\<^sub>1"
  shows "v t\<^sub>1 = v t\<^sub>2"
  using assms
proof (induct t\<^sub>1 rule: less_induct)
  case (less t\<^sub>1)

  hence hyp: "\<And> t\<^sub>1'. \<lbrakk> t\<^sub>1' < t\<^sub>1; proposed t\<^sub>1'; t\<^sub>2 \<le> t\<^sub>1' \<rbrakk> \<Longrightarrow> v t\<^sub>1' = v t\<^sub>2"
    using le_imp_less_or_eq by blast

  from `proposed t\<^sub>1` obtain q\<^sub>1 where
    q\<^sub>1_quorum:   "q\<^sub>1 \<in> Q" and
    q\<^sub>1_promised: "\<And>n. n \<in> q\<^sub>1 \<Longrightarrow> promised n t\<^sub>1" and
    q\<^sub>1_value:    "prevAccepted t\<^sub>1 q\<^sub>1 = {} \<or> v t\<^sub>1 = v (maxTerm (prevAccepted t\<^sub>1 q\<^sub>1))"
    by (meson proposed)

  from `committed t\<^sub>2` obtain q\<^sub>2 where
    q\<^sub>2_quorum:   "q\<^sub>2 \<in> Q" and
    q\<^sub>2_accepted: "\<And>n. n \<in> q\<^sub>2 \<Longrightarrow> accepted n t\<^sub>2"
    using committed by force

  have "q\<^sub>1 \<inter> q\<^sub>2 \<noteq> {}"
    using Q_intersects intersects_def less.prems q\<^sub>1_quorum q\<^sub>2_quorum by auto

  then obtain n where n\<^sub>1: "n \<in> q\<^sub>1" and n\<^sub>2: "n \<in> q\<^sub>2" by auto

  from n\<^sub>1 q\<^sub>1_promised have "promised n t\<^sub>1" by simp
  moreover from n\<^sub>2 q\<^sub>2_accepted have "accepted n t\<^sub>2" by simp
  ultimately obtain t\<^sub>2' where t\<^sub>2': "promised\<^sub>b n t\<^sub>1 t\<^sub>2'"
    using less.prems(3) promised\<^sub>f promised_def by blast

  have q\<^sub>1_value: "v t\<^sub>1 = v (maxTerm (prevAccepted t\<^sub>1 q\<^sub>1))"
    using n\<^sub>1 prevAccepted_def q\<^sub>1_value t\<^sub>2' by auto

  also have "... = v t\<^sub>2"
  proof (intro hyp)
    have p: "maxTerm (prevAccepted t\<^sub>1 q\<^sub>1) \<in> prevAccepted t\<^sub>1 q\<^sub>1"
      apply (intro maxTerm_mem prevAccepted_finite)
      using n\<^sub>1 prevAccepted_def t\<^sub>2' by auto

    show "maxTerm (prevAccepted t\<^sub>1 q\<^sub>1) < t\<^sub>1"
      using p prevAccepted_def promised\<^sub>b_lt by auto

    show "proposed (maxTerm (prevAccepted t\<^sub>1 q\<^sub>1))"
      using p prevAccepted_proposed by auto

    have "t\<^sub>2 \<le> t\<^sub>2'"
      by (meson \<open>accepted n t\<^sub>2\<close> less.prems(3) not_le promised\<^sub>b_max t\<^sub>2')
    also have "t\<^sub>2' \<le> maxTerm (prevAccepted t\<^sub>1 q\<^sub>1)"
      using n\<^sub>1 prevAccepted_def t\<^sub>2' prevAccepted_finite by (intro maxTerm_max, auto)
    finally show "t\<^sub>2 \<le> maxTerm (prevAccepted t\<^sub>1 q\<^sub>1)" .
  qed

  finally show ?case .
qed

text \<open>From this, it follows that any two committed values are equal as desired.\<close>

lemma (in oneSlot) consistent:
  assumes "committed t\<^sub>1" and "committed t\<^sub>2"
  shows "v t\<^sub>1 = v t\<^sub>2"
  using assms by (metis Q_nonempty accepted all_not_in_conv committed not_less_iff_gr_or_eq p2b)

text \<open>It will be useful later to know the conditions under which a value in a term can be committed,
which is spelled out here:\<close>

lemma (in oneSlot) commit:
  assumes q_quorum: "q \<in> Q"
  assumes q_accepted: "\<And>n. n \<in> q \<Longrightarrow> accepted n t\<^sub>0"
  defines "committed' t \<equiv> committed t \<or> t = t\<^sub>0"
  shows "oneSlot Q v promised\<^sub>f promised\<^sub>b proposed accepted committed'"
  by (smt committed'_def Q_intersects oneSlot_axioms oneSlot_def q_accepted q_quorum)

end
