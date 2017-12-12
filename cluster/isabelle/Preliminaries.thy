section \<open>Preliminaries\<close>

text \<open>We start with some definitions of the types involved.\<close>

theory Preliminaries
  imports Main
begin

subsection \<open>Slots\<close>

text \<open>Slots are identified by natural numbers.\<close>

type_synonym Slot = nat

subsection \<open>Terms\<close>

text \<open>Terms are identified by natural numbers.\<close>

type_synonym Term = nat

subsubsection \<open>Maximum term of a set\<close>

text \<open>A function for finding the maximum term in a set is as follows.\<close>

definition maxTerm :: "Term set \<Rightarrow> Term"
  where "maxTerm S \<equiv> THE t. t \<in> S \<and> (\<forall> t' \<in> S. t' \<le> t)"

text \<open>It works correctly on finite and nonempty sets as follows:\<close>

theorem
  fixes S :: "Term set"
  assumes finite: "finite S"
  shows maxTerm_mem: "S \<noteq> {} \<Longrightarrow> maxTerm S \<in> S"
    and maxTerm_max: "\<And> t'. t' \<in> S \<Longrightarrow> t' \<le> maxTerm S"
proof -
  presume "S \<noteq> {}"
  with assms
  obtain t where t: "t \<in> S" "\<And> t'. t' \<in> S \<Longrightarrow> t' \<le> t"
  proof (induct arbitrary: thesis)
    case empty
    then show ?case by simp
  next
    case (insert t S)
    show ?case
    proof (cases "S = {}")
      case True hence [simp]: "insert t S = {t}" by simp
      from insert.prems show ?thesis by simp
    next
      case False
      obtain t' where t': "t' \<in> S" "\<forall> t'' \<in> S. t'' \<le> t'"
        by (meson False insert.hyps(3))

      from t'
      show ?thesis
      proof (intro insert.prems ballI)
        fix t'' assume t'': "t'' \<in> insert t S"
        show "t'' \<le> (if t \<le> t' then t' else t)"
        proof (cases "t'' = t")
          case False
          with t'' have "t'' \<in> S" by simp
          with t' have "t'' \<le> t'" by simp
          thus ?thesis by auto
        qed simp
      qed simp
    qed
  qed

  from t have "maxTerm S = t"
    by (unfold maxTerm_def, intro the_equality, simp_all add: eq_iff)

  with t show "maxTerm S \<in> S" "\<And>t'. t' \<in> S \<Longrightarrow> t' \<le> maxTerm S" by simp_all
qed auto

lemma
  assumes "\<And>t. t \<in> S \<Longrightarrow> t \<le> t'" "finite S" "S \<noteq> {}"
  shows maxTerm_le: "maxTerm S \<le> t'" using assms maxTerm_mem by auto

subsection \<open>Configurations and quorums\<close>

text \<open>Nodes are simply identified by a natural number.\<close>

datatype Node = Node nat

definition natOfNode :: "Node \<Rightarrow> nat" where "natOfNode node \<equiv> case node of Node n \<Rightarrow> n"
lemma natOfNode_Node[simp]: "natOfNode (Node n) = n" by (simp add: natOfNode_def)
lemma Node_natOfNode[simp]: "Node (natOfNode n) = n" by (cases n, simp add: natOfNode_def)
lemma natOfNode_inj[simp]: "(natOfNode n\<^sub>1 = natOfNode n\<^sub>2) = (n\<^sub>1 = n\<^sub>2)" by (metis Node_natOfNode)

text \<open>It is useful to be able to talk about whether sets-of-sets-of nodes mutually intersect or not.\<close>

definition intersects :: "Node set set \<Rightarrow> Node set set \<Rightarrow> bool" (infixl "\<frown>" 50)
  where "A \<frown> B \<equiv> \<forall> a \<in> A. \<forall> b \<in> B. a \<inter> b \<noteq> {}"

definition majorities :: "Node set \<Rightarrow> Node set set"
  where "majorities votingNodes = { q. card votingNodes < card (q \<inter> votingNodes) * 2 }"

lemma majorities_nonempty: assumes "q \<in> majorities Q" shows "q \<noteq> {}"
  using assms by (auto simp add: majorities_def)

lemma majorities_member: assumes "q \<in> majorities Q" obtains n where "n \<in> q"
  using majorities_nonempty assms by fastforce

lemma majorities_intersect:
  assumes "finite votingNodes"
  shows "majorities votingNodes \<frown> majorities votingNodes"
  unfolding intersects_def
proof (intro ballI notI)
  fix q\<^sub>1 assume q\<^sub>1: "q\<^sub>1 \<in> majorities votingNodes"
  fix q\<^sub>2 assume q\<^sub>2: "q\<^sub>2 \<in> majorities votingNodes"
  assume disj: "q\<^sub>1 \<inter> q\<^sub>2 = {}"

  have 1: "card ((q\<^sub>1 \<inter> votingNodes) \<union> (q\<^sub>2 \<inter> votingNodes)) = card (q\<^sub>1 \<inter> votingNodes) + card (q\<^sub>2 \<inter> votingNodes)"
  proof (intro card_Un_disjoint)
    from assms show "finite (q\<^sub>1 \<inter> votingNodes)" by simp
    from assms show "finite (q\<^sub>2 \<inter> votingNodes)" by simp
    from disj show "q\<^sub>1 \<inter> votingNodes \<inter> (q\<^sub>2 \<inter> votingNodes) = {}" by auto
  qed

  have "card ((q\<^sub>1 \<inter> votingNodes) \<union> (q\<^sub>2 \<inter> votingNodes)) \<le> card votingNodes" by (simp add: assms card_mono)
  hence 2: "2 * card (q\<^sub>1 \<inter> votingNodes) + 2 * card (q\<^sub>2 \<inter> votingNodes) \<le> 2 * card votingNodes" by (simp add: 1)

  from q\<^sub>1 q\<^sub>2 have 3: "card votingNodes + card votingNodes < 2 * card (q\<^sub>1 \<inter> votingNodes) + 2 * card (q\<^sub>2 \<inter> votingNodes)"
    unfolding majorities_def by auto

  from 2 3 show False by simp
qed

text \<open>A configuration of the system defines the sets of master-eligible nodes whose votes count when calculating quorums.
The initial configuration of the system is fixed to some arbitrary value.\<close>

consts Vs\<^sub>0 :: "Node list"
definition V\<^sub>0 :: "Node set" where "V\<^sub>0 \<equiv> set Vs\<^sub>0"

lemma finite_V\<^sub>0: "finite V\<^sub>0" unfolding V\<^sub>0_def by auto
lemma V\<^sub>0_intersects: "majorities V\<^sub>0 \<frown> majorities V\<^sub>0" using finite_V\<^sub>0 by (intro majorities_intersect)

subsection \<open>Values\<close>

text \<open>The model is a replicated state machine, with transitions that either do nothing, alter
the configuration of the system or set a new \texttt{ClusterState}. \texttt{ClusterState} values
are modelled simply as natural numbers.\<close>

datatype ClusterState = ClusterState nat
consts CS\<^sub>0 :: ClusterState

datatype Value
  = NoOp
  | Reconfigure "Node list" (* update the set of voting nodes. A list rather than a set to force it to be finite *)
  | ClusterStateDiff "ClusterState \<Rightarrow> ClusterState" (* a ClusterState diff *)

text \<open>Some useful definitions and lemmas follow.\<close>

fun isReconfiguration :: "Value \<Rightarrow> bool"
  where "isReconfiguration (Reconfigure _) = True"
  | "isReconfiguration _ = False"

fun getConf :: "Value \<Rightarrow> Node set"
  where "getConf (Reconfigure conf) = set conf"
  | "getConf _                      = {}"

lemma getConf_finite: "finite (getConf v)"
  by (metis List.finite_set getConf.elims infinite_imp_nonempty)

lemma getConf_intersects: "majorities (getConf v) \<frown> majorities (getConf v)"
  by (simp add: getConf_finite majorities_intersect)

end
