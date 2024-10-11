subsection \<open>Modal Logics on LTS\<close>

theory LTS_Semantics
  imports
    LTS
begin

locale lts_semantics = LTS step
  for step :: \<open>'s \<Rightarrow> 'a \<Rightarrow> 's \<Rightarrow> bool\<close> (\<open>_ \<mapsto> _ _\<close> [70,70,70] 80) +
  fixes models :: \<open>'s \<Rightarrow> 'formula \<Rightarrow> bool\<close>
begin

definition entails :: \<open>'formula \<Rightarrow> 'formula \<Rightarrow> bool\<close> where
  entails_def[simp]: "entails \<phi>l \<phi>r \<equiv> (\<forall>p. (models p \<phi>l) \<longrightarrow> (models p \<phi>r))"

definition logical_eq :: \<open>'formula \<Rightarrow> 'formula \<Rightarrow> bool\<close> where
  logical_eq_def[simp]: \<open>logical_eq \<phi>l \<phi>r \<equiv> entails \<phi>l \<phi>r \<and> entails \<phi>r \<phi>l\<close>

text \<open>Formula implication is a pre-order. \<close>
lemma entails_preord: "reflp (entails)" "transp (entails)"
  by (simp add: reflpI transp_def)+

lemma eq_equiv: "equivp logical_eq"
  using equivpI reflpI sympI transpI
  unfolding logical_eq_def entails_def
  by (smt (verit, del_insts))

text \<open>
The definition given above is equivalent which means formula equivalence is a biimplication on the
models predicate.
\<close>
lemma eq_equality[simp]: "(logical_eq \<phi>l \<phi>r) = (\<forall>p. models p \<phi>l = models p \<phi>r)"
  by force

lemma logical_eqI[intro]:
  assumes
    \<open>\<And>s. models s \<phi>l \<Longrightarrow> models s \<phi>r\<close>
    \<open>\<And>s. models s \<phi>r \<Longrightarrow> models s \<phi>l\<close>
  shows
    \<open>logical_eq \<phi>l \<phi>r\<close>
  using assms by auto

definition distinguishes :: "'formula \<Rightarrow> 's \<Rightarrow> 's \<Rightarrow> bool" where
  distinguishes_def[simp]:
  "distinguishes \<phi> p q \<equiv> models p \<phi> \<and> \<not>(models q \<phi>)"

definition distinguishes_from :: "'formula \<Rightarrow> 's \<Rightarrow> 's set \<Rightarrow> bool" where
  distinguishes_from_def[simp]:
  "distinguishes_from \<phi> p Q \<equiv> models p \<phi> \<and> (\<forall>q \<in> Q. \<not>(models q \<phi>))"

lemma distinction_unlifting:
  assumes
    \<open>distinguishes_from \<phi> p Q\<close>
  shows
    \<open>\<forall>q\<in>Q. distinguishes \<phi> p q\<close>
  using assms by simp

lemma no_distinction_fom_self:
  assumes
    \<open>distinguishes \<phi> p p\<close>
  shows
    \<open>False\<close>
  using assms by simp

text \<open>If $\varphi$ is equivalent to $\varphi'$ and $\varphi$ distinguishes process @{term "p"} from
process @{term "q"}, the $\varphi'$ also distinguishes process @{term "p"} from process @{term "q"}.\<close>
lemma dist_equal_dist:
  assumes "logical_eq \<phi>l \<phi>r"
      and "distinguishes \<phi>l p q"
    shows "distinguishes \<phi>r p q"
  using assms
  by auto

abbreviation model_set :: "'formula \<Rightarrow> 's set" where
  "model_set \<phi> \<equiv> {p. models p \<phi>}"

subsection \<open>Preorders and Equivalences on Processes Derived from Formula Sets\<close>

text \<open> A set of formulas pre-orders two processes @{term "p"} and @{term "q"} if
for all formulas in this set the fact that @{term "p"} satisfies a formula means that also
@{term "q"} must satisfy this formula. \<close>
definition preordered :: "'formula set \<Rightarrow> 's \<Rightarrow> 's \<Rightarrow> bool" where
  preordered_def[simp]:
  "preordered \<phi>s p q \<equiv> \<forall>\<phi> \<in> \<phi>s. models p \<phi> \<longrightarrow> models q \<phi>"

text \<open>
If a set of formulas pre-orders two processes @{term "p"} and @{term "q"}, then no formula in that set
may distinguish @{term "p"} from @{term "q"}.
\<close>
lemma preordered_no_distinction: 
  "preordered \<phi>s p q = (\<forall>\<phi> \<in> \<phi>s. \<not>(distinguishes \<phi> p q))"
  by simp

text \<open>A formula set derived pre-order is a pre-order.\<close>
lemma preordered_preord:
  "reflp (preordered \<phi>s)"
  "transp (preordered \<phi>s)"
  unfolding reflp_def transp_def by auto

text \<open>A set of formulas equates two processes @{term "p"} and @{term "q"} if
this set of formulas pre-orders these two processes in both directions. \<close>
definition equivalent :: "'formula set \<Rightarrow> 's \<Rightarrow> 's \<Rightarrow> bool" where
  equivalent_def[simp]:
  "equivalent \<phi>s p q \<equiv> preordered \<phi>s p q \<and> preordered \<phi>s q p"

text \<open>
If a set of formulas equates two processes @{term "p"} and @{term "q"}, then no formula in that set
may distinguish @{term "p"} from @{term "q"} nor the other way around.
\<close>
lemma equivalent_no_distinction: "equivalent \<phi>s p q
     = (\<forall>\<phi> \<in> \<phi>s. \<not>(distinguishes \<phi> p q) \<and> \<not>(distinguishes \<phi> q p))"
  by auto

text \<open> A formula-set-derived equivalence is an equivalence. \<close>
lemma equivalent_equiv: "equivp (equivalent \<phi>s)"
proof (rule equivpI)
  show \<open>reflp (equivalent \<phi>s)\<close>
    by (simp add: reflpI)
  show \<open>symp (equivalent \<phi>s)\<close>
    unfolding equivalent_no_distinction symp_def
    by auto
  show \<open>transp (equivalent \<phi>s)\<close>
    unfolding transp_def equivalent_def preordered_def
    by blast
qed

end

end