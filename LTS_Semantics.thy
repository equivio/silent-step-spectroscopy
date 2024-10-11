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
  entails_def[simp]: \<open>entails \<phi>l \<phi>r \<equiv> (\<forall>p. (models p \<phi>l) \<longrightarrow> (models p \<phi>r))\<close>

definition logical_eq :: \<open>'formula \<Rightarrow> 'formula \<Rightarrow> bool\<close> where
  logical_eq_def[simp]: \<open>logical_eq \<phi>l \<phi>r \<equiv> entails \<phi>l \<phi>r \<and> entails \<phi>r \<phi>l\<close>

text \<open>Formula implication is a pre-order. \<close>
lemma entails_preord: \<open>reflp (entails)\<close> \<open>transp (entails)\<close>
  by (simp add: reflpI transp_def)+

lemma eq_equiv: \<open>equivp logical_eq\<close>
  using equivpI reflpI sympI transpI
  unfolding logical_eq_def entails_def
  by (smt (verit, del_insts))

text \<open>
The definition given above is equivalent which means formula equivalence is a biimplication on the
models predicate.
\<close>
lemma eq_equality[simp]: \<open>(logical_eq \<phi>l \<phi>r) = (\<forall>p. models p \<phi>l = models p \<phi>r)\<close>
  by force

lemma logical_eqI[intro]:
  assumes
    \<open>\<And>s. models s \<phi>l \<Longrightarrow> models s \<phi>r\<close>
    \<open>\<And>s. models s \<phi>r \<Longrightarrow> models s \<phi>l\<close>
  shows
    \<open>logical_eq \<phi>l \<phi>r\<close>
  using assms by auto

definition distinguishes :: \<open>'formula \<Rightarrow> 's \<Rightarrow> 's \<Rightarrow> bool\<close> where
  distinguishes_def[simp]:
  \<open>distinguishes \<phi> p q \<equiv> models p \<phi> \<and> \<not>(models q \<phi>)\<close>

definition distinguishes_from :: \<open>'formula \<Rightarrow> 's \<Rightarrow> 's set \<Rightarrow> bool\<close> where
  distinguishes_from_def[simp]:
  \<open>distinguishes_from \<phi> p Q \<equiv> models p \<phi> \<and> (\<forall>q \<in> Q. \<not>(models q \<phi>))\<close>

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

text \<open>If $\varphi$ is equivalent to $\varphi'$ and $\varphi$ distinguishes process @{term \<open>p\<close>} from
process @{term \<open>q\<close>}, the $\varphi'$ also distinguishes process @{term \<open>p\<close>} from process @{term \<open>q\<close>}.\<close>
lemma dist_equal_dist:
  assumes \<open>logical_eq \<phi>l \<phi>r\<close>
      and \<open>distinguishes \<phi>l p q\<close>
    shows \<open>distinguishes \<phi>r p q\<close>
  using assms
  by auto

abbreviation model_set :: \<open>'formula \<Rightarrow> 's set\<close> where
  \<open>model_set \<phi> \<equiv> {p. models p \<phi>}\<close>

subsection \<open>Preorders and Equivalences on Processes Derived from Formula Sets\<close>

text \<open> A set of formulas pre-orders two processes @{term \<open>p\<close>} and @{term \<open>q\<close>} if
for all formulas in this set the fact that @{term \<open>p\<close>} satisfies a formula means that also
@{term \<open>q\<close>} must satisfy this formula. \<close>
definition preordered :: \<open>'formula set \<Rightarrow> 's \<Rightarrow> 's \<Rightarrow> bool\<close> where
  preordered_def[simp]:
  \<open>preordered \<phi>s p q \<equiv> \<forall>\<phi> \<in> \<phi>s. models p \<phi> \<longrightarrow> models q \<phi>\<close>

text \<open>
If a set of formulas pre-orders two processes @{term \<open>p\<close>} and @{term \<open>q\<close>}, then no formula in that set
may distinguish @{term \<open>p\<close>} from @{term \<open>q\<close>}.
\<close>
lemma preordered_no_distinction: 
  \<open>preordered \<phi>s p q = (\<forall>\<phi> \<in> \<phi>s. \<not>(distinguishes \<phi> p q))\<close>
  by simp

text \<open>A formula set derived pre-order is a pre-order.\<close>
lemma preordered_preord:
  \<open>reflp (preordered \<phi>s)\<close>
  \<open>transp (preordered \<phi>s)\<close>
  unfolding reflp_def transp_def by auto

text \<open>A set of formulas equates two processes @{term \<open>p\<close>} and @{term \<open>q\<close>} if
this set of formulas pre-orders these two processes in both directions. \<close>
definition equivalent :: \<open>'formula set \<Rightarrow> 's \<Rightarrow> 's \<Rightarrow> bool\<close> where
  equivalent_def[simp]:
  \<open>equivalent \<phi>s p q \<equiv> preordered \<phi>s p q \<and> preordered \<phi>s q p\<close>

text \<open>
If a set of formulas equates two processes @{term \<open>p\<close>} and @{term \<open>q\<close>}, then no formula in that set
may distinguish @{term \<open>p\<close>} from @{term \<open>q\<close>} nor the other way around.
\<close>
lemma equivalent_no_distinction: \<open>equivalent \<phi>s p q
     = (\<forall>\<phi> \<in> \<phi>s. \<not>(distinguishes \<phi> p q) \<and> \<not>(distinguishes \<phi> q p))\<close>
  by auto

text \<open> A formula-set-derived equivalence is an equivalence. \<close>
lemma equivalent_equiv: \<open>equivp (equivalent \<phi>s)\<close>
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