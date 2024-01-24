theory HML_SRBB
  imports Main HML
begin

section \<open> Stability Respecting Branching Bisimilarity - Subset of HML \<close>

datatype 
  ('act, 'i) hml_srbb =
    TT |
    Internal "('act, 'i) hml_srbb_inner" |
    ImmConj "'i set" "'i \<Rightarrow> ('act, 'i) hml_srbb_conjunct"
and
  ('act, 'i) hml_srbb_inner =
    Obs 'act "('act, 'i) hml_srbb" |
    Conj "'i set" "'i \<Rightarrow> ('act, 'i) hml_srbb_conjunct" |
    StableConj "'i set" "'i \<Rightarrow> ('act, 'i) hml_srbb_conjunct" |
    BranchConj 'act "('act, 'i) hml_srbb"
               "'i set" "'i \<Rightarrow> ('act, 'i) hml_srbb_conjunct"
and
  ('act, 'i) hml_srbb_conjunct =
    Pos "('act, 'i) hml_srbb_inner" |
    Neg "('act, 'i) hml_srbb_inner"


context Inhabited_Tau_LTS
begin

primrec
      hml_srbb_to_hml :: "('a, 's) hml_srbb \<Rightarrow> ('a, 's) hml"
  and hml_srbb_inner_to_hml :: "('a, 's) hml_srbb_inner \<Rightarrow> ('a, 's) hml"
  and hml_srbb_conjunct_to_hml_conjunct :: "('a, 's) hml_srbb_conjunct \<Rightarrow> ('a, 's) hml_conjunct" where
  "hml_srbb_to_hml TT = hml.TT" |
  "hml_srbb_to_hml (Internal \<chi>) = hml.Internal (hml_srbb_inner_to_hml \<chi>)" |
  "hml_srbb_to_hml (ImmConj I \<psi>s) = hml.Conj I (hml_srbb_conjunct_to_hml_conjunct \<circ> \<psi>s)" |

  "hml_srbb_inner_to_hml (Obs a \<phi>) = HML_soft_poss a (hml_srbb_to_hml \<phi>)" |
(*equivalent to? (if a = \<tau> then hml_srbb_to_hml \<phi> else hml.Obs a (hml_srbb_to_hml \<phi>))*)
  "hml_srbb_inner_to_hml (Conj I \<psi>s) = hml.Conj I (hml_srbb_conjunct_to_hml_conjunct \<circ> \<psi>s)" |

  "hml_srbb_inner_to_hml (StableConj I \<psi>s) =
    (hml_conjunct.Neg (hml.Obs \<tau> hml.TT)
     \<and>hml hml_conjunct.Pos (hml.Conj I (hml_srbb_conjunct_to_hml_conjunct \<circ> \<psi>s)))" |

  "hml_srbb_inner_to_hml (BranchConj a \<phi> I \<psi>s) = 
     (hml_conjunct.Pos (HML_soft_poss a (hml_srbb_to_hml \<phi>))
      \<and>hml hml_conjunct.Pos (hml.Conj I (hml_srbb_conjunct_to_hml_conjunct \<circ> \<psi>s)))" |

  "hml_srbb_conjunct_to_hml_conjunct (Pos \<chi>) = hml_conjunct.Pos (hml.Internal (hml_srbb_inner_to_hml \<chi>))" |
  "hml_srbb_conjunct_to_hml_conjunct (Neg \<chi>) = hml_conjunct.Neg (hml.Internal (hml_srbb_inner_to_hml \<chi>))"


fun hml_srbb_models :: "'s \<Rightarrow> ('a, 's) hml_srbb \<Rightarrow> bool" (infix "\<Turnstile>SRBB" 60)where
  "hml_srbb_models state formula = (state \<Turnstile> (hml_srbb_to_hml formula))"

fun hml_srbb_inner_models :: "('a, 's) hml_srbb_inner \<Rightarrow> 's \<Rightarrow> bool" where
  "hml_srbb_inner_models \<chi> s = (s \<Turnstile> (hml_srbb_inner_to_hml \<chi>))"

fun hml_srbb_conjunct_models :: "('a, 's) hml_srbb_conjunct \<Rightarrow> 's \<Rightarrow> bool" where
  "hml_srbb_conjunct_models \<psi> s = (hml_conjunct_models s (hml_srbb_conjunct_to_hml_conjunct \<psi>))"


(*Some sanity checks*)

lemma "(state \<Turnstile>SRBB TT) = (state \<Turnstile>SRBB ImmConj {} \<psi>s)"
  by simp

lemma "(state \<Turnstile>SRBB TT) = (hml_srbb_inner_models (Conj {} \<psi>s) state)"
  by simp

lemma "(state \<Turnstile>SRBB TT) = (hml_srbb_inner_models (Obs \<tau> TT) state)"
  by simp

lemma "(state \<Turnstile>SRBB Internal \<chi>) = (state \<Turnstile>SRBB ImmConj {left} (\<lambda>i. if i = left then Pos \<chi> else undefined))"
  by simp


definition distinguishes :: "('a, 's) hml_srbb \<Rightarrow> 's \<Rightarrow> 's \<Rightarrow> bool" where
  "distinguishes \<phi> p q \<equiv> p \<Turnstile>SRBB \<phi> \<and> \<not>(q \<Turnstile>SRBB \<phi>)"

lemma dist_srbb_eq_dist_hml:
  "distinguishes \<phi> p q = p <> (hml_srbb_to_hml \<phi>) q"
  by (simp add: distinguishes_def distinguishes_hml_def)

definition distinguishes_inner :: "('a, 's) hml_srbb_inner \<Rightarrow> 's \<Rightarrow> 's \<Rightarrow> bool" where
  "distinguishes_inner \<chi> p q \<equiv> hml_srbb_inner_models \<chi> p \<and> \<not>(hml_srbb_inner_models \<chi> q)"

lemma dist_inner_srbb_eq_dist_hml:
  "distinguishes_inner \<chi> p q = p <> (hml_srbb_inner_to_hml \<chi>) q"
  by (simp add: distinguishes_inner_def distinguishes_hml_def)

definition distinguishes_conjunct :: "('a, 's) hml_srbb_conjunct \<Rightarrow> 's \<Rightarrow> 's \<Rightarrow> bool" where
  "distinguishes_conjunct \<psi> p q \<equiv> hml_srbb_conjunct_models \<psi> p \<and> \<not>(hml_srbb_conjunct_models \<psi> q)"

lemma dist_conjunct_srbb_eq_dist_conjunct_hml:
  "distinguishes_conjunct \<psi> p q = distinguishes_conjunct_hml p (hml_srbb_conjunct_to_hml_conjunct \<psi>) q"
  by (simp add: distinguishes_conjunct_def distinguishes_conjunct_hml_def)


definition distinguishes_from :: "('a, 's) hml_srbb \<Rightarrow> 's \<Rightarrow> 's set \<Rightarrow> bool" where
  "distinguishes_from \<phi> p Q \<equiv> p \<Turnstile>SRBB \<phi> \<and> (\<forall>q \<in> Q. \<not>(q \<Turnstile>SRBB \<phi>))"

lemma dist_from_srbb_eq_dist_from_hml:
  "distinguishes_from \<phi> p Q = p <> (hml_srbb_to_hml \<phi>) Q"
  by (simp add: distinguishes_from_def distinguishes_from_hml_def)

definition distinguishes_from' :: "('a, 's) hml_srbb \<Rightarrow> 's \<Rightarrow> 's set \<Rightarrow> bool" where
  "distinguishes_from' \<phi> p Q \<equiv> \<forall>q \<in> Q. distinguishes \<phi> p q"

lemma distinguishes_from_prime:
  assumes "Q \<noteq> {}"
  shows "distinguishes_from \<phi> p Q = distinguishes_from' \<phi> p Q"
  using assms distinguishes_def distinguishes_from'_def distinguishes_from_def ex_in_conv by auto

lemma distinguishes_from_priming:
  assumes "distinguishes_from \<phi> p Q"
  shows "distinguishes_from' \<phi> p Q"
  using assms distinguishes_def distinguishes_from'_def distinguishes_from_def ex_in_conv by auto


definition distinguishes_from_inner :: "('a, 's) hml_srbb_inner \<Rightarrow> 's \<Rightarrow> 's set \<Rightarrow> bool" where
  "distinguishes_from_inner \<chi> p Q \<equiv> hml_srbb_inner_models \<chi> p \<and> (\<forall>q \<in> Q. \<not>(hml_srbb_inner_models \<chi> q))"

lemma dist_from_inner_srbb_eq_dist_from_hml:
  "distinguishes_from_inner \<chi> p Q = p <> (hml_srbb_inner_to_hml \<chi>) Q"
  by (simp add: distinguishes_from_inner_def distinguishes_from_hml_def)

definition distinguishes_from_inner' :: "('a, 's) hml_srbb_inner \<Rightarrow> 's \<Rightarrow> 's set \<Rightarrow> bool" where
  "distinguishes_from_inner' \<chi> p Q \<equiv> \<forall>q \<in> Q. distinguishes_inner \<chi> p q"

lemma distinguishes_from_inner_prime:
  assumes "Q \<noteq> {}"
  shows "distinguishes_from_inner \<phi> p Q = distinguishes_from_inner' \<phi> p Q"
  using assms distinguishes_inner_def distinguishes_from_inner'_def distinguishes_from_inner_def ex_in_conv by auto

lemma distinguishes_from_inner_priming:
  assumes "distinguishes_from_inner \<phi> p Q"
  shows "distinguishes_from_inner' \<phi> p Q"
  using assms distinguishes_inner_def distinguishes_from_inner'_def distinguishes_from_inner_def ex_in_conv by auto


definition distinguishes_from_conjunct :: "('a, 's) hml_srbb_conjunct \<Rightarrow> 's \<Rightarrow> 's set \<Rightarrow> bool" where
  "distinguishes_from_conjunct \<psi> p Q \<equiv> hml_srbb_conjunct_models \<psi> p \<and> (\<forall>q \<in> Q. \<not>(hml_srbb_conjunct_models \<psi> q))"

lemma dist_from_conjunct_srbb_eq_dist_from_hml:
  "distinguishes_from_conjunct \<psi> p Q = distinguishes_conjunct_from_hml p (hml_srbb_conjunct_to_hml_conjunct \<psi>) Q"
  by (simp add: distinguishes_from_conjunct_def distinguishes_conjunct_from_hml_def)

definition distinguishes_from_conjunct' :: "('a, 's) hml_srbb_conjunct \<Rightarrow> 's \<Rightarrow> 's set \<Rightarrow> bool" where
  "distinguishes_from_conjunct' \<psi> p Q \<equiv> \<forall>q \<in> Q. distinguishes_conjunct \<psi> p q"

lemma distinguishes_from_conjunct_prime:
  assumes "Q \<noteq> {}"
  shows "distinguishes_from_conjunct \<phi> p Q = distinguishes_from_conjunct' \<phi> p Q"
  using assms distinguishes_conjunct_def distinguishes_from_conjunct'_def distinguishes_from_conjunct_def ex_in_conv by auto

lemma distinguishes_from_conjunct_priming:
  assumes "distinguishes_from_conjunct \<phi> p Q"
  shows "distinguishes_from_conjunct' \<phi> p Q"
  using assms distinguishes_conjunct_def distinguishes_from_conjunct'_def distinguishes_from_conjunct_def ex_in_conv by auto


lemma srbb_dist_imm_conjunction_implies_dist_conjunct:
  assumes "distinguishes (ImmConj I \<psi>s) p q"
  shows "\<exists>i\<in>I. distinguishes_conjunct (\<psi>s i) p q"
  using assms distinguishes_conjunct_def distinguishes_def by auto

lemma srbb_dist_conjunct_implies_dist_imm_conjunction:
  assumes "i\<in>I"
      and "distinguishes_conjunct (\<psi>s i) p q"
      and "\<forall>i\<in>I. hml_srbb_conjunct_models (\<psi>s i) p"
    shows "distinguishes (ImmConj I \<psi>s) p q"
  using assms distinguishes_conjunct_def distinguishes_def by auto

lemma srbb_dist_conjunction_implies_dist_conjunct:
  assumes "distinguishes_inner (Conj I \<psi>s) p q"
  shows "\<exists>i\<in>I. distinguishes_conjunct (\<psi>s i) p q"
  using assms distinguishes_conjunct_def distinguishes_inner_def by auto

lemma srbb_dist_conjunct_implies_dist_conjunction:
  assumes "i\<in>I"
      and "distinguishes_conjunct (\<psi>s i) p q"
      and "\<forall>i\<in>I. hml_srbb_conjunct_models (\<psi>s i) p"
  shows "distinguishes_inner (Conj I \<psi>s) p q"
  using assms distinguishes_conjunct_def distinguishes_inner_def by auto

lemma srbb_dist_stable_conjunction_implies_dist_conjunct_or_stable:
  assumes "distinguishes_inner (StableConj I \<psi>s) p q"
  shows "(\<exists>i\<in>I. distinguishes_conjunct (\<psi>s i) p q) \<or> (p <> (HML_not (hml.Obs \<tau> hml.TT)) q)"
  using assms
proof -
  assume "distinguishes_inner (StableConj I \<psi>s) p q"
  then have "hml_srbb_inner_models (StableConj I \<psi>s) p"
        and "\<not> hml_srbb_inner_models (StableConj I \<psi>s) q"
    unfolding distinguishes_inner_def by auto

  from \<open>hml_srbb_inner_models (StableConj I \<psi>s) p\<close>
  have "p \<Turnstile> hml_conjunct.Neg (hml.Obs \<tau> hml.TT)
            \<and>hml hml_conjunct.Pos (hml.Conj I (hml_srbb_conjunct_to_hml_conjunct \<circ> \<psi>s))"
    unfolding hml_srbb_inner_models.simps
          and hml_srbb_inner_to_hml.simps.
  with hml_and_and
  have "hml_conjunct_models p (hml_conjunct.Neg (hml.Obs \<tau> hml.TT))"
   and "hml_conjunct_models p (hml_conjunct.Pos (hml.Conj I (hml_srbb_conjunct_to_hml_conjunct \<circ> \<psi>s)))"
    by blast+

  from \<open>\<not> hml_srbb_inner_models (StableConj I \<psi>s) q\<close>
  have "\<not> hml_conjunct_models q (hml_conjunct.Neg (hml.Obs \<tau> hml.TT))
      \<or> \<not> hml_conjunct_models q (hml_conjunct.Pos (hml.Conj I (hml_srbb_conjunct_to_hml_conjunct \<circ> \<psi>s)))"
    unfolding hml_srbb_inner_models.simps
          and hml_srbb_inner_to_hml.simps
          and hml_and_and
          and de_Morgan_conj.
  then show "(\<exists>i\<in>I. distinguishes_conjunct (\<psi>s i) p q) \<or> (p <> (HML_not (hml.Obs \<tau> hml.TT)) q)"
  proof (rule disjE)
    assume "\<not> hml_conjunct_models q (hml_conjunct.Neg (hml.Obs \<tau> hml.TT))"
    with \<open>hml_conjunct_models p (hml_conjunct.Neg (hml.Obs \<tau> hml.TT))\<close>
    have "p <> (HML_not (hml.Obs \<tau> hml.TT)) q" 
      by (simp add: LTS_Tau.distinguishes_hml_def)
    then show ?thesis by auto
  next
    assume "\<not> hml_conjunct_models q (hml_conjunct.Pos (hml.Conj I (hml_srbb_conjunct_to_hml_conjunct \<circ> \<psi>s)))"
    hence "\<not> q \<Turnstile> (hml.Conj I (hml_srbb_conjunct_to_hml_conjunct \<circ> \<psi>s))" unfolding hml_conjunct_models.simps.
    moreover from \<open>hml_conjunct_models p (hml_conjunct.Pos (hml.Conj I (hml_srbb_conjunct_to_hml_conjunct \<circ> \<psi>s)))\<close>
    have "p \<Turnstile> (hml.Conj I (hml_srbb_conjunct_to_hml_conjunct \<circ> \<psi>s))" unfolding hml_conjunct_models.simps.
    ultimately have "\<exists>i\<in>I. distinguishes_conjunct (\<psi>s i) p q"
      using dist_conjunction_implies_dist_conjunct 
      by (simp add: distinguishes_conjunct_def hml_models.simps(5))
    then show ?thesis by auto
  qed
qed

lemma srbb_dist_conjunct_or_stable_implies_dist_stable_conjunction:
  assumes "\<forall>i \<in> I. hml_srbb_conjunct_models (\<psi>s i) p"
      and "p \<Turnstile> (HML_not (hml.Obs \<tau> hml.TT))"
      and "(i\<in>I \<and> distinguishes_conjunct (\<psi>s i) p q) \<or> (p <> (HML_not (hml.Obs \<tau> hml.TT)) q)"
  shows "distinguishes_inner (StableConj I \<psi>s) p q"
  using assms
proof -
  assume 
    "\<forall>i \<in> I. hml_srbb_conjunct_models (\<psi>s i) p"
    and p_stable:
    "p \<Turnstile> (HML_not (hml.Obs \<tau> hml.TT))"
    and
    "(i \<in> I \<and> distinguishes_conjunct (\<psi>s i) p q) \<or> (p <> (HML_not (hml.Obs \<tau> hml.TT)) q)"
  hence conj_dist_or_stable_dist:
    "(i \<in> I \<and> distinguishes_conjunct_hml p ((hml_srbb_conjunct_to_hml_conjunct \<circ> \<psi>s) i) q)
      \<or> (p <> (HML_not (hml.Obs \<tau> hml.TT)) q)"
    unfolding dist_conjunct_srbb_eq_dist_conjunct_hml o_apply by auto

  from \<open>\<forall>i \<in> I. hml_srbb_conjunct_models (\<psi>s i) p\<close>
  have p_sat_conj:
       "\<forall>i\<in>I. hml_conjunct_models p ((hml_srbb_conjunct_to_hml_conjunct \<circ> \<psi>s) i)"
    unfolding hml_srbb_conjunct_models.simps o_apply.

  show "distinguishes_inner (StableConj I \<psi>s) p q"
    unfolding dist_inner_srbb_eq_dist_hml
          and hml_srbb_inner_to_hml.simps
          and hml_and_dist_disj
  proof (rule conjI)
    from p_stable and p_sat_conj
    show "p \<Turnstile> hml_conjunct.Neg (hml.Obs \<tau> hml.TT)
              \<and>hml hml_conjunct.Pos (hml.Conj I (hml_srbb_conjunct_to_hml_conjunct \<circ> \<psi>s))" 
      by simp
  next
    from conj_dist_or_stable_dist
    show "\<not> hml_conjunct_models q (hml_conjunct.Neg (hml.Obs \<tau> hml.TT))
        \<or> \<not> hml_conjunct_models q (hml_conjunct.Pos (hml.Conj I (hml_srbb_conjunct_to_hml_conjunct \<circ> \<psi>s)))" 
      using distinguishes_conjunct_hml_def distinguishes_hml_def by auto
  qed
qed

lemma srbb_dist_branch_conjunction_implies_dist_conjunct_or_branch:
  assumes "distinguishes_inner (BranchConj \<alpha> \<phi> I \<psi>s) p q"
  shows "(\<exists>i\<in>I. distinguishes_conjunct (\<psi>s i) p q) \<or> (distinguishes_inner (Obs \<alpha> \<phi>) p q)"
  using assms
proof -
  assume "distinguishes_inner (BranchConj \<alpha> \<phi> I \<psi>s) p q"
  then have
    "p \<Turnstile> hml_conjunct.Pos (HML_soft_poss \<alpha> (hml_srbb_to_hml \<phi>))
         \<and>hml hml_conjunct.Pos (hml.Conj I (hml_srbb_conjunct_to_hml_conjunct \<circ> \<psi>s))"
    and
    "\<not> q \<Turnstile> hml_conjunct.Pos (HML_soft_poss \<alpha> (hml_srbb_to_hml \<phi>))
           \<and>hml hml_conjunct.Pos (hml.Conj I (hml_srbb_conjunct_to_hml_conjunct \<circ> \<psi>s))"
    unfolding distinguishes_inner_def and hml_srbb_inner_models.simps and hml_srbb_inner_to_hml.simps
    by auto

  from \<open>p \<Turnstile> hml_conjunct.Pos (HML_soft_poss \<alpha> (hml_srbb_to_hml \<phi>))
             \<and>hml hml_conjunct.Pos (hml.Conj I (hml_srbb_conjunct_to_hml_conjunct \<circ> \<psi>s))\<close>
  have "p \<Turnstile> HML_soft_poss \<alpha> (hml_srbb_to_hml \<phi>)"
    and "p \<Turnstile> hml.Conj I (hml_srbb_conjunct_to_hml_conjunct \<circ> \<psi>s)"
    unfolding hml_and_and hml_conjunct_models.simps by auto

  from \<open>\<not> q \<Turnstile> hml_conjunct.Pos (HML_soft_poss \<alpha> (hml_srbb_to_hml \<phi>))
           \<and>hml hml_conjunct.Pos (hml.Conj I (hml_srbb_conjunct_to_hml_conjunct \<circ> \<psi>s))\<close>
  show "(\<exists>i\<in>I. distinguishes_conjunct (\<psi>s i) p q) \<or> (distinguishes_inner (Obs \<alpha> \<phi>) p q)"
    unfolding hml_and_and de_Morgan_conj hml_conjunct_models.simps
  proof (rule disjE)
    assume "\<not> q \<Turnstile> HML_soft_poss \<alpha> (hml_srbb_to_hml \<phi>)"
    with \<open>p \<Turnstile> HML_soft_poss \<alpha> (hml_srbb_to_hml \<phi>)\<close>
    have "distinguishes_inner (Obs \<alpha> \<phi>) p q"
      unfolding distinguishes_inner_def hml_srbb_inner_models.simps hml_srbb_inner_to_hml.simps by auto
    then show ?thesis by auto
  next
    assume "\<not> q \<Turnstile> hml.Conj I (hml_srbb_conjunct_to_hml_conjunct \<circ> \<psi>s)"
    with \<open>p \<Turnstile> hml.Conj I (hml_srbb_conjunct_to_hml_conjunct \<circ> \<psi>s)\<close>
    have "\<exists>i\<in>I. distinguishes_conjunct (\<psi>s i) p q"
      by (simp add: distinguishes_conjunct_def)
    then show ?thesis by auto
  qed
qed

lemma srbb_dist_conjunct_or_branch_implies_dist_branch_conjunction:
  assumes "\<forall>i \<in> I. hml_srbb_conjunct_models (\<psi>s i) p"
      and "hml_srbb_inner_models (Obs \<alpha> \<phi>) p"
      and "(i\<in>I \<and> distinguishes_conjunct (\<psi>s i) p q) \<or> (distinguishes_inner (Obs \<alpha> \<phi>) p q)"
  shows "distinguishes_inner (BranchConj \<alpha> \<phi> I \<psi>s) p q"
  using assms
proof -
  assume 
    "\<forall>i \<in> I. hml_srbb_conjunct_models (\<psi>s i) p"
    and p_branch:
    "hml_srbb_inner_models (Obs \<alpha> \<phi>) p"
    and
    "(i \<in> I \<and> distinguishes_conjunct (\<psi>s i) p q) \<or> (distinguishes_inner (Obs \<alpha> \<phi>) p q)"
  hence conj_dist_or_branch_dist:
    "(i \<in> I \<and> distinguishes_conjunct_hml p ((hml_srbb_conjunct_to_hml_conjunct \<circ> \<psi>s) i) q)
      \<or> (p <> (HML_soft_poss \<alpha> (hml_srbb_to_hml \<phi>)) q)"
    unfolding dist_conjunct_srbb_eq_dist_conjunct_hml o_apply dist_inner_srbb_eq_dist_hml by auto

  from \<open>\<forall>i \<in> I. hml_srbb_conjunct_models (\<psi>s i) p\<close>
  have p_sat_conj:
       "\<forall>i\<in>I. hml_conjunct_models p ((hml_srbb_conjunct_to_hml_conjunct \<circ> \<psi>s) i)"
    unfolding hml_srbb_conjunct_models.simps o_apply.

  show "distinguishes_inner (BranchConj \<alpha> \<phi> I \<psi>s) p q"
    unfolding dist_inner_srbb_eq_dist_hml
          and hml_srbb_inner_to_hml.simps
          and hml_and_dist_disj
  proof (rule conjI)
    from p_branch and p_sat_conj
    show "p \<Turnstile> hml_conjunct.Pos (HML_soft_poss \<alpha> (hml_srbb_to_hml \<phi>))
              \<and>hml hml_conjunct.Pos (hml.Conj I (hml_srbb_conjunct_to_hml_conjunct \<circ> \<psi>s))" 
      by simp
  next
    from conj_dist_or_branch_dist
    show "\<not> hml_conjunct_models q (hml_conjunct.Pos (HML_soft_poss \<alpha> (hml_srbb_to_hml \<phi>)))
        \<or> \<not> hml_conjunct_models q (hml_conjunct.Pos (hml.Conj I (hml_srbb_conjunct_to_hml_conjunct \<circ> \<psi>s)))" 
      using distinguishes_conjunct_hml_def distinguishes_hml_def by auto
  qed
qed


definition hml_preordered :: "(('a, 's) hml_srbb) set \<Rightarrow> 's \<Rightarrow> 's \<Rightarrow> bool" where
  "hml_preordered \<phi>s p q \<equiv> \<forall>\<phi> \<in> \<phi>s. p \<Turnstile>SRBB \<phi> \<longrightarrow> q \<Turnstile>SRBB \<phi>"

definition hml_equivalent :: "(('a, 's) hml_srbb) set \<Rightarrow> 's \<Rightarrow> 's \<Rightarrow> bool" where
  "hml_equivalent \<phi>s p q \<equiv> hml_preordered \<phi>s p q \<and> hml_preordered \<phi>s q p"


lemma "hml_preordered \<phi>s p q = (\<forall>\<phi> \<in> \<phi>s. \<not>(distinguishes \<phi> p q))"
  by (simp add: distinguishes_def hml_preordered_def)

lemma "hml_equivalent \<phi>s p q = (\<forall>\<phi> \<in> \<phi>s. \<not>(distinguishes \<phi> p q) \<and> \<not>(distinguishes \<phi> q p))"
  using distinguishes_def hml_equivalent_def hml_preordered_def by auto

lemma "equivp (hml_equivalent \<phi>s)"
proof (rule equivpI)
  show "reflp (hml_equivalent \<phi>s)" 
    by (simp add: hml_equivalent_def hml_preordered_def reflpI)
next
  show "symp (hml_equivalent \<phi>s)" 
    by (metis hml_equivalent_def sympI)
next
  show "transp (hml_equivalent \<phi>s)" 
    by (smt (verit) hml_equivalent_def hml_preordered_def transpI)
qed

lemma "reflp (hml_preordered \<phi>s) \<and> transp (hml_preordered \<phi>s)"
proof (rule conjI)
  show "reflp (hml_preordered \<phi>s)" 
    by (simp add: hml_preordered_def reflpI)
next
  show "transp (hml_preordered \<phi>s)" 
    by (smt (verit, best) hml_preordered_def transpI)
qed

lemma
  assumes "\<phi>s \<subseteq> \<phi>s'"
      and "hml_equivalent \<phi>s' p q"
  shows "hml_equivalent \<phi>s p q"
  using assms
  by (meson hml_equivalent_def hml_preordered_def subsetD)

lemma "hml_preordered \<phi>s p q = (\<forall>\<phi> \<in> \<phi>s. \<not>(distinguishes \<phi> p q))"
  using distinguishes_def hml_preordered_def by auto

lemma "hml_equivalent \<phi>s p q = (\<forall>\<phi> \<in> \<phi>s. \<not>(distinguishes \<phi> p q) \<and> \<not>(distinguishes \<phi> q p))"
  using distinguishes_def hml_equivalent_def hml_preordered_def by auto


subsection \<open> \<open>hml_srbb\<close> Implication \<close>

definition hml_srbb_impl :: "('a, 's) hml_srbb \<Rightarrow> ('a, 's) hml_srbb \<Rightarrow> bool" (infix "\<Rrightarrow>" 70) where
  "\<phi>l \<Rrightarrow> \<phi>r \<equiv> \<forall>p. p \<Turnstile>SRBB \<phi>l \<longrightarrow> p \<Turnstile>SRBB \<phi>r"

lemma srbb_impl_to_hml_impl:
  fixes \<phi>l and \<phi>r :: "('a, 's) hml_srbb"
  assumes "\<phi>l \<Rrightarrow> \<phi>r"
  shows "hml_srbb_to_hml \<phi>l \<Rrightarrow> hml_srbb_to_hml \<phi>r"
  using assms
  by (simp add: LTS_Tau.hml_impl_iffI hml_srbb_impl_def)

lemma hml_srbb_impl_preord: "reflp (hml_srbb_impl) \<and> transp (hml_srbb_impl)"
  by (metis hml_srbb_impl_def reflpI transpI)


definition hml_srbb_impl_inner :: "('a, 's) hml_srbb_inner \<Rightarrow> ('a, 's) hml_srbb_inner \<Rightarrow> bool" (infix "\<chi>\<Rrightarrow>" 70) where
  "\<chi>l \<chi>\<Rrightarrow> \<chi>r \<equiv> \<forall>p. hml_srbb_inner_models \<chi>l p \<longrightarrow> hml_srbb_inner_models \<chi>r p"

lemma hml_srbb_impl_inner_preord: "reflp (hml_srbb_impl_inner) \<and> transp (hml_srbb_impl_inner)"
  by (metis hml_srbb_impl_inner_def reflpI transpI)

lemma srbb_impl_inner_to_hml_impl:
  assumes "\<chi>l \<chi>\<Rrightarrow> \<chi>r"
  shows "hml_srbb_inner_to_hml \<chi>l \<Rrightarrow> hml_srbb_inner_to_hml \<chi>r"
  using assms
  by (simp add: LTS_Tau.hml_impl_iffI hml_srbb_impl_inner_def)


definition hml_srbb_impl_conjunct :: "('a, 's) hml_srbb_conjunct \<Rightarrow> ('a, 's) hml_srbb_conjunct \<Rightarrow> bool" (infix "\<psi>\<Rrightarrow>" 70) where
  "\<psi>l \<psi>\<Rrightarrow> \<psi>r \<equiv> \<forall>p. hml_srbb_conjunct_models \<psi>l p \<longrightarrow> hml_srbb_conjunct_models \<psi>r p"

lemma hml_srbb_impl_conjunct_preord: "reflp (hml_srbb_impl_conjunct) \<and> transp (hml_srbb_impl_conjunct)"
  by (metis hml_srbb_impl_conjunct_def reflpI transpI)

lemma srbb_impl_conjunct_to_hml_impl:
  assumes "\<psi>l \<psi>\<Rrightarrow> \<psi>r"
  shows "hml_srbb_conjunct_to_hml_conjunct \<psi>l \<and>\<Rrightarrow> hml_srbb_conjunct_to_hml_conjunct \<psi>r"
  using assms
  by (simp add: hml_conjunct_impl_def hml_srbb_impl_conjunct_def)


subsection \<open> \<open>hml__srbb\<close> Equivalence \<close>

definition hml_srbb_eq :: "('a, 's) hml_srbb \<Rightarrow> ('a, 's) hml_srbb \<Rightarrow> bool" (infix "\<Lleftarrow>srbb\<Rrightarrow>" 70) where
  "\<phi>l \<Lleftarrow>srbb\<Rrightarrow> \<phi>r \<equiv> \<phi>l \<Rrightarrow> \<phi>r \<and> \<phi>r \<Rrightarrow> \<phi>l"

lemma hml_srbb_eq_iff: "\<phi>l \<Lleftarrow>srbb\<Rrightarrow> \<phi>r = (\<forall>p. p \<Turnstile>SRBB \<phi>l \<longleftrightarrow> p \<Turnstile>SRBB \<phi>r)"
  using hml_srbb_eq_def hml_srbb_impl_def by blast

lemma srbb_eq_hml_eq:
  shows "\<phi>l \<Lleftarrow>srbb\<Rrightarrow> \<phi>r = (hml_srbb_to_hml \<phi>l \<Lleftarrow>\<Rrightarrow> hml_srbb_to_hml \<phi>r)"
  by (simp add: hml_eq_equality hml_srbb_eq_iff)

lemma hml_srbb_eq_equiv: "equivp (\<Lleftarrow>srbb\<Rrightarrow>)"
  by (smt (verit, ccfv_threshold) equivpI hml_srbb_eq_def hml_srbb_impl_preord reflp_on_def sympI transpE transpI)


definition hml_srbb_eq_inner :: "('a, 's) hml_srbb_inner \<Rightarrow> ('a, 's) hml_srbb_inner \<Rightarrow> bool" (infix "\<Lleftarrow>\<chi>\<Rrightarrow>" 70) where
  "\<chi>l \<Lleftarrow>\<chi>\<Rrightarrow> \<chi>r \<equiv> \<chi>l \<chi>\<Rrightarrow> \<chi>r \<and> \<chi>r \<chi>\<Rrightarrow> \<chi>l"

lemma hml_srbb_eq_inner_iff: "\<chi>l \<Lleftarrow>\<chi>\<Rrightarrow> \<chi>r = (\<forall>p. hml_srbb_inner_models \<chi>l p  \<longleftrightarrow> hml_srbb_inner_models \<chi>r p)"
  using hml_srbb_eq_inner_def hml_srbb_impl_inner_def by blast

lemma srbb_eq_inner_hml_eq:
  shows "\<chi>l \<Lleftarrow>\<chi>\<Rrightarrow> \<chi>r = (hml_srbb_inner_to_hml \<chi>l \<Lleftarrow>\<Rrightarrow> hml_srbb_inner_to_hml \<chi>r)"
  by (simp add: hml_eq_equality hml_srbb_eq_inner_iff)

lemma hml_srbb_eq_inner_equiv: "equivp (\<Lleftarrow>\<chi>\<Rrightarrow>)"
  using hml_srbb_impl_inner_preord
  by (smt (verit, best) hml_srbb_eq_inner_def Inhabited_Tau_LTS_axioms equivpI reflpD reflpI symp_def transpE transpI)


definition hml_srbb_eq_conjunct :: "('a, 's) hml_srbb_conjunct \<Rightarrow> ('a, 's) hml_srbb_conjunct \<Rightarrow> bool" (infix "\<Lleftarrow>\<psi>\<Rrightarrow>" 70) where
  "\<psi>l \<Lleftarrow>\<psi>\<Rrightarrow> \<psi>r \<equiv> \<psi>l \<psi>\<Rrightarrow> \<psi>r \<and> \<psi>r \<psi>\<Rrightarrow> \<psi>l"

lemma hml_srbb_eq_conjunct_iff: "\<psi>l \<Lleftarrow>\<psi>\<Rrightarrow> \<psi>r = (\<forall>p. hml_srbb_conjunct_models \<psi>l p  \<longleftrightarrow> hml_srbb_conjunct_models \<psi>r p)"
  using hml_srbb_eq_conjunct_def hml_srbb_impl_conjunct_def by blast

lemma srbb_eq_conjunct_hml_conjunct_eq:
  shows "\<psi>l \<Lleftarrow>\<psi>\<Rrightarrow> \<psi>r = (hml_srbb_conjunct_to_hml_conjunct \<psi>l \<Lleftarrow>\<and>\<Rrightarrow> hml_srbb_conjunct_to_hml_conjunct \<psi>r)"
  using hml_conjunct_eq_def hml_conjunct_impl_def hml_srbb_eq_conjunct_iff by auto

lemma hml_srbb_eq_conjunct_equiv: "equivp (\<Lleftarrow>\<psi>\<Rrightarrow>)"
  using equivp_def hml_srbb_eq_conjunct_iff by fastforce


subsection \<open> Substitution \<close>

lemma srbb_internal_subst:
  assumes "\<chi>l \<Lleftarrow>\<chi>\<Rrightarrow> \<chi>r"
      and "\<phi> \<Lleftarrow>srbb\<Rrightarrow> (Internal \<chi>l)"
    shows "\<phi> \<Lleftarrow>srbb\<Rrightarrow> (Internal \<chi>r)"
  by (smt (verit) assms(1) assms(2) hml_impl_iffI hml_models.simps(3) hml_srbb_eq_def hml_srbb_eq_inner_def hml_srbb_impl_def hml_srbb_models.elims(2) hml_srbb_models.elims(3) hml_srbb_to_hml.simps(2) srbb_impl_inner_to_hml_impl)


subsection \<open> Congruence \<close>

lemma internal_srbb_cong:
  assumes "\<chi>l \<Lleftarrow>\<chi>\<Rrightarrow> \<chi>r"
  shows "(Internal \<chi>l) \<Lleftarrow>srbb\<Rrightarrow> (Internal \<chi>r)"
  using assms
  by (smt (verit) hml_models.simps(3) hml_srbb_inner_models.elims(2) hml_srbb_inner_models.elims(3) hml_srbb_eq_inner_def hml_srbb_eq_def hml_srbb_impl_inner_def hml_srbb_impl_def hml_srbb_models.elims(2) hml_srbb_models.elims(3) hml_srbb_to_hml.simps(2))

lemma immconj_cong:
  assumes "\<psi>sl ` I = \<psi>sr ` I"
      and "\<psi>sl s \<Lleftarrow>\<psi>\<Rrightarrow> \<psi>sr s"
  shows "ImmConj (I \<union> {s}) \<psi>sl \<Lleftarrow>srbb\<Rrightarrow> ImmConj (I \<union> {s}) \<psi>sr"
  using assms
proof -
  assume "\<psi>sl ` I = \<psi>sr ` I"
    and "\<psi>sl s \<Lleftarrow>\<psi>\<Rrightarrow> \<psi>sr s"
  then have "(\<forall>p. hml_srbb_conjunct_models (\<psi>sl s) p \<longrightarrow> hml_srbb_conjunct_models (\<psi>sr s) p) \<and>
             (\<forall>p. hml_srbb_conjunct_models (\<psi>sr s) p \<longrightarrow> hml_srbb_conjunct_models (\<psi>sl s) p)"
    unfolding hml_srbb_eq_conjunct_def and hml_srbb_impl_conjunct_def by auto
  then have "\<forall>p. hml_srbb_conjunct_models (\<psi>sl s) p \<longrightarrow> hml_srbb_conjunct_models (\<psi>sr s) p"
        and "\<forall>p. hml_srbb_conjunct_models (\<psi>sr s) p \<longrightarrow> hml_srbb_conjunct_models (\<psi>sl s) p" by auto

  show "ImmConj (I \<union> {s}) \<psi>sl \<Lleftarrow>srbb\<Rrightarrow> ImmConj (I \<union> {s}) \<psi>sr"
    unfolding hml_srbb_eq_def
          and hml_srbb_impl_def
          and hml_srbb_models.simps
          and hml_srbb_to_hml.simps
          and hml_models.simps
  proof (rule conjI)
    show "\<forall>p. (\<forall>i\<in>I \<union> {s}. hml_conjunct_models p ((hml_srbb_conjunct_to_hml_conjunct \<circ> \<psi>sl) i)) \<longrightarrow>
              (\<forall>i\<in>I \<union> {s}. hml_conjunct_models p ((hml_srbb_conjunct_to_hml_conjunct \<circ> \<psi>sr) i))"
    proof (rule allI, rule impI)
      fix p
      assume "\<forall>i\<in>I \<union> {s}. hml_conjunct_models p ((hml_srbb_conjunct_to_hml_conjunct \<circ> \<psi>sl) i)"
      then have "(hml_conjunct_models p ((hml_srbb_conjunct_to_hml_conjunct \<circ> \<psi>sl) s))
               \<and> (\<forall>i\<in>I. hml_conjunct_models p ((hml_srbb_conjunct_to_hml_conjunct \<circ> \<psi>sl) i))"
        by fastforce
      then have "hml_conjunct_models p ((hml_srbb_conjunct_to_hml_conjunct \<circ> \<psi>sl) s)"
            and "\<forall>i\<in>I. hml_conjunct_models p ((hml_srbb_conjunct_to_hml_conjunct \<circ> \<psi>sl) i)" by auto

      from \<open>hml_conjunct_models p ((hml_srbb_conjunct_to_hml_conjunct \<circ> \<psi>sl) s)\<close>
       and \<open>\<forall>p. hml_srbb_conjunct_models (\<psi>sl s) p \<longrightarrow> hml_srbb_conjunct_models (\<psi>sr s) p\<close>
      have "hml_conjunct_models p ((hml_srbb_conjunct_to_hml_conjunct \<circ> \<psi>sr) s)" 
        by simp

      from \<open>\<psi>sl ` I = \<psi>sr ` I\<close> and \<open>\<forall>i\<in>I. hml_conjunct_models p ((hml_srbb_conjunct_to_hml_conjunct \<circ> \<psi>sl) i)\<close>
      have "\<forall>i\<in>I. hml_conjunct_models p ((hml_srbb_conjunct_to_hml_conjunct \<circ> \<psi>sr) i)" 
        by (metis comp_apply image_iff)

      from \<open>hml_conjunct_models p ((hml_srbb_conjunct_to_hml_conjunct \<circ> \<psi>sr) s)\<close>
       and \<open>\<forall>i\<in>I. hml_conjunct_models p ((hml_srbb_conjunct_to_hml_conjunct \<circ> \<psi>sr) i)\<close>
      show "\<forall>i\<in>I \<union> {s}. hml_conjunct_models p ((hml_srbb_conjunct_to_hml_conjunct \<circ> \<psi>sr) i)" 
        by fastforce
    qed
  next
    show "\<forall>p. (\<forall>i\<in>I \<union> {s}. hml_conjunct_models p ((hml_srbb_conjunct_to_hml_conjunct \<circ> \<psi>sr) i)) \<longrightarrow>
              (\<forall>i\<in>I \<union> {s}. hml_conjunct_models p ((hml_srbb_conjunct_to_hml_conjunct \<circ> \<psi>sl) i))"
    proof (rule allI, rule impI)
      fix p
      assume "\<forall>i\<in>I \<union> {s}. hml_conjunct_models p ((hml_srbb_conjunct_to_hml_conjunct \<circ> \<psi>sr) i)"
      then have "(hml_conjunct_models p ((hml_srbb_conjunct_to_hml_conjunct \<circ> \<psi>sr) s))
               \<and> (\<forall>i\<in>I. hml_conjunct_models p ((hml_srbb_conjunct_to_hml_conjunct \<circ> \<psi>sr) i))"
        by fastforce
      then have "hml_conjunct_models p ((hml_srbb_conjunct_to_hml_conjunct \<circ> \<psi>sr) s)"
            and "\<forall>i\<in>I. hml_conjunct_models p ((hml_srbb_conjunct_to_hml_conjunct \<circ> \<psi>sr) i)" by auto

      from \<open>hml_conjunct_models p ((hml_srbb_conjunct_to_hml_conjunct \<circ> \<psi>sr) s)\<close>
       and \<open>\<forall>p. hml_srbb_conjunct_models (\<psi>sr s) p \<longrightarrow> hml_srbb_conjunct_models (\<psi>sl s) p\<close>
      have "hml_conjunct_models p ((hml_srbb_conjunct_to_hml_conjunct \<circ> \<psi>sl) s)" 
        by simp

      from \<open>\<psi>sl ` I = \<psi>sr ` I\<close>
       and \<open>\<forall>i\<in>I. hml_conjunct_models p ((hml_srbb_conjunct_to_hml_conjunct \<circ> \<psi>sr) i)\<close>
      have "\<forall>i\<in>I. hml_conjunct_models p ((hml_srbb_conjunct_to_hml_conjunct \<circ> \<psi>sl) i)"
        by (smt (verit, ccfv_SIG) image_eq_imp_comp image_iff)

      from \<open>hml_conjunct_models p ((hml_srbb_conjunct_to_hml_conjunct \<circ> \<psi>sl) s)\<close>
       and \<open>\<forall>i\<in>I. hml_conjunct_models p ((hml_srbb_conjunct_to_hml_conjunct \<circ> \<psi>sl) i)\<close>
      show "\<forall>i\<in>I \<union> {s}. hml_conjunct_models p ((hml_srbb_conjunct_to_hml_conjunct \<circ> \<psi>sl) i)" 
        by fastforce
    qed
  qed
qed

lemma obs_srbb_cong:
  assumes "\<phi>l \<Lleftarrow>srbb\<Rrightarrow> \<phi>r"
  shows "(Obs \<alpha> \<phi>l) \<Lleftarrow>\<chi>\<Rrightarrow> (Obs \<alpha> \<phi>r)"
  using assms 
  apply (cases "\<alpha> \<noteq> \<tau>")
  apply (smt (verit) hml_impl_iffI hml_models.simps(2) hml_srbb_eq_def hml_srbb_eq_inner_def hml_srbb_impl_inner_def hml_srbb_inner_models.elims(2) hml_srbb_inner_models.elims(3) hml_srbb_inner_to_hml.simps(1) srbb_impl_to_hml_impl)
  using hml_impl_iffI hml_models.simps(4) hml_srbb_eq_def hml_srbb_eq_inner_def hml_srbb_impl_inner_def hml_srbb_inner_models.elims(2) hml_srbb_inner_models.elims(3) hml_srbb_inner_to_hml.simps(1) srbb_impl_to_hml_impl by auto

subsection \<open> Known Equivalence Elements \<close>

lemma srbb_obs_\<tau>_is_\<chi>TT: "Obs \<tau> TT \<Lleftarrow>\<chi>\<Rrightarrow> Conj {} \<psi>s"
  by (simp add: hml_srbb_eq_inner_def hml_srbb_impl_inner_def)

lemma srbb_obs_is_empty_branch_conj: "Obs \<alpha> \<phi> \<Lleftarrow>\<chi>\<Rrightarrow> BranchConj \<alpha> \<phi> {} \<psi>s"
  unfolding srbb_eq_inner_hml_eq and hml_srbb_inner_to_hml.simps
proof -
  from T_is_empty_conj
  have "hml.Conj {} (hml_srbb_conjunct_to_hml_conjunct \<circ> \<psi>s) \<Lleftarrow>\<Rrightarrow> hml.TT" 
    using hml_eq_equality by force
  have    "(hml_conjunct.Pos (HML_soft_poss \<alpha> (hml_srbb_to_hml \<phi>))
      \<and>hml hml_conjunct.Pos (hml.Conj {} (hml_srbb_conjunct_to_hml_conjunct \<circ> \<psi>s)))
  \<Lleftarrow>\<Rrightarrow>      (hml_conjunct.Pos (HML_soft_poss \<alpha> (hml_srbb_to_hml \<phi>))
      \<and>hml hml_conjunct.Pos (hml.Conj {} (hml_srbb_conjunct_to_hml_conjunct \<circ> \<psi>s)))"
    using hml_eq_equality by blast
  then have "(hml_conjunct.Pos (HML_soft_poss \<alpha> (hml_srbb_to_hml \<phi>))
      \<and>hml hml_conjunct.Pos (hml.Conj {} (hml_srbb_conjunct_to_hml_conjunct \<circ> \<psi>s)))
  \<Lleftarrow>\<Rrightarrow>      (hml_conjunct.Pos (HML_soft_poss \<alpha> (hml_srbb_to_hml \<phi>))
      \<and>hml hml_conjunct.Pos hml.TT)"
    using and_subst_right[OF pos_cong[OF \<open>hml.Conj {} (hml_srbb_conjunct_to_hml_conjunct \<circ> \<psi>s) \<Lleftarrow>\<Rrightarrow> hml.TT\<close>]] by auto
  then have "(hml_conjunct.Pos (HML_soft_poss \<alpha> (hml_srbb_to_hml \<phi>))
      \<and>hml hml_conjunct.Pos (hml.Conj {} (hml_srbb_conjunct_to_hml_conjunct \<circ> \<psi>s)))
  \<Lleftarrow>\<Rrightarrow>      (HML_soft_poss \<alpha> (hml_srbb_to_hml \<phi>))"
    using hml_and_right_tt 
    by (simp add: LTS_Tau.hml_eq_equality)
  then show "HML_soft_poss \<alpha> (hml_srbb_to_hml \<phi>) \<Lleftarrow>\<Rrightarrow>
    hml_conjunct.Pos
     (HML_soft_poss \<alpha> (hml_srbb_to_hml \<phi>)) \<and>hml hml_conjunct.Pos (hml.Conj {} (hml_srbb_conjunct_to_hml_conjunct \<circ> \<psi>s))"
    by (meson LTS_Tau.hml_eq_equality)
qed

lemma srbb_TT_is_\<chi>TT: "TT \<Lleftarrow>srbb\<Rrightarrow> Internal (Conj {} \<psi>s)"
  using \<epsilon>T_is_T hml_eq_def hml_impl_iffI hml_srbb_eq_def hml_srbb_impl_def by auto

lemma srbb_TT_is_empty_conj: "TT \<Lleftarrow>srbb\<Rrightarrow> ImmConj {} \<psi>s"
  by (simp add: hml_srbb_eq_def hml_srbb_impl_def)

subsection \<open> Distinguishing Conjunction Thinning \<close>

text \<open>
The following four lemmata (dist\_...\_thinn) lift the result
  [that a conjunction which distinguishes
   a process p from a set of processes Q may be reduced (thinned) to have at most one conjunct per
   element of Q while still being able to distinguish p from Q]
  (dist\_conj\_thinning)
from unrestricted hml to hml\_srbb.
\<close>

lemma extract_converter:
  assumes "p <> (hml.Conj Q (\<lambda>q. (f \<circ> \<psi>s) (SOME i. i \<in> I \<and> \<not>(hml_conjunct_models q ((f \<circ> \<psi>s) i))))) Q"
  shows "p <> (hml.Conj Q (f \<circ> (\<lambda>q. \<psi>s (SOME i. i \<in> I \<and> \<not>(hml_conjunct_models q ((f \<circ> \<psi>s) i)))))) Q"
  using assms and comp_apply
  by (simp add: LTS_Tau.distinguishes_hml_def distinguishes_from_hml_def)


lemma dist_immconj_thinn:
  defines 
    "distinguishing_conjunct \<equiv> (\<lambda>I.\<lambda>\<psi>s.
       \<lambda>q. \<psi>s (SOME i. i \<in> I \<and> \<not>(hml_srbb_conjunct_models (\<psi>s i) q)))"
  assumes "distinguishes_from (ImmConj I \<psi>s) p Q"
  shows "distinguishes_from (ImmConj Q (distinguishing_conjunct I \<psi>s)) p Q"
  using assms
  unfolding distinguishes_from_def
        and distinguishes_def
        and hml_srbb_models.simps
        and hml_srbb_to_hml.simps
        and distinguishing_conjunct_def
proof -
  assume "p \<Turnstile> hml.Conj I (hml_srbb_conjunct_to_hml_conjunct \<circ> \<psi>s) \<and>
           (\<forall>q\<in>Q. \<not> q \<Turnstile> hml.Conj I (hml_srbb_conjunct_to_hml_conjunct \<circ> \<psi>s))"
  hence "p <> (hml.Conj I (hml_srbb_conjunct_to_hml_conjunct \<circ> \<psi>s)) Q"
    by (simp add: LTS_Tau.distinguishes_hml_def distinguishes_from_hml_def)

  with dist_conj_thinning
  have "p <> (hml.Conj Q (\<lambda>q. (hml_srbb_conjunct_to_hml_conjunct \<circ> \<psi>s) (SOME i. i \<in> I \<and> \<not>(hml_conjunct_models q ((hml_srbb_conjunct_to_hml_conjunct \<circ> \<psi>s) i))))) Q"
    by blast

  with extract_converter
  have "p <> (hml.Conj Q (hml_srbb_conjunct_to_hml_conjunct \<circ> (\<lambda>q. \<psi>s (SOME i. i \<in> I \<and> \<not>(hml_conjunct_models q ((hml_srbb_conjunct_to_hml_conjunct \<circ> \<psi>s) i)))))) Q"
    by auto

  then show "p \<Turnstile> hml.Conj Q
                (hml_srbb_conjunct_to_hml_conjunct \<circ> (\<lambda>q. \<psi>s (SOME i. i \<in> I \<and> \<not> hml_srbb_conjunct_models (\<psi>s i) q))) \<and>
           (\<forall>q\<in>Q. \<not> q \<Turnstile> hml.Conj Q
                   (hml_srbb_conjunct_to_hml_conjunct \<circ> (\<lambda>q. \<psi>s (SOME i. i \<in> I \<and> \<not> hml_srbb_conjunct_models (\<psi>s i) q))))"
    unfolding distinguishes_from_hml_def and distinguishes_hml_def and hml_srbb_conjunct_models.simps and comp_apply
    by blast
qed


lemma dist_conj_thinn:
  defines 
    "distinguishing_conjunct \<equiv> (\<lambda>I.\<lambda>\<psi>s.
       \<lambda>q. \<psi>s (SOME i. i \<in> I \<and> \<not>(hml_srbb_conjunct_models (\<psi>s i) q)))"
  assumes "distinguishes_from_inner (Conj I \<psi>s) p Q"
  shows "distinguishes_from_inner (Conj Q (distinguishing_conjunct I \<psi>s)) p Q"
  using assms
  unfolding distinguishes_from_inner_def
        and distinguishes_inner_def
        and hml_srbb_inner_models.simps
        and hml_srbb_inner_to_hml.simps
        and distinguishing_conjunct_def
proof -
  assume "p \<Turnstile> hml.Conj I (hml_srbb_conjunct_to_hml_conjunct \<circ> \<psi>s) \<and>
           (\<forall>q\<in>Q. \<not> q \<Turnstile> hml.Conj I (hml_srbb_conjunct_to_hml_conjunct \<circ> \<psi>s))"
  hence "p <> (hml.Conj I (hml_srbb_conjunct_to_hml_conjunct \<circ> \<psi>s)) Q"
    by (simp add: LTS_Tau.distinguishes_hml_def distinguishes_from_hml_def)

  with dist_conj_thinning
  have "p <> (hml.Conj Q (\<lambda>q. (hml_srbb_conjunct_to_hml_conjunct \<circ> \<psi>s) (SOME i. i \<in> I \<and> \<not>(hml_conjunct_models q ((hml_srbb_conjunct_to_hml_conjunct \<circ> \<psi>s) i))))) Q"
    by blast

  with extract_converter
  have "p <> (hml.Conj Q (hml_srbb_conjunct_to_hml_conjunct \<circ> (\<lambda>q. \<psi>s (SOME i. i \<in> I \<and> \<not>(hml_conjunct_models q ((hml_srbb_conjunct_to_hml_conjunct \<circ> \<psi>s) i)))))) Q"
    by auto

  then have "p <> (hml.Conj Q (hml_srbb_conjunct_to_hml_conjunct \<circ> (\<lambda>q. \<psi>s (SOME i. i \<in> I \<and> \<not>(hml_conjunct_models q (hml_srbb_conjunct_to_hml_conjunct (\<psi>s i))))))) Q"
    using comp_apply by auto

  then have "p <> (hml.Conj Q (hml_srbb_conjunct_to_hml_conjunct \<circ> (\<lambda>q. \<psi>s (SOME i. i \<in> I \<and> \<not>(hml_srbb_conjunct_models (\<psi>s i) q))))) Q"
    using hml_srbb_conjunct_models.simps by auto

  then show "p \<Turnstile> hml.Conj Q
                (hml_srbb_conjunct_to_hml_conjunct \<circ> (\<lambda>q. \<psi>s (SOME i. i \<in> I \<and> \<not> hml_srbb_conjunct_models (\<psi>s i) q))) \<and>
           (\<forall>q\<in>Q. \<not> q \<Turnstile> hml.Conj Q
                   (hml_srbb_conjunct_to_hml_conjunct \<circ> (\<lambda>q. \<psi>s (SOME i. i \<in> I \<and> \<not> hml_srbb_conjunct_models (\<psi>s i) q))))"
    unfolding distinguishes_from_hml_def and distinguishes_hml_def by auto
qed


lemma dist_stableconj_thinn:
  defines 
    "distinguishing_conjunct \<equiv> (\<lambda>I.\<lambda>\<psi>s.
       \<lambda>q. if I = {}
           then Pos (Conj {} undefined)
           else if \<exists>i \<in> I. \<not>(hml_srbb_conjunct_models (\<psi>s i) q)
                then \<psi>s (SOME i. i \<in> I \<and> \<not>(hml_srbb_conjunct_models (\<psi>s i) q))
                else \<psi>s (SOME i. i \<in> I))"
  (* These if-then-else's are necessary, as the distinction might come from the stability condition.
     If that is the case then the stability condition could be the only distinction from some or even all elements of Q.
     Due to the way that StableConj is translated (via two stacked conjunctions, c.f. the translate function),
     this can lead to the situation where I might be empty (i.e. there are no conjuncts apart from the stability
     condition) or there may be conjuncts via I, but some elements of Q model all of these (i.e. so they are
     distinguished from p only via the stability condition).  Since we want to pick a conjunct for each element in Q,
     we must describe what to do in these cases. *)
  assumes "distinguishes_from_inner (StableConj I \<psi>s) p Q"
  shows "distinguishes_from_inner (StableConj Q (distinguishing_conjunct I \<psi>s)) p Q"
  using assms
  unfolding distinguishes_from_inner_def
        and distinguishes_inner_def
        and hml_srbb_inner_models.simps
        and hml_srbb_inner_to_hml.simps
proof -
  assume "p \<Turnstile> hml_conjunct.Neg (hml.Obs \<tau> hml.TT)
                       \<and>hml hml_conjunct.Pos (hml.Conj I (hml_srbb_conjunct_to_hml_conjunct \<circ> \<psi>s))
                 \<and> (\<forall>q\<in>Q. \<not> q \<Turnstile> hml_conjunct.Neg (hml.Obs \<tau> hml.TT)
                       \<and>hml hml_conjunct.Pos (hml.Conj I (hml_srbb_conjunct_to_hml_conjunct \<circ> \<psi>s)))"

  then have "p \<Turnstile> hml_conjunct.Neg (hml.Obs \<tau> hml.TT)
                        \<and>hml hml_conjunct.Pos (hml.Conj I (hml_srbb_conjunct_to_hml_conjunct \<circ> \<psi>s))
                 \<and> (\<forall>q\<in>Q. (\<not> hml_conjunct_models q (hml_conjunct.Neg (hml.Obs \<tau> hml.TT))
                 \<or> \<not> hml_conjunct_models q (hml_conjunct.Pos (hml.Conj I (hml_srbb_conjunct_to_hml_conjunct \<circ> \<psi>s)))))"
    unfolding hml_and_dist_disj hml_and_and by blast
  hence p_models_stable_conj:
    "p \<Turnstile> hml_conjunct.Neg (hml.Obs \<tau> hml.TT)
                \<and>hml hml_conjunct.Pos (hml.Conj I (hml_srbb_conjunct_to_hml_conjunct \<circ> \<psi>s))"
    and no_q_models_stable_conj:
    "\<forall>q\<in>Q. \<not> hml_conjunct_models q (hml_conjunct.Neg (hml.Obs \<tau> hml.TT))
         \<or> \<not> hml_conjunct_models q (hml_conjunct.Pos (hml.Conj I (hml_srbb_conjunct_to_hml_conjunct \<circ> \<psi>s)))"
    by auto

  show "p \<Turnstile> hml_conjunct.Neg (hml.Obs \<tau> hml.TT)
                  \<and>hml hml_conjunct.Pos (hml.Conj Q (hml_srbb_conjunct_to_hml_conjunct \<circ> distinguishing_conjunct I \<psi>s))
            \<and> (\<forall>q\<in>Q. \<not> q \<Turnstile> hml_conjunct.Neg (hml.Obs \<tau> hml.TT)
                    \<and>hml hml_conjunct.Pos (hml.Conj Q (hml_srbb_conjunct_to_hml_conjunct \<circ> distinguishing_conjunct I \<psi>s)))"
  proof (rule conjI)
    from p_models_stable_conj and hml_and_and
    have "hml_conjunct_models p (hml_conjunct.Neg (hml.Obs \<tau> hml.TT))
        \<and> hml_conjunct_models p (hml_conjunct.Pos (hml.Conj I (hml_srbb_conjunct_to_hml_conjunct \<circ> \<psi>s)))"
      by blast
    hence "hml_conjunct_models p (hml_conjunct.Neg (hml.Obs \<tau> hml.TT))"
      and "hml_conjunct_models p (hml_conjunct.Pos (hml.Conj I (hml_srbb_conjunct_to_hml_conjunct \<circ> \<psi>s)))"
      by auto
    then have "p \<Turnstile> hml.Conj I (hml_srbb_conjunct_to_hml_conjunct \<circ> \<psi>s)"
      unfolding hml_conjunct_models.simps by auto

    from \<open>hml_conjunct_models p (hml_conjunct.Neg (hml.Obs \<tau> hml.TT))\<close>
    show "p \<Turnstile> hml_conjunct.Neg (hml.Obs \<tau> hml.TT)
              \<and>hml hml_conjunct.Pos (hml.Conj Q (hml_srbb_conjunct_to_hml_conjunct \<circ> distinguishing_conjunct I \<psi>s))"
      unfolding hml_and_and and hml_conjunct_models.simps
    proof (rule conjI)
      from \<open>p \<Turnstile> hml.Conj I (hml_srbb_conjunct_to_hml_conjunct \<circ> \<psi>s)\<close>
       and models_full_models_dist_subset'
      have "p \<Turnstile> hml.Conj Q
           (\<lambda>q. if I = {} then hml_conjunct.Pos (hml.Internal (hml.Conj {} (hml_srbb_conjunct_to_hml_conjunct \<circ> undefined)))
                else (if \<exists>i\<in>I. \<not> hml_conjunct_models q ((hml_srbb_conjunct_to_hml_conjunct \<circ> \<psi>s) i)
                     then (hml_srbb_conjunct_to_hml_conjunct \<circ> \<psi>s) (SOME i. i \<in> I \<and> \<not> hml_conjunct_models q ((hml_srbb_conjunct_to_hml_conjunct \<circ> \<psi>s) i))
                     else (hml_srbb_conjunct_to_hml_conjunct \<circ> \<psi>s) (SOME i. i \<in> I)))" by simp

      then have "p \<Turnstile> hml.Conj Q
           (\<lambda>q. if I = {} then hml_srbb_conjunct_to_hml_conjunct (hml_srbb_conjunct.Pos (hml_srbb_inner.Conj {} undefined))
                else (if \<exists>i\<in>I. \<not> hml_conjunct_models q (hml_srbb_conjunct_to_hml_conjunct (\<psi>s i))
                     then (hml_srbb_conjunct_to_hml_conjunct \<circ> \<psi>s) (SOME i. i \<in> I \<and> \<not> hml_conjunct_models q (hml_srbb_conjunct_to_hml_conjunct (\<psi>s i)))
                     else (hml_srbb_conjunct_to_hml_conjunct \<circ> \<psi>s) (SOME i. i \<in> I)))"
        unfolding hml_models.simps(5)
              and comp_apply
              and hml_srbb_conjunct_to_hml_conjunct.simps
              and hml_srbb_inner_to_hml.simps.

      then show "p \<Turnstile> hml.Conj Q (hml_srbb_conjunct_to_hml_conjunct \<circ> distinguishing_conjunct I \<psi>s)"
        unfolding distinguishing_conjunct_def
              and hml_srbb_conjunct_models.simps
        by (smt (verit, ccfv_threshold) LTS_Tau.hml_models.simps(5) comp_apply)
    qed
  next
    from no_q_models_stable_conj
    have "\<forall>q\<in>Q. \<not> hml_conjunct_models q (hml_conjunct.Neg (hml.Obs \<tau> hml.TT))
         \<or> \<not> hml_conjunct_models q (hml_conjunct.Pos (hml.Conj I (hml_srbb_conjunct_to_hml_conjunct \<circ> \<psi>s)))"
      by auto
    show "\<forall>q\<in>Q. \<not> q \<Turnstile> hml_conjunct.Neg (hml.Obs \<tau> hml.TT)
                 \<and>hml hml_conjunct.Pos (hml.Conj Q (hml_srbb_conjunct_to_hml_conjunct \<circ> distinguishing_conjunct I \<psi>s))"
      unfolding hml_and_and
            and de_Morgan_conj
    proof (rule ballI)
      fix q
      assume "q \<in> Q"
      with \<open>\<forall>q\<in>Q. \<not> hml_conjunct_models q (hml_conjunct.Neg (hml.Obs \<tau> hml.TT))
                \<or> \<not> hml_conjunct_models q (hml_conjunct.Pos (hml.Conj I (hml_srbb_conjunct_to_hml_conjunct \<circ> \<psi>s)))\<close>
      have "\<not> hml_conjunct_models q (hml_conjunct.Neg (hml.Obs \<tau> hml.TT))
          \<or> \<not> hml_conjunct_models q (hml_conjunct.Pos (hml.Conj I (hml_srbb_conjunct_to_hml_conjunct \<circ> \<psi>s)))" by auto
      then show "\<not> hml_conjunct_models q (hml_conjunct.Neg (hml.Obs \<tau> hml.TT))
               \<or> \<not> hml_conjunct_models q (hml_conjunct.Pos (hml.Conj Q (hml_srbb_conjunct_to_hml_conjunct \<circ> distinguishing_conjunct I \<psi>s)))"
        apply (rule disjE)
        using disjI1 apply auto[1]
        unfolding hml_conjunct_models.simps
              and hml_models.simps
      proof (rule disjI2)
        assume "\<not> (\<forall>i\<in>I. hml_conjunct_models q ((hml_srbb_conjunct_to_hml_conjunct \<circ> \<psi>s) i))"
        hence "\<exists>i\<in>I. \<not> hml_conjunct_models q ((hml_srbb_conjunct_to_hml_conjunct \<circ> \<psi>s) i)" by auto
        hence "\<exists>i\<in>I. \<not> hml_conjunct_models q (hml_srbb_conjunct_to_hml_conjunct (\<psi>s i))"
          using comp_apply by simp
        hence "\<exists>i\<in>I. \<not> hml_srbb_conjunct_models (\<psi>s i) q"
          using hml_srbb_conjunct_models.simps by simp
        then have "I \<noteq> {}" by blast

        from \<open>I \<noteq> {}\<close>
        have red_dist_conjunct: "distinguishing_conjunct I \<psi>s =
          (\<lambda>q. if \<exists>i \<in> I. \<not>(hml_srbb_conjunct_models (\<psi>s i) q)
               then \<psi>s (SOME i. i \<in> I \<and> \<not>(hml_srbb_conjunct_models (\<psi>s i) q))
               else \<psi>s (SOME i. i \<in> I))"
          unfolding distinguishing_conjunct_def
          by presburger

        from \<open>\<exists>i\<in>I. \<not> hml_srbb_conjunct_models (\<psi>s i) q\<close>
        have "\<not> hml_srbb_conjunct_models (\<psi>s (SOME i. i \<in> I \<and> \<not>(hml_srbb_conjunct_models (\<psi>s i) q))) q"
          using someI_ex by (smt (verit))

        then have "\<not> hml_conjunct_models q (hml_srbb_conjunct_to_hml_conjunct
                                        (if \<exists>i \<in> I. \<not>(hml_srbb_conjunct_models (\<psi>s i) q)
                                         then \<psi>s (SOME i. i \<in> I \<and> \<not>(hml_srbb_conjunct_models (\<psi>s i) q))
                                         else \<psi>s (SOME i. i \<in> I)))"
          unfolding hml_srbb_conjunct_models.simps
          using \<open>\<exists>i\<in>I. \<not> hml_srbb_conjunct_models (\<psi>s i) q\<close> by simp

        then show "\<not> (\<forall>q'\<in>Q. hml_conjunct_models q ((hml_srbb_conjunct_to_hml_conjunct \<circ> distinguishing_conjunct I \<psi>s) q'))"
          using \<open>q \<in> Q\<close> and comp_apply and red_dist_conjunct by force
      qed
    qed
  qed
qed



lemma dist_branchconj_thinn:
  defines 
    "distinguishing_conjunct \<equiv> (\<lambda>I.\<lambda>\<psi>s.
       \<lambda>q. if I = {}
           then Pos (Conj {} undefined)
           else if \<exists>i \<in> I. \<not>(hml_srbb_conjunct_models (\<psi>s i) q)
                then \<psi>s (SOME i. i \<in> I \<and> \<not>(hml_srbb_conjunct_models (\<psi>s i) q))
                else \<psi>s (SOME i. i \<in> I))" (* c.f. dist_stableconj_thinn for an explanation of this function. *)
  assumes "distinguishes_from_inner (BranchConj \<alpha> \<phi> I \<psi>s) p Q"
  shows "distinguishes_from_inner (BranchConj \<alpha> \<phi> Q (distinguishing_conjunct I \<psi>s)) p Q"
  using assms(2)
  unfolding distinguishes_from_inner_def
        and distinguishes_inner_def
        and hml_srbb_inner_models.simps
        and hml_srbb_inner_to_hml.simps
proof -
  assume "p \<Turnstile> hml_conjunct.Pos (HML_soft_poss \<alpha> (hml_srbb_to_hml \<phi>)) 
                    \<and>hml hml_conjunct.Pos (hml.Conj I (hml_srbb_conjunct_to_hml_conjunct \<circ> \<psi>s))
              \<and> (\<forall>q\<in>Q. \<not> q \<Turnstile> hml_conjunct.Pos (HML_soft_poss \<alpha> (hml_srbb_to_hml \<phi>))
                      \<and>hml hml_conjunct.Pos (hml.Conj I (hml_srbb_conjunct_to_hml_conjunct \<circ> \<psi>s)))"
  with hml_and_dist_disj
  have "(p \<Turnstile> (hml_conjunct.Pos (HML_soft_poss \<alpha> (hml_srbb_to_hml \<phi>))) 
                   \<and>hml (hml_conjunct.Pos (hml.Conj I (hml_srbb_conjunct_to_hml_conjunct \<circ> \<psi>s))))
            \<and> (\<forall>q\<in>Q. (\<not> hml_conjunct_models q (hml_conjunct.Pos (HML_soft_poss \<alpha> (hml_srbb_to_hml \<phi>)))
             \<or> \<not> hml_conjunct_models q (hml_conjunct.Pos (hml.Conj I (hml_srbb_conjunct_to_hml_conjunct \<circ> \<psi>s)))))"
    using hml_and_and by blast
  then have p_models_branch_conj:
    "p \<Turnstile> (hml_conjunct.Pos (HML_soft_poss \<alpha> (hml_srbb_to_hml \<phi>))) 
           \<and>hml (hml_conjunct.Pos (hml.Conj I (hml_srbb_conjunct_to_hml_conjunct \<circ> \<psi>s)))"
       and no_q_models_branch_conj:
    "\<forall>q\<in>Q. (\<not> hml_conjunct_models q (hml_conjunct.Pos (HML_soft_poss \<alpha> (hml_srbb_to_hml \<phi>)))
            \<or> \<not> hml_conjunct_models q (hml_conjunct.Pos (hml.Conj I (hml_srbb_conjunct_to_hml_conjunct \<circ> \<psi>s))))"
    by auto

  show "p \<Turnstile> hml_conjunct.Pos (HML_soft_poss \<alpha> (hml_srbb_to_hml \<phi>))
                  \<and>hml hml_conjunct.Pos (hml.Conj Q (hml_srbb_conjunct_to_hml_conjunct \<circ> distinguishing_conjunct I \<psi>s))
          \<and> (\<forall>q\<in>Q. \<not> q \<Turnstile> hml_conjunct.Pos (HML_soft_poss \<alpha> (hml_srbb_to_hml \<phi>))
                  \<and>hml hml_conjunct.Pos (hml.Conj Q (hml_srbb_conjunct_to_hml_conjunct \<circ> distinguishing_conjunct I \<psi>s)))"
  proof (rule conjI)
    from p_models_branch_conj
    have "p \<Turnstile> (hml_conjunct.Pos (HML_soft_poss \<alpha> (hml_srbb_to_hml \<phi>))) 
                \<and>hml (hml_conjunct.Pos (hml.Conj I (hml_srbb_conjunct_to_hml_conjunct \<circ> \<psi>s)))"
      by auto
    then have "hml_conjunct_models p (hml_conjunct.Pos (HML_soft_poss \<alpha> (hml_srbb_to_hml \<phi>)))"
          and "hml_conjunct_models p (hml_conjunct.Pos (hml.Conj I (hml_srbb_conjunct_to_hml_conjunct \<circ> \<psi>s)))"
      unfolding hml_and_and by auto

    from \<open>hml_conjunct_models p (hml_conjunct.Pos (HML_soft_poss \<alpha> (hml_srbb_to_hml \<phi>)))\<close>
    show "p \<Turnstile> hml_conjunct.Pos (HML_soft_poss \<alpha> (hml_srbb_to_hml \<phi>))
              \<and>hml hml_conjunct.Pos (hml.Conj Q (hml_srbb_conjunct_to_hml_conjunct \<circ> distinguishing_conjunct I \<psi>s))"
      unfolding hml_and_and
    proof (rule conjI)
      from \<open>hml_conjunct_models p (hml_conjunct.Pos (hml.Conj I (hml_srbb_conjunct_to_hml_conjunct \<circ> \<psi>s)))\<close>
       and models_full_models_dist_subset'
      have "p \<Turnstile> hml.Conj Q
           (\<lambda>q. if I = {}
                then hml_srbb_conjunct_to_hml_conjunct (hml_srbb_conjunct.Pos (hml_srbb_inner.Conj {} undefined))
                else (if \<exists>i\<in>I. \<not> hml_srbb_conjunct_models (\<psi>s i) q
                     then (hml_srbb_conjunct_to_hml_conjunct \<circ> \<psi>s) (SOME i. i \<in> I \<and> \<not> hml_srbb_conjunct_models (\<psi>s i) q)
                     else (hml_srbb_conjunct_to_hml_conjunct \<circ> \<psi>s) (SOME i. i \<in> I)))"
        unfolding hml_srbb_conjunct_to_hml_conjunct.simps
              and hml_srbb_inner_to_hml.simps
              and hml_srbb_conjunct_models.simps
              and comp_apply and hml_conjunct_models.simps by blast

      then have "p \<Turnstile> hml.Conj Q
          (hml_srbb_conjunct_to_hml_conjunct \<circ>
           (\<lambda>q. if I = {} then hml_srbb_conjunct.Pos (hml_srbb_inner.Conj {} undefined)
                else if \<exists>i\<in>I. \<not> hml_srbb_conjunct_models (\<psi>s i) q
                     then \<psi>s (SOME i. i \<in> I \<and> \<not> hml_srbb_conjunct_models (\<psi>s i) q) else \<psi>s (SOME i. i \<in> I)))"
        using comp_apply and o_def by (smt (verit) hml_models.simps(5))

      then show "hml_conjunct_models p (hml_conjunct.Pos (hml.Conj Q (hml_srbb_conjunct_to_hml_conjunct \<circ> distinguishing_conjunct I \<psi>s)))"
        unfolding hml_conjunct_models.simps
              and distinguishing_conjunct_def.
    qed
  next
    show "\<forall>q\<in>Q. \<not> q \<Turnstile> hml_conjunct.Pos (HML_soft_poss \<alpha> (hml_srbb_to_hml \<phi>))
                     \<and>hml hml_conjunct.Pos (hml.Conj Q (hml_srbb_conjunct_to_hml_conjunct \<circ> distinguishing_conjunct I \<psi>s))"
    proof (rule ballI)
      fix q
      assume "q \<in> Q"
      with no_q_models_branch_conj
      have "\<not> hml_conjunct_models q (hml_conjunct.Pos (HML_soft_poss \<alpha> (hml_srbb_to_hml \<phi>)))
            \<or> \<not> hml_conjunct_models q (hml_conjunct.Pos (hml.Conj I (hml_srbb_conjunct_to_hml_conjunct \<circ> \<psi>s)))"
        by auto
      then show "\<not> q \<Turnstile> hml_conjunct.Pos (HML_soft_poss \<alpha> (hml_srbb_to_hml \<phi>))
                     \<and>hml hml_conjunct.Pos (hml.Conj Q (hml_srbb_conjunct_to_hml_conjunct \<circ> distinguishing_conjunct I \<psi>s))"
        unfolding hml_and_and and de_Morgan_conj
      proof (rule disjE)
        assume "\<not> hml_conjunct_models q (hml_conjunct.Pos (HML_soft_poss \<alpha> (hml_srbb_to_hml \<phi>)))"
        then show "\<not> hml_conjunct_models q (hml_conjunct.Pos (HML_soft_poss \<alpha> (hml_srbb_to_hml \<phi>)))
               \<or> \<not> hml_conjunct_models q (hml_conjunct.Pos (hml.Conj Q (hml_srbb_conjunct_to_hml_conjunct \<circ> distinguishing_conjunct I \<psi>s)))"
          by (rule disjI1)
      next
        assume "\<not> hml_conjunct_models q (hml_conjunct.Pos (hml.Conj I (hml_srbb_conjunct_to_hml_conjunct \<circ> \<psi>s)))"
        hence "\<exists>i\<in>I. \<not> hml_conjunct_models q ((hml_srbb_conjunct_to_hml_conjunct \<circ> \<psi>s) i)"
          unfolding hml_conjunct_models.simps and hml_models.simps by auto
        then have "I \<noteq> {}" by auto

        then have "distinguishing_conjunct I \<psi>s =
        (\<lambda>q. if \<exists>i \<in> I. \<not>(hml_srbb_conjunct_models (\<psi>s i) q)
             then \<psi>s (SOME i. i \<in> I \<and> \<not>(hml_srbb_conjunct_models (\<psi>s i) q))
             else \<psi>s (SOME i. i \<in> I))"
          using distinguishing_conjunct_def by auto

        with \<open>\<exists>i\<in>I. \<not> hml_conjunct_models q ((hml_srbb_conjunct_to_hml_conjunct \<circ> \<psi>s) i)\<close>

        have "distinguishing_conjunct I \<psi>s q = \<psi>s (SOME i. i \<in> I \<and> \<not>(hml_srbb_conjunct_models (\<psi>s i) q))"
          unfolding hml_srbb_conjunct_models.simps by auto

        show "\<not> hml_conjunct_models q (hml_conjunct.Pos (HML_soft_poss \<alpha> (hml_srbb_to_hml \<phi>)))
         \<or> \<not> hml_conjunct_models q (hml_conjunct.Pos (hml.Conj Q (hml_srbb_conjunct_to_hml_conjunct \<circ> distinguishing_conjunct I \<psi>s)))"
          unfolding hml_conjunct_models.simps and hml_models.simps
        proof (rule disjI2)
          from \<open>\<exists>i\<in>I. \<not> hml_conjunct_models q ((hml_srbb_conjunct_to_hml_conjunct \<circ> \<psi>s) i)\<close>
          have "\<not>hml_conjunct_models q (hml_srbb_conjunct_to_hml_conjunct (\<psi>s (SOME i. i \<in> I \<and> \<not>(hml_srbb_conjunct_models (\<psi>s i) q))))"
            using someI_ex by (metis (mono_tags, lifting) Inhabited_Tau_LTS.hml_srbb_conjunct_models.elims(1) Inhabited_Tau_LTS_axioms comp_eq_dest_lhs)
          then have "\<not>hml_conjunct_models q (hml_srbb_conjunct_to_hml_conjunct (distinguishing_conjunct I \<psi>s q))"
            using \<open>distinguishing_conjunct I \<psi>s q = \<psi>s (SOME i. i \<in> I \<and> \<not>(hml_srbb_conjunct_models (\<psi>s i) q))\<close> by simp
          then have "\<exists>q'\<in>Q. \<not>hml_conjunct_models q (hml_srbb_conjunct_to_hml_conjunct (distinguishing_conjunct I \<psi>s q'))" 
            using \<open>q \<in> Q\<close> by auto
          then have "\<exists>q'\<in>Q. \<not>hml_conjunct_models q ((hml_srbb_conjunct_to_hml_conjunct \<circ> distinguishing_conjunct I \<psi>s) q')"
            unfolding comp_apply.
          then show "\<not> (\<forall>i\<in>Q. hml_conjunct_models q ((hml_srbb_conjunct_to_hml_conjunct \<circ> distinguishing_conjunct I \<psi>s) i))"
            by auto
        qed
      qed
    qed
  qed
qed

end (* Inhabited_Tau_LTS *)

end
