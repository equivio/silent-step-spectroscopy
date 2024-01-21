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

definition distinguishes_inner :: "('a, 's) hml_srbb_inner \<Rightarrow> 's \<Rightarrow> 's \<Rightarrow> bool" where
  "distinguishes_inner \<chi> p q \<equiv> hml_srbb_inner_models \<chi> p \<and> \<not>(hml_srbb_inner_models \<chi> q)"

definition distinguishes_conjunct :: "('a, 's) hml_srbb_conjunct \<Rightarrow> 's \<Rightarrow> 's \<Rightarrow> bool" where
  "distinguishes_conjunct \<chi> p q \<equiv> hml_srbb_conjunct_models \<chi> p \<and> \<not>(hml_srbb_conjunct_models \<chi> q)"

definition distinguishes_from :: "('a, 's) hml_srbb \<Rightarrow> 's \<Rightarrow> 's set \<Rightarrow> bool" where
  "distinguishes_from \<phi> p Q \<equiv> \<forall>q \<in> Q. distinguishes \<phi> p q"

definition distinguishes_from_inner :: "('a, 's) hml_srbb_inner \<Rightarrow> 's \<Rightarrow> 's set \<Rightarrow> bool" where
  "distinguishes_from_inner \<chi> p Q \<equiv> \<forall>q \<in> Q. distinguishes_inner \<chi> p q"

definition distinguishes_from_conjunct :: "('a, 's) hml_srbb_conjunct \<Rightarrow> 's \<Rightarrow> 's set \<Rightarrow> bool" where
  "distinguishes_from_conjunct \<chi> p Q \<equiv> \<forall>q \<in> Q. distinguishes_conjunct \<chi> p q"


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


definition hml_srbb_impl_inner :: "('a, 's) hml_srbb_inner \<Rightarrow> ('a, 's) hml_srbb_inner \<Rightarrow> bool" (infix "\<chi>\<Rrightarrow>" 70) where
  "\<chi>l \<chi>\<Rrightarrow> \<chi>r \<equiv> \<forall>p. hml_srbb_inner_models \<chi>l p \<longrightarrow> hml_srbb_inner_models \<chi>r p"

lemma srbb_impl_inner_to_hml_impl:
  assumes "\<chi>l \<chi>\<Rrightarrow> \<chi>r"
  shows "hml_srbb_inner_to_hml \<chi>l \<Rrightarrow> hml_srbb_inner_to_hml \<chi>r"
  using assms
  by (simp add: LTS_Tau.hml_impl_iffI hml_srbb_impl_inner_def)


definition hml_srbb_impl_conjunct :: "('a, 's) hml_srbb_conjunct \<Rightarrow> ('a, 's) hml_srbb_conjunct \<Rightarrow> bool" (infix "\<psi>\<Rrightarrow>" 70) where
  "\<psi>l \<psi>\<Rrightarrow> \<psi>r \<equiv> \<forall>p. hml_srbb_conjunct_models \<psi>l p \<longrightarrow> hml_srbb_conjunct_models \<psi>r p"

lemma srbb_impl_conjunct_to_hml_impl:
  assumes "\<psi>l \<psi>\<Rrightarrow> \<psi>r"
  shows "hml_srbb_conjunct_to_hml_conjunct \<psi>l \<and>\<Rrightarrow> hml_srbb_conjunct_to_hml_conjunct \<psi>r"
  using assms
  by (simp add: hml_conjunct_impl_def hml_srbb_impl_conjunct_def)


subsection \<open> \<open>hml__srbb\<close> Equivalence \<close>

definition hml_srbb_eq :: "('a, 's) hml_srbb \<Rightarrow> ('a, 's) hml_srbb \<Rightarrow> bool" (infix "\<Lleftarrow>srbb\<Rrightarrow>" 70) where
  "\<phi>l \<Lleftarrow>srbb\<Rrightarrow> \<phi>r \<equiv> \<phi>l \<Rrightarrow> \<phi>r \<and> \<phi>r \<Rrightarrow> \<phi>l"

definition hml_srbb_eq_inner :: "('a, 's) hml_srbb_inner \<Rightarrow> ('a, 's) hml_srbb_inner \<Rightarrow> bool" (infix "\<Lleftarrow>\<chi>\<Rrightarrow>" 70) where
  "\<chi>l \<Lleftarrow>\<chi>\<Rrightarrow> \<chi>r \<equiv> \<chi>l \<chi>\<Rrightarrow> \<chi>r \<and> \<chi>r \<chi>\<Rrightarrow> \<chi>l"

definition hml_srbb_eq_conjunct :: "('a, 's) hml_srbb_conjunct \<Rightarrow> ('a, 's) hml_srbb_conjunct \<Rightarrow> bool" (infix "\<Lleftarrow>\<psi>\<Rrightarrow>" 70) where
  "\<psi>l \<Lleftarrow>\<psi>\<Rrightarrow> \<psi>r \<equiv> \<psi>l \<psi>\<Rrightarrow> \<psi>r \<and> \<psi>r \<psi>\<Rrightarrow> \<psi>l"


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

subsection \<open> Known Equivalence Elements \<close>

lemma "Obs \<tau> TT \<Lleftarrow>\<chi>\<Rrightarrow> Conj {} \<psi>s"
  by (simp add: hml_srbb_eq_inner_def hml_srbb_impl_inner_def)

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
  assume "\<forall>q\<in>Q. p \<Turnstile> hml.Conj I (hml_srbb_conjunct_to_hml_conjunct \<circ> \<psi>s) \<and>
           \<not> q \<Turnstile> hml.Conj I (hml_srbb_conjunct_to_hml_conjunct \<circ> \<psi>s)"
  hence "p <> (hml.Conj I (hml_srbb_conjunct_to_hml_conjunct \<circ> \<psi>s)) Q"
    by (simp add: LTS_Tau.distinguishes_hml_def distinguishes_from_hml_def)

  with dist_conj_thinning
  have "p <> (hml.Conj Q (\<lambda>q. (hml_srbb_conjunct_to_hml_conjunct \<circ> \<psi>s) (SOME i. i \<in> I \<and> \<not>(hml_conjunct_models q ((hml_srbb_conjunct_to_hml_conjunct \<circ> \<psi>s) i))))) Q"
    by blast

  with extract_converter
  have "p <> (hml.Conj Q (hml_srbb_conjunct_to_hml_conjunct \<circ> (\<lambda>q. \<psi>s (SOME i. i \<in> I \<and> \<not>(hml_conjunct_models q ((hml_srbb_conjunct_to_hml_conjunct \<circ> \<psi>s) i)))))) Q"
    by auto

  then show "\<forall>q\<in>Q. p \<Turnstile> hml.Conj Q
                (hml_srbb_conjunct_to_hml_conjunct \<circ> (\<lambda>q. \<psi>s (SOME i. i \<in> I \<and> \<not> hml_srbb_conjunct_models (\<psi>s i) q))) \<and>
           \<not> q \<Turnstile> hml.Conj Q
                   (hml_srbb_conjunct_to_hml_conjunct \<circ> (\<lambda>q. \<psi>s (SOME i. i \<in> I \<and> \<not> hml_srbb_conjunct_models (\<psi>s i) q)))"
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
  assume "\<forall>q\<in>Q. p \<Turnstile> hml.Conj I (hml_srbb_conjunct_to_hml_conjunct \<circ> \<psi>s) \<and>
           \<not> q \<Turnstile> hml.Conj I (hml_srbb_conjunct_to_hml_conjunct \<circ> \<psi>s)"
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

  then show "\<forall>q\<in>Q. p \<Turnstile> hml.Conj Q
                (hml_srbb_conjunct_to_hml_conjunct \<circ> (\<lambda>q. \<psi>s (SOME i. i \<in> I \<and> \<not> hml_srbb_conjunct_models (\<psi>s i) q))) \<and>
           \<not> q \<Turnstile> hml.Conj Q
                   (hml_srbb_conjunct_to_hml_conjunct \<circ> (\<lambda>q. \<psi>s (SOME i. i \<in> I \<and> \<not> hml_srbb_conjunct_models (\<psi>s i) q)))"
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
  assume "\<forall>q\<in>Q. p \<Turnstile> hml_conjunct.Neg (hml.Obs \<tau> hml.TT)
                       \<and>hml hml_conjunct.Pos (hml.Conj I (hml_srbb_conjunct_to_hml_conjunct \<circ> \<psi>s))
                 \<and> \<not> q \<Turnstile> hml_conjunct.Neg (hml.Obs \<tau> hml.TT)
                       \<and>hml hml_conjunct.Pos (hml.Conj I (hml_srbb_conjunct_to_hml_conjunct \<circ> \<psi>s))"

  then have "\<forall>q\<in>Q. p <> (hml_conjunct.Neg (hml.Obs \<tau> hml.TT)
                         \<and>hml hml_conjunct.Pos (hml.Conj I (hml_srbb_conjunct_to_hml_conjunct \<circ> \<psi>s)))
                   q"
    unfolding distinguishes_hml_def.

  then have "\<forall>q\<in>Q. p \<Turnstile> hml_conjunct.Neg (hml.Obs \<tau> hml.TT)
                        \<and>hml hml_conjunct.Pos (hml.Conj I (hml_srbb_conjunct_to_hml_conjunct \<circ> \<psi>s))
                 \<and> (\<not> hml_conjunct_models q (hml_conjunct.Neg (hml.Obs \<tau> hml.TT))
                 \<or> \<not> hml_conjunct_models q (hml_conjunct.Pos (hml.Conj I (hml_srbb_conjunct_to_hml_conjunct \<circ> \<psi>s))))"
    unfolding hml_and_dist_disj.
  hence p_models_stable_conj:
    "\<forall>q\<in>Q. p \<Turnstile> hml_conjunct.Neg (hml.Obs \<tau> hml.TT)
                \<and>hml hml_conjunct.Pos (hml.Conj I (hml_srbb_conjunct_to_hml_conjunct \<circ> \<psi>s))"
    and no_q_models_stable_conj:
    "\<forall>q\<in>Q. \<not> hml_conjunct_models q (hml_conjunct.Neg (hml.Obs \<tau> hml.TT))
         \<or> \<not> hml_conjunct_models q (hml_conjunct.Pos (hml.Conj I (hml_srbb_conjunct_to_hml_conjunct \<circ> \<psi>s)))"
    by auto

  show "\<forall>q\<in>Q. p \<Turnstile> hml_conjunct.Neg (hml.Obs \<tau> hml.TT)
                  \<and>hml hml_conjunct.Pos (hml.Conj Q (hml_srbb_conjunct_to_hml_conjunct \<circ> distinguishing_conjunct I \<psi>s))
            \<and> \<not> q \<Turnstile> hml_conjunct.Neg (hml.Obs \<tau> hml.TT)
                    \<and>hml hml_conjunct.Pos (hml.Conj Q (hml_srbb_conjunct_to_hml_conjunct \<circ> distinguishing_conjunct I \<psi>s))"
  proof (rule ballI, rule conjI)
    fix q
    assume "q \<in> Q"
    with p_models_stable_conj and hml_and_and
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
    fix q
    assume "q \<in> Q"
    with no_q_models_stable_conj
    have "\<not> hml_conjunct_models q (hml_conjunct.Neg (hml.Obs \<tau> hml.TT))
         \<or> \<not> hml_conjunct_models q (hml_conjunct.Pos (hml.Conj I (hml_srbb_conjunct_to_hml_conjunct \<circ> \<psi>s)))"
      by auto
    then show "\<not> q \<Turnstile> hml_conjunct.Neg (hml.Obs \<tau> hml.TT)
                 \<and>hml hml_conjunct.Pos (hml.Conj Q (hml_srbb_conjunct_to_hml_conjunct \<circ> distinguishing_conjunct I \<psi>s))"
      unfolding hml_and_and
            and de_Morgan_conj
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
  assume "\<forall>q\<in>Q. p \<Turnstile> hml_conjunct.Pos (HML_soft_poss \<alpha> (hml_srbb_to_hml \<phi>)) 
                    \<and>hml hml_conjunct.Pos (hml.Conj I (hml_srbb_conjunct_to_hml_conjunct \<circ> \<psi>s))
              \<and> \<not> q \<Turnstile> hml_conjunct.Pos (HML_soft_poss \<alpha> (hml_srbb_to_hml \<phi>))
                      \<and>hml hml_conjunct.Pos (hml.Conj I (hml_srbb_conjunct_to_hml_conjunct \<circ> \<psi>s))"
  hence "\<forall>q\<in>Q. p <> (hml_conjunct.Pos (HML_soft_poss \<alpha> (hml_srbb_to_hml \<phi>)) 
                    \<and>hml hml_conjunct.Pos (hml.Conj I (hml_srbb_conjunct_to_hml_conjunct \<circ> \<psi>s)))
               q" using distinguishes_hml_def by blast
  with hml_and_dist_disj
  have "\<forall>q\<in>Q. (p \<Turnstile> (hml_conjunct.Pos (HML_soft_poss \<alpha> (hml_srbb_to_hml \<phi>))) 
                   \<and>hml (hml_conjunct.Pos (hml.Conj I (hml_srbb_conjunct_to_hml_conjunct \<circ> \<psi>s)))
            \<and> (\<not> hml_conjunct_models q (hml_conjunct.Pos (HML_soft_poss \<alpha> (hml_srbb_to_hml \<phi>)))
             \<or> \<not> hml_conjunct_models q (hml_conjunct.Pos (hml.Conj I (hml_srbb_conjunct_to_hml_conjunct \<circ> \<psi>s)))))"
    by blast
  then have p_models_branch_conj:
    "\<forall>q\<in>Q. p \<Turnstile> (hml_conjunct.Pos (HML_soft_poss \<alpha> (hml_srbb_to_hml \<phi>))) 
                 \<and>hml (hml_conjunct.Pos (hml.Conj I (hml_srbb_conjunct_to_hml_conjunct \<circ> \<psi>s)))"
       and no_q_models_branch_conj:
    "\<forall>q\<in>Q. (\<not> hml_conjunct_models q (hml_conjunct.Pos (HML_soft_poss \<alpha> (hml_srbb_to_hml \<phi>)))
            \<or> \<not> hml_conjunct_models q (hml_conjunct.Pos (hml.Conj I (hml_srbb_conjunct_to_hml_conjunct \<circ> \<psi>s))))"
    by auto

  show "\<forall>q\<in>Q. p \<Turnstile> hml_conjunct.Pos (HML_soft_poss \<alpha> (hml_srbb_to_hml \<phi>))
                  \<and>hml hml_conjunct.Pos (hml.Conj Q (hml_srbb_conjunct_to_hml_conjunct \<circ> distinguishing_conjunct I \<psi>s))
          \<and> \<not> q \<Turnstile> hml_conjunct.Pos (HML_soft_poss \<alpha> (hml_srbb_to_hml \<phi>))
                  \<and>hml hml_conjunct.Pos (hml.Conj Q (hml_srbb_conjunct_to_hml_conjunct \<circ> distinguishing_conjunct I \<psi>s))"
  proof (rule ballI, rule conjI)
    fix q
    assume "q \<in> Q"
    with p_models_branch_conj
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

end (* Inhabited_Tau_LTS *)

end
