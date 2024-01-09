theory HML_SRBB
  imports Main HML
begin

datatype 
  ('act, 'i) hml_srbb =
    TT |
    Internal "('act, 'i) hml_srbb_conjunction" |
    ImmConj "'i set" "'i \<Rightarrow> ('act, 'i) hml_srbb_conjunct"
and
  ('act, 'i) hml_srbb_conjunction =
    Obs 'act "('act, 'i) hml_srbb" |
    Conj "'i set" "'i \<Rightarrow> ('act, 'i) hml_srbb_conjunct" |
    StableConj "'i set" "'i \<Rightarrow> ('act, 'i) hml_srbb_conjunct" |
    BranchConj 'act "('act, 'i) hml_srbb"
               "'i set" "'i \<Rightarrow> ('act, 'i) hml_srbb_conjunct"
and
  ('act, 'i) hml_srbb_conjunct =
    Pos "('act, 'i) hml_srbb_conjunction" |
    Neg "('act, 'i) hml_srbb_conjunction"


context Inhabited_Tau_LTS
begin

primrec
      hml_srbb_to_hml :: "('a, 's) hml_srbb \<Rightarrow> ('a, 's) hml"
  and hml_srbb_conjunction_to_hml :: "('a, 's) hml_srbb_conjunction \<Rightarrow> ('a, 's) hml"
  and hml_srbb_conjunct_to_hml_conjunct :: "('a, 's) hml_srbb_conjunct \<Rightarrow> ('a, 's) hml_conjunct" where
  "hml_srbb_to_hml TT = hml.TT" |
  "hml_srbb_to_hml (Internal \<chi>) = hml.Internal (hml_srbb_conjunction_to_hml \<chi>)" |
  "hml_srbb_to_hml (ImmConj I \<psi>s) = hml.Conj I (hml_srbb_conjunct_to_hml_conjunct \<circ> \<psi>s)" |

  "hml_srbb_conjunction_to_hml (Obs a \<phi>) = HML_soft_poss a (hml_srbb_to_hml \<phi>)" |
(*equivalent to? (if a = \<tau> then hml_srbb_to_hml \<phi> else hml.Obs a (hml_srbb_to_hml \<phi>))*)
  "hml_srbb_conjunction_to_hml (Conj I \<psi>s) = hml.Conj I (hml_srbb_conjunct_to_hml_conjunct \<circ> \<psi>s)" |

  "hml_srbb_conjunction_to_hml (StableConj I \<psi>s) =
    (hml_conjunct.Neg (hml.Obs \<tau> hml.TT)
     \<and>hml hml_conjunct.Pos (hml.Conj I (hml_srbb_conjunct_to_hml_conjunct \<circ> \<psi>s)))" |

  "hml_srbb_conjunction_to_hml (BranchConj a \<phi> I \<psi>s) = 
     (hml_conjunct.Pos (HML_soft_poss a (hml_srbb_to_hml \<phi>))
      \<and>hml hml_conjunct.Pos (hml.Conj I (hml_srbb_conjunct_to_hml_conjunct \<circ> \<psi>s)))" |

  "hml_srbb_conjunct_to_hml_conjunct (Pos \<chi>) = hml_conjunct.Pos (hml.Internal (hml_srbb_conjunction_to_hml \<chi>))" |
  "hml_srbb_conjunct_to_hml_conjunct (Neg \<chi>) = hml_conjunct.Neg (hml.Internal (hml_srbb_conjunction_to_hml \<chi>))"


fun hml_srbb_models :: "'s \<Rightarrow> ('a, 's) hml_srbb \<Rightarrow> bool" (infix "\<Turnstile>SRBB" 60)where
  "hml_srbb_models state formula = (state \<Turnstile> (hml_srbb_to_hml formula))"

fun hml_srbb_conjunction_models :: "('a, 's) hml_srbb_conjunction \<Rightarrow> 's \<Rightarrow> bool" where
  "hml_srbb_conjunction_models \<chi> s = (s \<Turnstile> (hml_srbb_conjunction_to_hml \<chi>))"

fun hml_srbb_conjunct_models :: "('a, 's) hml_srbb_conjunct \<Rightarrow> 's \<Rightarrow> bool" where
  "hml_srbb_conjunct_models \<psi> s = (hml_conjunct_models s (hml_srbb_conjunct_to_hml_conjunct \<psi>))"

(*Some sanity checks*)

lemma "(state \<Turnstile>SRBB TT) = (state \<Turnstile>SRBB ImmConj {} \<psi>s)"
  by simp

lemma "(state \<Turnstile>SRBB Internal \<chi>) = (state \<Turnstile>SRBB ImmConj {left} (\<lambda>i. if i = left then Pos \<chi> else undefined))"
  by simp


definition distinguishes :: "('a, 's) hml_srbb \<Rightarrow> 's \<Rightarrow> 's \<Rightarrow> bool" where
  "distinguishes \<phi> p q \<equiv> p \<Turnstile>SRBB \<phi> \<and> \<not>(q \<Turnstile>SRBB \<phi>)"

definition distinguishes_\<chi> :: "('a, 's) hml_srbb_conjunction \<Rightarrow> 's \<Rightarrow> 's \<Rightarrow> bool" where
  "distinguishes_\<chi> \<chi> p q \<equiv> hml_srbb_conjunction_models \<chi> p \<and> \<not>(hml_srbb_conjunction_models \<chi> q)"

definition distinguishes_from :: "('a, 's) hml_srbb \<Rightarrow> 's \<Rightarrow> 's set \<Rightarrow> bool" where
  "distinguishes_from \<phi> p Q \<equiv> \<forall>q \<in> Q. distinguishes \<phi> p q"

definition distinguishes_from_\<chi> :: "('a, 's) hml_srbb_conjunction \<Rightarrow> 's \<Rightarrow> 's set \<Rightarrow> bool" where
  "distinguishes_from_\<chi> \<chi> p Q \<equiv> \<forall>q \<in> Q. distinguishes_\<chi> \<chi> p q"


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

lemma "\<phi>s \<subseteq> \<phi>s' \<Longrightarrow> hml_equivalent \<phi>s' p q \<Longrightarrow> hml_equivalent \<phi>s p q"
  by (meson hml_equivalent_def hml_preordered_def subsetD)

lemma "hml_preordered \<phi>s p q = (\<forall>\<phi> \<in> \<phi>s. \<not>(distinguishes \<phi> p q))"
  using distinguishes_def hml_preordered_def by auto

lemma "hml_equivalent \<phi>s p q = (\<forall>\<phi> \<in> \<phi>s. \<not>(distinguishes \<phi> p q) \<and> \<not>(distinguishes \<phi> q p))"
  using distinguishes_def hml_equivalent_def hml_preordered_def by auto


subsection \<open> HML\_SRBB Implication \<close>

definition hml_srbb_impl :: "('a, 's) hml_srbb \<Rightarrow> ('a, 's) hml_srbb \<Rightarrow> bool" (infix "\<Rrightarrow>" 70) where
  "\<phi>l \<Rrightarrow> \<phi>r \<equiv> \<forall>p. p \<Turnstile>SRBB \<phi>l \<longrightarrow> p \<Turnstile>SRBB \<phi>r"

lemma srbb_impl_to_hml_impl: "\<phi>l \<Rrightarrow> \<phi>r \<Longrightarrow> hml_srbb_to_hml \<phi>l \<Rrightarrow> hml_srbb_to_hml \<phi>r"
  by (simp add: LTS_Tau.hml_impl_iffI hml_srbb_impl_def)


definition hml_srbb_impl_\<chi> :: "('a, 's) hml_srbb_conjunction \<Rightarrow> ('a, 's) hml_srbb_conjunction \<Rightarrow> bool" (infix "\<chi>\<Rrightarrow>" 70) where
  "\<chi>l \<chi>\<Rrightarrow> \<chi>r \<equiv> \<forall>p. hml_srbb_conjunction_models \<chi>l p \<longrightarrow> hml_srbb_conjunction_models \<chi>r p"

lemma srbb_impl_\<chi>_to_hml_impl: "\<chi>l \<chi>\<Rrightarrow> \<chi>r \<Longrightarrow> hml_srbb_conjunction_to_hml \<chi>l \<Rrightarrow> hml_srbb_conjunction_to_hml \<chi>r"
  by (simp add: LTS_Tau.hml_impl_iffI hml_srbb_impl_\<chi>_def)


definition hml_srbb_impl_\<psi> :: "('a, 's) hml_srbb_conjunct \<Rightarrow> ('a, 's) hml_srbb_conjunct \<Rightarrow> bool" (infix "\<psi>\<Rrightarrow>" 70) where
  "\<psi>l \<psi>\<Rrightarrow> \<psi>r \<equiv> \<forall>p. hml_srbb_conjunct_models \<psi>l p \<longrightarrow> hml_srbb_conjunct_models \<psi>r p"

lemma srbb_impl_\<psi>_to_hml_impl: "\<psi>l \<psi>\<Rrightarrow> \<psi>r \<Longrightarrow> hml_srbb_conjunct_to_hml_conjunct \<psi>l \<and>\<Rrightarrow> hml_srbb_conjunct_to_hml_conjunct \<psi>r"
  by (simp add: hml_conjunct_impl_def hml_srbb_impl_\<psi>_def)


subsection \<open> Pre-Congruence \<close>


subsection \<open> HML\_SRBB Equivalence \<close>

definition hml_srbb_eq :: "('a, 's) hml_srbb \<Rightarrow> ('a, 's) hml_srbb \<Rightarrow> bool" (infix "\<Lleftarrow>srbb\<Rrightarrow>" 70) where
  "\<phi>l \<Lleftarrow>srbb\<Rrightarrow> \<phi>r \<equiv> \<phi>l \<Rrightarrow> \<phi>r \<and> \<phi>r \<Rrightarrow> \<phi>l"

definition hml_srbb_eq_\<chi> :: "('a, 's) hml_srbb_conjunction \<Rightarrow> ('a, 's) hml_srbb_conjunction \<Rightarrow> bool" (infix "\<Lleftarrow>\<chi>\<Rrightarrow>" 70) where
  "\<chi>l \<Lleftarrow>\<chi>\<Rrightarrow> \<chi>r \<equiv> \<chi>l \<chi>\<Rrightarrow> \<chi>r \<and> \<chi>r \<chi>\<Rrightarrow> \<chi>l"

definition hml_srbb_eq_\<psi> :: "('a, 's) hml_srbb_conjunct \<Rightarrow> ('a, 's) hml_srbb_conjunct \<Rightarrow> bool" (infix "\<Lleftarrow>\<psi>\<Rrightarrow>" 70) where
  "\<psi>l \<Lleftarrow>\<psi>\<Rrightarrow> \<psi>r \<equiv> \<psi>l \<psi>\<Rrightarrow> \<psi>r \<and> \<psi>r \<psi>\<Rrightarrow> \<psi>l"


subsection \<open> Congruence \<close>

lemma internal_srbb_cong: "\<chi>l \<Lleftarrow>\<chi>\<Rrightarrow> \<chi>r \<Longrightarrow> (Internal \<chi>l) \<Lleftarrow>srbb\<Rrightarrow> (Internal \<chi>r)"
  by (smt (verit) hml_models.simps(3) hml_srbb_conjunction_models.elims(2) hml_srbb_conjunction_models.elims(3) hml_srbb_eq_\<chi>_def hml_srbb_eq_def hml_srbb_impl_\<chi>_def hml_srbb_impl_def hml_srbb_models.elims(2) hml_srbb_models.elims(3) hml_srbb_to_hml.simps(2))

lemma immconj_cong: "\<psi>sl ` I = \<psi>sr ` I \<Longrightarrow> \<psi>sl s \<Lleftarrow>\<psi>\<Rrightarrow> \<psi>sr s \<Longrightarrow> ImmConj (I \<union> {s}) \<psi>sl \<Lleftarrow>srbb\<Rrightarrow> ImmConj (I \<union> {s}) \<psi>sr"
proof -
  assume "\<psi>sl ` I = \<psi>sr ` I"
    and "\<psi>sl s \<Lleftarrow>\<psi>\<Rrightarrow> \<psi>sr s"
  then have "(\<forall>p. hml_srbb_conjunct_models (\<psi>sl s) p \<longrightarrow> hml_srbb_conjunct_models (\<psi>sr s) p) \<and>
             (\<forall>p. hml_srbb_conjunct_models (\<psi>sr s) p \<longrightarrow> hml_srbb_conjunct_models (\<psi>sl s) p)"
    unfolding hml_srbb_eq_\<psi>_def and hml_srbb_impl_\<psi>_def by auto
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
  by (simp add: LTS_Tau.dist_def distFrom_def)


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
    by (simp add: LTS_Tau.dist_def distFrom_def)

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
    unfolding distFrom_def and dist_def and hml_srbb_conjunct_models.simps and comp_apply
    by blast
qed


lemma dist_conj_thinn:
  defines 
    "distinguishing_conjunct \<equiv> (\<lambda>I.\<lambda>\<psi>s.
       \<lambda>q. \<psi>s (SOME i. i \<in> I \<and> \<not>(hml_srbb_conjunct_models (\<psi>s i) q)))"
  assumes "distinguishes_from_\<chi> (Conj I \<psi>s) p Q"
  shows "distinguishes_from_\<chi> (Conj Q (distinguishing_conjunct I \<psi>s)) p Q"
  using assms
  unfolding distinguishes_from_\<chi>_def
        and distinguishes_\<chi>_def
        and hml_srbb_conjunction_models.simps
        and hml_srbb_conjunction_to_hml.simps
        and distinguishing_conjunct_def
proof -
  assume "\<forall>q\<in>Q. p \<Turnstile> hml.Conj I (hml_srbb_conjunct_to_hml_conjunct \<circ> \<psi>s) \<and>
           \<not> q \<Turnstile> hml.Conj I (hml_srbb_conjunct_to_hml_conjunct \<circ> \<psi>s)"
  hence "p <> (hml.Conj I (hml_srbb_conjunct_to_hml_conjunct \<circ> \<psi>s)) Q"
    by (simp add: LTS_Tau.dist_def distFrom_def)

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
    unfolding distFrom_def and dist_def by auto
qed


lemma dist_stableconj_thinn:
  defines 
    "distinguishing_conjunct \<equiv> (\<lambda>I.\<lambda>\<psi>s.
       \<lambda>q. \<psi>s (SOME i. i \<in> I \<and> \<not>(hml_srbb_conjunct_models (\<psi>s i) q)))"
  assumes "distinguishes_from_\<chi> (StableConj I \<psi>s) p Q"
  shows "distinguishes_from_\<chi> (StableConj Q (distinguishing_conjunct I \<psi>s)) p Q"
  oops


lemma dist_branchconj_thinn:
  defines 
    "distinguishing_conjunct \<equiv> (\<lambda>I.\<lambda>\<psi>s.
       \<lambda>q. \<psi>s (SOME i. i \<in> I \<and> \<not>(hml_srbb_conjunct_models (\<psi>s i) q)))"
  assumes "distinguishes_from_\<chi> (BranchConj \<alpha> \<phi> I \<psi>s) p Q"
  shows "distinguishes_from_\<chi> (BranchConj \<alpha> \<phi> Q (distinguishing_conjunct I \<psi>s)) p Q"
  oops

end (* Inhabited_Tau_LTS *)

end
