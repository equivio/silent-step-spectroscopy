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

  "hml_srbb_conjunction_to_hml (Obs a \<phi>) = hml.Obs a (hml_srbb_to_hml \<phi>)" |
  "hml_srbb_conjunction_to_hml (Conj I \<psi>s) = hml.Conj I (hml_srbb_conjunct_to_hml_conjunct \<circ> \<psi>s)" |

  "hml_srbb_conjunction_to_hml (StableConj I \<psi>s) =
    (hml_conjunct.Neg (hml.Obs \<tau> hml.TT)
     \<and>hml hml_conjunct.Pos (hml.Conj I (hml_srbb_conjunct_to_hml_conjunct \<circ> \<psi>s)))" |

  "hml_srbb_conjunction_to_hml (BranchConj a \<phi> I \<psi>s) = 
     (hml_conjunct.Pos (HML_soft_poss a (hml_srbb_to_hml \<phi>))
      \<and>hml hml_conjunct.Pos (hml.Conj I (hml_srbb_conjunct_to_hml_conjunct \<circ> \<psi>s)))" |

  "hml_srbb_conjunct_to_hml_conjunct (Pos \<chi>) = hml_conjunct.Pos (hml.Internal (hml_srbb_conjunction_to_hml \<chi>))" |
  "hml_srbb_conjunct_to_hml_conjunct (Neg \<chi>) = hml_conjunct.Neg (hml.Internal (hml_srbb_conjunction_to_hml \<chi>))"

fun hml_srbb_models :: "('a, 's) hml_srbb \<Rightarrow> 's \<Rightarrow> bool" (infix "\<Turnstile>SRBB" 60)where
  "hml_srbb_models formula state = ((hml_srbb_to_hml formula) \<Turnstile> state)"

(*Some sanity checks*)

lemma "(TT \<Turnstile>SRBB state) = (ImmConj {} \<psi>s \<Turnstile>SRBB state)"
  by simp

lemma "(Internal \<chi> \<Turnstile>SRBB state) = (ImmConj {left} (\<lambda>i. if i = left then Pos \<chi> else undefined) \<Turnstile>SRBB state)"
  by simp

definition hml_preordered :: "(('a, 's) hml_srbb) set \<Rightarrow> 's \<Rightarrow> 's \<Rightarrow> bool" where
  "hml_preordered \<phi>s l r \<equiv> \<forall>\<phi> \<in> \<phi>s. \<phi> \<Turnstile>SRBB l \<longrightarrow> \<phi> \<Turnstile>SRBB r"

definition distinguishes :: "('a, 's) hml_srbb \<Rightarrow> 's \<Rightarrow> 's \<Rightarrow> bool" where
  "distinguishes \<phi> l r \<equiv> \<phi> \<Turnstile>SRBB l \<and> \<not>(\<phi> \<Turnstile>SRBB r)"

definition hml_equivalent :: "(('a, 's) hml_srbb) set \<Rightarrow> 's \<Rightarrow> 's \<Rightarrow> bool" where
  "hml_equivalent \<phi>s l r \<equiv> hml_preordered \<phi>s l r \<and> hml_preordered \<phi>s r l"


lemma "hml_preordered \<phi>s l r = (\<forall>\<phi> \<in> \<phi>s. \<not>(distinguishes \<phi> l r))"
  by (simp add: distinguishes_def hml_preordered_def)

lemma "hml_equivalent \<phi>s l r = (\<forall>\<phi> \<in> \<phi>s. \<not>(distinguishes \<phi> l r) \<and> \<not>(distinguishes \<phi> r l))"
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

lemma "\<phi>s \<subseteq> \<phi>s' \<Longrightarrow> hml_equivalent \<phi>s' l r \<Longrightarrow> hml_equivalent \<phi>s l r"
  by (meson hml_equivalent_def hml_preordered_def subsetD)

lemma "hml_preordered \<phi>s l r = (\<forall>\<phi> \<in> \<phi>s. \<not>(distinguishes \<phi> l r))"
  using distinguishes_def hml_preordered_def by auto

lemma "hml_equivalent \<phi>s l r = (\<forall>\<phi> \<in> \<phi>s. \<not>(distinguishes \<phi> l r) \<and> \<not>(distinguishes \<phi> r l))"
  using distinguishes_def hml_equivalent_def hml_preordered_def by auto

end (* Inhabited_Tau_LTS *)

end
