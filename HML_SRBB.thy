theory HML_SRBB
  imports Main "./HML"
begin

datatype 
  ('act, 'i) hml_srbb =
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
    Neg "('act, 'i) hml_srbb_conjunction" |
    TT

abbreviation HML_srbb_true :: "('a, 's) hml_srbb" where
  "HML_srbb_true \<equiv> ImmConj {} (\<lambda>_. TT)"

context Inhabited_Tau_LTS
begin

abbreviation HML_srbb_TT :: "('a, 's) hml_srbb" where
  "HML_srbb_TT \<equiv> ImmConj {left} (\<lambda>_. TT)"

primrec
      hml_srbb_to_hml :: "('a, 's) hml_srbb \<Rightarrow> ('a, 's) hml"
  and hml_srbb_conjunction_to_hml :: "('a, 's) hml_srbb_conjunction \<Rightarrow> ('a, 's) hml"
  and hml_srbb_conjunct_to_hml_neg :: "('a, 's) hml_srbb_conjunct \<Rightarrow> ('a, 's) hml_conjunct" where
  "hml_srbb_to_hml (Internal \<chi>) = hml.Internal (hml_srbb_conjunction_to_hml \<chi>)" |
  "hml_srbb_to_hml (ImmConj I \<psi>s) = hml.Conj I (hml_srbb_conjunct_to_hml_neg \<circ> \<psi>s)" |

  "hml_srbb_conjunction_to_hml (Obs a \<phi>) = hml.Obs a (hml_srbb_to_hml \<phi>)" |
  "hml_srbb_conjunction_to_hml (Conj I \<psi>s) = hml.Conj I (hml_srbb_conjunct_to_hml_neg \<circ> \<psi>s)" |

  "hml_srbb_conjunction_to_hml (StableConj I \<psi>s) =
    (hml_conjunct.Neg (hml.Obs \<tau> hml.TT)
     \<and>hml hml_conjunct.Pos (hml.Conj I (hml_srbb_conjunct_to_hml_neg \<circ> \<psi>s)))" |

  "hml_srbb_conjunction_to_hml (BranchConj a \<phi> I \<psi>s) = 
     (hml_conjunct.Pos (HML_soft_poss a (hml_srbb_to_hml \<phi>))
      \<and>hml hml_conjunct.Pos (hml.Conj I (hml_srbb_conjunct_to_hml_neg \<circ> \<psi>s)))" |

  "hml_srbb_conjunct_to_hml_neg (Pos \<chi>) = hml_conjunct.Pos (hml.Internal (hml_srbb_conjunction_to_hml \<chi>))" |
  "hml_srbb_conjunct_to_hml_neg (Neg \<chi>) = hml_conjunct.Neg (hml.Internal (hml_srbb_conjunction_to_hml \<chi>))" |
  "hml_srbb_conjunct_to_hml_neg TT      = hml_conjunct.Pos hml.TT"

fun hml_srbb_models :: "('a, 's) hml_srbb \<Rightarrow> 's \<Rightarrow> bool" (infix "\<Turnstile>SRBB" 60)where
  "hml_srbb_models formula state = ((hml_srbb_to_hml formula) \<Turnstile> state)"

lemma "HML_srbb_TT \<Turnstile>SRBB state = HML_srbb_true \<Turnstile>SRBB state"
  by simp

lemma "HML_srbb_true \<Turnstile>SRBB state" by simp

lemma "Internal \<chi> \<Turnstile>SRBB state = ImmConj {left} (\<lambda>i. if i = left then Pos \<chi> else TT) \<Turnstile>SRBB state"
  by simp

end (* Inhabited_Tau_LTS *)

end