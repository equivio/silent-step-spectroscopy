theory HML_SRBB
  imports Main "./HML"
begin

datatype 
  ('act, 'i) HML_srbb =
    HML_srbb_true |
    HML_srbb_silent "('act, 'i) HML_srbb_conjunction" |
    HML_srbb_iconj "'i set" "'i \<Rightarrow> ('act, 'i) HML_srbb_conjunct"
and
  ('act, 'i) HML_srbb_conjunction =
    HML_srbb_poss 'act "('act, 'i) HML_srbb" |
    HML_srbb_conj "'i set" "'i \<Rightarrow> ('act, 'i) HML_srbb_conjunct" |
    HML_srbb_stable_conj "'i set" "'i \<Rightarrow> ('act, 'i) HML_srbb_conjunct" |
    HML_srbb_branch_conj 'act "('act, 'i) HML_srbb"
                         "'i set" "'i \<Rightarrow> ('act, 'i) HML_srbb_conjunct"
and
  ('act, 'i) HML_srbb_conjunct =
    HML_srbb_silent_pos "('act, 'i) HML_srbb_conjunction" |
    HML_srbb_silent_neg "('act, 'i) HML_srbb_conjunction"

primrec
      modal_depth_srbb :: "('act, 'i) HML_srbb \<Rightarrow> nat"
  and modal_depth_srbb_conjunction :: "('act, 'i) HML_srbb_conjunction \<Rightarrow> nat"
  and modal_depth_srbb_conjunct :: "('act, 'i) HML_srbb_conjunct \<Rightarrow> nat" where
 "modal_depth_srbb HML_srbb_true = 0" |
 "modal_depth_srbb (HML_srbb_silent \<chi>) = modal_depth_srbb_conjunction \<chi>" |
 "modal_depth_srbb (HML_srbb_iconj I \<psi>s) = Sup ({0} \<union> {modal_depth_srbb_conjunct (\<psi>s i) | i. i \<in> I})" |

 "modal_depth_srbb_conjunction (HML_srbb_poss \<alpha> \<phi>) = 1 + modal_depth_srbb \<phi>" |
 "modal_depth_srbb_conjunction (HML_srbb_conj I \<psi>s) =
    Sup ({0} \<union> {modal_depth_srbb_conjunct (\<psi>s i) | i. i \<in> I})" |
 "modal_depth_srbb_conjunction (HML_srbb_stable_conj I \<psi>s) = 
    Sup ({0} \<union> {modal_depth_srbb_conjunct (\<psi>s i) | i. i \<in> I})" |
 "modal_depth_srbb_conjunction (HML_srbb_branch_conj a \<phi> I \<psi>s) =
    Sup ({1 + modal_depth_srbb \<phi>} \<union> {modal_depth_srbb_conjunct (\<psi>s i) | i. i \<in> I})" |

 "modal_depth_srbb_conjunct (HML_srbb_silent_pos \<chi>) = modal_depth_srbb_conjunction \<chi>" |
 "modal_depth_srbb_conjunct (HML_srbb_silent_neg \<chi>) = modal_depth_srbb_conjunction \<chi>"
  

context Inhabited_Tau_LTS
begin

primrec
      hml_srbb_to_hml :: "('a, 's) HML_srbb \<Rightarrow> ('a, 's) HML"
  and hml_srbb_conjunction_to_hml :: "('a, 's) HML_srbb_conjunction \<Rightarrow> ('a, 's) HML"
  and hml_srbb_conjunct_to_hml_neg :: "('a, 's) HML_srbb_conjunct \<Rightarrow> ('a, 's) HML_neg" where
  "hml_srbb_to_hml HML_srbb_true = HML_true" |
  "hml_srbb_to_hml (HML_srbb_silent \<chi>) = HML_silent (hml_srbb_conjunction_to_hml \<chi>)" |
  "hml_srbb_to_hml (HML_srbb_iconj I \<psi>s) = HML_conj I (hml_srbb_conjunct_to_hml_neg \<circ> \<psi>s)" |

  "hml_srbb_conjunction_to_hml (HML_srbb_poss a \<phi>) = HML_poss a (hml_srbb_to_hml \<phi>)" |
  "hml_srbb_conjunction_to_hml (HML_srbb_conj I \<psi>s) = HML_conj I (hml_srbb_conjunct_to_hml_neg \<circ> \<psi>s)" |

  "hml_srbb_conjunction_to_hml (HML_srbb_stable_conj I \<psi>s) =
    (HML_not (HML_poss \<tau> HML_true)
     \<and>hml HML_just (HML_conj I (hml_srbb_conjunct_to_hml_neg \<circ> \<psi>s)))" |

  "hml_srbb_conjunction_to_hml (HML_srbb_branch_conj a \<phi> I \<psi>s) = 
     (HML_just (HML_soft_poss a (hml_srbb_to_hml \<phi>))
      \<and>hml HML_just (HML_conj I (hml_srbb_conjunct_to_hml_neg \<circ> \<psi>s)))" |

  "hml_srbb_conjunct_to_hml_neg (HML_srbb_silent_pos \<chi>) = HML_just (hml_srbb_conjunction_to_hml \<chi>)" |
  "hml_srbb_conjunct_to_hml_neg (HML_srbb_silent_neg \<chi>) = HML_not (hml_srbb_conjunction_to_hml \<chi>)"


fun hml_srbb_models :: "('a, 's) HML_srbb \<Rightarrow> 's \<Rightarrow> bool" ("_ \<Turnstile>SRBB _" 60)where
  "hml_srbb_models formula state = ((hml_srbb_to_hml formula) \<Turnstile> state)"

lemma "(HML_srbb_true \<Turnstile>SRBB state) = (HML_srbb_iconj {} \<psi>s \<Turnstile>SRBB state)"
  by simp

end

end