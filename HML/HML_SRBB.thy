theory HML_SRBB
  imports Main "./HML"
begin

datatype 
  ('act, 'i) HML_srbb =
    HML_srbb_true |
    HML_srbb_silent "('act, 'i) HML_srbb_conjunction"
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

context LTS_Tau
begin

function
      hml_srbb_to_hml :: "('a, 's) HML_srbb \<Rightarrow> ('a, 's) HML"
  and hml_srbb_conjunction_to_hml :: "('a, 's) HML_srbb_conjunction \<Rightarrow> ('a, 's) HML"
  and hml_srbb_conjunct_to_hml_neg :: "('a, 's) HML_srbb_conjunct \<Rightarrow> ('a, 's) HML_neg" where
  "hml_srbb_to_hml HML_srbb_true = HML_true" |
  "hml_srbb_to_hml (HML_srbb_silent \<chi>) = HML_silent (hml_srbb_conjunction_to_hml \<chi>)" |

  "hml_srbb_conjunction_to_hml (HML_srbb_poss a \<phi>) = HML_poss a (hml_srbb_to_hml \<phi>)" |
  "hml_srbb_conjunction_to_hml (HML_srbb_conj I \<psi>s) = HML_conj I (hml_srbb_conjunct_to_hml_neg \<circ> \<psi>s)" |

  "hml_srbb_conjunction_to_hml (HML_srbb_stable_conj I \<psi>s) =
     (let new_i = (SOME i. i \<notin> I) in 
       (HML_conj (I \<union> {new_i})
                 (\<lambda>i. if i = new_i 
                      then HML_not (HML_poss \<tau> HML_true)
                      else hml_srbb_conjunct_to_hml_neg (\<psi>s i))))" |

  "hml_srbb_conjunction_to_hml (HML_srbb_branch_conj a \<phi> I \<psi>s) = 
     (let new_i = (SOME i. i \<notin> I) in
        (HML_conj (I \<union> {new_i})
                  (\<lambda>i. if i = new_i
                       then if a = \<tau>
                            then HML_just (HML_internal (hml_srbb_to_hml \<phi>))
                            else HML_just (HML_poss a (hml_srbb_to_hml \<phi>))
                       else hml_srbb_conjunct_to_hml_neg (\<psi>s i))))" |

  "hml_srbb_conjunct_to_hml_neg (HML_srbb_silent_pos \<chi>) = HML_just (hml_srbb_conjunction_to_hml \<chi>)" |
  "hml_srbb_conjunct_to_hml_neg (HML_srbb_silent_neg \<chi>) = HML_not (hml_srbb_conjunction_to_hml \<chi>)"
  
  apply (metis HML_srbb.exhaust HML_srbb_conjunct.exhaust HML_srbb_conjunction.exhaust sumE)
  by fastforce+

end

end