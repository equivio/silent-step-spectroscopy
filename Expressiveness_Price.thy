theory Expressiveness_Price
  imports Main "./HML_SRBB"
begin

primrec
      modal_depth_srbb :: "('act, 'i) hml_srbb \<Rightarrow> nat"
  and modal_depth_srbb_conjunction :: "('act, 'i) hml_srbb_conjunction \<Rightarrow> nat"
  and modal_depth_srbb_conjunct :: "('act, 'i) hml_srbb_conjunct \<Rightarrow> nat" where
 "modal_depth_srbb (Internal \<chi>) = modal_depth_srbb_conjunction \<chi>" |
 "modal_depth_srbb (ImmConj I \<psi>s) = Sup ({0} \<union> {modal_depth_srbb_conjunct (\<psi>s i) | i. i \<in> I})" |

 "modal_depth_srbb_conjunction (Obs \<alpha> \<phi>) = 1 + modal_depth_srbb \<phi>" |
 "modal_depth_srbb_conjunction (Conj I \<psi>s) =
    Sup ({0} \<union> {modal_depth_srbb_conjunct (\<psi>s i) | i. i \<in> I})" |
 "modal_depth_srbb_conjunction (StableConj I \<psi>s) = 
    Sup ({0} \<union> {modal_depth_srbb_conjunct (\<psi>s i) | i. i \<in> I})" |
 "modal_depth_srbb_conjunction (BranchConj a \<phi> I \<psi>s) =
    Sup ({1 + modal_depth_srbb \<phi>} \<union> {modal_depth_srbb_conjunct (\<psi>s i) | i. i \<in> I})" |

 "modal_depth_srbb_conjunct (Pos \<chi>) = modal_depth_srbb_conjunction \<chi>" |
 "modal_depth_srbb_conjunct (Neg \<chi>) = modal_depth_srbb_conjunction \<chi>" |
 "modal_depth_srbb_conjunct TT = 0"

end