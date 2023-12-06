theory Expressiveness_Price
  imports Main "./HML_SRBB" "~~/src/HOL/Library/Extended_Nat"
begin

primrec
      modal_depth_srbb :: "('act, 'i) hml_srbb \<Rightarrow> enat"
  and modal_depth_srbb_conjunction :: "('act, 'i) hml_srbb_conjunction \<Rightarrow> enat"
  and modal_depth_srbb_conjunct :: "('act, 'i) hml_srbb_conjunct \<Rightarrow> enat" where
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

lemma "modal_depth_srbb HML_srbb_true = 0" by simp

lemma "modal_depth_srbb (Internal (Obs \<alpha> (Internal (BranchConj \<beta> HML_srbb_true {} \<psi>s2)))) = 2" by simp

fun observe_n_alphas :: "'a \<Rightarrow> nat \<Rightarrow> ('a, nat) hml_srbb" where
  "observe_n_alphas \<alpha> 0 = HML_srbb_true" |
  "observe_n_alphas \<alpha> (Suc n) = Internal (Obs \<alpha> (observe_n_alphas \<alpha> n))"

lemma obs_n_\<alpha>_depth_n: "modal_depth_srbb (observe_n_alphas \<alpha> n) = n"
proof (induct n)
  case 0
  show ?case unfolding observe_n_alphas.simps(1) and modal_depth_srbb.simps(2)
    using zero_enat_def by force
next
  case (Suc n)
  then show ?case 
    using eSuc_enat plus_1_eSuc(1) by auto
qed

lemma "modal_depth_srbb (ImmConj {i. True} (\<lambda>n. Pos (Obs \<alpha> (observe_n_alphas \<alpha> n)))) = \<infinity>"
  using obs_n_\<alpha>_depth_n sorry

\<comment> \<open>==========================================================================================\<close>

primrec branching_conjunction_depth :: "('a, 's) hml_srbb \<Rightarrow> enat"
  and branch_conj_depth_\<chi> :: "('a, 's) hml_srbb_conjunction \<Rightarrow> enat"
  and branch_conj_depth_\<psi> :: "('a, 's) hml_srbb_conjunct \<Rightarrow> enat" where
"branching_conjunction_depth (Internal \<chi>) = branch_conj_depth_\<chi> \<chi>" |
"branching_conjunction_depth (ImmConj I \<psi>s) = Sup ({0} \<union> {branch_conj_depth_\<psi> (\<psi>s i) | i . i \<in> I})" |

"branch_conj_depth_\<chi> (Obs _ \<psi>) = branching_conjunction_depth \<psi>" |
"branch_conj_depth_\<chi> (Conj I \<psi>s) = Sup ({0} \<union> {branch_conj_depth_\<psi> (\<psi>s i) | i . i \<in> I})" |
  "branch_conj_depth_\<chi> (StableConj I \<psi>s) = Sup ({0} \<union> {branch_conj_depth_\<psi> (\<psi>s i) | i . i \<in> I})" |
  "branch_conj_depth_\<chi> (BranchConj _ \<phi> I \<psi>s) = 1 + Sup ({branching_conjunction_depth \<phi>} \<union> {branch_conj_depth_\<psi> (\<psi>s i) | i . i \<in> I})" |

"branch_conj_depth_\<psi> (Pos \<chi>) = branch_conj_depth_\<chi> \<chi>" |
  "branch_conj_depth_\<psi> (Neg \<chi>) = branch_conj_depth_\<chi> \<chi>" |
  "branch_conj_depth_\<psi> TT = 0"

\<comment> \<open>==========================================================================================\<close>


primrec
      immediate_conjunction_depth :: "('a, 's) hml_srbb \<Rightarrow> enat"
  and imm_conj_depth_\<chi> :: "('a, 's) hml_srbb_conjunction \<Rightarrow> enat"
  and imm_conj_depth_\<psi> :: "('a, 's) hml_srbb_conjunct \<Rightarrow> enat" where
  "immediate_conjunction_depth (Internal \<chi>) = imm_conj_depth_\<chi> \<chi>" |
  "immediate_conjunction_depth (ImmConj I \<psi>s) = 1 + Sup ({0} \<union> {imm_conj_depth_\<psi> (\<psi>s i) | i . i \<in> I})" |

  "imm_conj_depth_\<chi> (Obs _ \<phi>) = immediate_conjunction_depth \<phi>" |
  "imm_conj_depth_\<chi> (Conj I \<psi>s) = Sup ({0} \<union> {imm_conj_depth_\<psi> (\<psi>s i) | i . i \<in> I})" |
  "imm_conj_depth_\<chi> (StableConj I \<psi>s) = Sup ({0} \<union> {imm_conj_depth_\<psi> (\<psi>s i) | i . i \<in> I})" |
  "imm_conj_depth_\<chi> (BranchConj _ \<phi> I \<psi>s) = Sup ({immediate_conjunction_depth \<phi>} \<union> {imm_conj_depth_\<psi> (\<psi>s i) | i . i \<in> I})" |

  "imm_conj_depth_\<psi> (Pos \<chi>) = imm_conj_depth_\<chi> \<chi>" |
  "imm_conj_depth_\<psi> (Neg \<chi>) = imm_conj_depth_\<chi> \<chi>" |
  "imm_conj_depth_\<psi> TT = 0"

\<comment> \<open>==========================================================================================\<close>

\<comment> \<open>==========================================================================================\<close>

\<comment> \<open>==========================================================================================\<close>

primrec
      negation_depth :: "('a, 's) hml_srbb \<Rightarrow> enat"
  and neg_depth_\<chi> :: "('a, 's) hml_srbb_conjunction \<Rightarrow> enat"
  and neg_depth_\<psi> :: "('a, 's) hml_srbb_conjunct \<Rightarrow> enat" where
  "negation_depth (Internal \<chi>) = neg_depth_\<chi> \<chi>" |
  "negation_depth (ImmConj I \<psi>s) = Sup ({0} \<union> {neg_depth_\<psi> (\<psi>s i) | i . i \<in> I})" |

  "neg_depth_\<chi> (Obs _ \<phi>) = negation_depth \<phi>" |
  "neg_depth_\<chi> (Conj I \<psi>s) = Sup ({0} \<union> {neg_depth_\<psi> (\<psi>s i) | i . i \<in> I})" |
  "neg_depth_\<chi> (StableConj I \<psi>s) = Sup ({0} \<union> {neg_depth_\<psi> (\<psi>s i) | i . i \<in> I})" |
  "neg_depth_\<chi> (BranchConj _ \<phi> I \<psi>s) = Sup ({negation_depth \<phi>} \<union> {neg_depth_\<psi> (\<psi>s i) | i . i \<in> I})" |

  "neg_depth_\<psi> (Pos \<chi>) = neg_depth_\<chi> \<chi>" |
  "neg_depth_\<psi> (Neg \<chi>) = neg_depth_\<chi> \<chi>" |
  "neg_depth_\<psi> TT = 0"

end
