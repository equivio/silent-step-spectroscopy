theory Expressiveness_Price
  imports Main "./HML_SRBB" "~~/src/HOL/Library/Extended_Nat"
begin

primrec
      modal_depth_srbb :: "('act, 'i) hml_srbb \<Rightarrow> enat"
  and modal_depth_srbb_conjunction :: "('act, 'i) hml_srbb_conjunction \<Rightarrow> enat"
  and modal_depth_srbb_conjunct :: "('act, 'i) hml_srbb_conjunct \<Rightarrow> enat" where
 "modal_depth_srbb (Internal \<chi>) = modal_depth_srbb_conjunction \<chi>" |
 "modal_depth_srbb (ImmConj I \<psi>s) = Sup {modal_depth_srbb_conjunct (\<psi>s i) | i. i \<in> I}" |

 "modal_depth_srbb_conjunction (Obs \<alpha> \<phi>) = 1 + modal_depth_srbb \<phi>" |
 "modal_depth_srbb_conjunction (Conj I \<psi>s) =
    Sup {modal_depth_srbb_conjunct (\<psi>s i) | i. i \<in> I}" |
 "modal_depth_srbb_conjunction (StableConj I \<psi>s) = 
    Sup {modal_depth_srbb_conjunct (\<psi>s i) | i. i \<in> I}" |
 "modal_depth_srbb_conjunction (BranchConj a \<phi> I \<psi>s) =
    Sup ({1 + modal_depth_srbb \<phi>} \<union> {modal_depth_srbb_conjunct (\<psi>s i) | i. i \<in> I})" |

 "modal_depth_srbb_conjunct (Pos \<chi>) = modal_depth_srbb_conjunction \<chi>" |
 "modal_depth_srbb_conjunct (Neg \<chi>) = modal_depth_srbb_conjunction \<chi>" |
 "modal_depth_srbb_conjunct TT = 0"

lemma "modal_depth_srbb HML_srbb_true = 0"
  using Sup_enat_def by simp

lemma "modal_depth_srbb (Internal (Obs \<alpha> (Internal (BranchConj \<beta> HML_srbb_true {} \<psi>s2)))) = 2"
  using Sup_enat_def by simp

fun observe_n_alphas :: "'a \<Rightarrow> nat \<Rightarrow> ('a, nat) hml_srbb" where
  "observe_n_alphas \<alpha> 0 = HML_srbb_true" |
  "observe_n_alphas \<alpha> (Suc n) = Internal (Obs \<alpha> (observe_n_alphas \<alpha> n))"

lemma obs_n_\<alpha>_depth_n: "modal_depth_srbb (observe_n_alphas \<alpha> n) = n"
proof (induct n)
  case 0
  show ?case unfolding observe_n_alphas.simps(1) and modal_depth_srbb.simps(2)
    using zero_enat_def and Sup_enat_def by force
next
  case (Suc n)
  then show ?case 
    using eSuc_enat plus_1_eSuc(1) by auto
qed

lemma inj_keeps_infinity: "infinite S \<Longrightarrow> inj f \<Longrightarrow> infinite {f(x) | x . x \<in> S}" 
  by (smt (verit) finite_imageD finite_subset image_subsetI mem_Collect_eq subset_UNIV subset_inj_on)

lemma enat_infinite: "infinite {1 + enat i |i. i \<in> \<nat>}"
  apply (rule inj_keeps_infinity)
  apply (rule Nats_infinite)
  by (simp add: inj_def)

lemma "modal_depth_srbb (ImmConj \<nat> (\<lambda>n. Pos (Obs \<alpha> (observe_n_alphas \<alpha> n)))) = \<infinity>"
  unfolding modal_depth_srbb.simps(2)
    and modal_depth_srbb_conjunct.simps(1)
    and modal_depth_srbb_conjunction.simps(1)
    and obs_n_\<alpha>_depth_n
    and Sup_enat_def
  using enat_infinite by force

\<comment> \<open>==========================================================================================\<close>

primrec branching_conjunction_depth :: "('a, 's) hml_srbb \<Rightarrow> enat"
  and branch_conj_depth_\<chi> :: "('a, 's) hml_srbb_conjunction \<Rightarrow> enat"
  and branch_conj_depth_\<psi> :: "('a, 's) hml_srbb_conjunct \<Rightarrow> enat" where
  "branching_conjunction_depth (Internal \<chi>) = branch_conj_depth_\<chi> \<chi>" |
  "branching_conjunction_depth (ImmConj I \<psi>s) = Sup {branch_conj_depth_\<psi> (\<psi>s i) | i . i \<in> I}" |

  "branch_conj_depth_\<chi> (Obs _ \<phi>) = branching_conjunction_depth \<phi>" |
  "branch_conj_depth_\<chi> (Conj I \<psi>s) = Sup {branch_conj_depth_\<psi> (\<psi>s i) | i . i \<in> I}" |
  "branch_conj_depth_\<chi> (StableConj I \<psi>s) = Sup {branch_conj_depth_\<psi> (\<psi>s i) | i . i \<in> I}" |
  "branch_conj_depth_\<chi> (BranchConj _ \<phi> I \<psi>s) = 1 + Sup ({branching_conjunction_depth \<phi>} \<union> {branch_conj_depth_\<psi> (\<psi>s i) | i . i \<in> I})" |

  "branch_conj_depth_\<psi> (Pos \<chi>) = branch_conj_depth_\<chi> \<chi>" |
  "branch_conj_depth_\<psi> (Neg \<chi>) = branch_conj_depth_\<chi> \<chi>" |
  "branch_conj_depth_\<psi> TT = 0"

\<comment> \<open>==========================================================================================\<close>

primrec
instable_conjunction_depth :: "('a, 's) hml_srbb \<Rightarrow> enat"
  and inst_conj_depth_\<chi> :: "('a, 's) hml_srbb_conjunction \<Rightarrow> enat"
  and inst_conj_depth_\<psi> :: "('a, 's) hml_srbb_conjunct \<Rightarrow> enat" where
  "instable_conjunction_depth (Internal \<chi>) = inst_conj_depth_\<chi> \<chi>" |
  "instable_conjunction_depth (ImmConj I \<psi>s) = 1 + Sup {inst_conj_depth_\<psi> (\<psi>s i) | i . i \<in> I}" |

  "inst_conj_depth_\<chi> (Obs _ \<phi>) = instable_conjunction_depth \<phi>" |
  "inst_conj_depth_\<chi> (Conj I \<psi>s) = 1 + Sup {inst_conj_depth_\<psi> (\<psi>s i) | i . i \<in> I}" |
  "inst_conj_depth_\<chi> (StableConj I \<psi>s) = Sup {inst_conj_depth_\<psi> (\<psi>s i) | i . i \<in> I}" |
  "inst_conj_depth_\<chi> (BranchConj _ \<phi> I \<psi>s) = Sup ({instable_conjunction_depth \<phi>} \<union> {inst_conj_depth_\<psi> (\<psi>s i) | i . i \<in> I})" |

  "inst_conj_depth_\<psi> (Pos \<chi>) = inst_conj_depth_\<chi> \<chi>" |
  "inst_conj_depth_\<psi> (Neg \<chi>) = inst_conj_depth_\<chi> \<chi>" |
  "inst_conj_depth_\<psi> TT = 0"

\<comment> \<open>==========================================================================================\<close>

primrec
stable_conjunction_depth :: "('a, 's) hml_srbb \<Rightarrow> enat"
  and st_conj_depth_\<chi> :: "('a, 's) hml_srbb_conjunction \<Rightarrow> enat"
  and st_conj_depth_\<psi> :: "('a, 's) hml_srbb_conjunct \<Rightarrow> enat" where
  "stable_conjunction_depth (Internal \<chi>) = st_conj_depth_\<chi> \<chi>" |
  "stable_conjunction_depth (ImmConj I \<psi>s) = Sup {st_conj_depth_\<psi> (\<psi>s i) | i . i \<in> I}" |

  "st_conj_depth_\<chi> (Obs _ \<phi>) = stable_conjunction_depth \<phi>" |
  "st_conj_depth_\<chi> (Conj I \<psi>s) = Sup {st_conj_depth_\<psi> (\<psi>s i) | i . i \<in> I}" |
  "st_conj_depth_\<chi> (StableConj I \<psi>s) = 1 + Sup {st_conj_depth_\<psi> (\<psi>s i) | i . i \<in> I}" |
  "st_conj_depth_\<chi> (BranchConj _ \<phi> I \<psi>s) = Sup ({stable_conjunction_depth \<phi>} \<union> {st_conj_depth_\<psi> (\<psi>s i) | i . i \<in> I})" |

  "st_conj_depth_\<psi> (Pos \<chi>) = st_conj_depth_\<chi> \<chi>" |
  "st_conj_depth_\<psi> (Neg \<chi>) = st_conj_depth_\<chi> \<chi>" |
  "st_conj_depth_\<psi> TT = 0"

\<comment> \<open>==========================================================================================\<close>

primrec
      immediate_conjunction_depth :: "('a, 's) hml_srbb \<Rightarrow> enat"
  and imm_conj_depth_\<chi> :: "('a, 's) hml_srbb_conjunction \<Rightarrow> enat"
  and imm_conj_depth_\<psi> :: "('a, 's) hml_srbb_conjunct \<Rightarrow> enat" where
  "immediate_conjunction_depth (Internal \<chi>) = imm_conj_depth_\<chi> \<chi>" |
  "immediate_conjunction_depth (ImmConj I \<psi>s) = 1 + Sup {imm_conj_depth_\<psi> (\<psi>s i) | i . i \<in> I}" |

  "imm_conj_depth_\<chi> (Obs _ \<phi>) = immediate_conjunction_depth \<phi>" |
  "imm_conj_depth_\<chi> (Conj I \<psi>s) = Sup {imm_conj_depth_\<psi> (\<psi>s i) | i . i \<in> I}" |
  "imm_conj_depth_\<chi> (StableConj I \<psi>s) = Sup {imm_conj_depth_\<psi> (\<psi>s i) | i . i \<in> I}" |
  "imm_conj_depth_\<chi> (BranchConj _ \<phi> I \<psi>s) = Sup ({immediate_conjunction_depth \<phi>} \<union> {imm_conj_depth_\<psi> (\<psi>s i) | i . i \<in> I})" |

  "imm_conj_depth_\<psi> (Pos \<chi>) = imm_conj_depth_\<chi> \<chi>" |
  "imm_conj_depth_\<psi> (Neg \<chi>) = imm_conj_depth_\<chi> \<chi>" |
  "imm_conj_depth_\<psi> TT = 0"

\<comment> \<open>==========================================================================================\<close>

primrec
      max_positive_conjunct_depth :: "('a, 's) hml_srbb \<Rightarrow> enat"
  and max_pos_conj_depth_\<chi> :: "('a, 's) hml_srbb_conjunction \<Rightarrow> enat"
  and max_pos_conj_depth_\<psi> :: "('a, 's) hml_srbb_conjunct \<Rightarrow> enat" where
  "max_positive_conjunct_depth (Internal \<chi>) = max_pos_conj_depth_\<chi> \<chi>" |
  "max_positive_conjunct_depth (ImmConj I \<psi>s) = Sup {max_pos_conj_depth_\<psi> (\<psi>s i) | i . i \<in> I}" |

  "max_pos_conj_depth_\<chi> (Obs _ \<phi>) = max_positive_conjunct_depth \<phi>" |
  "max_pos_conj_depth_\<chi> (Conj I \<psi>s) = Sup {max_pos_conj_depth_\<psi> (\<psi>s i) | i . i \<in> I}" |
  "max_pos_conj_depth_\<chi> (StableConj I \<psi>s) = Sup {max_pos_conj_depth_\<psi> (\<psi>s i) | i . i \<in> I}" |
  "max_pos_conj_depth_\<chi> (BranchConj _ \<phi> I \<psi>s) = Sup ({max_positive_conjunct_depth \<phi>} \<union> {max_pos_conj_depth_\<psi> (\<psi>s i) | i . i \<in> I})" |

  "max_pos_conj_depth_\<psi> (Pos \<chi>) = modal_depth_srbb_conjunction \<chi>" |
  "max_pos_conj_depth_\<psi> (Neg \<chi>) = max_pos_conj_depth_\<chi> \<chi>" |
  "max_pos_conj_depth_\<psi> TT = 0"

\<comment> \<open>==========================================================================================\<close>

primrec
      max_negative_conjunct_depth :: "('a, 's) hml_srbb \<Rightarrow> enat"
  and max_neg_conj_depth_\<chi> :: "('a, 's) hml_srbb_conjunction \<Rightarrow> enat"
  and max_neg_conj_depth_\<psi> :: "('a, 's) hml_srbb_conjunct \<Rightarrow> enat" where
  "max_negative_conjunct_depth (Internal \<chi>) = max_neg_conj_depth_\<chi> \<chi>" |
  "max_negative_conjunct_depth (ImmConj I \<psi>s) = Sup {max_neg_conj_depth_\<psi> (\<psi>s i) | i . i \<in> I}" |

  "max_neg_conj_depth_\<chi> (Obs _ \<phi>) = max_negative_conjunct_depth \<phi>" |
  "max_neg_conj_depth_\<chi> (Conj I \<psi>s) = Sup {max_neg_conj_depth_\<psi> (\<psi>s i) | i . i \<in> I}" |
  "max_neg_conj_depth_\<chi> (StableConj I \<psi>s) = Sup {max_neg_conj_depth_\<psi> (\<psi>s i) | i . i \<in> I}" |
  "max_neg_conj_depth_\<chi> (BranchConj _ \<phi> I \<psi>s) = Sup ({max_negative_conjunct_depth \<phi>} \<union> {max_neg_conj_depth_\<psi> (\<psi>s i) | i . i \<in> I})" |

  "max_neg_conj_depth_\<psi> (Pos \<chi>) = max_neg_conj_depth_\<chi> \<chi>" |
  "max_neg_conj_depth_\<psi> (Neg \<chi>) = modal_depth_srbb_conjunction \<chi>" |
  "max_neg_conj_depth_\<psi> TT = 0"

\<comment> \<open>==========================================================================================\<close>

primrec
      negation_depth :: "('a, 's) hml_srbb \<Rightarrow> enat"
  and neg_depth_\<chi> :: "('a, 's) hml_srbb_conjunction \<Rightarrow> enat"
  and neg_depth_\<psi> :: "('a, 's) hml_srbb_conjunct \<Rightarrow> enat" where
  "negation_depth (Internal \<chi>) = neg_depth_\<chi> \<chi>" |
  "negation_depth (ImmConj I \<psi>s) = Sup {neg_depth_\<psi> (\<psi>s i) | i . i \<in> I}" |

  "neg_depth_\<chi> (Obs _ \<phi>) = negation_depth \<phi>" |
  "neg_depth_\<chi> (Conj I \<psi>s) = Sup {neg_depth_\<psi> (\<psi>s i) | i . i \<in> I}" |
  "neg_depth_\<chi> (StableConj I \<psi>s) = Sup {neg_depth_\<psi> (\<psi>s i) | i . i \<in> I}" |
  "neg_depth_\<chi> (BranchConj _ \<phi> I \<psi>s) = Sup ({negation_depth \<phi>} \<union> {neg_depth_\<psi> (\<psi>s i) | i . i \<in> I})" |

  "neg_depth_\<psi> (Pos \<chi>) = neg_depth_\<chi> \<chi>" |
  "neg_depth_\<psi> (Neg \<chi>) = 1 + neg_depth_\<chi> \<chi>" |
  "neg_depth_\<psi> TT = 0"

end
