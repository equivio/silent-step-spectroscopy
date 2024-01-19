theory Expressiveness_Price
  imports Main HML_SRBB "HOL-Library.Extended_Nat" Energy
begin

section \<open>The expressiveness price function\<close>
subsection \<open>Modal depth\<close>

primrec
      modal_depth_srbb :: "('act, 'i) hml_srbb \<Rightarrow> enat"
  and modal_depth_srbb_inner :: "('act, 'i) hml_srbb_inner \<Rightarrow> enat"
  and modal_depth_srbb_conjunct :: "('act, 'i) hml_srbb_conjunct \<Rightarrow> enat" where
"modal_depth_srbb TT = 0" |
 "modal_depth_srbb (Internal \<chi>) = modal_depth_srbb_inner \<chi>" |
 "modal_depth_srbb (ImmConj I \<psi>s) = (if (I={}) then 0 else Sup ((modal_depth_srbb_conjunct \<circ> \<psi>s) ` I))" |

 "modal_depth_srbb_inner (Obs \<alpha> \<phi>) = 1 + modal_depth_srbb \<phi>" |
 "modal_depth_srbb_inner (Conj I \<psi>s) =
    (if (I={}) then 0 else Sup ((modal_depth_srbb_conjunct \<circ> \<psi>s) ` I))" |
 "modal_depth_srbb_inner (StableConj I \<psi>s) = 
    (if (I={}) then 0 else Sup ((modal_depth_srbb_conjunct \<circ> \<psi>s) ` I))" |
 "modal_depth_srbb_inner (BranchConj a \<phi> I \<psi>s) =
    (if (I={}) then 0 else Sup ({1 + modal_depth_srbb \<phi>} \<union> ((modal_depth_srbb_conjunct \<circ> \<psi>s) ` I)))" |

 "modal_depth_srbb_conjunct (Pos \<chi>) = modal_depth_srbb_inner \<chi>" |
 "modal_depth_srbb_conjunct (Neg \<chi>) = modal_depth_srbb_inner \<chi>" 

lemma "modal_depth_srbb TT = 0"
  using Sup_enat_def by simp

lemma "modal_depth_srbb (Internal (Obs \<alpha> (Internal (BranchConj \<beta> TT {} \<psi>s2)))) = 1"
  using Sup_enat_def by simp

fun observe_n_alphas :: "'a \<Rightarrow> nat \<Rightarrow> ('a, nat) hml_srbb" where
  "observe_n_alphas \<alpha> 0 = TT" |
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

lemma sup_nats_in_enats_infinite: "(SUP x\<in>\<nat>. enat x) = \<infinity>"
  by (metis Nats_infinite Sup_enat_def enat.inject finite.emptyI finite_imageD inj_on_def)

lemma sucs_of_nats_in_enats_sup_infinite: "(SUP x\<in>\<nat>. 1 + enat x) = \<infinity>"
  using sup_nats_in_enats_infinite
  by (metis Sup.SUP_cong eSuc_Sup eSuc_infinity image_image image_is_empty plus_1_eSuc(1))

lemma "modal_depth_srbb (ImmConj \<nat> (\<lambda>n. Pos (Obs \<alpha> (observe_n_alphas \<alpha> n)))) = \<infinity>"
  unfolding modal_depth_srbb.simps(3)
        and o_def
        and modal_depth_srbb_conjunct.simps(1)
        and modal_depth_srbb_inner.simps(1)
        and obs_n_\<alpha>_depth_n
  by (metis Nats_0 emptyE sucs_of_nats_in_enats_sup_infinite) 

subsection \<open>Depth of branching conjunctions\<close>

primrec branching_conjunction_depth :: "('a, 's) hml_srbb \<Rightarrow> enat"
  and branch_conj_depth_inner :: "('a, 's) hml_srbb_inner \<Rightarrow> enat"
  and branch_conj_depth_conjunct :: "('a, 's) hml_srbb_conjunct \<Rightarrow> enat" where
  "branching_conjunction_depth TT = 0" |
  "branching_conjunction_depth (Internal \<chi>) = branch_conj_depth_inner \<chi>" |
  "branching_conjunction_depth (ImmConj I \<psi>s) = (if (I={}) then 0 else Sup ((branch_conj_depth_conjunct \<circ> \<psi>s) ` I))" |

  "branch_conj_depth_inner (Obs _ \<phi>) = branching_conjunction_depth \<phi>" |
  "branch_conj_depth_inner (Conj I \<psi>s) = (if (I={}) then 0 else Sup ((branch_conj_depth_conjunct \<circ> \<psi>s) ` I))" |
  "branch_conj_depth_inner (StableConj I \<psi>s) =(if (I={}) then 0 else Sup ((branch_conj_depth_conjunct \<circ> \<psi>s) ` I))" |
  "branch_conj_depth_inner (BranchConj _ \<phi> I \<psi>s) = (if (I={}) then 0 else 1 + Sup ({branching_conjunction_depth \<phi>} \<union> ((branch_conj_depth_conjunct \<circ> \<psi>s) ` I)))" |

  "branch_conj_depth_conjunct (Pos \<chi>) = branch_conj_depth_inner \<chi>" |
  "branch_conj_depth_conjunct (Neg \<chi>) = branch_conj_depth_inner \<chi>" 

subsection \<open>Depth of instable conjunctions\<close>

primrec
instable_conjunction_depth :: "('a, 's) hml_srbb \<Rightarrow> enat"
  and inst_conj_depth_inner :: "('a, 's) hml_srbb_inner \<Rightarrow> enat"
  and inst_conj_depth_conjunct :: "('a, 's) hml_srbb_conjunct \<Rightarrow> enat" where
  "instable_conjunction_depth TT = 0" |
  "instable_conjunction_depth (Internal \<chi>) = inst_conj_depth_inner \<chi>" |
  "instable_conjunction_depth (ImmConj I \<psi>s) = (if (I={}) then 0 else 1 + Sup ((inst_conj_depth_conjunct \<circ> \<psi>s) ` I))" |

  "inst_conj_depth_inner (Obs _ \<phi>) = instable_conjunction_depth \<phi>" |
  "inst_conj_depth_inner (Conj I \<psi>s) = (if (I={}) then 0 else 1 + Sup ((inst_conj_depth_conjunct \<circ> \<psi>s) ` I))" |
  "inst_conj_depth_inner (StableConj I \<psi>s) = (if (I={}) then 0 else Sup ((inst_conj_depth_conjunct \<circ> \<psi>s) ` I))" |
  "inst_conj_depth_inner (BranchConj _ \<phi> I \<psi>s) = (if (I={}) then 0 else Sup ({instable_conjunction_depth \<phi>} \<union> ((inst_conj_depth_conjunct \<circ> \<psi>s) ` I)))" |

  "inst_conj_depth_conjunct (Pos \<chi>) = inst_conj_depth_inner \<chi>" |
  "inst_conj_depth_conjunct (Neg \<chi>) = inst_conj_depth_inner \<chi>" 

subsection \<open>Depth of stable conjunctions\<close>

primrec
stable_conjunction_depth :: "('a, 's) hml_srbb \<Rightarrow> enat"
  and st_conj_depth_inner :: "('a, 's) hml_srbb_inner \<Rightarrow> enat"
  and st_conj_depth_conjunct :: "('a, 's) hml_srbb_conjunct \<Rightarrow> enat" where
  "stable_conjunction_depth TT = 0" |
  "stable_conjunction_depth (Internal \<chi>) = st_conj_depth_inner \<chi>" |
  "stable_conjunction_depth (ImmConj I \<psi>s) = (if (I={}) then 0 else Sup ((st_conj_depth_conjunct \<circ> \<psi>s) ` I))" |

  "st_conj_depth_inner (Obs _ \<phi>) = stable_conjunction_depth \<phi>" |
  "st_conj_depth_inner (Conj I \<psi>s) = (if (I={}) then 0 else Sup ((st_conj_depth_conjunct \<circ> \<psi>s) ` I))" |
  "st_conj_depth_inner (StableConj I \<psi>s) = (if (I={}) then 0 else 1 + Sup ((st_conj_depth_conjunct \<circ> \<psi>s) ` I))" |
  "st_conj_depth_inner (BranchConj _ \<phi> I \<psi>s) = (if (I={}) then 0 else Sup ({stable_conjunction_depth \<phi>} \<union> ((st_conj_depth_conjunct \<circ> \<psi>s) ` I)))" |

  "st_conj_depth_conjunct (Pos \<chi>) = st_conj_depth_inner \<chi>" |
  "st_conj_depth_conjunct (Neg \<chi>) = st_conj_depth_inner \<chi>" 

subsection \<open>Depth of immediate conjunctions\<close>

primrec
      immediate_conjunction_depth :: "('a, 's) hml_srbb \<Rightarrow> enat"
  and imm_conj_depth_inner :: "('a, 's) hml_srbb_inner \<Rightarrow> enat"
  and imm_conj_depth_conjunct :: "('a, 's) hml_srbb_conjunct \<Rightarrow> enat" where 
  "immediate_conjunction_depth TT = 0" |
  "immediate_conjunction_depth (Internal \<chi>) = imm_conj_depth_inner \<chi>" |
  "immediate_conjunction_depth (ImmConj I \<psi>s) = (if (I={}) then 0 else 1 + Sup ((imm_conj_depth_conjunct \<circ> \<psi>s) ` I))" |

  "imm_conj_depth_inner (Obs _ \<phi>) = immediate_conjunction_depth \<phi>" |
  "imm_conj_depth_inner (Conj I \<psi>s) = (if (I={}) then 0 else Sup ((imm_conj_depth_conjunct \<circ> \<psi>s) ` I))" |
  "imm_conj_depth_inner (StableConj I \<psi>s) = (if (I={}) then 0 else Sup ((imm_conj_depth_conjunct \<circ> \<psi>s) ` I))" |
  "imm_conj_depth_inner (BranchConj _ \<phi> I \<psi>s) = (if (I={}) then 0 else Sup ({immediate_conjunction_depth \<phi>} \<union> ((imm_conj_depth_conjunct \<circ> \<psi>s) ` I)))" |

  "imm_conj_depth_conjunct (Pos \<chi>) = imm_conj_depth_inner \<chi>" |
  "imm_conj_depth_conjunct (Neg \<chi>) = imm_conj_depth_inner \<chi>"

section \<open>Maximal modal depth of positive clauses in conjunctions\<close>

primrec
      max_positive_conjunct_depth :: "('a, 's) hml_srbb \<Rightarrow> enat"
  and max_pos_conj_depth_inner :: "('a, 's) hml_srbb_inner \<Rightarrow> enat"
  and max_pos_conj_depth_conjunct :: "('a, 's) hml_srbb_conjunct \<Rightarrow> enat" where
  "max_positive_conjunct_depth TT = 0"|
  "max_positive_conjunct_depth (Internal \<chi>) = max_pos_conj_depth_inner \<chi>" |
  "max_positive_conjunct_depth (ImmConj I \<psi>s) = (if (I={}) then 0 else Sup ((max_pos_conj_depth_conjunct \<circ> \<psi>s) ` I))" |

  "max_pos_conj_depth_inner (Obs _ \<phi>) = max_positive_conjunct_depth \<phi>" |
  "max_pos_conj_depth_inner (Conj I \<psi>s) = (if (I={}) then 0 else Sup ((max_pos_conj_depth_conjunct \<circ> \<psi>s) ` I))" |
  "max_pos_conj_depth_inner (StableConj I \<psi>s) = (if (I={}) then 0 else Sup ((max_pos_conj_depth_conjunct \<circ> \<psi>s) ` I))" |
  "max_pos_conj_depth_inner (BranchConj _ \<phi> I \<psi>s) = (if (I={}) then 0 else Sup ({max_positive_conjunct_depth \<phi>} \<union> ((max_pos_conj_depth_conjunct \<circ> \<psi>s) ` I)))" |

  "max_pos_conj_depth_conjunct (Pos \<chi>) = modal_depth_srbb_inner \<chi>" |
  "max_pos_conj_depth_conjunct (Neg \<chi>) = max_pos_conj_depth_inner \<chi>"

subsection \<open>Maximal modal depth of negative clauses in conjunctions\<close>

primrec
      max_negative_conjunct_depth :: "('a, 's) hml_srbb \<Rightarrow> enat"
  and max_neg_conj_depth_inner :: "('a, 's) hml_srbb_inner \<Rightarrow> enat"
  and max_neg_conj_depth_conjunct :: "('a, 's) hml_srbb_conjunct \<Rightarrow> enat" where
  "max_negative_conjunct_depth TT = 0" |
  "max_negative_conjunct_depth (Internal \<chi>) = max_neg_conj_depth_inner \<chi>" |
  "max_negative_conjunct_depth (ImmConj I \<psi>s) = (if (I={}) then 0 else Sup ((max_neg_conj_depth_conjunct \<circ> \<psi>s) ` I))" |

  "max_neg_conj_depth_inner (Obs _ \<phi>) = max_negative_conjunct_depth \<phi>" |
  "max_neg_conj_depth_inner (Conj I \<psi>s) = (if (I={}) then 0 else Sup ((max_neg_conj_depth_conjunct \<circ> \<psi>s) ` I))" |
  "max_neg_conj_depth_inner (StableConj I \<psi>s) = (if (I={}) then 0 else Sup ((max_neg_conj_depth_conjunct \<circ> \<psi>s) ` I))" |
  "max_neg_conj_depth_inner (BranchConj _ \<phi> I \<psi>s) = (if (I={}) then 0 else Sup ({max_negative_conjunct_depth \<phi>} \<union> ((max_neg_conj_depth_conjunct \<circ> \<psi>s) ` I)))" |

  "max_neg_conj_depth_conjunct (Pos \<chi>) = max_neg_conj_depth_inner \<chi>" |
  "max_neg_conj_depth_conjunct (Neg \<chi>) = modal_depth_srbb_inner \<chi>"

subsection \<open>Depth of negations\<close>

primrec
      negation_depth :: "('a, 's) hml_srbb \<Rightarrow> enat"
  and neg_depth_inner :: "('a, 's) hml_srbb_inner \<Rightarrow> enat"
  and neg_depth_conjunct :: "('a, 's) hml_srbb_conjunct \<Rightarrow> enat" where
  "negation_depth TT = 0" |
  "negation_depth (Internal \<chi>) = neg_depth_inner \<chi>" |
  "negation_depth (ImmConj I \<psi>s) = (if (I={}) then 0 else Sup ((neg_depth_conjunct \<circ> \<psi>s) ` I))" |

  "neg_depth_inner (Obs _ \<phi>) = negation_depth \<phi>" |
  "neg_depth_inner (Conj I \<psi>s) = (if (I={}) then 0 else Sup ((neg_depth_conjunct \<circ> \<psi>s) ` I))" |
  "neg_depth_inner (StableConj I \<psi>s) = (if (I={}) then 0 else Sup ((neg_depth_conjunct \<circ> \<psi>s) ` I))" |
  "neg_depth_inner (BranchConj _ \<phi> I \<psi>s) = (if (I={}) then 0 else Sup ({negation_depth \<phi>} \<union> ((neg_depth_conjunct \<circ> \<psi>s) ` I)))" |

  "neg_depth_conjunct (Pos \<chi>) = neg_depth_inner \<chi>" |
  "neg_depth_conjunct (Neg \<chi>) = 1 + neg_depth_inner \<chi>" 

subsection \<open>Expressiveness price function\<close>

fun expressiveness_price :: "('a, 's) hml_srbb \<Rightarrow> energy" where
  "expressiveness_price \<phi> = E (modal_depth_srbb            \<phi>)
                              (branching_conjunction_depth \<phi>)
                              (instable_conjunction_depth  \<phi>)
                              (stable_conjunction_depth    \<phi>)
                              (immediate_conjunction_depth \<phi>)
                              (max_positive_conjunct_depth \<phi>)
                              (max_negative_conjunct_depth \<phi>)
                              (negation_depth              \<phi>)"

lemma srbb_price_never_neg : "expressiveness_price \<phi> \<noteq> eneg"
  by simp

definition \<O> :: "energy \<Rightarrow> (('a, 's) hml_srbb) set" where
  "\<O> energy \<equiv> {\<phi> . expressiveness_price \<phi> \<le> energy}"

fun expr_pr_inner :: "('a, 's) hml_srbb_inner \<Rightarrow> energy" where
  "expr_pr_inner \<chi> = E (modal_depth_srbb_inner \<chi>)
                 (branch_conj_depth_inner \<chi>)
                 (inst_conj_depth_inner \<chi>)
                 (st_conj_depth_inner \<chi>)
                 (imm_conj_depth_inner \<chi>)
                 (max_pos_conj_depth_inner \<chi>)
                 (max_neg_conj_depth_inner \<chi>)
                 (neg_depth_inner \<chi>)"

lemma \<chi>_price_never_neg: "expr_pr_inner \<chi> \<noteq> eneg"
  by simp

definition \<O>_inner :: "energy \<Rightarrow> (('a, 's) hml_srbb_inner) set" where
  "\<O>_inner energy \<equiv> {\<chi> . expr_pr_inner \<chi> \<le> energy}"

fun expr_pr_conjunct :: "('a, 's) hml_srbb_conjunct \<Rightarrow> energy" where
  "expr_pr_conjunct \<psi> = E (modal_depth_srbb_conjunct \<psi>)
                 (branch_conj_depth_conjunct \<psi>)
                 (inst_conj_depth_conjunct \<psi>)
                 (st_conj_depth_conjunct \<psi>)
                 (imm_conj_depth_conjunct \<psi>)
                 (max_pos_conj_depth_conjunct \<psi>)
                 (max_neg_conj_depth_conjunct \<psi>)
                 (neg_depth_conjunct \<psi>)"

definition \<O>_conjunct :: "energy \<Rightarrow> (('a, 's) hml_srbb_conjunct) set" where
  "\<O>_conjunct energy \<equiv> {\<chi> . expr_pr_conjunct \<chi> \<le> energy}"

subsection \<open>characterizing equivalence by energy coordinates\<close>

context Inhabited_Tau_LTS
begin

definition expr_preord :: "'s \<Rightarrow> energy \<Rightarrow> 's \<Rightarrow> bool" ("_ \<preceq> _ _" 60) where
  "(p \<preceq> e q) \<equiv> hml_preordered (\<O> e) p q"

definition expr_equiv :: "'s \<Rightarrow> energy \<Rightarrow> 's \<Rightarrow> bool" ("_ \<sim> _ _" 60) where
  "(p \<sim> e q) \<equiv> hml_equivalent (\<O> e) p q"

end


context Inhabited_LTS
begin

lemma example_\<phi>_cp:
  fixes op::"'a" and a:: "'a" and b::"'a"
  defines \<phi>: "\<phi> \<equiv> 
    (Internal
      (Obs op 
        (Internal 
          (Conj {left, right} 
                (\<lambda>i. (if i = left
                      then (Pos (Obs a TT))
                      else if i = right
                           then (Pos (Obs b TT))
                           else undefined))))))"
  shows
      "modal_depth_srbb            \<phi> = 2"
  and "branching_conjunction_depth \<phi> = 0"
  and "instable_conjunction_depth  \<phi> = 1"
  and "stable_conjunction_depth    \<phi> = 0"
  and "immediate_conjunction_depth \<phi> = 0"
  and "max_positive_conjunct_depth \<phi> = 1"
  and "max_negative_conjunct_depth \<phi> = 0"
  and "negation_depth              \<phi> = 0"
  unfolding \<phi>
  by simp+

lemma "expressiveness_price (Internal
      (Obs op 
        (Internal 
          (Conj {left, right} 
                (\<lambda>i. (if i = left
                      then (Pos (Obs a TT))
                      else if i = right
                           then (Pos (Obs b TT))
                           else undefined)))))) = E 2 0 1 0 0 1 0 0"
  by simp

end

end
