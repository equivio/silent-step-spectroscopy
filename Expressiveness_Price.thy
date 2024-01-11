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
 "modal_depth_srbb (ImmConj I \<psi>s) = Sup ((modal_depth_srbb_conjunct \<circ> \<psi>s) ` I)" |

 "modal_depth_srbb_inner (Obs \<alpha> \<phi>) = 1 + modal_depth_srbb \<phi>" |
 "modal_depth_srbb_inner (Conj I \<psi>s) =
    Sup ((modal_depth_srbb_conjunct \<circ> \<psi>s) ` I)" |
 "modal_depth_srbb_inner (StableConj I \<psi>s) = 
    Sup ((modal_depth_srbb_conjunct \<circ> \<psi>s) ` I)" |
 "modal_depth_srbb_inner (BranchConj a \<phi> I \<psi>s) =
    Sup ({1 + modal_depth_srbb \<phi>} \<union> ((modal_depth_srbb_conjunct \<circ> \<psi>s) ` I))" |

 "modal_depth_srbb_conjunct (Pos \<chi>) = modal_depth_srbb_inner \<chi>" |
 "modal_depth_srbb_conjunct (Neg \<chi>) = modal_depth_srbb_inner \<chi>" 

lemma "modal_depth_srbb TT = 0"
  using Sup_enat_def by simp

lemma "modal_depth_srbb (Internal (Obs \<alpha> (Internal (BranchConj \<beta> TT {} \<psi>s2)))) = 2"
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
  by (rule sucs_of_nats_in_enats_sup_infinite)

subsection \<open>Depth of branching conjunctions\<close>

primrec branching_conjunction_depth :: "('a, 's) hml_srbb \<Rightarrow> enat"
  and branch_conj_depth_\<chi> :: "('a, 's) hml_srbb_inner \<Rightarrow> enat"
  and branch_conj_depth_\<psi> :: "('a, 's) hml_srbb_conjunct \<Rightarrow> enat" where
  "branching_conjunction_depth TT = 0" |
  "branching_conjunction_depth (Internal \<chi>) = branch_conj_depth_\<chi> \<chi>" |
  "branching_conjunction_depth (ImmConj I \<psi>s) = Sup ((branch_conj_depth_\<psi> \<circ> \<psi>s) ` I)" |

  "branch_conj_depth_\<chi> (Obs _ \<phi>) = branching_conjunction_depth \<phi>" |
  "branch_conj_depth_\<chi> (Conj I \<psi>s) = Sup ((branch_conj_depth_\<psi> \<circ> \<psi>s) ` I)" |
  "branch_conj_depth_\<chi> (StableConj I \<psi>s) = Sup ((branch_conj_depth_\<psi> \<circ> \<psi>s) ` I)" |
  "branch_conj_depth_\<chi> (BranchConj _ \<phi> I \<psi>s) = 1 + Sup ({branching_conjunction_depth \<phi>} \<union> ((branch_conj_depth_\<psi> \<circ> \<psi>s) ` I))" |

  "branch_conj_depth_\<psi> (Pos \<chi>) = branch_conj_depth_\<chi> \<chi>" |
  "branch_conj_depth_\<psi> (Neg \<chi>) = branch_conj_depth_\<chi> \<chi>" 

subsection \<open>Depth of instable conjunctions\<close>

primrec
instable_conjunction_depth :: "('a, 's) hml_srbb \<Rightarrow> enat"
  and inst_conj_depth_\<chi> :: "('a, 's) hml_srbb_inner \<Rightarrow> enat"
  and inst_conj_depth_\<psi> :: "('a, 's) hml_srbb_conjunct \<Rightarrow> enat" where
  "instable_conjunction_depth TT = 0" |
  "instable_conjunction_depth (Internal \<chi>) = inst_conj_depth_\<chi> \<chi>" |
  "instable_conjunction_depth (ImmConj I \<psi>s) = 1 + Sup ((inst_conj_depth_\<psi> \<circ> \<psi>s) ` I)" |

  "inst_conj_depth_\<chi> (Obs _ \<phi>) = instable_conjunction_depth \<phi>" |
  "inst_conj_depth_\<chi> (Conj I \<psi>s) = 1 + Sup ((inst_conj_depth_\<psi> \<circ> \<psi>s) ` I)" |
  "inst_conj_depth_\<chi> (StableConj I \<psi>s) = Sup ((inst_conj_depth_\<psi> \<circ> \<psi>s) ` I)" |
  "inst_conj_depth_\<chi> (BranchConj _ \<phi> I \<psi>s) = Sup ({instable_conjunction_depth \<phi>} \<union> ((inst_conj_depth_\<psi> \<circ> \<psi>s) ` I))" |

  "inst_conj_depth_\<psi> (Pos \<chi>) = inst_conj_depth_\<chi> \<chi>" |
  "inst_conj_depth_\<psi> (Neg \<chi>) = inst_conj_depth_\<chi> \<chi>" 

subsection \<open>Depth of stable conjunctions\<close>

primrec
stable_conjunction_depth :: "('a, 's) hml_srbb \<Rightarrow> enat"
  and st_conj_depth_\<chi> :: "('a, 's) hml_srbb_inner \<Rightarrow> enat"
  and st_conj_depth_\<psi> :: "('a, 's) hml_srbb_conjunct \<Rightarrow> enat" where
  "stable_conjunction_depth TT = 0" |
  "stable_conjunction_depth (Internal \<chi>) = st_conj_depth_\<chi> \<chi>" |
  "stable_conjunction_depth (ImmConj I \<psi>s) = Sup ((st_conj_depth_\<psi> \<circ> \<psi>s) ` I)" |

  "st_conj_depth_\<chi> (Obs _ \<phi>) = stable_conjunction_depth \<phi>" |
  "st_conj_depth_\<chi> (Conj I \<psi>s) = Sup ((st_conj_depth_\<psi> \<circ> \<psi>s) ` I)" |
  "st_conj_depth_\<chi> (StableConj I \<psi>s) = 1 + Sup ((st_conj_depth_\<psi> \<circ> \<psi>s) ` I)" |
  "st_conj_depth_\<chi> (BranchConj _ \<phi> I \<psi>s) = Sup ({stable_conjunction_depth \<phi>} \<union> ((st_conj_depth_\<psi> \<circ> \<psi>s) ` I))" |

  "st_conj_depth_\<psi> (Pos \<chi>) = st_conj_depth_\<chi> \<chi>" |
  "st_conj_depth_\<psi> (Neg \<chi>) = st_conj_depth_\<chi> \<chi>" 

subsection \<open>Depth of immediate conjunctions\<close>

primrec
      immediate_conjunction_depth :: "('a, 's) hml_srbb \<Rightarrow> enat"
  and imm_conj_depth_\<chi> :: "('a, 's) hml_srbb_inner \<Rightarrow> enat"
  and imm_conj_depth_\<psi> :: "('a, 's) hml_srbb_conjunct \<Rightarrow> enat" where 
  "immediate_conjunction_depth TT = 0" |
  "immediate_conjunction_depth (Internal \<chi>) = imm_conj_depth_\<chi> \<chi>" |
  "immediate_conjunction_depth (ImmConj I \<psi>s) = 1 + Sup ((imm_conj_depth_\<psi> \<circ> \<psi>s) ` I)" |

  "imm_conj_depth_\<chi> (Obs _ \<phi>) = immediate_conjunction_depth \<phi>" |
  "imm_conj_depth_\<chi> (Conj I \<psi>s) = Sup ((imm_conj_depth_\<psi> \<circ> \<psi>s) ` I)" |
  "imm_conj_depth_\<chi> (StableConj I \<psi>s) = Sup ((imm_conj_depth_\<psi> \<circ> \<psi>s) ` I)" |
  "imm_conj_depth_\<chi> (BranchConj _ \<phi> I \<psi>s) = Sup ({immediate_conjunction_depth \<phi>} \<union> ((imm_conj_depth_\<psi> \<circ> \<psi>s) ` I))" |

  "imm_conj_depth_\<psi> (Pos \<chi>) = imm_conj_depth_\<chi> \<chi>" |
  "imm_conj_depth_\<psi> (Neg \<chi>) = imm_conj_depth_\<chi> \<chi>"

section \<open>Maximal modal depth of positive clauses in conjunctions\<close>

primrec
      max_positive_conjunct_depth :: "('a, 's) hml_srbb \<Rightarrow> enat"
  and max_pos_conj_depth_\<chi> :: "('a, 's) hml_srbb_inner \<Rightarrow> enat"
  and max_pos_conj_depth_\<psi> :: "('a, 's) hml_srbb_conjunct \<Rightarrow> enat" where
  "max_positive_conjunct_depth TT = 0"|
  "max_positive_conjunct_depth (Internal \<chi>) = max_pos_conj_depth_\<chi> \<chi>" |
  "max_positive_conjunct_depth (ImmConj I \<psi>s) = Sup ((max_pos_conj_depth_\<psi> \<circ> \<psi>s) ` I)" |

  "max_pos_conj_depth_\<chi> (Obs _ \<phi>) = max_positive_conjunct_depth \<phi>" |
  "max_pos_conj_depth_\<chi> (Conj I \<psi>s) = Sup ((max_pos_conj_depth_\<psi> \<circ> \<psi>s) ` I)" |
  "max_pos_conj_depth_\<chi> (StableConj I \<psi>s) = Sup ((max_pos_conj_depth_\<psi> \<circ> \<psi>s) ` I)" |
  "max_pos_conj_depth_\<chi> (BranchConj _ \<phi> I \<psi>s) = Sup ({max_positive_conjunct_depth \<phi>} \<union> ((max_pos_conj_depth_\<psi> \<circ> \<psi>s) ` I))" |

  "max_pos_conj_depth_\<psi> (Pos \<chi>) = modal_depth_srbb_inner \<chi>" |
  "max_pos_conj_depth_\<psi> (Neg \<chi>) = max_pos_conj_depth_\<chi> \<chi>"

subsection \<open>Maximal modal depth of negative clauses in conjunctions\<close>

primrec
      max_negative_conjunct_depth :: "('a, 's) hml_srbb \<Rightarrow> enat"
  and max_neg_conj_depth_\<chi> :: "('a, 's) hml_srbb_inner \<Rightarrow> enat"
  and max_neg_conj_depth_\<psi> :: "('a, 's) hml_srbb_conjunct \<Rightarrow> enat" where
  "max_negative_conjunct_depth TT = 0" |
  "max_negative_conjunct_depth (Internal \<chi>) = max_neg_conj_depth_\<chi> \<chi>" |
  "max_negative_conjunct_depth (ImmConj I \<psi>s) = Sup ((max_neg_conj_depth_\<psi> \<circ> \<psi>s) ` I)" |

  "max_neg_conj_depth_\<chi> (Obs _ \<phi>) = max_negative_conjunct_depth \<phi>" |
  "max_neg_conj_depth_\<chi> (Conj I \<psi>s) = Sup ((max_neg_conj_depth_\<psi> \<circ> \<psi>s) ` I)" |
  "max_neg_conj_depth_\<chi> (StableConj I \<psi>s) = Sup ((max_neg_conj_depth_\<psi> \<circ> \<psi>s) ` I)" |
  "max_neg_conj_depth_\<chi> (BranchConj _ \<phi> I \<psi>s) = Sup ({max_negative_conjunct_depth \<phi>} \<union> ((max_neg_conj_depth_\<psi> \<circ> \<psi>s) ` I))" |

  "max_neg_conj_depth_\<psi> (Pos \<chi>) = max_neg_conj_depth_\<chi> \<chi>" |
  "max_neg_conj_depth_\<psi> (Neg \<chi>) = modal_depth_srbb_inner \<chi>"

subsection \<open>Depth of negations\<close>

primrec
      negation_depth :: "('a, 's) hml_srbb \<Rightarrow> enat"
  and neg_depth_\<chi> :: "('a, 's) hml_srbb_inner \<Rightarrow> enat"
  and neg_depth_\<psi> :: "('a, 's) hml_srbb_conjunct \<Rightarrow> enat" where
  "negation_depth TT = 0" |
  "negation_depth (Internal \<chi>) = neg_depth_\<chi> \<chi>" |
  "negation_depth (ImmConj I \<psi>s) = Sup ((neg_depth_\<psi> \<circ> \<psi>s) ` I)" |

  "neg_depth_\<chi> (Obs _ \<phi>) = negation_depth \<phi>" |
  "neg_depth_\<chi> (Conj I \<psi>s) = Sup ((neg_depth_\<psi> \<circ> \<psi>s) ` I)" |
  "neg_depth_\<chi> (StableConj I \<psi>s) = Sup ((neg_depth_\<psi> \<circ> \<psi>s) ` I)" |
  "neg_depth_\<chi> (BranchConj _ \<phi> I \<psi>s) = Sup ({negation_depth \<phi>} \<union> ((neg_depth_\<psi> \<circ> \<psi>s) ` I))" |

  "neg_depth_\<psi> (Pos \<chi>) = neg_depth_\<chi> \<chi>" |
  "neg_depth_\<psi> (Neg \<chi>) = 1 + neg_depth_\<chi> \<chi>" 

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

fun expr_pr_\<chi> :: "('a, 's) hml_srbb_inner \<Rightarrow> energy" where
  "expr_pr_\<chi> \<chi> = E (modal_depth_srbb_inner \<chi>)
                 (branch_conj_depth_\<chi> \<chi>)
                 (inst_conj_depth_\<chi> \<chi>)
                 (st_conj_depth_\<chi> \<chi>)
                 (imm_conj_depth_\<chi> \<chi>)
                 (max_pos_conj_depth_\<chi> \<chi>)
                 (max_neg_conj_depth_\<chi> \<chi>)
                 (neg_depth_\<chi> \<chi>)"

lemma \<chi>_price_never_neg: "expr_pr_\<chi> \<chi> \<noteq> eneg"
  by simp

definition \<O>_\<chi> :: "energy \<Rightarrow> (('a, 's) hml_srbb_inner) set" where
  "\<O>_\<chi> energy \<equiv> {\<chi> . expr_pr_\<chi> \<chi> \<le> energy}"

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
