theory HML_SRBB
  imports Main "HOL-Library.Countable_Set_Type" "./HML"
begin

datatype 
  'act HML_srbb =
    HML_srbb_silent       "'act HML_srbb_conjunction" |
    HML_srbb_imm_conj     "'act HML_srbb_conjunct cset"
and
  'act HML_srbb_conjunction =
    HML_srbb_poss         'act "'act HML_srbb" |
    HML_srbb_conj         "'act HML_srbb_conjunct cset" |
    HML_srbb_stable_conj  "'act HML_srbb_conjunct cset" |
    HML_srbb_branch_conj  'act "'act HML_srbb"
                          "'act HML_srbb_conjunct cset"
and
  'act HML_srbb_conjunct =
    HML_srbb_silent_pos   "'act HML_srbb_conjunction" |
    HML_srbb_silent_neg   "'act HML_srbb_conjunction"

function
  modal_depth_srbb             :: "'act HML_srbb \<Rightarrow> nat" and
  modal_depth_srbb_conjunction :: "'act HML_srbb_conjunction \<Rightarrow> nat" and
  modal_depth_srbb_conjunct    :: "'act HML_srbb_conjunct \<Rightarrow> nat"
  where
    "modal_depth_srbb (HML_srbb_silent \<chi>) = modal_depth_srbb_conjunction \<chi>" |
    "modal_depth_srbb (HML_srbb_imm_conj \<psi>s) =
      Max (rcset (cinsert 0 (cimage modal_depth_srbb_conjunct \<psi>s)))" |

    "modal_depth_srbb_conjunction (HML_srbb_poss \<alpha> \<phi>) = 1 + modal_depth_srbb \<phi>" |
    "modal_depth_srbb_conjunction (HML_srbb_conj \<psi>s) =
      Max (rcset (cinsert 0 (cimage modal_depth_srbb_conjunct \<psi>s)))" |
    "modal_depth_srbb_conjunction (HML_srbb_stable_conj \<psi>s) = 
      Max (rcset (cinsert 0 (cimage modal_depth_srbb_conjunct \<psi>s)))" |
    "modal_depth_srbb_conjunction (HML_srbb_branch_conj a \<phi> \<psi>s) =
      Max (rcset (cinsert (1 + modal_depth_srbb \<phi>) (cimage modal_depth_srbb_conjunct \<psi>s)))" |

    "modal_depth_srbb_conjunct (HML_srbb_silent_pos \<chi>) = modal_depth_srbb_conjunction \<chi>" |
    "modal_depth_srbb_conjunct (HML_srbb_silent_neg \<chi>) = modal_depth_srbb_conjunction \<chi>"
  using HML_srbb.exhaust HML_srbb_conjunction.exhaust HML_srbb_conjunct.exhaust
  sorry \<comment>\<open>Probably impossible due to \<^theory_text>\<open>Max\<close> being defined only on finite sets?\<close>

type_synonym 'act HML_srbb_sum = "'act HML_srbb + 'act HML_srbb_conjunction + 'act HML_srbb_conjunct"

inductive_set modal_depth_srbb_arg_space :: "'act HML_srbb_sum rel" where
  "(Inr (Inl \<chi>), 
   Inl (HML_srbb_silent \<chi>)) \<in> modal_depth_srbb_arg_space" |
  "cin \<psi> \<psi>s \<Longrightarrow>
   (Inr (Inr \<psi>),
    Inl (HML_srbb_imm_conj \<psi>s)) \<in> modal_depth_srbb_arg_space" |

  "(Inl \<phi>,
    Inr (Inl (HML_srbb_poss \<alpha> \<phi>))) \<in> modal_depth_srbb_arg_space" |
  "cin \<psi> \<psi>s \<Longrightarrow>
   (Inr (Inr \<psi>),
    Inr (Inl (HML_srbb_conj \<psi>s))) \<in> modal_depth_srbb_arg_space" |
  "cin \<psi> \<psi>s \<Longrightarrow>
   (Inr (Inr \<psi>),
    Inr (Inl (HML_srbb_stable_conj \<psi>s))) \<in> modal_depth_srbb_arg_space" |
  "(Inl \<phi>,
    Inr (Inl (HML_srbb_branch_conj a \<phi> \<psi>s))) \<in> modal_depth_srbb_arg_space" |
  "cin \<psi> \<psi>s \<Longrightarrow>
   (Inr (Inr \<psi>),
    Inr (Inl (HML_srbb_branch_conj a \<phi> \<psi>s))) \<in> modal_depth_srbb_arg_space" |

  "(Inr (Inl \<chi>),
   Inr (Inr (HML_srbb_silent_pos \<chi>))) \<in> modal_depth_srbb_arg_space" |
  "(Inr (Inl \<chi>),
   Inr (Inr (HML_srbb_silent_neg \<chi>))) \<in> modal_depth_srbb_arg_space"

lemma wf_modal_depth_srbb_arg_space : "wf modal_depth_srbb_arg_space"
  unfolding wf_def
proof safe
  fix P and x :: "'act HML_srbb_sum"
  assume "\<forall>x :: 'act HML_srbb_sum. (\<forall>y. (y, x) \<in> modal_depth_srbb_arg_space \<longrightarrow> P y) \<longrightarrow> P x"
  then show "P x"
  proof (induct x)
    fix \<phi>
    fix \<chi>\<psi>
    show "P (Inl \<phi>)" and "P (Inr \<chi>\<psi>)"
    proof (induct \<chi>\<psi>)
      fix \<chi>
      fix \<psi>
      show "P (Inl \<phi>)" and "P (Inr (Inl \<chi>))" and "P (Inr (Inr \<psi>))"
        using \<open>\<forall>x. (\<forall>y. (y, x) \<in> modal_depth_srbb_arg_space \<longrightarrow> P y) \<longrightarrow> P x\<close>
      proof (induct \<phi> and \<chi> and \<psi>)
        case (HML_srbb_silent x)
        then show ?case
          by (smt (verit) HML_srbb.distinct(2) HML_srbb.inject(1) Inl_inject modal_depth_srbb_arg_space.simps sum.simps(4))
(*
          by (smt (verit) HML_srbb.distinct(1) HML_srbb.inject(1) Inl_Inr_False Inl_inject modal_depth_srbb_arg_space.cases)
*)
      next
        case (HML_srbb_imm_conj x)
        then show ?case
          by (smt (verit) HML_srbb.distinct(1) HML_srbb.inject(2) Inl_Inr_False Inl_inject cin.rep_eq modal_depth_srbb_arg_space.cases)
      next
        case (HML_srbb_poss x1 x2)
        then show ?case
          by (smt (verit) HML_srbb_conjunction.distinct(1) HML_srbb_conjunction.distinct(3) HML_srbb_conjunction.distinct(5) HML_srbb_conjunction.inject(1) Inl_Inr_False Inl_inject Inr_inject modal_depth_srbb_arg_space.cases)
      next
        case (HML_srbb_conj x)
        then show ?case
          by (smt (verit) HML_srbb_conjunction.distinct(1) HML_srbb_conjunction.distinct(7) HML_srbb_conjunction.distinct(9) HML_srbb_conjunction.inject(2) Inl_Inr_False Inl_inject Inr_inject cin.rep_eq modal_depth_srbb_arg_space.cases)
(*
          by (smt (verit) HML_srbb_conjunction.distinct(1) HML_srbb_conjunction.distinct(7) HML_srbb_conjunction.distinct(9) HML_srbb_conjunction.inject(2) Inl_Inr_False Inr_inject cin.rep_eq modal_depth_srbb_arg_space.cases sum.inject(1))
*)
      next
        case (HML_srbb_stable_conj x)
        then show ?case
          by (smt (verit) HML_srbb_conjunction.distinct(11) HML_srbb_conjunction.distinct(3) HML_srbb_conjunction.distinct(7) HML_srbb_conjunction.inject(3) Inl_Inr_False cin.rep_eq modal_depth_srbb_arg_space.cases sum.inject(1) sum.inject(2))
(*
          by (smt (verit) HML_srbb_conjunction.distinct(11) HML_srbb_conjunction.distinct(3) HML_srbb_conjunction.distinct(7) HML_srbb_conjunction.inject(3) Inl_Inr_False Inl_inject Inr_inject cin.rep_eq modal_depth_srbb_arg_space.cases)
          by (smt (verit) HML_srbb_conjunction.distinct(11) HML_srbb_conjunction.distinct(3) HML_srbb_conjunction.distinct(7) HML_srbb_conjunction.inject(3) Inl_Inr_False Inr_inject cin.rep_eq modal_depth_srbb_arg_space.cases sum.inject(1))
*)
      next
        case (HML_srbb_branch_conj x1 x2 x3)
        then show ?case
          by (smt (verit) HML_srbb_conjunction.distinct(11) HML_srbb_conjunction.distinct(5) HML_srbb_conjunction.distinct(9) HML_srbb_conjunction.inject(4) Inl_Inr_False Inl_inject Inr_inject cin.rep_eq modal_depth_srbb_arg_space.cases)
(*
          by (smt (verit) HML_srbb_conjunction.distinct(11) HML_srbb_conjunction.distinct(5) HML_srbb_conjunction.distinct(9) HML_srbb_conjunction.inject(4) Inl_Inr_False Inr_inject cin.rep_eq modal_depth_srbb_arg_space.cases sum.inject(1))
*)
      next
        case (HML_srbb_silent_pos x)
        then show ?case
          by (smt (verit) HML_srbb_conjunct.distinct(1) HML_srbb_conjunct.inject(1) Inl_Inr_False Inr_inject modal_depth_srbb_arg_space.cases)
      next
        case (HML_srbb_silent_neg x)
        then show ?case
          using modal_depth_srbb_arg_space.cases by auto
      qed
      show "P (Inl \<phi>)" using \<open>P (Inl \<phi>)\<close> .
    qed
  qed
qed

termination
  using wf_modal_depth_srbb_arg_space
  by (relation modal_depth_srbb_arg_space) (auto simp add: modal_depth_srbb_arg_space.intros cin.rep_eq)

context LTS_Tau
begin

function
  hml_srbb_to_hml              :: "'a HML_srbb \<Rightarrow> 'a hml" and
  hml_srbb_conjunction_to_hml  :: "'a HML_srbb_conjunction \<Rightarrow> 'a hml" and
  hml_srbb_conjunct_to_hml_neg :: "'a HML_srbb_conjunct \<Rightarrow> 'a hml_conjunct"
where
  "hml_srbb_to_hml (HML_srbb_silent    \<chi>) = HML.Silent (hml_srbb_conjunction_to_hml \<chi>)" |
  "hml_srbb_to_hml (HML_srbb_imm_conj \<psi>s) = HML.Conj (cimage hml_srbb_conjunct_to_hml_neg \<psi>s)" |

  "hml_srbb_conjunction_to_hml (HML_srbb_poss a \<phi>) = HML.Obs a (hml_srbb_to_hml \<phi>)" |
  "hml_srbb_conjunction_to_hml (HML_srbb_conj  \<psi>s) = HML.Conj (cimage hml_srbb_conjunct_to_hml_neg \<psi>s)" |

  "hml_srbb_conjunction_to_hml (HML_srbb_stable_conj \<psi>s) =
    (let foo = HML.Neg (HML.Obs \<tau> HML.TT) in
    HML.Conj (cinsert foo (cimage hml_srbb_conjunct_to_hml_neg \<psi>s)))" |

  "hml_srbb_conjunction_to_hml (HML_srbb_branch_conj a \<phi> \<psi>s) = 
    (let foo =
      if a = \<tau>
        then HML.Pos (HML.Internal (hml_srbb_to_hml \<phi>))
        else HML.Pos (HML.Obs a    (hml_srbb_to_hml \<phi>)) in
    HML.Conj (cinsert foo (cimage hml_srbb_conjunct_to_hml_neg \<psi>s)))" |

  "hml_srbb_conjunct_to_hml_neg (HML_srbb_silent_pos \<chi>) = HML.Pos (hml_srbb_conjunction_to_hml \<chi>)" |
  "hml_srbb_conjunct_to_hml_neg (HML_srbb_silent_neg \<chi>) = HML.Neg (hml_srbb_conjunction_to_hml \<chi>)"

  by (metis HML_srbb.exhaust HML_srbb_conjunct.exhaust HML_srbb_conjunction.exhaust sumE, fastforce+)


end

end