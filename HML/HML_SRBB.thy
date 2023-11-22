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

function
      modal_depth_srbb :: "('act, 'i) HML_srbb \<Rightarrow> nat"
  and modal_depth_srbb_conjunction :: "('act, 'i) HML_srbb_conjunction \<Rightarrow> nat"
  and modal_depth_srbb_conjunct :: "('act, 'i) HML_srbb_conjunct \<Rightarrow> nat" where
 "modal_depth_srbb HML_srbb_true = 0" |
 "modal_depth_srbb (HML_srbb_silent \<chi>) = modal_depth_srbb_conjunction \<chi>" |

 "modal_depth_srbb_conjunction (HML_srbb_poss \<alpha> \<phi>) = 1 + modal_depth_srbb \<phi>" |
 "modal_depth_srbb_conjunction (HML_srbb_conj I \<psi>s) =
    Max ({0} \<union> {modal_depth_srbb_conjunct (\<psi>s i) | i. i \<in> I})" |
 "modal_depth_srbb_conjunction (HML_srbb_stable_conj I \<psi>s) = 
    Max ({0} \<union> {modal_depth_srbb_conjunct (\<psi>s i) | i. i \<in> I})" |
 "modal_depth_srbb_conjunction (HML_srbb_branch_conj a \<phi> I \<psi>s) =
    Max ({1 + modal_depth_srbb \<phi>} \<union> {modal_depth_srbb_conjunct (\<psi>s i) | i. i \<in> I})" |

 "modal_depth_srbb_conjunct (HML_srbb_silent_pos \<chi>) = modal_depth_srbb_conjunction \<chi>" |
 "modal_depth_srbb_conjunct (HML_srbb_silent_neg \<chi>) = modal_depth_srbb_conjunction \<chi>"
  
  apply (metis HML_srbb.exhaust HML_srbb_conjunct.exhaust HML_srbb_conjunction.exhaust old.sum.exhaust)
  by blast+

inductive_set modal_depth_srbb_arg_space 
           :: "(('act, 'i) HML_srbb + 
                ('act, 'i) HML_srbb_conjunction + 
                ('act, 'i) HML_srbb_conjunct) rel" where
  "(Inr (Inl \<chi>), 
   Inl (HML_srbb_silent \<chi>)) \<in> modal_depth_srbb_arg_space" |

  "(Inl \<phi>,
   Inr (Inl (HML_srbb_poss \<alpha> \<phi>))) \<in> modal_depth_srbb_arg_space" |
  "(Inr (Inr (\<psi>s xa)),
   Inr (Inl (HML_srbb_conj I \<psi>s))) \<in> modal_depth_srbb_arg_space" |
  "(Inr (Inr (\<psi>s xa)),
   Inr (Inl (HML_srbb_stable_conj I \<psi>s))) \<in> modal_depth_srbb_arg_space" |
  "(Inl \<phi>,
   Inr (Inl (HML_srbb_branch_conj a \<phi> I \<psi>s))) \<in> modal_depth_srbb_arg_space" |
  "(Inr (Inr (\<psi>s xa)),
   Inr (Inl (HML_srbb_branch_conj a \<phi> I \<psi>s))) \<in> modal_depth_srbb_arg_space" |

  "(Inr (Inl \<chi>),
   Inr (Inr (HML_srbb_silent_pos \<chi>))) \<in> modal_depth_srbb_arg_space" |
  "(Inr (Inl \<chi>),
   Inr (Inr (HML_srbb_silent_neg \<chi>))) \<in> modal_depth_srbb_arg_space"

lemma wf_modal_depth_srbb_arg_space : "wf modal_depth_srbb_arg_space"
  unfolding wf_def
proof safe
  fix P x
  assume "\<forall>x. (\<forall>y. (y, x) \<in> modal_depth_srbb_arg_space \<longrightarrow> P y) \<longrightarrow> P x"
  then show "P x"
  proof (induct x)
    fix \<phi>
    fix \<chi>\<psi>
    show "P (Inl \<phi>)" and "P (Inr \<chi>\<psi>)"
    proof (induct \<chi>\<psi>)
      fix \<chi>
      fix \<psi>
      have "P (Inl \<phi>)" and "P (Inr (Inl \<chi>))" and "P (Inr (Inr \<psi>))"
        using \<open>\<forall>x. (\<forall>y. (y, x) \<in> modal_depth_srbb_arg_space \<longrightarrow> P y) \<longrightarrow> P x\<close>
      proof (induct \<phi> and \<chi> and \<psi>)
        case HML_srbb_true
        then show ?case 
          by (smt (verit) HML_srbb.distinct(1) Inl_inject modal_depth_srbb_arg_space.simps sum.distinct(1))
      next
        case (HML_srbb_silent x)
        then show ?case 
          by (smt (verit) HML_srbb.inject Inl_inject modal_depth_srbb_arg_space.simps sum.distinct(1))
      next
        case (HML_srbb_poss x1 x2)
        then show ?case 
          by (smt (verit) HML_srbb_conjunction.distinct(1) HML_srbb_conjunction.distinct(3) HML_srbb_conjunction.distinct(5) HML_srbb_conjunction.inject(1) Inl_Inr_False Inl_inject Inr_inject modal_depth_srbb_arg_space.simps)
      next
        case (HML_srbb_conj x1 x2)
        then show ?case 
          by (smt (verit) HML_srbb_conjunction.distinct(1) HML_srbb_conjunction.distinct(7) HML_srbb_conjunction.distinct(9) HML_srbb_conjunction.inject(2) Inl_Inr_False Inl_inject Inr_inject modal_depth_srbb_arg_space.simps range_eqI)
      next
        case (HML_srbb_stable_conj x1 x2)
        then show ?case 
          by (smt (verit) HML_srbb_conjunction.distinct(11) HML_srbb_conjunction.distinct(3) HML_srbb_conjunction.distinct(7) HML_srbb_conjunction.inject(3) Inl_Inr_False Inr_inject modal_depth_srbb_arg_space.simps range_eqI sum.inject(1))
      next
        case (HML_srbb_branch_conj x1 x2 x3 x4)
        then show ?case 
          by (smt (verit) HML_srbb_conjunction.distinct(11) HML_srbb_conjunction.distinct(5) HML_srbb_conjunction.distinct(9) HML_srbb_conjunction.inject(4) Inl_Inr_False Inl_inject Inr_inject modal_depth_srbb_arg_space.simps range_eqI)
      next
        case (HML_srbb_silent_pos x)
        then show ?case 
          by (smt (verit) HML_srbb_conjunct.distinct(1) HML_srbb_conjunct.inject(1) Inl_Inr_False Inr_inject modal_depth_srbb_arg_space.simps)
      next
        case (HML_srbb_silent_neg x)
        then show ?case 
          by (smt (verit) HML_srbb_conjunct.distinct(1) HML_srbb_conjunct.inject(2) Inl_Inr_False Inr_inject modal_depth_srbb_arg_space.simps)
      qed
      then show "P (Inl \<phi>)" and "P (Inr (Inl \<chi>))" and "P (Inl \<phi>)" and "P (Inr (Inr \<psi>))" by auto
    qed
  qed
qed

termination
  using wf_modal_depth_srbb_arg_space and modal_depth_srbb_arg_space.intros 
  by (relation modal_depth_srbb_arg_space) force+

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