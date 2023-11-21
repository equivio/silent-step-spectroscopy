theory HML
  imports Main "../LTS"
begin

datatype 
  ('act, 'i) HML =
    HML_true |
    HML_poss 'act "('act, 'i) HML" |
    HML_silent "('act, 'i) HML" |
    HML_internal "('act, 'i) HML" |
    HML_conj "'i set" "'i \<Rightarrow> ('act, 'i) HML_neg"
and
  ('act, 'i) HML_neg =
    HML_just "('act, 'i) HML" |
    HML_not "('act, 'i) HML"

context LTS_Tau
begin

function
      hml_models     :: "('a, 's) HML     \<Rightarrow> 's \<Rightarrow> bool" ("_ \<Turnstile> _" 60) 
  and hml_neg_models :: "('a, 's) HML_neg \<Rightarrow> 's \<Rightarrow> bool"
where
  "(HML_true         \<Turnstile> _) = True" |
  "((HML_poss a \<phi>)   \<Turnstile> p) = (\<exists>p'. p \<mapsto> a p' \<and> (\<phi> \<Turnstile> p'))" |
  "((HML_silent \<phi>)   \<Turnstile> p) = (\<exists>p'. p \<Zsurj> p' \<and> (\<phi> \<Turnstile> p'))" |
  "((HML_internal \<phi>) \<Turnstile> p) = ((\<exists>p'. p \<mapsto> \<tau> p' \<and> (\<phi> \<Turnstile> p')) \<or> (\<phi> \<Turnstile> p))" |
  "((HML_conj I \<psi>s)  \<Turnstile> p) = (\<forall>i \<in> I. hml_neg_models (\<psi>s i) p)" |

  "(hml_neg_models (HML_just \<phi>) p) = (\<phi> \<Turnstile> p)" |
  "(hml_neg_models (HML_not \<phi>) p) = (\<not>(\<phi> \<Turnstile> p))"
  by (metis HML.exhaust HML_neg.exhaust sumE surj_pair, auto)
            
inductive_set hml_models_wf_arg_space :: "(('a, 's) HML \<times> 's, ('a, 's) HML_neg \<times> 's) sum rel" where
                         "(Inl (\<phi>, x), Inl (HML_poss   a \<phi>, p)) \<in> hml_models_wf_arg_space" |
                         "(Inl (\<phi>, x), Inl (HML_silent   \<phi>, p)) \<in> hml_models_wf_arg_space" |
                         "(Inl (\<phi>, x), Inl (HML_internal \<phi>, p)) \<in> hml_models_wf_arg_space" |
  "i \<in> I \<Longrightarrow> \<psi> = \<psi>s i \<Longrightarrow> (Inr (\<psi>, p), Inl (HML_conj  I \<psi>s, p)) \<in> hml_models_wf_arg_space" |
                         "(Inl (\<phi>, p), Inr (HML_just     \<phi>, p)) \<in> hml_models_wf_arg_space" |
                         "(Inl (\<phi>, p), Inr (HML_not      \<phi>, p)) \<in> hml_models_wf_arg_space"

lemma wf_hml_models_wf_arg_space: "wf hml_models_wf_arg_space"
  unfolding wf_def
proof safe
  fix P :: "('a, 's) HML \<times> 's + ('a, 's) HML_neg \<times> 's \<Rightarrow> bool"
  fix \<phi>Or\<psi>s :: "('a, 's) HML \<times> 's + ('a, 's) HML_neg \<times> 's"

  assume "\<forall>x. (\<forall>y. (y, x) \<in> hml_models_wf_arg_space \<longrightarrow> P y) \<longrightarrow> P x"

  then show "P \<phi>Or\<psi>s"
  proof (induct \<phi>Or\<psi>s)
    fix \<phi>s :: "('a, 's) HML \<times> 's"
    obtain \<phi> and sl where "\<phi>s = (\<phi>, sl)" by fastforce

    fix \<psi>s :: "('a, 's) HML_neg \<times> 's"
    obtain \<psi> and sr where "\<psi>s = (\<psi>, sr)" by fastforce

    show "P (Inl \<phi>s)" and "P (Inr \<psi>s)"
      unfolding \<open>\<phi>s = (\<phi>, sl)\<close> and \<open>\<psi>s = (\<psi>, sr)\<close>
    proof (induct \<phi> and \<psi> arbitrary: sl and sr)
      case HML_true
      then show ?case 
        by (smt (verit) HML.distinct(1) HML.distinct(3) HML.distinct(5) HML.distinct(7) Inl_inject Pair_inject \<open>\<forall>x. (\<forall>y. (y, x) \<in> hml_models_wf_arg_space \<longrightarrow> P y) \<longrightarrow> P x\<close> hml_models_wf_arg_space.simps sum.distinct(1))
    next
      case (HML_poss x1 x2)
      then show ?case 
        by (smt (verit, best) HML.distinct(11) HML.distinct(13) HML.distinct(9) HML.inject(1) Inl_Inr_False \<open>\<forall>x. (\<forall>y. (y, x) \<in> hml_models_wf_arg_space \<longrightarrow> P y) \<longrightarrow> P x\<close> hml_models_wf_arg_space.simps prod.inject sum.sel(1))
    next
      case (HML_silent x)
      then show ?case 
        by (smt (verit, best) HML.distinct(15) HML.distinct(17) HML.distinct(9) HML.inject(2) Inl_Inr_False Inl_inject Pair_inject \<open>\<forall>x. (\<forall>y. (y, x) \<in> hml_models_wf_arg_space \<longrightarrow> P y) \<longrightarrow> P x\<close> hml_models_wf_arg_space.simps)
    next
      case (HML_internal x)
      then show ?case 
        by (smt (verit) HML.distinct(11) HML.distinct(15) HML.distinct(19) HML.inject(3) Inl_Inr_False Inl_inject \<open>\<forall>x. (\<forall>y. (y, x) \<in> hml_models_wf_arg_space \<longrightarrow> P y) \<longrightarrow> P x\<close> hml_models_wf_arg_space.simps prod.inject)
    next
      case (HML_conj x1 x2)
      then show ?case 
        by (smt (verit) HML.distinct(13) HML.distinct(17) HML.distinct(19) HML.inject(4) Inl_Inr_False Inl_inject Pair_inject \<open>\<forall>x. (\<forall>y. (y, x) \<in> hml_models_wf_arg_space \<longrightarrow> P y) \<longrightarrow> P x\<close> hml_models_wf_arg_space.simps range_eqI)
    next
      case (HML_just x)
      then show ?case 
        by (smt (verit) HML_neg.distinct(1) HML_neg.inject(1) Inl_Inr_False Inr_inject Pair_inject \<open>\<forall>x. (\<forall>y. (y, x) \<in> hml_models_wf_arg_space \<longrightarrow> P y) \<longrightarrow> P x\<close> hml_models_wf_arg_space.simps)
    next
      case (HML_not x)
      then show ?case 
        by (smt (verit) HML_neg.distinct(1) HML_neg.inject(2) Inl_Inr_False \<open>\<forall>x. (\<forall>y. (y, x) \<in> hml_models_wf_arg_space \<longrightarrow> P y) \<longrightarrow> P x\<close> fst_conv hml_models_wf_arg_space.simps sum.sel(2))
    qed
  qed
qed

termination
  using wf_hml_models_wf_arg_space
  by (standard) (simp add: hml_models_wf_arg_space.intros)+

end

end