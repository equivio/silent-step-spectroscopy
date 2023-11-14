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

function
    hml_depth     :: "('act, 'i) HML     \<Rightarrow> nat" and
    hml_neg_depth :: "('act, 'i) HML_neg \<Rightarrow> nat"
  where
    "hml_depth         HML_true = 0" |
    "hml_depth (HML_poss   a \<phi>) = Suc (hml_depth \<phi>)" |
    "hml_depth (HML_silent   \<phi>) = Suc (hml_depth \<phi>)" |
    "hml_depth (HML_internal \<phi>) = Suc (hml_depth \<phi>)" |
    "hml_depth (HML_conj  I \<psi>s) = Max {n . \<exists>i \<in> I. n = (hml_neg_depth (\<psi>s i))}" |

    "hml_neg_depth (HML_just \<phi>) = hml_depth \<phi>" |
    "hml_neg_depth (HML_not \<phi>)  = Suc (hml_depth \<phi>)"
  apply (metis HML.exhaust HML_neg.exhaust obj_sumE)
  by blast+

inductive_set hml_depth_argument_space :: "(('act, 'i) HML, ('act, 'i) HML_neg) sum rel" where
             "(Inl \<phi>,       Inl (HML_poss   a \<phi>)) \<in> hml_depth_argument_space" |
             "(Inl \<phi>,       Inl (HML_silent   \<phi>)) \<in> hml_depth_argument_space" |
             "(Inl \<phi>,       Inl (HML_internal \<phi>)) \<in> hml_depth_argument_space" |
  "xa \<in> I \<Longrightarrow> (Inr (\<psi>s xa), Inl (HML_conj  I \<psi>s)) \<in> hml_depth_argument_space" |
             "(Inl \<phi>,       Inr (HML_just     \<phi>)) \<in> hml_depth_argument_space" |
             "(Inl \<phi>,       Inr (HML_not      \<phi>)) \<in> hml_depth_argument_space"

lemma wf_hml_depth_argument_space: "wf hml_depth_argument_space"
  unfolding wf_def
proof safe
  fix P :: "('act, 'i) HML + ('act, 'i) HML_neg \<Rightarrow> bool"
  fix x :: "('act, 'i) HML + ('act, 'i) HML_neg"
  assume "\<forall>x. (\<forall>y. (y, x) \<in> hml_depth_argument_space \<longrightarrow> P y) \<longrightarrow> P x"
  then show "P x"
  proof (induct x)
    fix l :: "('act, 'i) HML"
    fix r :: "('act, 'i) HML_neg"

    show "\<forall>x. (\<forall>y. (y, x) \<in> hml_depth_argument_space \<longrightarrow> P y) \<longrightarrow> P x \<Longrightarrow> P (Inl l)"
     and "\<forall>x. (\<forall>y. (y, x) \<in> hml_depth_argument_space \<longrightarrow> P y) \<longrightarrow> P x \<Longrightarrow> P (Inr r)"
    proof (induct l and r)
      case HML_true
      then show ?case 
        by (smt (verit, ccfv_SIG) HML.distinct(1) HML.distinct(3) HML.distinct(5) HML.distinct(7) Inl_Inr_False Inl_inject hml_depth_argument_space.simps)
    next
      case (HML_poss x1 x2)
      then show ?case 
        by (smt (verit, ccfv_SIG) HML.distinct(11) HML.distinct(13) HML.distinct(9) HML.inject(1) Inl_Inr_False hml_depth_argument_space.simps sum.sel(1))
    next
      case (HML_silent x)
      then show ?case 
        by (smt (verit, ccfv_SIG) HML.distinct(15) HML.distinct(17) HML.distinct(9) HML.inject(2) Inl_Inr_False hml_depth_argument_space.simps sum.sel(1))
    next
      case (HML_internal x)
      then show ?case 
        by (smt (verit, del_insts) HML.distinct(11) HML.distinct(15) HML.distinct(19) HML.inject(3) Inl_Inr_False Inl_inject hml_depth_argument_space.simps)
    next
      case (HML_conj x1 x2)
      then show ?case 
        by (smt (verit, best) HML.distinct(13) HML.distinct(17) HML.distinct(19) HML.inject(4) Inl_Inr_False Inl_inject hml_depth_argument_space.cases rangeI)
    next
      case (HML_just x)
      then show ?case 
        by (smt (verit, ccfv_threshold) HML_neg.distinct(1) HML_neg.inject(1) Inl_Inr_False Inr_inject hml_depth_argument_space.simps) 
    next
      case (HML_not x)
      then show ?case 
        by (smt (verit, ccfv_threshold) HML_neg.distinct(1) HML_neg.inject(2) Inl_Inr_False Inr_inject hml_depth_argument_space.simps)
    qed
  qed
qed

termination hml_depth
  apply standard
  apply (rule wf_hml_depth_argument_space)
  using hml_depth_argument_space.intros by metis+

context LTS_Tau
begin

\<comment> \<open>
inductive_set processes :: "'s set" where
  "(s::'s) \<in> processes"

fun hml_semantic :: "('a, 's) HML \<Rightarrow> 's set" ("\<lbrakk>_\<rbrakk>HML" 60) where
  "\<lbrakk>HML_true\<rbrakk>HML = processes"
\<close>

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
                      apply (metis HML.exhaust HML_neg.exhaust sumE surj_pair)
                      apply simp
                      apply blast
                      apply fastforce
                      apply simp
                      apply force
                      apply blast
                      apply force
                      apply force
                     apply force
                    apply blast
                   apply force
                  apply fastforce
                 apply force
                apply simp
               apply blast
              apply blast
             apply fastforce
            apply simp
           apply simp
          apply fastforce
         apply fastforce
        apply force
       apply simp
      apply force
     apply fastforce
    apply simp
   apply simp
  by fastforce


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

  show "P \<phi>Or\<psi>s"
  proof (cases \<phi>Or\<psi>s)
    case (Inl \<phi>s)
    hence "\<phi>Or\<psi>s = Inl \<phi>s".
    then obtain \<phi> and s where "\<phi>Or\<psi>s = Inl (\<phi>, s)" by fastforce

    have "P (Inl (\<phi>, s))"
    proof (induct \<phi> arbitrary: s)
      case HML_true
      then show ?case 
        by (smt (verit) HML.distinct(1) HML.distinct(3) HML.distinct(5) HML.distinct(7) Inl_Inr_False \<open>\<forall>x. (\<forall>y. (y, x) \<in> hml_models_wf_arg_space \<longrightarrow> P y) \<longrightarrow> P x\<close> fst_conv hml_models_wf_arg_space.simps sum.sel(1)) 
    next
      case (HML_poss x1 \<phi>)
      then show ?case 
        by (smt (verit, best) HML.distinct(11) HML.distinct(13) HML.distinct(9) HML.inject(1) Inl_Inr_False \<open>\<forall>x. (\<forall>y. (y, x) \<in> hml_models_wf_arg_space \<longrightarrow> P y) \<longrightarrow> P x\<close> hml_models_wf_arg_space.simps prod.inject sum.inject(1))
    next
      case (HML_silent \<phi>)
      then show ?case 
        by (smt (verit, best) HML.distinct(15) HML.distinct(17) HML.distinct(9) HML.inject(2) Inl_Inr_False \<open>\<forall>x. (\<forall>y. (y, x) \<in> hml_models_wf_arg_space \<longrightarrow> P y) \<longrightarrow> P x\<close> hml_models_wf_arg_space.simps prod.inject sum.inject(1))
    next
      case (HML_internal \<phi>)
      then show ?case 
        by (smt (verit) HML.distinct(11) HML.distinct(15) HML.distinct(19) HML.inject(3) Inl_Inr_False \<open>\<forall>x. (\<forall>y. (y, x) \<in> hml_models_wf_arg_space \<longrightarrow> P y) \<longrightarrow> P x\<close> hml_models_wf_arg_space.simps prod.inject sum.inject(1))
    next
      case (HML_just \<phi>)
      then show ?thesis sorry
    next
      case (HML_not \<phi>)
      then show ?thesis sorry
    next 
      fix I :: "'s set"
      fix \<psi>s :: "'s \<Rightarrow> ('a, 's) HML_neg"
      fix p :: 's
      assume 
        "(\<And>x2a. x2a \<in> range \<psi>s  \<Longrightarrow> P (Inl (\<phi>, s)))"
      then show "P (Inl (HML_conj I \<psi>s, p))" sorry
    qed
      
    then show "P \<phi>Or\<psi>s" using \<open>\<phi>Or\<psi>s = Inl (\<phi>, s)\<close> by blast
  next
    case (Inr \<psi>s)
    then show "P \<phi>Or\<psi>s" sorry
  qed
qed

termination
  apply (relation hml_models_wf_arg_space)
  apply (rule wf_hml_models_wf_arg_space)
  using hml_models_wf_arg_space.intros by blast+

end

end