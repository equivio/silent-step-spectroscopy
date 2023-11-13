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
            "(Inl (\<phi>, x),    Inl (HML_poss   a \<phi>, p)) \<in> hml_models_wf_arg_space" |
            "(Inl (\<phi>, x),    Inl (HML_silent   \<phi>, p)) \<in> hml_models_wf_arg_space" |
            "(Inl (\<phi>, x),    Inl (HML_internal \<phi>, p)) \<in> hml_models_wf_arg_space" |
  "x \<in> I \<Longrightarrow> (Inr (\<psi>s x, p), Inl (HML_conj  I \<psi>s, p)) \<in> hml_models_wf_arg_space" |
            "(Inl (\<phi>, p),    Inr (HML_just     \<phi>, p)) \<in> hml_models_wf_arg_space" |
            "(Inl (\<phi>, p),    Inr (HML_not      \<phi>, p)) \<in> hml_models_wf_arg_space"

lemma wf_hml_models_wf_arg_space: "wf hml_models_wf_arg_space"
  unfolding wf_def
proof safe
  fix P p
  assume "\<forall>x. (\<forall>y. (y, x) \<in> hml_models_wf_arg_space \<longrightarrow>  P y) \<longrightarrow> P x"
  then show "P p"
  proof (cases p)
    case (Inl \<phi>x)
    hence "p = Inl \<phi>x".
    then show ?thesis sorry
  next
    case (Inr \<psi>x)
    then show ?thesis sorry
  qed
qed

termination
  apply standard
  apply (rule wf_hml_models_wf_arg_space)
  using hml_models_wf_arg_space.intros(1) apply blast
  apply (simp add: hml_models_wf_arg_space.intros(2))
  apply (simp add: hml_models_wf_arg_space.intros(3))
  using hml_models_wf_arg_space.intros(3) apply auto[1]
  using hml_models_wf_arg_space.intros(4) apply blast
  using hml_models_wf_arg_space.intros(5) apply auto[1]
  by (simp add: hml_models_wf_arg_space.intros(6))
  

end

end