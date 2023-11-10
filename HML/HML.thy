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
fun hml_semantic :: "('a, 's) HML \<Rightarrow> 's set" ("\<lbrakk>_\<rbrakk>HML" 60) where
  "\<lbrakk>HML_true\<rbrakk>HML = {}" (* How to get the set of all processes? 's set? *)
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

termination
proof

end

end