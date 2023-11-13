theory HML
  imports Main "../LTS"
begin

datatype 
  ('act, 'i) HML =
    HML_true |
    HML_poss 'act "('act, 'i) HML" |
    HML_silent "('act, 'i) HML" |
    HML_internal "('act, 'i) HML" |
    HML_conj "'i set" "'i \<Rightarrow>  (('act, 'i) HML, ('act, 'i) HML) sum"


context LTS_Tau
begin

\<comment> \<open>
fun hml_semantic :: "('a, 's) HML \<Rightarrow> 's set" ("\<lbrakk>_\<rbrakk>HML" 60) where
  "\<lbrakk>HML_true\<rbrakk>HML = {}" (* How to get the set of all processes? 's set? *)
\<close>

function hml_models     :: "('a, 's) HML     \<Rightarrow> 's \<Rightarrow> bool" ("_ \<Turnstile> _" 60) 
where
  "(HML_true         \<Turnstile> _) = True" |
  "((HML_poss a \<phi>)   \<Turnstile> p) = (\<exists>p'. p \<mapsto> a p' \<and> (\<phi> \<Turnstile> p'))" |
  "((HML_silent \<phi>)   \<Turnstile> p) = (\<exists>p'. p \<Zsurj> p' \<and> (\<phi> \<Turnstile> p'))" |
  "((HML_internal \<phi>) \<Turnstile> p) = ((\<exists>p'. p \<mapsto> \<tau> p' \<and> (\<phi> \<Turnstile> p')) \<or> (\<phi> \<Turnstile> p))" |
  "((HML_conj I \<psi>s)  \<Turnstile> p) = (\<forall>i \<in> I. (\<lambda>x. case x of Inl tr \<Rightarrow> (tr \<Turnstile> p) | Inr fl \<Rightarrow> \<not>(fl \<Turnstile> p)) (\<psi>s i))" 
                 apply (metis HML.exhaust surj_pair)
                apply simp
               apply simp
              apply fastforce
             apply blast
            apply simp
           apply fastforce
          apply fastforce
         apply force
        apply fastforce
       apply fastforce
      apply simp
     apply fastforce
    apply force
   apply simp
  by fastforce

termination
proof
 
end

end