theory Hennessy_Milner_Logic
imports Behavioral_Equivalences
begin

datatype ('a, 'i) hml_formula =
HML_true
| HML_conj \<open>'i set\<close> \<open>'i \<Rightarrow> ('a,'i) hml_psi\<close>  (\<open>AND _ _\<close>)
| HML_poss \<open>'a\<close> \<open>('a,'i) hml_formula\<close>            (\<open>\<langle>_\<rangle>_\<close> [60] 60)
| HML_tau \<open>('a, 'i) hml_formula\<close>
| HML_eps \<open>('a, 'i) hml_formula\<close>

and ('a, 'i) hml_psi = 
HML_neg \<open>('a,'i) hml_formula\<close>                  (\<open>~_\<close> [20] 60)
| HML_phi \<open>('a, 'i) hml_formula\<close>

context lts_tau
begin

function satisfies :: \<open>'s \<Rightarrow> ('a,'s) hml_formula \<Rightarrow> bool\<close> (infix \<open>\<Turnstile>\<close> 50) 
and psi_sat :: \<open>'s \<Rightarrow> ('a,'s) hml_psi \<Rightarrow> bool\<close> (infix \<open>\<TTurnstile>\<close> 50)
where
\<open>(_ \<Turnstile> HML_true) = True\<close> |
  \<open>(p \<Turnstile> \<langle>\<alpha>\<rangle>\<phi>) = (\<exists>p'. p \<mapsto> \<alpha> p' \<and> p' \<Turnstile> \<phi>)\<close>|
  \<open>(p \<Turnstile> AND I \<Phi>) = (\<forall>i \<in> I. p \<TTurnstile> (\<Phi> i))\<close> |
\<open>p \<Turnstile> HML_tau \<phi> = (\<exists>p'. p \<mapsto> \<tau> p' \<and> p' \<Turnstile> \<phi>)\<close> |
\<open>p \<Turnstile> HML_eps \<phi> = (\<exists>p'. p \<Zsurj> p' \<and> p' \<Turnstile> \<phi>)\<close> |
\<open>psi_sat p (HML_neg \<phi>) = (\<not> (p \<Turnstile> \<phi>))\<close> |
\<open>psi_sat p (HML_phi \<phi>) = (p \<Turnstile> \<phi>)\<close>
  using hml_formula.exhaust hml_psi.exhaust
  by (metis sumE surj_pair, blast+)

inductive_set wf_rel_formula :: "(('s \<times> ('a, 's) hml_formula) + ('s \<times> ('a, 's) hml_psi)) rel" where
"(Inl (p, \<phi>), Inl (p', HML_poss \<alpha> \<phi>)) \<in> wf_rel_formula" |
"(Inl (p, \<phi>), Inl (p', HML_tau \<phi>)) \<in> wf_rel_formula" |
"(Inl (p, \<phi>), Inl (p', HML_eps \<phi>)) \<in> wf_rel_formula" |
"\<phi> = \<Phi> i \<and> i \<in> I \<Longrightarrow> (Inr (p, \<phi>), Inl (p, HML_conj I \<Phi>)) \<in> wf_rel_formula" |
"(Inl (p, \<phi>), Inr (p, HML_neg \<phi>)) \<in> wf_rel_formula" |
"(Inl (p, \<phi>), Inr (p, HML_phi \<phi>)) \<in> wf_rel_formula" 

lemma wf_rel_formula_wf: "wf wf_rel_formula"
  unfolding wf_def
proof safe
  show "\<And>P x. \<forall>x. (\<forall>y. (y, x) \<in> wf_rel_formula \<longrightarrow> P y) \<longrightarrow> P x \<Longrightarrow> P x" sorry
qed

termination
  using wf_rel_formula_wf wf_rel_formula.intros
  by (simp add: "termination")

end
end