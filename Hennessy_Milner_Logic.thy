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

thm hml_formula.induct
thm hml_psi.induct

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

find_theorems local.satisfies

inductive_set wf_rel_formula :: "(('s \<times> ('a, 's) hml_formula) + ('s \<times> ('a, 's) hml_psi)) rel" where
"(Inl (p, \<phi>), Inl (p', HML_poss \<alpha> \<phi>)) \<in> wf_rel_formula" |
"(Inl (p, \<phi>), Inl (p', HML_tau \<phi>)) \<in> wf_rel_formula" |
"(Inl (p, \<phi>), Inl (p', HML_eps \<phi>)) \<in> wf_rel_formula" |
"\<phi> = \<Phi> i \<and> i \<in> I \<Longrightarrow> (Inr (p, \<phi>), Inl (p, HML_conj I \<Phi>)) \<in> wf_rel_formula" |
"(Inl (p, \<phi>), Inr (p, HML_neg \<phi>)) \<in> wf_rel_formula" |
"(Inl (p, \<phi>), Inr (p, HML_phi \<phi>)) \<in> wf_rel_formula" 

find_theorems wf_rel_formula

lemma wf_rel_formula_wf: "wf wf_rel_formula"
  unfolding wf_def
proof safe
  fix P and tuple :: "'s \<times> ('a, 's) hml_formula + 's \<times> ('a, 's) hml_psi"
  assume  A1 :"\<forall>x. (\<forall>y. (y, x) \<in> wf_rel_formula \<longrightarrow> P y) \<longrightarrow> P x"
  then show "P tuple"
  proof(induct tuple)
    fix l :: "'s  \<times> ('a, 's) hml_formula" and 
        r :: "'s \<times> ('a, 's) hml_psi"
obtain \<phi> p \<psi> p' where
      l_def: "l = (p, \<phi>)" and
      r_def: "r = (p', \<psi>)" by fastforce
      show "\<forall>y. (\<forall>x. (x, y) \<in> wf_rel_formula \<longrightarrow> P x) \<longrightarrow> P y \<Longrightarrow> P (Inl l)"  and
         "\<forall>y. (\<forall>x. (x, y) \<in> wf_rel_formula \<longrightarrow> P x) \<longrightarrow> P y \<Longrightarrow> P (Inr r)"
        unfolding l_def r_def
      proof(induct \<phi> and \<psi> arbitrary: p and p')
        case HML_true
        then show ?case using hml_formula.distinct wf_rel_formula.simps 
          by (smt (verit) Inl_inject Inr_not_Inl Pair_inject) 
      next
        case (HML_conj x1 x2)
        then show ?case using hml_formula.distinct wf_rel_formula.simps
          by (smt (verit) Inl_inject Inr_not_Inl Pair_inject hml_formula.inject(1) range_eqI)
      next
        case (HML_poss x1 x2)
        then show ?case using hml_formula.distinct wf_rel_formula.simps
          by (smt (verit) Inl_inject Inr_not_Inl Pair_inject hml_formula.inject(2))
      next
        case (HML_tau x)
        then show ?case using hml_formula.distinct wf_rel_formula.simps
          by (smt (verit) Inl_inject Inr_not_Inl Pair_inject hml_formula.inject(3))
      next
        case (HML_eps x)
        then show ?case using hml_formula.distinct wf_rel_formula.simps
          by (smt (verit) Inl_inject Inr_not_Inl Pair_inject hml_formula.inject(4))
      next
        case (HML_neg x)
        then show ?case using hml_formula.distinct wf_rel_formula.simps
          by (smt (verit) Inr_inject Inr_not_Inl Pair_inject hml_psi.distinct(1) hml_psi.inject(1))
      next
        case (HML_phi x)
        then show ?case using hml_formula.distinct wf_rel_formula.simps
          by (smt (verit) Inr_inject Inr_not_Inl Pair_inject hml_psi.distinct(1) hml_psi.inject(2))
      qed
    qed
  qed

termination
  using wf_rel_formula_wf wf_rel_formula.intros
  by (simp add: "termination")

end
end