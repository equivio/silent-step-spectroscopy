section \<open> Alternative LTS locale with $\tau$ Steps \label{appndx:LTSOptTau}\<close>

theory LTS_Prime
  imports Main
begin

locale Tau_LTS =
  fixes step :: "'s \<Rightarrow> 'a option \<Rightarrow> 's \<Rightarrow> bool" ("_ \<mapsto> _ _" [70,70,70] 80)
begin

definition step_set :: "'s set \<Rightarrow> 'a option \<Rightarrow> 's set" where
  "step_set P \<alpha> \<equiv> { q . \<exists>p \<in> P. p \<mapsto> \<alpha> q }"

abbreviation \<tau> :: "'a option" where
  "\<tau> \<equiv> None"

definition soft_step ("_ \<mapsto>a _ _" [70,70,70] 80) where
  "p \<mapsto>a \<alpha> q \<equiv> p \<mapsto> \<alpha> q \<or> (\<alpha> = \<tau> \<and> p = q)"

definition soft_step_set :: "'s set \<Rightarrow> 'a option \<Rightarrow> 's set" where
  "soft_step_set P \<alpha> \<equiv> { q . \<exists>p \<in> P. p \<mapsto>a \<alpha> q }"

inductive silent_reachable :: "'s \<Rightarrow> 's \<Rightarrow> bool" (infix "\<Zsurj>" 80) where
  self_sreachable: "p \<Zsurj> p" |
  tau_step_sreachable: "p \<Zsurj> r" if "p \<mapsto> \<tau> q" and "q \<Zsurj> r"

definition silent_reachable_set :: "'s set \<Rightarrow> 's set" where
  "silent_reachable_set P \<equiv> { q . \<exists>p \<in> P. p \<Zsurj> q }"

lemma silent_reachable_trans:
  assumes "p \<Zsurj> q"
      and "q \<Zsurj> r"
    shows "p \<Zsurj> r"
  using assms
  apply (induct rule: silent_reachable.induct)
  by (simp add: Tau_LTS.tau_step_sreachable)+

definition weak_step :: "'s \<Rightarrow> 'a \<Rightarrow> 's \<Rightarrow> bool" ("_ \<Zsurj>\<mapsto>\<Zsurj> _ _" [70, 70, 70] 80) where
  "p \<Zsurj>\<mapsto>\<Zsurj> a q \<equiv> \<exists>p' q'. p \<Zsurj> p' \<and> p' \<mapsto> (Some a) q' \<and> q' \<Zsurj> q"

lemma step_to_weak_step:
  assumes "p \<mapsto> (Some a) q"
  shows "p \<Zsurj>\<mapsto>\<Zsurj> a q"
  using assms 
  using self_sreachable weak_step_def by auto

lemma weak_step_prepend_silent:
  assumes "p \<Zsurj> q"
      and "q \<Zsurj>\<mapsto>\<Zsurj> a r"
    shows "p \<Zsurj>\<mapsto>\<Zsurj> a r"
  using assms and weak_step_def and silent_reachable_trans
  by blast

lemma silent_prepend_weak_step:
  assumes "p \<Zsurj>\<mapsto>\<Zsurj> a q" 
      and "q \<Zsurj> r"
    shows "p \<Zsurj>\<mapsto>\<Zsurj> a r"
  using assms and weak_step_def and silent_reachable_trans
  by blast

inductive weak_step_sequence :: "'s \<Rightarrow> 'a list \<Rightarrow> 's \<Rightarrow> bool" ("_ \<Zsurj>\<mapsto>\<Zsurj>$ _ _" [70,70,70] 80) where
  self_wsseq: "p \<Zsurj>\<mapsto>\<Zsurj>$ [] q" if "p \<Zsurj> q" |
  step_wsseq: "p \<Zsurj>\<mapsto>\<Zsurj>$ (a#as) r" if "p \<Zsurj>\<mapsto>\<Zsurj> a q" and "q \<Zsurj>\<mapsto>\<Zsurj>$ as r"

lemma weak_step_sequence_trans:
  assumes "p \<Zsurj>\<mapsto>\<Zsurj>$ trl q"
      and "q \<Zsurj>\<mapsto>\<Zsurj>$ trr r"
    shows "p \<Zsurj>\<mapsto>\<Zsurj>$ (trl @ trr) r"
  using assms
  apply induct
  unfolding append_Nil using weak_step_prepend_silent
  apply (smt (verit) silent_reachable_trans weak_step_sequence.simps)
  by (simp add: step_wsseq)

definition weak_traces :: "'s \<Rightarrow> 'a list set" where
  "weak_traces p \<equiv> {tr. \<exists>p'. p \<Zsurj>\<mapsto>\<Zsurj>$ tr p'}"

lemma empty_trace_allways_weak_trace:
  shows "[] \<in> weak_traces p"
  using self_sreachable self_wsseq weak_traces_def by auto

lemma silent_prepend_weak_traces:
  assumes "p \<Zsurj> p'"
      and "tr \<in> weak_traces p'"
    shows "tr \<in> weak_traces p"
  using assms 
  by (smt (verit, best) Tau_LTS.weak_traces_def append_Nil mem_Collect_eq self_wsseq weak_step_sequence_trans)

lemma step_prepend_weak_traces:
  assumes "p \<mapsto> (Some a) p'"
      and "tr \<in> weak_traces p'"
    shows "(a # tr) \<in> weak_traces p"
  using assms and step_to_weak_step mem_Collect_eq step_wsseq weak_traces_def
  by fastforce

lemma weak_step_prepend_weak_traces:
  assumes "p \<Zsurj>\<mapsto>\<Zsurj> a p'"
      and "tr \<in> weak_traces p'"
    shows "(a # tr) \<in> weak_traces p"
  using assms 
  using silent_prepend_weak_traces step_prepend_weak_traces weak_step_def by auto

definition weakly_trace_preordered (infix "\<lesssim>WT" 60) where
  "p \<lesssim>WT q \<equiv> weak_traces p \<subseteq> weak_traces q"

definition weakly_trace_equivalent (infix "\<simeq>WT" 60) where
  "p \<simeq>WT q \<equiv> p \<lesssim>WT q \<and> q \<lesssim>WT p"

end (* Tau_LTS *)

end