theory LTS
  imports Main
begin

locale LTS =
  fixes step :: "'s \<Rightarrow> 'a \<Rightarrow> 's \<Rightarrow> bool" ("_ \<mapsto> _ _" [70,70,70] 80)
begin
abbreviation step_set ("_ \<mapsto>S _ _" [70,70,70] 80) where "P \<mapsto>S \<alpha> Q \<equiv> \<forall>p \<in> P. \<forall>q \<in> Q. p \<mapsto> \<alpha> q"
end

locale LTS_Tau =
  LTS step
    for step :: "'s \<Rightarrow> 'a \<Rightarrow> 's \<Rightarrow> bool" ("_ \<mapsto> _ _" [70,70,70] 80) +
    fixes \<tau> :: 'a
begin

abbreviation non_tau_step ("_ \<mapsto>a _ _" [70,70,70] 80) where
  "p \<mapsto>a \<alpha> q \<equiv> (if \<alpha> = \<tau> then p = q else p \<mapsto>\<alpha> q)" 

inductive silent_reachable :: "'s \<Rightarrow> 's \<Rightarrow> bool"  (infix "\<Zsurj>" 80)
  where
    "p \<Zsurj> p" |
    "p \<Zsurj> p''" if "p \<mapsto> \<tau> p'" and "p' \<Zsurj> p''"

lemma silent_reachable_append_\<tau>: "p \<Zsurj> p' \<Longrightarrow> p' \<mapsto> \<tau> p'' \<Longrightarrow> p \<Zsurj> p''"
  apply (induct rule: silent_reachable.induct)
  using silent_reachable.intros by blast+

lemma silent_reachable_trans:
  assumes
    \<open>p \<Zsurj> p'\<close>
    \<open>p' \<Zsurj> p''\<close>
  shows
    \<open>p \<Zsurj> p''\<close>
using assms silent_reachable.intros(2)
by (induct, blast+)


definition weak_step ("_ \<Zsurj>\<mapsto>\<Zsurj> _ _" [70, 70, 70] 80) where
  "p  \<Zsurj>\<mapsto>\<Zsurj> \<alpha> p' \<equiv> if \<alpha> = \<tau> 
                    then p \<Zsurj> p'
                    else \<exists>p1 p2. p \<Zsurj> p1 \<and> p1 \<mapsto> \<alpha> p2 \<and> p2 \<Zsurj> p'"

inductive weak_step_sequence :: "'s \<Rightarrow> 'a list \<Rightarrow> 's \<Rightarrow> bool" ("_ \<Zsurj>\<mapsto>\<Zsurj>$ _ _" [70,70,70] 80) where
  "p \<Zsurj>\<mapsto>\<Zsurj>$ [] p" |
  "p \<Zsurj>\<mapsto>\<Zsurj>$ (\<alpha>#rt) p''" if "p \<Zsurj>\<mapsto>\<Zsurj> \<alpha> p'" "p' \<Zsurj>\<mapsto>\<Zsurj>$ rt p''"

lemma weak_step_sequence_trans:
  assumes "p \<Zsurj>\<mapsto>\<Zsurj>$ tr_1 p'" and "p' \<Zsurj>\<mapsto>\<Zsurj>$ tr_2 p''"
  shows "p \<Zsurj>\<mapsto>\<Zsurj>$ (tr_1 @ tr_2) p''"
  using assms weak_step_sequence.intros(2)
  by(induct, force+)

abbreviation weak_traces :: "'s \<Rightarrow> 'a list set"
  where "weak_traces p \<equiv> {tr. \<exists>p'. p \<Zsurj>\<mapsto>\<Zsurj>$ tr p'}"

definition weakly_trace_preordered (infix "\<lesssim>WT" 60) where
  "p \<lesssim>WT q \<equiv> weak_traces p \<subseteq> weak_traces q"

definition weakly_trace_equivalent (infix "\<simeq>WT" 60) where
"p \<simeq>WT q \<equiv> p \<lesssim>WT q \<and> q \<lesssim>WT p"

abbreviation silent_reachable_set (infix "\<Zsurj>S" 80) where "P \<Zsurj>S Q \<equiv> \<forall>p \<in> P. \<forall>q \<in> Q. p \<Zsurj> q"

lemma "Q \<Zsurj>S {}"
  by blast

abbreviation non_tau_step_set ("_ \<mapsto>aS _ _" [70,70,70] 80) where "P \<mapsto>aS \<alpha> Q \<equiv> \<forall>p \<in> P. \<forall>q \<in> Q. p \<mapsto>a \<alpha> q"

end (* locale LTS_Tau *)

locale Inhabited_LTS = LTS step
  for step :: "'s \<Rightarrow> 'a \<Rightarrow> 's \<Rightarrow> bool" ("_ \<mapsto> _ _" [70,70,70] 80) +
  fixes left :: 's
    and right :: 's
  assumes "(left::'s) \<noteq> (right::'s)"

locale Inhabited_Tau_LTS = Inhabited_LTS step left right + LTS_Tau step \<tau>
  for step :: "'s \<Rightarrow> 'a \<Rightarrow> 's \<Rightarrow> bool" ("_ \<mapsto> _ _" [70,70,70] 80)
  and left :: 's
  and right :: 's
  and \<tau> :: 'a

end (* theory LTS *)
