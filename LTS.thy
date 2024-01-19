theory LTS
  imports Main
begin

locale LTS =
  fixes step :: "'s \<Rightarrow> 'a \<Rightarrow> 's \<Rightarrow> bool" ("_ \<mapsto> _ _" [70,70,70] 80)
begin

abbreviation step_setp ("_ \<mapsto>S _ _" [70,70,70] 80) where
  "P \<mapsto>S \<alpha> Q \<equiv> (\<forall>q \<in> Q. \<exists>p \<in> P. p \<mapsto> \<alpha> q) \<and> (\<forall>p \<in> P. \<forall>q. p \<mapsto> \<alpha> q \<longrightarrow> q \<in> Q)"

definition step_set :: "'s set \<Rightarrow> 'a \<Rightarrow> 's set" where
  "step_set P \<alpha> \<equiv> { q . \<exists>p \<in> P. p \<mapsto> \<alpha> q }"

lemma step_set_is_step_set: "P \<mapsto>S \<alpha> (step_set P \<alpha>)"
  using step_set_def by force

lemma exactly_one_step_set: "\<exists>!Q. P \<mapsto>S \<alpha> Q"
proof -
  from step_set_is_step_set
  have "P \<mapsto>S \<alpha> (step_set P \<alpha>)"
    and "\<And>Q. P \<mapsto>S \<alpha> Q \<Longrightarrow> Q = (step_set P \<alpha>)"
    by fastforce+
  then show "\<exists>!Q. P \<mapsto>S \<alpha> Q"
    by blast
qed

lemma step_set_eq:
  assumes "P \<mapsto>S \<alpha> Q"
  shows "Q = step_set P \<alpha>"
  using assms step_set_is_step_set exactly_one_step_set by fastforce

end (* locale LTS *)


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


abbreviation silent_reachable_setp (infix "\<Zsurj>S" 80) where
  "P \<Zsurj>S Q \<equiv> ((\<forall>q \<in> Q. \<exists>p \<in> P. p \<Zsurj> q) \<and> (\<forall>p \<in> P. \<forall>q. p \<Zsurj> q \<longrightarrow> q \<in> Q))"

definition silent_reachable_set :: "'s set \<Rightarrow> 's set" where
  "silent_reachable_set P \<equiv> { q . \<exists>p \<in> P. p \<Zsurj> q }"

lemma sreachable_set_is_sreachable: "P \<Zsurj>S (silent_reachable_set P)"
  using silent_reachable_set_def by auto

lemma exactly_one_sreachable_set: "\<exists>!Q. P \<Zsurj>S Q"
proof -
  from sreachable_set_is_sreachable
  have "P \<Zsurj>S (silent_reachable_set P)".

  have "\<And>Q. P \<Zsurj>S Q \<Longrightarrow> Q = (silent_reachable_set P)"
  proof -
    fix Q
    assume "P \<Zsurj>S Q"

    with sreachable_set_is_sreachable
    have "\<forall>q \<in> Q. q \<in> (silent_reachable_set P)" 
      by meson

    from \<open>P \<Zsurj>S Q\<close>
     and sreachable_set_is_sreachable
    have "\<forall>q \<in> (silent_reachable_set P). q \<in> Q"
      by meson

    from \<open>\<forall>q \<in> Q. q \<in> (silent_reachable_set P)\<close>
     and \<open>\<forall>q \<in> (silent_reachable_set P). q \<in> Q\<close>
    show "Q = (silent_reachable_set P)" by auto
  qed

  with \<open>P \<Zsurj>S (silent_reachable_set P)\<close> 
  show "\<exists>!Q. P \<Zsurj>S Q" 
    by blast
qed


lemma sreachable_set_eq:
  assumes "P \<Zsurj>S Q"
  shows "Q = silent_reachable_set P"
  using exactly_one_sreachable_set sreachable_set_is_sreachable assms by fastforce

abbreviation non_tau_step_setp ("_ \<mapsto>aS _ _" [70,70,70] 80) where
  "P \<mapsto>aS \<alpha> Q \<equiv> (\<forall>q \<in> Q. \<exists>p \<in> P. p \<mapsto>a \<alpha> q) \<and> (\<forall>p \<in> P. \<forall>q. p \<mapsto>a \<alpha> q \<longrightarrow> q \<in> Q)"

definition non_tau_step_set :: "'s set \<Rightarrow> 'a \<Rightarrow> 's set" where
  "non_tau_step_set P \<alpha> \<equiv> { q . \<exists>p \<in> P. p \<mapsto>a \<alpha> q }"

lemma non_tau_step_set_is_non_tau_step_set:
  "P \<mapsto>aS \<alpha> (non_tau_step_set P \<alpha>)"
  using non_tau_step_set_def by auto

lemma exactly_one_non_tau_step_set:
  "\<exists>!Q. P \<mapsto>aS \<alpha> Q"
proof -
  from non_tau_step_set_is_non_tau_step_set
  have "P \<mapsto>aS \<alpha> (non_tau_step_set P \<alpha>)"
    and "\<And>Q. P \<mapsto>aS \<alpha> Q \<Longrightarrow> Q = (non_tau_step_set P \<alpha>)"
    by fastforce+
  then show "\<exists>!Q. P \<mapsto>aS \<alpha> Q"
    by blast
qed  

lemma non_tau_step_set_eq:
  assumes "P \<mapsto>aS \<alpha> Q"
  shows "Q = non_tau_step_set P \<alpha>"
  using exactly_one_non_tau_step_set non_tau_step_set_is_non_tau_step_set assms 
    by fastforce

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
