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

abbreviation soft_step ("_ \<mapsto>a _ _" [70,70,70] 80) where
  "p \<mapsto>a \<alpha> q \<equiv> p \<mapsto>\<alpha> q \<or> (\<alpha> = \<tau> \<and> p = q)" 

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

inductive silent_reachable_loopless :: "'s \<Rightarrow> 's \<Rightarrow> bool"  (infix "\<Zsurj>L" 80)
  where
    "p \<Zsurj>L p" |
    "p \<Zsurj>L p''" if "p \<mapsto> \<tau> p'" and "p' \<Zsurj>L p''" and "p \<noteq> p'"

lemma silent_reachable_impl_loopless:
  assumes "p \<Zsurj> p'"
  shows "p \<Zsurj>L p'"
  using assms proof(induct rule: silent_reachable.induct)
  case (1 p)
  thus ?case by (rule silent_reachable_loopless.intros(1))
next
  case (2 p p' p'')
  thus ?case proof(cases "p = p'")
    case True
    thus ?thesis using "2.hyps"(3) by auto
  next
    case False
    thus ?thesis using "2.hyps" silent_reachable_loopless.intros(2) by blast
  qed
qed

definition weak_step ("_ \<Zsurj>\<mapsto>\<Zsurj> _ _" [70, 70, 70] 80) where
  "p  \<Zsurj>\<mapsto>\<Zsurj> \<alpha> p' \<equiv> if \<alpha> = \<tau> 
                    then p \<Zsurj> p'
                    else \<exists>p1 p2. p \<Zsurj> p1 \<and> p1 \<mapsto> \<alpha> p2 \<and> p2 \<Zsurj> p'"

lemma silent_prepend_weak_step: "p \<Zsurj> p' \<Longrightarrow> p' \<Zsurj>\<mapsto>\<Zsurj> \<alpha> p'' \<Longrightarrow> p \<Zsurj>\<mapsto>\<Zsurj> \<alpha> p''"
proof (cases "\<alpha> = \<tau>")
  case True
  assume "p \<Zsurj> p'"
     and "p' \<Zsurj>\<mapsto>\<Zsurj> \<alpha> p''"
     and "\<alpha> = \<tau>"
  hence "p' \<Zsurj>\<mapsto>\<Zsurj> \<tau> p''" by auto
  then have "p' \<Zsurj> p''" unfolding weak_step_def by auto
  with \<open>p \<Zsurj> p'\<close>
  have "p \<Zsurj> p''" using silent_reachable_trans 
    by blast
  then have "p \<Zsurj>\<mapsto>\<Zsurj> \<tau> p''" unfolding weak_step_def by auto
  with \<open>\<alpha> = \<tau>\<close>
  show "p \<Zsurj>\<mapsto>\<Zsurj> \<alpha> p''" by auto
next
  case False
  assume "p \<Zsurj> p'"
    and "p' \<Zsurj>\<mapsto>\<Zsurj> \<alpha> p''"
    and "\<alpha> \<noteq> \<tau>"
  then have "\<exists>p1 p2. p' \<Zsurj> p1 \<and> p1 \<mapsto> \<alpha> p2 \<and> p2 \<Zsurj> p''" 
    using weak_step_def by auto
  then obtain p1 and p2 where "p' \<Zsurj> p1" and "p1 \<mapsto> \<alpha> p2" and "p2 \<Zsurj> p''" by auto

  from \<open>p \<Zsurj> p'\<close> and \<open>p' \<Zsurj> p1\<close>
  have "p \<Zsurj> p1" by (rule silent_reachable_trans)

  with \<open>p1 \<mapsto> \<alpha> p2\<close> and \<open>p2 \<Zsurj> p''\<close> and \<open>\<alpha> \<noteq> \<tau>\<close>
  show "p \<Zsurj>\<mapsto>\<Zsurj> \<alpha> p''" 
    using weak_step_def by auto
qed

inductive weak_step_sequence :: "'s \<Rightarrow> 'a list \<Rightarrow> 's \<Rightarrow> bool" ("_ \<Zsurj>\<mapsto>\<Zsurj>$ _ _" [70,70,70] 80) where
  "p \<Zsurj>\<mapsto>\<Zsurj>$ [] p'" if "p \<Zsurj> p'" |
  "p \<Zsurj>\<mapsto>\<Zsurj>$ (\<alpha>#rt) p''" if "p \<Zsurj>\<mapsto>\<Zsurj> \<alpha> p'" "p' \<Zsurj>\<mapsto>\<Zsurj>$ rt p''"

lemma weak_step_sequence_trans:
  assumes "p \<Zsurj>\<mapsto>\<Zsurj>$ tr_1 p'" and "p' \<Zsurj>\<mapsto>\<Zsurj>$ tr_2 p''"
  shows "p \<Zsurj>\<mapsto>\<Zsurj>$ (tr_1 @ tr_2) p''"
  using assms weak_step_sequence.intros(2)
  apply induct
  using silent_prepend_weak_step
  apply (smt (verit) LTS_Tau.weak_step_sequence.simps append_Nil silent_reachable_trans)
  by force


abbreviation weak_traces :: "'s \<Rightarrow> 'a list set"
  where "weak_traces p \<equiv> {tr. \<exists>p'. p \<Zsurj>\<mapsto>\<Zsurj>$ tr p'}"

lemma empty_trace_allways_weak_trace:
  shows "[] \<in> weak_traces p"
  using silent_reachable.intros(1) weak_step_sequence.intros(1) by fastforce

lemma prepend_\<tau>_weak_trace:
  assumes "tr \<in> weak_traces p"
  shows "(\<tau> # tr) \<in> weak_traces p"
  using silent_reachable.intros(1)
    and weak_step_def
    and assms
    and mem_Collect_eq
    and weak_step_sequence.intros(2)
  by fastforce

lemma silent_prepend_weak_traces:
  assumes "p \<Zsurj> p'"
      and "tr \<in> weak_traces p'"
    shows "tr \<in> weak_traces p"
  using assms
proof-
  assume "p \<Zsurj> p'"
     and "tr \<in> weak_traces p'"
  hence "\<exists>p''. p' \<Zsurj>\<mapsto>\<Zsurj>$ tr p''" by auto
  then obtain p'' where "p' \<Zsurj>\<mapsto>\<Zsurj>$ tr p''" by auto
  
  from \<open>p' \<Zsurj>\<mapsto>\<Zsurj>$ tr p''\<close>
    and \<open>p \<Zsurj> p'\<close>
  have "p \<Zsurj>\<mapsto>\<Zsurj>$ tr p''" 
    by (metis append_self_conv2 weak_step_sequence.intros(1) weak_step_sequence_trans)

  hence "\<exists>p''. p \<Zsurj>\<mapsto>\<Zsurj>$ tr p''" by auto
  then show "tr \<in> weak_traces p" 
    by blast
qed

lemma step_prepend_weak_traces:
  assumes "p \<mapsto> \<alpha> p'"
      and "tr \<in> weak_traces p'"
    shows "(\<alpha> # tr) \<in> weak_traces p"
  using assms
proof -
  from \<open>tr \<in> weak_traces p'\<close>
  have "\<exists>p''. p' \<Zsurj>\<mapsto>\<Zsurj>$ tr p''" by auto
  then obtain p'' where "p' \<Zsurj>\<mapsto>\<Zsurj>$ tr p''" by auto
  with \<open>p \<mapsto> \<alpha> p'\<close>
  have "p \<Zsurj>\<mapsto>\<Zsurj>$ (\<alpha> # tr) p''" 
    by (metis LTS_Tau.silent_reachable.intros(1) LTS_Tau.silent_reachable_append_\<tau> LTS_Tau.weak_step_def LTS_Tau.weak_step_sequence.intros(2))
  then have "\<exists>p''. p \<Zsurj>\<mapsto>\<Zsurj>$ (\<alpha> # tr) p''" by auto
  then show "(\<alpha> # tr) \<in> weak_traces p" by auto
qed

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

abbreviation soft_step_setp ("_ \<mapsto>aS _ _" [70,70,70] 80) where
  "P \<mapsto>aS \<alpha> Q \<equiv> (\<forall>q \<in> Q. \<exists>p \<in> P. p \<mapsto>a \<alpha> q) \<and> (\<forall>p \<in> P. \<forall>q. p \<mapsto>a \<alpha> q \<longrightarrow> q \<in> Q)"

definition soft_step_set :: "'s set \<Rightarrow> 'a \<Rightarrow> 's set" where
  "soft_step_set P \<alpha> \<equiv> { q . \<exists>p \<in> P. p \<mapsto>a \<alpha> q }"

lemma soft_step_set_is_soft_step_set:
  "P \<mapsto>aS \<alpha> (soft_step_set P \<alpha>)"
  using soft_step_set_def by auto

lemma exactly_one_soft_step_set:
  "\<exists>!Q. P \<mapsto>aS \<alpha> Q"
proof -
  from soft_step_set_is_soft_step_set
  have "P \<mapsto>aS \<alpha> (soft_step_set P \<alpha>)"
    and "\<And>Q. P \<mapsto>aS \<alpha> Q \<Longrightarrow> Q = (soft_step_set P \<alpha>)"
    by fastforce+
  show "\<exists>!Q. P \<mapsto>aS \<alpha> Q"
  proof
    from \<open>P \<mapsto>aS \<alpha> (soft_step_set P \<alpha>)\<close>
    show "P \<mapsto>aS \<alpha> (soft_step_set P \<alpha>)".
  next
    from \<open>\<And>Q. P \<mapsto>aS \<alpha> Q \<Longrightarrow> Q = (soft_step_set P \<alpha>)\<close>
    show "\<And>Q. P \<mapsto>aS \<alpha> Q \<Longrightarrow> Q = (soft_step_set P \<alpha>)".
  qed
qed  

lemma soft_step_set_eq:
  assumes "P \<mapsto>aS \<alpha> Q"
  shows "Q = soft_step_set P \<alpha>"
  using exactly_one_soft_step_set soft_step_set_is_soft_step_set assms 
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
