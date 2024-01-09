theory Silent_Step_Spectroscopy
  imports Spectroscopy_Game Expressiveness_Price HML_SRBB Weak_Traces
begin

context full_spec_game begin

inductive Strat :: "('s, 'a) spectroscopy_position \<Rightarrow> ('a, 's) hml_srbb \<Rightarrow> bool"  

lemma upwards_closure:
  assumes "in_wina e p" "e \<le> e'"
  shows "in_wina e' p"
proof-
  {
    have "\<forall>(e::energy) (e'::energy) (e''::energy). e \<le> e' \<and> e' \<le> e'' \<longrightarrow> e \<le> e''" by force
    moreover have "\<forall>e :: energy. e \<le> e" by simp
    moreover have "\<forall>(e :: energy) (e' :: energy). e \<le> e' \<and> e' \<le> e \<longrightarrow> e = e'" by auto
    moreover have "\<forall>e. eneg \<le> e" by (simp add: eneg_leq)
    moreover have "\<forall>g g' e e'. spectroscopy_moves g g' \<noteq> None \<and> e \<le> e' \<longrightarrow> weight g g' e \<le> weight g g' e'" sorry
    moreover have "\<forall>g g' e. spectroscopy_moves g g' \<noteq> None \<longrightarrow> weight g g' e \<le> e" sorry
    moreover assume "in_wina e p"
    ultimately have "\<forall>e'\<ge>e. in_wina e' p" by(rule win_a_upwards_closure[of "Orderings.ord_class.less_eq" "e" "p"])
    moreover assume "e \<le> e'"
    ultimately have "in_wina e' p" by simp
  }
  with assms show "in_wina e' p" by simp
qed


lemma one:
  assumes "distinguishes_from \<phi> p Q"
  shows "in_wina (expressiveness_price \<phi>) (Attacker_Immediate p Q)"
  sorry

lemma two:
  assumes "in_wina e (Attacker_Immediate p Q)"
  shows "\<exists>\<phi>. Strat (Attacker_Immediate p Q) \<phi> \<and> expressiveness_price \<phi> \<le> e"
  sorry

lemma three:
  assumes "Strat (Attacker_Immediate p Q) \<phi>"
  shows "distinguishes_from \<phi> p Q"
  sorry

theorem spectroscopy_game_correctness:
  shows "(\<exists>\<phi> \<in> \<O> e. distinguishes_from \<phi> p Q)
       = (in_wina e (Attacker_Immediate p Q))"
proof
  assume "\<exists>\<phi>\<in>\<O> e. distinguishes_from \<phi> p Q"
  then obtain \<phi> where "distinguishes_from \<phi> p Q" and le: "expressiveness_price \<phi> \<le> e" unfolding \<O>_def by blast 
  from this(1) have budget: "in_wina (expressiveness_price \<phi>) (Attacker_Immediate p Q)" by (rule one)
  thus "in_wina e (Attacker_Immediate p Q)" using upwards_closure le by simp
next
  assume "in_wina e (Attacker_Immediate p Q)"
  hence "\<exists>\<phi>. Strat (Attacker_Immediate p Q) \<phi> \<and> expressiveness_price \<phi> \<le> e" by (rule two)
  hence "\<exists>\<phi>\<in>\<O> e. Strat (Attacker_Immediate p Q) \<phi>" unfolding \<O>_def by blast
  thus "\<exists>\<phi>\<in>\<O> e. distinguishes_from \<phi> p Q" using three by blast
qed


end \<comment> \<open>end of context full_spec_game\<close>


end
