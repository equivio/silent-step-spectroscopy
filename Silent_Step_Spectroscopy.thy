subsection \<open>Correctness Theorem\<close>

theory Silent_Step_Spectroscopy
  imports
    Distinction_Implies_Winning_Budgets
    Strategy_Formulas
begin

context weak_spectroscopy_game
begin

theorem spectroscopy_game_correctness:
  fixes e p Q
  shows \<open>(\<exists>\<phi>. distinguishes_from \<phi> p Q \<and> expressiveness_price \<phi> \<le> e)
       \<longleftrightarrow> attacker_wins e (Attacker_Immediate p Q)\<close>
proof
  assume \<open>\<exists>\<phi>. distinguishes_from \<phi> p Q \<and> expressiveness_price \<phi> \<le> e\<close>
  then obtain \<phi> where \<phi>_spec:
    \<open>distinguishes_from \<phi> p Q\<close> \<open>expressiveness_price \<phi> \<le> e\<close>
    by blast
  from distinction_implies_winning_budgets \<phi>_spec(1) have
    \<open>attacker_wins (expressiveness_price \<phi>) (Attacker_Immediate p Q)\<close> .
  thus \<open>attacker_wins e (Attacker_Immediate p Q)\<close>
    using win_a_upwards_closure \<phi>_spec(2) by simp
next
  assume \<open>attacker_wins e (Attacker_Immediate p Q)\<close>
  with winning_budget_implies_strategy_formula have
    \<open>\<exists>\<phi>. strategy_formula (Attacker_Immediate p Q) e \<phi> \<and> expressiveness_price \<phi> \<le> e\<close>
    by force
  hence \<open>\<exists>\<phi>. strategy_formula (Attacker_Immediate p Q) e \<phi> \<and> expressiveness_price \<phi> \<le> e\<close>
    by blast
  thus \<open>\<exists>\<phi>. distinguishes_from \<phi> p Q \<and> expressiveness_price \<phi> \<le> e\<close>
    using strategy_formulas_distinguish by fastforce
qed

proposition attacker_subet_wins:
  assumes
    \<open>attacker_wins e (Attacker_Immediate p Q)\<close>
    \<open>Q' \<subseteq> Q\<close>
  shows
    \<open>attacker_wins e (Attacker_Immediate p Q')\<close>
  using assms spectroscopy_game_correctness
  unfolding distinguishes_from_def subset_iff
  by meson

end (* context weak_spectroscopy_game *)

end
