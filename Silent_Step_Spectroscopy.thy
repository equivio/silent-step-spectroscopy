theory Silent_Step_Spectroscopy
  imports Spectroscopy_Game Expressiveness_Price HML_SRBB Weak_Traces
begin

context full_spec_game begin

inductive Strat :: "('s, 'a) spectroscopy_position \<Rightarrow> ('a, 's) hml_srbb \<Rightarrow> bool"  

lemma distinction_implies_winning_budgets:
  assumes "distinguishes_from \<phi> p Q"
  shows "in_wina (expressiveness_price \<phi>) (Attacker_Immediate p Q)"
  sorry

inductive_set spectroscopy_pos_order :: "(('s, 'a) spectroscopy_position \<times> energy) rel" 
  where 
"((g', e'), (g, e)) \<in> spectroscopy_pos_order" 
if "(\<not>(spectroscopy_defender g) \<and> (spectroscopy_moves g g' \<noteq> None) )" |
(* \<and> 
    (in_wina (e - (E (spectroscopy_moves g g'))) g') \<and> (e' = (e - (spectroscopy_moves g g')))*)
"((g', e'), (g, e)) \<in> spectroscopy_pos_order"
if "(spectroscopy_defender g) \<and> 
((spectroscopy_moves g g' \<noteq> None))"
(* \<and> (e' = (e - (spectroscopy_moves g g')))*)

thm spectroscopy_pos_order.induct

lemma spectroscopy_pos_order_is_wf:
  shows "wf spectroscopy_pos_order"
  sorry

lemma winning_budget_implies_strategy_formula:
  shows 
"(in_wina e (Attacker_Immediate p Q)) \<longrightarrow> 
    (\<exists>\<phi>. strategy_formula (Attacker_Immediate p Q) e \<phi> \<and> expressiveness_price \<phi> \<le> e)"
"(in_wina e (Attacker_Delayed p Q)) \<longrightarrow> 
  (\<exists>\<phi>. strategy_formula_inner (Attacker_Delayed p Q) e \<phi> \<and> expressiveness_price_inner \<phi> \<le> e)"
"(in_wina e (Attacker_Clause p q)) \<longrightarrow> 
  (\<exists>\<phi>. strategy_formula_conjunct (Attacker_Clause p q) e \<phi> \<and> expressiveness_price_conjunct \<phi> \<le> e)"

"(in_wina e (Defender_Conj p Q)) \<longrightarrow>
(\<exists>\<phi>. strategy_formula (Defender_Conj p Q) e \<phi> \<and> expressiveness_price \<phi> \<le> e) \<or> 
(\<exists>\<phi>. strategy_formula_inner (Defender_Conj p Q) e \<phi> \<and> expressiveness_price_inner \<phi> \<le> e)"
"(in_wina e (Defender_Stable_Conj p Q)) \<longrightarrow>
(\<exists>\<phi>. strategy_formula_inner (Defender_Stable_Conj p Q) e \<phi> \<and> expressiveness_price_inner \<phi> \<le> e)"
"(in_wina e (Defender_Branch p \<alpha> p' Q Qa)) \<longrightarrow>
(\<exists>\<phi>. strategy_formula_inner (Defender_Branch p \<alpha> p' Q Qa) e \<phi> \<and> expressiveness_price_inner \<phi> \<le> e)"

proof(induct rule: wf_induct[OF spectroscopy_pos_order_is_wf])
  case (1 x)
  {
    case 1
    then show ?case sorry
  next
    case 2
    then show ?case sorry
  next
    case 3
    then show ?case sorry
  next
    case 4
    then show ?case sorry
  next
    case 5
    then show ?case sorry
  next
    case 6
    then show ?case sorry
  }
qed

lemma strategy_formulas_distinguish:
  assumes "Strat (Attacker_Immediate p Q) \<phi>"
  shows "distinguishes_from \<phi> p Q"
  sorry

theorem spectroscopy_game_correctness:
  shows "(\<exists>\<phi> \<in> \<O> e. distinguishes_from \<phi> p Q)
       = (in_wina e (Attacker_Immediate p Q))"
proof
  assume "\<exists>\<phi>\<in>\<O> e. distinguishes_from \<phi> p Q"
  then obtain \<phi> where
    "distinguishes_from \<phi> p Q" and le: "expressiveness_price \<phi> \<le> e"
    unfolding \<O>_def by blast 
  from distinction_implies_winning_budgets this(1)
    have budget: "in_wina (expressiveness_price \<phi>) (Attacker_Immediate p Q)" .
  thus "in_wina e (Attacker_Immediate p Q)" using win_a_upwards_closure le by simp
next
  assume "in_wina e (Attacker_Immediate p Q)"
  with winning_budget_implies_strategy_formula
    have "\<exists>\<phi>. Strat (Attacker_Immediate p Q) \<phi> \<and> expressiveness_price \<phi> \<le> e" .
  hence "\<exists>\<phi>\<in>\<O> e. Strat (Attacker_Immediate p Q) \<phi>" unfolding \<O>_def by blast
  thus "\<exists>\<phi>\<in>\<O> e. distinguishes_from \<phi> p Q"
    using strategy_formulas_distinguish by blast
qed


end (* context full_spec_game *)

end
