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
      if "(\<not>(spectroscopy_defender g) \<and> (spectroscopy_moves g g' \<noteq> None) ) \<and> 
          (in_wina e g) \<and>(in_wina e' g') \<and> (e' = the (spectroscopy_moves g g') e)" |
   "((g', e'), (g, e)) \<in> spectroscopy_pos_order"
      if "(spectroscopy_defender g) \<and> ((spectroscopy_moves g g' \<noteq> None)) \<and> 
          (in_wina e g) \<and>(e' = the (spectroscopy_moves g g') e)" 

lemma spectroscopy_pos_order_is_wf:
  shows "wf spectroscopy_pos_order"
  unfolding wf_def
proof safe
  fix P g e
  assume ih: "\<forall>x. (\<forall>y. (y, x) \<in> spectroscopy_pos_order \<longrightarrow> P y) \<longrightarrow> P x"
  then show "P(g, e)"
  proof(induction g arbitrary: e)
    case (Attacker_Immediate x1 x2)
    hence ih: "(\<forall>y. (y, ((Attacker_Immediate x1 x2), e)) \<in> spectroscopy_pos_order \<longrightarrow> P y) \<Longrightarrow> 
            P ((Attacker_Immediate x1 x2), e)"
      by blast
    show ?case
    proof(rule ih, safe)
      fix g' e'
      assume "((g', e'), Attacker_Immediate x1 x2, e) \<in> spectroscopy_pos_order"
      then show "P (g', e')"
      proof(cases)
        case 1
        then have "(attacker (Attacker_Immediate x1 x2) \<and> spectroscopy_moves (Attacker_Immediate x1 x2) g' \<noteq> None) \<and>
  in_wina e (Attacker_Immediate x1 x2) \<and> in_wina e' g' \<and> e' = weight (Attacker_Immediate x1 x2) g' e"
          by blast
        then show ?thesis using Attacker_Immediate sorry
      next
        case 2
        then have False 
          by simp
        then show ?thesis by simp
      qed
    qed
  next
    case (Attacker_Branch x1 x2)
    then show ?case sorry
  next
    case (Attacker_Clause x1 x2)
    then show ?case sorry
  next
    case (Attacker_Delayed x1 x2)
    then show ?case sorry
  next
    case (Defender_Branch x1 x2 x3 x4 x5)
    then show ?case sorry
  next
    case (Defender_Conj x1 x2)
    then show ?case sorry
  next
    case (Defender_Stable_Conj x1 x2)
    then show ?case sorry
  qed

(*
lemma pos_order_min_is_leaf:
  assumes "\<forall> g' e'. ((g', e'), (g, e))\<notin> spectroscopy_pos_order" and "in_wina e g"
  shows "\<forall>g''. (spectroscopy_moves g g''= None)"
  sorry

corollary pos_order_min_is_leaf_is_d:
  assumes "\<forall> g' e'. ((g', e'), (g, e))\<notin> spectroscopy_pos_order" and "in_wina e g"
  shows "spectroscopy_defender g"
  using pos_order_min_is_leaf in_wina.simps assms by meson
*)

lemma winning_budget_implies_strategy_formula:
  assumes "in_wina e g"
  shows "(\<exists>\<phi>. strategy_formula g e \<phi> \<and> expressiveness_price \<phi> \<le> e) \<or>
        (\<exists>\<phi>. strategy_formula_inner g e \<phi> \<and> expressiveness_price_inner \<phi> \<le> e) \<or>
        (\<exists>\<phi>. strategy_formula_conjunct g e \<phi> \<and> expressiveness_price_conjunct \<phi> \<le> e)"

proof- 
  define x where X: "x\<equiv>(g,e)"
  show ?thesis
    using assms proof (induction x rule: wf_induct[OF spectroscopy_pos_order_is_wf])
    case (1 x)
    then show ?case proof (cases g)
      case (Attacker_Immediate p Q)
      from assms have "in_wina e (Attacker_Immediate p Q)"
        by (simp add: Attacker_Immediate)
      hence "(\<exists>g'. (((spectroscopy_moves (Attacker_Immediate p Q) g')\<noteq>None) \<and> (in_wina (the (spectroscopy_moves (Attacker_Immediate p Q) g') e) g')))"
        by (metis in_wina.cases spectroscopy_defender.simps(1))
      from this obtain g' where "((spectroscopy_moves (Attacker_Immediate p Q) g')\<noteq>None) \<and> (in_wina (the (spectroscopy_moves (Attacker_Immediate p Q) g') e) g')" by auto
      hence "((g', (the (spectroscopy_moves (Attacker_Immediate p Q) g') e)),((Attacker_Immediate p Q),e)) \<in> spectroscopy_pos_order" using spectroscopy_pos_order.simps
        by (simp add: \<open>in_wina e (Attacker_Immediate p Q)\<close>)
      hence "\<exists>y. (y,((Attacker_Immediate p Q),e)) \<in> spectroscopy_pos_order" by auto
      hence "\<exists>y. (y,(g,e)) \<in> spectroscopy_pos_order" using Attacker_Immediate by simp
      hence "\<exists>y.  (y, x) \<in> spectroscopy_pos_order" using X sorry
      then show ?thesis using 1 by simp
    next
      case (Attacker_Branch x21 x22)
      then show ?thesis sorry
    next
      case (Attacker_Clause x31 x32)
      then show ?thesis sorry
    next
      case (Attacker_Delayed x41 x42)
      then show ?thesis sorry
    next
      case (Defender_Branch x51 x52 x53 x54 x55)
      then show ?thesis sorry
    next
      case (Defender_Conj x61 x62)
      then show ?thesis sorry
    next
      case (Defender_Stable_Conj x71 x72)
      then show ?thesis sorry
    qed 
  qed
qed

(*
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
    assume A: "\<forall>y. (y, x) \<in> spectroscopy_pos_order \<longrightarrow>
             ((in_wina e (Attacker_Immediate p Q) \<longrightarrow>
               (\<exists>\<phi>. strategy_formula (Attacker_Immediate p Q) e \<phi> \<and> expressiveness_price \<phi> \<le> e)) \<and>
              
               (in_wina e (Attacker_Delayed p Q) \<longrightarrow>
               (\<exists>\<phi>. strategy_formula_inner (Attacker_Delayed p Q) e \<phi> \<and>
                     expressiveness_price_inner \<phi> \<le> e)) \<and>

              (in_wina e (Attacker_Clause p q) \<longrightarrow>
               (\<exists>\<phi>. strategy_formula_conjunct (Attacker_Clause p q) e \<phi> \<and>
                     expressiveness_price_conjunct \<phi> \<le> e))) \<and>

             (in_wina e (Defender_Conj p Q) \<longrightarrow>
              (\<exists>\<phi>. strategy_formula (Defender_Conj p Q) e \<phi> \<and> expressiveness_price \<phi> \<le> e) \<or>
              (\<exists>\<phi>. strategy_formula_inner (Defender_Conj p Q) e \<phi> \<and>
                    expressiveness_price_inner \<phi> \<le> e)) \<and>

             (in_wina e (Defender_Stable_Conj p Q) \<longrightarrow>
              (\<exists>\<phi>. strategy_formula_inner (Defender_Stable_Conj p Q) e \<phi> \<and>
                    expressiveness_price_inner \<phi> \<le> e)) \<and>

             (in_wina e (Defender_Branch p \<alpha> p' Q Qa) \<longrightarrow>
              (\<exists>\<phi>. strategy_formula_inner (Defender_Branch p \<alpha> p' Q Qa) e \<phi> \<and>
                    expressiveness_price_inner \<phi> \<le> e))"

    show "in_wina e (Attacker_Immediate p Q) \<longrightarrow>
         (\<exists>\<phi>. strategy_formula (Attacker_Immediate p Q) e \<phi> \<and> expressiveness_price \<phi> \<le> e)" 
    proof (rule impI)
      assume "in_wina e (Attacker_Immediate p Q)"
      hence "(\<exists>g'. (((spectroscopy_moves (Attacker_Immediate p Q) g')\<noteq>None) \<and> (in_wina (the (spectroscopy_moves (Attacker_Immediate p Q) g') e) g')))"
        by (metis in_wina.cases spectroscopy_defender.simps(1))
      from this obtain g' where "((spectroscopy_moves (Attacker_Immediate p Q) g')\<noteq>None) \<and> (in_wina (the (spectroscopy_moves (Attacker_Immediate p Q) g') e) g')" by auto
      hence "((g', (the (spectroscopy_moves (Attacker_Immediate p Q) g') e)),((Attacker_Immediate p Q),e)) \<in> spectroscopy_pos_order" using spectroscopy_pos_order.simps
        by (simp add: \<open>in_wina e (Attacker_Immediate p Q)\<close>)
      hence "\<exists>y.  (y, x) \<in> spectroscopy_pos_order" sorry
      then show "\<exists>\<phi>. strategy_formula (Attacker_Immediate p Q) e \<phi> \<and> expressiveness_price \<phi> \<le> e" using A by simp
    qed
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
*)

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
