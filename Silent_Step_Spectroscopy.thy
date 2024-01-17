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
  fixes g e
  defines "x \<equiv> (g, e)"
  assumes "in_wina e g"
  shows "(\<exists>\<phi>. strategy_formula g e \<phi> \<and> expressiveness_price \<phi> \<le> e) \<or>
        (\<exists>\<phi>. strategy_formula_inner g e \<phi> \<and> expressiveness_price_inner \<phi> \<le> e) \<or>
        (\<exists>\<phi>. strategy_formula_conjunct g e \<phi> \<and> expressiveness_price_conjunct \<phi> \<le> e)"
  using assms
proof (induction x arbitrary: g e rule: wf_induct[OF spectroscopy_pos_order_is_wf])
  case 1
  then show ?case
    proof(induction g)
      case (Attacker_Immediate p Q)
      hence "(\<exists>g'. (((spectroscopy_moves (Attacker_Immediate p Q) g')\<noteq>None) \<and> (in_wina (the (spectroscopy_moves (Attacker_Immediate p Q) g') e) g')))"
        by (metis in_wina.cases spectroscopy_defender.simps(1))
      then obtain g' where move: "((spectroscopy_moves (Attacker_Immediate p Q) g')\<noteq>None) \<and> (in_wina (the (spectroscopy_moves (Attacker_Immediate p Q) g') e) g')" 
        using in_wina.cases spectroscopy_defender.simps(1)       
        by auto
      hence in_spec_order: "((g', (the (spectroscopy_moves (Attacker_Immediate p Q) g') e)),((Attacker_Immediate p Q),e)) \<in> spectroscopy_pos_order" 
        using spectroscopy_pos_order.simps
        by (simp add: \<open>in_wina e (Attacker_Immediate p Q)\<close>)
      hence "(\<exists>p' Q'. g' = (Attacker_Delayed p' Q')) \<or> (\<exists> p' Q'. g' = (Defender_Conj p' Q'))"
        using spectroscopy_moves.simps 
        by (smt (verit) move spectroscopy_defender.elims(1))
      then show ?case
      proof(rule disjE)
        assume "\<exists>p' Q'. g' = Attacker_Delayed p' Q'"
        then obtain p' Q' where g'_att_del: "g' = Attacker_Delayed p' Q'" by blast
        hence spec_order: "(((Attacker_Delayed p' Q'), (the (spectroscopy_moves (Attacker_Immediate p Q) (Attacker_Delayed p' Q')) e)),
                ((Attacker_Immediate p Q),e)) \<in> spectroscopy_pos_order"
          using in_spec_order by fastforce
        have "(the (spectroscopy_moves (Attacker_Immediate p Q) (Attacker_Delayed p' Q')) e) = (id e)"
          by (smt (verit, ccfv_threshold) Inhabited_Tau_LTS_axioms Spectroscopy_Game.Inhabited_Tau_LTS.delay g'_att_del move option.exhaust_sel option.inject)
        with spec_order have spec_order: "(((Attacker_Delayed p' Q'), e),
                ((Attacker_Immediate p Q),e)) \<in> spectroscopy_pos_order"
          by fastforce
        have "p' = p"
          by (metis \<open>g' = Attacker_Delayed p' Q'\<close> move spectroscopy_moves.simps(1))
        have "(\<exists>Q'. (spectroscopy_moves (Attacker_Immediate p Q) (Attacker_Delayed p Q') 
        = (Some (id:: energy \<Rightarrow> energy))))"
          by auto
        have "(in_wina e (Attacker_Delayed p Q'))"
          using \<open>g' = Attacker_Delayed p' Q'\<close> \<open>p' = p\<close> move update_gets_smaller win_a_upwards_closure 
          by blast
        from spec_order have \<phi>_ex:"(\<exists>\<phi>. strategy_formula (Attacker_Delayed p Q') e \<phi> \<and> expressiveness_price \<phi> \<le> e) \<or>
            (\<exists>\<phi>. strategy_formula_inner (Attacker_Delayed p Q') e \<phi> \<and> expressiveness_price_inner \<phi> \<le> e) \<or>
            (\<exists>\<phi>. strategy_formula_conjunct (Attacker_Delayed p Q') e \<phi> \<and>
                  expressiveness_price_conjunct \<phi> \<le> e)"
          using Attacker_Immediate \<open>in_wina e (Attacker_Delayed p Q')\<close> 
          using \<open>p' = p\<close> by presburger
        have \<phi>_not_\<phi>: "(\<nexists>\<phi>. strategy_formula (Attacker_Delayed p Q') e \<phi> \<and> expressiveness_price \<phi> \<le> e)"
          using strategy_formula.simps 
          by (smt (verit) spectroscopy_defender.simps(1) spectroscopy_defender.simps(4) spectroscopy_defender.simps(5) spectroscopy_defender.simps(6) 
spectroscopy_position.distinct(37) spectroscopy_position.distinct(5))
        have "(\<nexists>\<phi>. strategy_formula_conjunct (Attacker_Delayed p Q') e \<phi> \<and> expressiveness_price_conjunct \<phi> \<le> e)"
          using spectroscopy_defender.simps
          using strategy_formula_conjunct.simps by auto
        hence "(\<exists>\<phi>. strategy_formula_inner (Attacker_Delayed p Q') e \<phi> \<and> expressiveness_price_inner \<phi> \<le> e)"
          using \<open>in_wina e (Attacker_Delayed p Q')\<close> \<phi>_ex \<phi>_not_\<phi>
          by blast
        then obtain \<chi> where "(strategy_formula_inner (Attacker_Delayed p Q') e \<chi> \<and> expressiveness_price_inner \<chi> \<le> e)"
          by blast
        hence "((\<exists>Q'. (spectroscopy_moves (Attacker_Immediate p Q) (Attacker_Delayed p Q') 
        = (Some (id:: energy \<Rightarrow> energy))) \<and> (in_wina e (Attacker_Delayed p Q')) 
          \<and> strategy_formula_inner (Attacker_Delayed p Q') e \<chi>))"
          by (metis (mono_tags, lifting) Inhabited_Tau_LTS.spectroscopy_moves.simps(1) Inhabited_Tau_LTS_axioms \<open>in_wina e (Attacker_Delayed p Q')\<close> g'_att_del move)

        hence "strategy_formula (Attacker_Immediate p Q) e (Internal \<chi>)"
          using strategy_formula_strategy_formula_inner_strategy_formula_conjunct.delay by blast
        have "expressiveness_price (Internal \<chi>) \<le> e"
          using \<open>(strategy_formula_inner (Attacker_Delayed p Q') e \<chi> \<and> expressiveness_price_inner \<chi> \<le> e)\<close>
        proof
          have expr_internal: "expressiveness_price (Internal \<chi>) = E (modal_depth_srbb (Internal \<chi>))
                              (branching_conjunction_depth (Internal \<chi>))
                              (instable_conjunction_depth  (Internal \<chi>))
                              (stable_conjunction_depth    (Internal \<chi>))
                              (immediate_conjunction_depth (Internal \<chi>))
                              (max_positive_conjunct_depth (Internal \<chi>))
                              (max_negative_conjunct_depth (Internal \<chi>))
                              (negation_depth              (Internal \<chi>))"
            using expressiveness_price.simps by blast
          have "modal_depth_srbb (Internal \<chi>) = modal_depth_srbb_inner \<chi>"
            "(branching_conjunction_depth (Internal \<chi>)) = branch_conj_depth_inner \<chi>"
"(instable_conjunction_depth  (Internal \<chi>)) = inst_conj_depth_inner \<chi>"
"(stable_conjunction_depth    (Internal \<chi>)) = st_conj_depth_inner \<chi>"
"(immediate_conjunction_depth (Internal \<chi>)) = imm_conj_depth_inner \<chi>"
"max_positive_conjunct_depth (Internal \<chi>) = max_pos_conj_depth_inner \<chi>"
"max_negative_conjunct_depth (Internal \<chi>) = max_neg_conj_depth_inner \<chi>"
"negation_depth (Internal \<chi>) = neg_depth_inner \<chi>"
            by simp+
          with expr_internal have "expressiveness_price (Internal \<chi>) = expressiveness_price_inner \<chi>"
            using expressiveness_price_inner.simps
            by force
          then show ?thesis
            using \<open>strategy_formula_inner (Attacker_Delayed p Q') e \<chi> \<and> expressiveness_price_inner \<chi> \<le> e\<close> 
            by presburger
        qed
        then show ?case 
          using \<open>strategy_formula (Attacker_Immediate p Q) e (Internal \<chi>)\<close>
          by force

    next
      assume "\<exists>p' Q'. g' = Defender_Conj p' Q'"
      then obtain p' Q' where "g' = Defender_Conj p' Q'" by blast
      hence "(((Defender_Conj p' Q'), 
                (the (spectroscopy_moves (Attacker_Immediate p Q) (Defender_Conj p' Q')) e)),
               ((Attacker_Immediate p Q),e)) \<in> spectroscopy_pos_order"
          using 
\<open>((g', (the (spectroscopy_moves (Attacker_Immediate p Q) g') e)),((Attacker_Immediate p Q),e)) 
                                                                      \<in> spectroscopy_pos_order\<close>
          by blast
        then show ?case
        proof(cases "Q = {} \<and> Q' = {}")
          case True
          hence "p = p'"
            by (metis \<open>g' = Defender_Conj p' Q'\<close> move spectroscopy_moves.simps(4))
          with True have 
              "(the (spectroscopy_moves (Attacker_Immediate p Q) (Defender_Conj p' Q')) e) = id e"
            by simp
          with in_spec_order \<open>g' = Defender_Conj p' Q'\<close> have spec_order: 
            "(((Defender_Conj p' Q') , e), Attacker_Immediate p Q, e) \<in> spectroscopy_pos_order"
            by fastforce
          have "(\<exists>Q'. (spectroscopy_moves (Attacker_Immediate p Q) (Attacker_Delayed p Q') 
            = (Some (id:: energy \<Rightarrow> energy))))"
          by auto
        have "(in_wina e (Defender_Conj p Q'))"
          using \<open>g' = Defender_Conj p' Q'\<close> \<open>p = p'\<close> move update_gets_smaller win_a_upwards_closure 
          by blast
          
        from spec_order have \<phi>_ex:"(\<exists>\<phi>. strategy_formula (Defender_Conj p Q') e \<phi> \<and> expressiveness_price \<phi> \<le> e) \<or>
            (\<exists>\<phi>. strategy_formula_inner (Defender_Conj p Q') e \<phi> \<and> expressiveness_price_inner \<phi> \<le> e) \<or>
            (\<exists>\<phi>. strategy_formula_conjunct (Defender_Conj p Q') e \<phi> \<and>
                  expressiveness_price_conjunct \<phi> \<le> e)"
          using Attacker_Immediate \<open>in_wina e (Defender_Conj p Q')\<close> 
          using \<open>p = p'\<close>
          by force                                      
        have "(\<nexists>\<phi>. strategy_formula_conjunct (Defender_Conj p Q') e \<phi> \<and> expressiveness_price_conjunct \<phi> \<le> e)"
          using spectroscopy_defender.simps
          using strategy_formula_conjunct.simps 
          by auto
        hence "(\<exists>\<phi>. strategy_formula (Defender_Conj p Q') e \<phi> \<and> expressiveness_price \<phi> \<le> e) \<or>
(\<exists>\<phi>. strategy_formula_inner (Defender_Conj p Q') e \<phi> \<and> expressiveness_price_inner \<phi> \<le> e)"
          using \<open>in_wina e (Defender_Conj p Q')\<close> \<phi>_ex by blast
(*Wie können wir das darauf beschränken, dass \<phi> den Typ hml_srbb hat?/Auf die erste disj beschränken*)
        then show ?thesis
          sorry
        next
          case False
          hence "p = p'"
"Q = Q'"
            using \<open>g' = Defender_Conj p' Q'\<close> move spectroscopy_moves.simps
            by meson+
          then show ?thesis sorry
        qed
      qed
    next
      case (Attacker_Branch p Q)
      hence "(\<exists>g'. (((spectroscopy_moves (Attacker_Branch p Q) g')\<noteq>None) \<and> (in_wina (the (spectroscopy_moves (Attacker_Branch p Q) g') e) g')))"
        using in_wina.cases spectroscopy_defender.simps
        by fastforce
      then obtain g' where move: "((spectroscopy_moves (Attacker_Branch p Q) g')\<noteq>None) \<and> (in_wina (the (spectroscopy_moves (Attacker_Branch p Q) g') e) g')" 
        using in_wina.cases spectroscopy_defender.simps(1)       
        by auto
      hence in_spec_order: "((g', (the (spectroscopy_moves (Attacker_Branch p Q) g') e)),((Attacker_Branch p Q),e)) \<in> spectroscopy_pos_order" 
        using spectroscopy_pos_order.simps
        by (simp add: \<open>in_wina e (Attacker_Branch p Q)\<close>)
      hence "(\<exists>p' Q'. g' = (Attacker_Immediate p' Q'))"
        using spectroscopy_moves.simps 
        by (smt (verit) move spectroscopy_defender.elims(1))
      then obtain p' Q' where "g' = (Attacker_Immediate p' Q')"
        by blast
      hence spec_order: "(((Attacker_Immediate p' Q'), (the (spectroscopy_moves (Attacker_Branch p Q) (Attacker_Immediate p' Q')) e)),
                ((Attacker_Branch p Q),e)) \<in> spectroscopy_pos_order"
          using in_spec_order by fastforce
        have "(the (spectroscopy_moves (Attacker_Branch p Q) (Attacker_Immediate p' Q')) e) = e -  (E 1 0 0 0 0 0 0 0)"
          by (metis \<open>g' = Attacker_Immediate p' Q'\<close> move option.sel spectroscopy_moves.simps(13))
        with spec_order have spec_order: "(((Attacker_Immediate p' Q'), (e - (E 1 0 0 0 0 0 0 0))),
                ((Attacker_Branch p Q),e)) \<in> spectroscopy_pos_order"
          by fastforce
        have "p = p'" "Q = Q'"
          by (metis \<open>g' = Attacker_Immediate p' Q'\<close> move spectroscopy_moves.simps(13))+
        hence "(in_wina (e - (E 1 0 0 0 0 0 0 0)) (Attacker_Immediate p Q))"
          using \<open>g' = Attacker_Immediate p' Q'\<close> move update_gets_smaller win_a_upwards_closure 
          by simp
        from spec_order have \<phi>_ex:"(\<exists>\<phi>. strategy_formula (Attacker_Immediate p Q) (e - (E 1 0 0 0 0 0 0 0)) \<phi> \<and> expressiveness_price \<phi> \<le> (e - (E 1 0 0 0 0 0 0 0))) \<or>
            (\<exists>\<phi>. strategy_formula_inner (Attacker_Immediate p Q) (e - (E 1 0 0 0 0 0 0 0)) \<phi> \<and> expressiveness_price_inner \<phi> \<le> (e - (E 1 0 0 0 0 0 0 0))) \<or>
            (\<exists>\<phi>. strategy_formula_conjunct (Attacker_Immediate p Q) (e - (E 1 0 0 0 0 0 0 0)) \<phi> \<and>
                  expressiveness_price_conjunct \<phi> \<le> (e - (E 1 0 0 0 0 0 0 0)))"
          using Attacker_Branch \<open>in_wina (e - (E 1 0 0 0 0 0 0 0)) (Attacker_Immediate p Q)\<close> 
          using \<open>Q = Q'\<close> \<open>p = p'\<close> by blast 
        have "(\<nexists>\<phi>. strategy_formula_inner (Attacker_Immediate p Q) (e - (E 1 0 0 0 0 0 0 0)) \<phi> \<and> expressiveness_price_inner \<phi> \<le> (e - (E 1 0 0 0 0 0 0 0))) \<and>
            (\<nexists>\<phi>. strategy_formula_conjunct (Attacker_Immediate p Q) (e - (E 1 0 0 0 0 0 0 0)) \<phi> \<and>
                  expressiveness_price_conjunct \<phi> \<le> (e - (E 1 0 0 0 0 0 0 0)))"
          using spectroscopy_position.distinct spectroscopy_position.simps strategy_formula_conjunct.cases strategy_formula_inner.simps
          by (smt (verit))
        hence \<phi>_ex: "(\<exists>\<phi>. strategy_formula (Attacker_Immediate p Q) (e - (E 1 0 0 0 0 0 0 0)) \<phi> \<and> expressiveness_price \<phi> \<le> (e - (E 1 0 0 0 0 0 0 0)))"
          using strategy_formula.simps spectroscopy_defender.simps
          using \<open>Q = Q'\<close> \<open>p = p'\<close> \<phi>_ex by force
        then obtain \<phi> where "(strategy_formula (Attacker_Immediate p Q) (e - (E 1 0 0 0 0 0 0 0)) \<phi> \<and> expressiveness_price \<phi> \<le> (e - (E 1 0 0 0 0 0 0 0)))"
          by blast
        hence "((spectroscopy_moves (Attacker_Branch p Q) (Attacker_Immediate p Q) 
        = ((subtract 1 0 0 0 0 0 0 0))) \<and> (in_wina (e - (E 1 0 0 0 0 0 0 0)) (Attacker_Immediate p Q)) 
          \<and> strategy_formula (Attacker_Immediate p Q) (e - (E 1 0 0 0 0 0 0 0)) \<phi>)"
          using Inhabited_Tau_LTS.spectroscopy_moves.simps
          by (metis \<open>in_wina (e - E 1 0 0 0 0 0 0 0) (Attacker_Immediate p Q)\<close> local.br_acct)

        hence "strategy_formula (Attacker_Branch p Q) e (Internal \<phi>)"
          using strategy_formula_strategy_formula_inner_strategy_formula_conjunct.delay by blast
        have "expressiveness_price (Internal \<chi>) \<le> e"
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
qed


proof- 
  define x where X: "x=(g,e)"
  show ?thesis
    using assms proof (induction x rule: wf_induct[OF spectroscopy_pos_order_is_wf])
    case (1 z)
    then show ?case proof (induction g)
      case (Attacker_Immediate p Q)
      from assms have "in_wina e (Attacker_Immediate p Q)"
        by (simp add: Attacker_Immediate)
      hence "(\<exists>g'. (((spectroscopy_moves (Attacker_Immediate p Q) g')\<noteq>None) \<and> (in_wina (the (spectroscopy_moves (Attacker_Immediate p Q) g') e) g')))"
        by (metis in_wina.cases spectroscopy_defender.simps(1))
      from this obtain g' where g'_props: "((spectroscopy_moves (Attacker_Immediate p Q) g')\<noteq>None) \<and> (in_wina (the (spectroscopy_moves (Attacker_Immediate p Q) g') e) g')" by auto
      hence "((g', (the (spectroscopy_moves (Attacker_Immediate p Q) g') e)),((Attacker_Immediate p Q),e)) \<in> spectroscopy_pos_order" using spectroscopy_pos_order.simps
        by (simp add: \<open>in_wina e (Attacker_Immediate p Q)\<close>)
      hence "(\<exists>p' Q'. g' = (Attacker_Delayed p' Q')) \<or> (\<exists> p' Q'. g' = (Defender_Conj p' Q'))"
        using spectroscopy_moves.simps 
        by (smt (verit) g'_props spectroscopy_defender.elims(1))
      then show ?case
      proof(rule disjE)
        assume "\<exists>p' Q'. g' = Attacker_Delayed p' Q'"
        then obtain p' Q' where "g' = Attacker_Delayed p' Q'" by blast
        hence "(((Attacker_Delayed p' Q'), 
                (the (spectroscopy_moves (Attacker_Immediate p Q) (Attacker_Delayed p' Q')) e)),
               ((Attacker_Immediate p Q),e)) \<in> spectroscopy_pos_order"
          using 
\<open>((g', (the (spectroscopy_moves (Attacker_Immediate p Q) g') e)),((Attacker_Immediate p Q),e)) 
                                                                      \<in> spectroscopy_pos_order\<close>
          by blast
        have "p' = p"
          by (metis \<open>g' = Attacker_Delayed p' Q'\<close> g'_props spectroscopy_moves.simps(1))
        have "(\<exists>Q'. (spectroscopy_moves (Attacker_Immediate p Q) (Attacker_Delayed p Q') 
        = (Some (id:: energy \<Rightarrow> energy))))"
          by auto
        have "(in_wina e (Attacker_Delayed p Q'))"
          using \<open>g' = Attacker_Delayed p' Q'\<close> \<open>p' = p\<close> g'_props update_gets_smaller win_a_upwards_closure 
          by blast
        have "((((Attacker_Delayed p Q'), e), ((Attacker_Immediate p Q)), e)) \<in> spectroscopy_pos_order"
          sledgehammer
        have "\<exists>\<chi>. strategy_formula_inner (Attacker_Delayed p Q') e \<chi>"
          sorry
      hence "\<exists>y. (y,((Attacker_Immediate p Q),e)) \<in> spectroscopy_pos_order" by auto
      hence "\<exists>y. (y,(g,e)) \<in> spectroscopy_pos_order" using Attacker_Immediate by simp
      hence "\<exists>\<phi>. strategy_formula g e \<phi>"
        
      from this obtain y where "(y,(g,e)) \<in> spectroscopy_pos_order" by (rule exE)
      from this have "\<exists>z. (y, z) \<in> spectroscopy_pos_order" by auto
      from this obtain z where "(y, z) \<in> spectroscopy_pos_order" by auto
      hence "\<exists>y. (y, z) \<in> spectroscopy_pos_order" by blast
      then show ?thesis using 1 sorry
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
      case (Defender_Conj p Q)
        from assms have A: "in_wina e (Defender_Conj p Q)"
          by (simp add: Defender_Conj)
        consider (m0) "in_wina e (Defender_Conj p Q) = (spectroscopy_defender g) \<and> (\<forall>g'. spectroscopy_moves g g' = None)" | 
        (m1) "in_wina e (Defender_Conj p Q) = (\<not>spectroscopy_defender g) \<and> (\<exists>g'. spectroscopy_moves g g' \<noteq>  None \<and> (in_wina (the (spectroscopy_moves g g') e) g'))" |
        (m2) "in_wina e (Defender_Conj p Q) = (spectroscopy_defender g) \<and> (\<forall>g'. spectroscopy_moves g g' \<noteq>  None \<longrightarrow>  (in_wina (the (spectroscopy_moves g g') e) g'))"
          by (metis A Defender_Conj in_wina.cases)
        from A show ?thesis
        proof(cases)
          case 1
          then show ?thesis sorry
        next
          case 2
          then show ?thesis by simp 
        next
          case 3
          then show ?thesis sorry
        qed
      

        (*proof(cases "in_wina e (Defender_Conj p Q) = (spectroscopy_defender g) \<and> (\<forall>g'. spectroscopy_moves g g' = None)|
              in_wina e (Defender_Conj p Q) = (\<not>spectroscopy_defender g) \<and> (\<exists>g'. spectroscopy_moves g g' \<noteq>  None \<and> (in_wina (the (spectroscopy_moves g g') e) g')) |
              in_wina e (Defender_Conj p Q) = (spectroscopy_defender g) \<and> (\<forall>g'. spectroscopy_moves g g' \<noteq>  None \<longrightarrow>  (in_wina (the (spectroscopy_moves g g') e) g'))")
          case*)
          
          (*case True
            from A True have "\<forall>g'. (spectroscopy_moves (Defender_Conj p Q) g')\<noteq>None \<longrightarrow> (in_wina (the (spectroscopy_moves (Defender_Conj p Q) g') e) g')"
              using Defender_Conj spectroscopy_moves.simps(69) by blast
            then show ?thesis by (meson True spectroscopy_moves.simps(38))
          next
            case False
            from False have "\<exists>g'. (spectroscopy_moves (Defender_Conj p Q) g') = None" by simp
            from A False have "\<forall>g'. (spectroscopy_moves (Defender_Conj p Q) g') = None"
           then show ?thesis by*)
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
