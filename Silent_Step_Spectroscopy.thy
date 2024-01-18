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
  next
    case (Defender_Immediate_Conj x1 x2)
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

lemma expr_internal_eq:
  shows "expressiveness_price (Internal \<chi>) = expressiveness_price_inner \<chi>"
proof-
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
          with expr_internal show ?thesis
            by auto
        qed

lemma expr_pos:
  assumes "expressiveness_price_inner \<chi> \<le> (min1_6 e)"
  shows "expressiveness_price_conjunct (Pos \<chi>) \<le> e"
proof-
  have expr_internal: "expressiveness_price_conjunct (Pos \<chi>) = E (modal_depth_srbb_conjunct (Pos \<chi>))
                              (branch_conj_depth_conjunct (Pos \<chi>))
                              (inst_conj_depth_conjunct  (Pos \<chi>))
                              (st_conj_depth_conjunct    (Pos \<chi>))
                              (imm_conj_depth_conjunct (Pos \<chi>))
                              (max_pos_conj_depth_conjunct (Pos \<chi>))
                              (max_neg_conj_depth_conjunct (Pos \<chi>))
                              (neg_depth_conjunct            (Pos \<chi>))"
            using expressiveness_price_conjunct.simps by blast
          have pos_upd: "(modal_depth_srbb_conjunct (Pos \<chi>)) = modal_depth_srbb_inner \<chi>"
            "(branch_conj_depth_conjunct (Pos \<chi>)) = branch_conj_depth_inner \<chi>"
  "(inst_conj_depth_conjunct  (Pos \<chi>)) = inst_conj_depth_inner \<chi>"
  "(st_conj_depth_conjunct    (Pos \<chi>)) = st_conj_depth_inner \<chi>"
  "(imm_conj_depth_conjunct (Pos \<chi>)) = imm_conj_depth_inner \<chi>"
  "(max_pos_conj_depth_conjunct (Pos \<chi>)) = modal_depth_srbb_inner \<chi>"
  "(max_neg_conj_depth_conjunct (Pos \<chi>)) = max_neg_conj_depth_inner \<chi>"
  "(neg_depth_conjunct            (Pos \<chi>)) = neg_depth_inner \<chi>"
            by simp+
          have "expressiveness_price_inner \<chi> \<le> (min1_6 e)"
            using assms 
            by blast
          obtain e1 e2 e3 e4 e5 e6 e7 e8 where "e = E e1 e2 e3 e4 e5 e6 e7 e8"
            by (metis antysim assms eneg_leq energy.exhaust_sel expressiveness_price_inner.simps min_eneg(1))
          hence "min1_6 e = (E (min e1 e6) e2 e3 e4 e5 e6 e7 e8)"  
            by (simp add: min1_6_def)
          hence "modal_depth_srbb_inner \<chi> \<le> (min e1 e6)"
            using \<open>expressiveness_price_inner \<chi> \<le> (min1_6 e)\<close> expressiveness_price_inner.simps 
            by (simp add: leq_not_eneg)
          hence "modal_depth_srbb_inner \<chi> \<le> e6"
            using min.boundedE by blast
          thus "expressiveness_price_conjunct (Pos \<chi>) \<le> e"
            using expr_internal pos_upd \<open>e = E e1 e2 e3 e4 e5 e6 e7 e8\<close>
            using \<open>expressiveness_price_inner \<chi> \<le> min1_6 e\<close> \<open>min1_6 e = E (min e1 e6) e2 e3 e4 e5 e6 e7 e8\<close> leq_not_eneg by force
        qed

lemma winning_budget_implies_strategy_formula:
  fixes g e
  defines "x \<equiv> (g, e)"
  assumes "in_wina e g"
  shows
  "case g of
    Attacker_Immediate p Q \<Rightarrow> (\<exists>\<phi>. strategy_formula g e \<phi> \<and> expressiveness_price \<phi> \<le> e)
  | Attacker_Delayed p Q => (\<exists>\<phi>. strategy_formula_inner g e \<phi> \<and> expressiveness_price_inner \<phi> \<le> e)
  | Attacker_Clause p q => (\<exists>\<phi>. strategy_formula_conjunct g e \<phi> \<and> expressiveness_price_conjunct \<phi> \<le> e)
  
  | Defender_Immediate_Conj p Q => (\<exists>\<phi>. strategy_formula g e \<phi> \<and> expressiveness_price \<phi> \<le> e)
  | Defender_Conj p Q \<Rightarrow> (\<exists>\<phi>. strategy_formula_inner g e \<phi> \<and> expressiveness_price_inner \<phi> \<le> e)
  | Defender_Stable_Conj p Q => (\<exists>\<phi>. strategy_formula_inner g e \<phi> \<and> expressiveness_price_inner \<phi> \<le> e)
  | Defender_Branch p \<alpha> p' Q Qa => (\<exists>\<phi>. strategy_formula_inner g e \<phi> \<and> expressiveness_price_inner \<phi> \<le> e)

  | Attacker_Branch p Q \<Rightarrow> True"
  using assms
  proof (induction x arbitrary: g e rule: wf_induct[OF spectroscopy_pos_order_is_wf])
    case 1
    then show ?case
    proof(induction g)
      case (Attacker_Immediate p Q)
      hence "(\<exists>g'. (((spectroscopy_moves (Attacker_Immediate p Q) g')\<noteq>None) \<and> (in_wina (the (spectroscopy_moves (Attacker_Immediate p Q) g') e) g')))"
        using energy_game.in_wina_Ga energy_game_axioms by fastforce
      then obtain g' where move: "((spectroscopy_moves (Attacker_Immediate p Q) g')\<noteq>None) \<and> (in_wina (the (spectroscopy_moves (Attacker_Immediate p Q) g') e) g')" 
        using in_wina.cases spectroscopy_defender.simps(1)       
        by auto
      hence in_spec_order: "((g', (the (spectroscopy_moves (Attacker_Immediate p Q) g') e)),((Attacker_Immediate p Q),e)) \<in> spectroscopy_pos_order" 
        using spectroscopy_pos_order.simps
        by (simp add: \<open>in_wina e (Attacker_Immediate p Q)\<close>)
      hence "(\<exists>p' Q'. g' = (Attacker_Delayed p' Q')) \<or> (\<exists> p' Q'. g' = (Defender_Immediate_Conj p' Q'))"
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
          using \<open>p' = p\<close> 
          by fastforce
        have \<phi>_not_\<phi>: "(\<nexists>\<phi>. strategy_formula (Attacker_Delayed p Q') e \<phi> \<and> expressiveness_price \<phi> \<le> e)"
          using strategy_formula.simps spectroscopy_defender.simps spectroscopy_position.distinct(5)
          by blast
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
            expr_internal_eq
          by force
        then show ?case 
          using \<open>strategy_formula (Attacker_Immediate p Q) e (Internal \<chi>)\<close>
          by force

    next
      assume "\<exists>p' Q'. g' = Defender_Immediate_Conj p' Q'"
      then obtain p' Q' where "g' = Defender_Immediate_Conj p' Q'" by blast
      hence "(((Defender_Immediate_Conj p' Q'), 
                (the (spectroscopy_moves (Attacker_Immediate p Q) (Defender_Immediate_Conj p' Q')) e)),
               ((Attacker_Immediate p Q),e)) \<in> spectroscopy_pos_order"
          using 
\<open>((g', (the (spectroscopy_moves (Attacker_Immediate p Q) g') e)),((Attacker_Immediate p Q),e)) 
                                                                      \<in> spectroscopy_pos_order\<close>
          by blast
        then show ?case
        proof(cases "Q = {} \<and> Q' = {}")
          case True
          hence "p = p'"
            by (metis \<open>g' = Defender_Immediate_Conj p' Q'\<close> move spectroscopy_moves.simps(4))
          with True have 
              "(the (spectroscopy_moves (Attacker_Immediate p Q) (Defender_Immediate_Conj p' Q')) e) = id e"
            by simp
          with in_spec_order \<open>g' = Defender_Immediate_Conj p' Q'\<close> have spec_order: 
            "(((Defender_Immediate_Conj p' Q') , e), Attacker_Immediate p Q, e) \<in> spectroscopy_pos_order"
            by fastforce
          have "(\<exists>Q'. (spectroscopy_moves (Attacker_Immediate p Q) (Attacker_Delayed p Q') 
            = (Some (id:: energy \<Rightarrow> energy))))"
          by auto
        have "(in_wina e (Defender_Immediate_Conj p Q'))"
          using \<open>g' = Defender_Immediate_Conj p' Q'\<close> \<open>p = p'\<close> move update_gets_smaller win_a_upwards_closure 
          by blast
          
        from spec_order have \<phi>_ex:"(\<exists>\<phi>. strategy_formula (Defender_Immediate_Conj p Q') e \<phi> \<and> expressiveness_price \<phi> \<le> e) \<or>
            (\<exists>\<phi>. strategy_formula_inner (Defender_Immediate_Conj p Q') e \<phi> \<and> expressiveness_price_inner \<phi> \<le> e) \<or>
            (\<exists>\<phi>. strategy_formula_conjunct (Defender_Immediate_Conj p Q') e \<phi> \<and>
                  expressiveness_price_conjunct \<phi> \<le> e)"
          using Attacker_Immediate \<open>in_wina e (Defender_Immediate_Conj p Q')\<close> 
          using \<open>p = p'\<close>
          by force                                      
        have "(\<nexists>\<phi>. strategy_formula_conjunct (Defender_Immediate_Conj p Q') e \<phi> \<and> expressiveness_price_conjunct \<phi> \<le> e)"
          "(\<nexists>\<phi>. strategy_formula_inner (Defender_Immediate_Conj p Q') e \<phi> \<and> expressiveness_price_inner \<phi> \<le> e)"
          using spectroscopy_defender.simps
          using strategy_formula_conjunct.simps 
           apply auto
          using spectroscopy_defender.simps
          using strategy_formula_inner.simps 
           \<open>g' = Defender_Immediate_Conj p' Q'\<close> \<open>p = p'\<close> move spectroscopy_moves.simps(76, 90, 97)
          by (smt (verit))
        hence "(\<exists>\<phi>. strategy_formula (Defender_Immediate_Conj p Q') e \<phi> \<and> expressiveness_price \<phi> \<le> e)"
          using \<open>in_wina e (Defender_Immediate_Conj p Q')\<close> \<phi>_ex by blast
         then obtain \<phi> where "(strategy_formula (Defender_Immediate_Conj p Q') e \<phi> \<and> expressiveness_price \<phi> \<le> e)"
            by blast
          hence "((\<exists>Q'. (spectroscopy_moves (Attacker_Immediate p Q) (Defender_Immediate_Conj p Q') 
          = (Some (id:: energy \<Rightarrow> energy))) \<and> (in_wina e (Defender_Immediate_Conj p Q')) 
            \<and> strategy_formula (Defender_Immediate_Conj p Q') e \<phi>))"
            using True \<open>in_wina e (Defender_Immediate_Conj p Q')\<close> by auto
  
          hence "strategy_formula (Attacker_Immediate p Q) e \<phi>"
            using strategy_formula_strategy_formula_inner_strategy_formula_conjunct.delay early_conj
            by (meson True)
          have "expressiveness_price \<phi> \<le> e"
            using \<open>strategy_formula (Defender_Immediate_Conj p Q') e \<phi> \<and> expressiveness_price \<phi> \<le> e\<close> by blast
          then show ?thesis
            using \<open>strategy_formula (Attacker_Immediate p Q) e \<phi>\<close> by auto
        next
          case False
          hence "p = p'" "Q = Q'"
            using \<open>g' = Defender_Immediate_Conj p' Q'\<close> move spectroscopy_moves.simps
            by meson+
          with False have 
              "(the (spectroscopy_moves (Attacker_Immediate p Q) (Defender_Immediate_Conj p' Q')) e) 
                = e - (E 0 0 0 0 1 0 0 0)"
            by simp
          with in_spec_order \<open>g' = Defender_Immediate_Conj p' Q'\<close> have spec_order: 
            "(((Defender_Immediate_Conj p' Q') , (e - (E 0 0 0 0 1 0 0 0))), Attacker_Immediate p Q, e) \<in> spectroscopy_pos_order"
            by fastforce
          have "(\<exists>Q'. (spectroscopy_moves (Attacker_Immediate p Q) (Attacker_Delayed p Q') 
            = (Some (id:: energy \<Rightarrow> energy))))"
            by auto
          have "(in_wina (e - (E 0 0 0 0 1 0 0 0)) (Defender_Immediate_Conj p Q'))"
            using \<open>g' = Defender_Immediate_Conj p' Q'\<close> \<open>p = p'\<close> move update_gets_smaller win_a_upwards_closure 
            using \<open>weight (Attacker_Immediate p Q) (Defender_Immediate_Conj p' Q') e = e - E 0 0 0 0 1 0 0 0\<close> by force
            
          from spec_order have \<phi>_ex:"(\<exists>\<phi>. strategy_formula (Defender_Immediate_Conj p Q) (e - (E 0 0 0 0 1 0 0 0)) \<phi> \<and> expressiveness_price \<phi> \<le> (e - (E 0 0 0 0 1 0 0 0))) \<or>
              (\<exists>\<phi>. strategy_formula_inner (Defender_Immediate_Conj p Q) (e - (E 0 0 0 0 1 0 0 0)) \<phi> \<and> expressiveness_price_inner \<phi> \<le> (e - (E 0 0 0 0 1 0 0 0))) \<or>
              (\<exists>\<phi>. strategy_formula_conjunct (Defender_Immediate_Conj p Q) (e - (E 0 0 0 0 1 0 0 0)) \<phi> \<and>
                    expressiveness_price_conjunct \<phi> \<le> (e - (E 0 0 0 0 1 0 0 0)))"
            using Attacker_Immediate \<open>in_wina (e - (E 0 0 0 0 1 0 0 0)) (Defender_Immediate_Conj p Q')\<close> 
            using \<open>p = p'\<close> \<open>Q = Q'\<close>
            by force
          have "(\<nexists>\<phi>. strategy_formula_conjunct (Defender_Immediate_Conj p Q) (e - (E 0 0 0 0 1 0 0 0)) \<phi> \<and> expressiveness_price_conjunct \<phi> \<le> (e - (E 0 0 0 0 1 0 0 0)))"
            "(\<nexists>\<phi>. strategy_formula_inner (Defender_Immediate_Conj p Q) (e - (E 0 0 0 0 1 0 0 0)) \<phi> \<and> expressiveness_price_inner \<phi> \<le> (e - (E 0 0 0 0 1 0 0 0)))"
            using spectroscopy_defender.simps
            using strategy_formula_conjunct.simps 
             apply auto
            using spectroscopy_defender.simps
            using strategy_formula_inner.simps 
             \<open>g' = Defender_Immediate_Conj p' Q'\<close> \<open>p = p'\<close> move spectroscopy_moves.simps(76, 90, 97) \<open>Q = Q'\<close>
            by (smt (verit))
          hence "(\<exists>\<phi>. strategy_formula (Defender_Immediate_Conj p Q) (e - (E 0 0 0 0 1 0 0 0)) \<phi> \<and> expressiveness_price \<phi> \<le> (e - (E 0 0 0 0 1 0 0 0)))"
            using \<open>in_wina (e - (E 0 0 0 0 1 0 0 0)) (Defender_Immediate_Conj p Q')\<close> \<phi>_ex by blast

          then obtain \<phi> where "(strategy_formula (Defender_Immediate_Conj p Q) (e - (E 0 0 0 0 1 0 0 0)) \<phi> \<and> expressiveness_price \<phi> \<le> (e - (E 0 0 0 0 1 0 0 0)))"
            by blast
          hence "((\<exists>Q'. (spectroscopy_moves (Attacker_Immediate p Q) (Defender_Immediate_Conj p Q') 
          = ((subtract 0 0 0 0 1 0 0 0))) \<and> (in_wina (e - (E 0 0 0 0 1 0 0 0)) (Defender_Immediate_Conj p Q')) 
            \<and> strategy_formula (Defender_Immediate_Conj p Q') (e - (E 0 0 0 0 1 0 0 0)) \<phi>))"
            using False \<open>in_wina (e - (E 0 0 0 0 1 0 0 0)) (Defender_Immediate_Conj p Q')\<close> 
            by (simp add: \<open>Q = Q'\<close>)
  
          hence "strategy_formula (Attacker_Immediate p Q) e \<phi>"
            using strategy_formula_strategy_formula_inner_strategy_formula_conjunct.delay early_conj False
            by (metis \<open>Q = Q'\<close>)
          have "expressiveness_price \<phi> \<le> (e - (E 0 0 0 0 1 0 0 0))"
            using \<open>strategy_formula (Defender_Immediate_Conj p Q) (e - (E 0 0 0 0 1 0 0 0)) \<phi> \<and> expressiveness_price \<phi> \<le> (e - (E 0 0 0 0 1 0 0 0))\<close> by blast
          then show ?thesis
            using \<open>strategy_formula (Attacker_Immediate p Q) e \<phi>\<close> 
            using gets_smaller transitivity by fastforce
        qed
      qed
    next
      case (Attacker_Branch x21 x22)
      then show ?case 
        by simp
    next
      case (Attacker_Clause p q)
      hence "(\<exists>g'. (((spectroscopy_moves (Attacker_Clause p q) g')\<noteq>None) \<and> (in_wina (the (spectroscopy_moves (Attacker_Clause p q) g') e) g')))"
        using energy_game.in_wina_Ga energy_game_axioms by fastforce
      then obtain g' where move: "((spectroscopy_moves (Attacker_Clause p q) g')\<noteq>None) \<and> (in_wina (the (spectroscopy_moves (Attacker_Clause p q) g') e) g')" 
        using in_wina.cases spectroscopy_defender.simps(1)       
        by auto
      hence in_spec_order: "((g', (the (spectroscopy_moves (Attacker_Clause p q) g') e)),((Attacker_Clause p q),e)) \<in> spectroscopy_pos_order" 
        using spectroscopy_pos_order.simps
        by (simp add: \<open>in_wina e (Attacker_Clause p q)\<close>)
      hence "(\<exists>p' Q'. g' = (Attacker_Delayed p' Q'))"
        using spectroscopy_moves.simps move spectroscopy_moves.elims
        by (smt (verit) spectroscopy_defender.elims(1))
      then obtain p' Q' where g'_att_del: "g' = Attacker_Delayed p' Q'" by blast
      hence spec_order: "(((Attacker_Delayed p' Q'), (the (spectroscopy_moves (Attacker_Clause p q) (Attacker_Delayed p' Q')) e)),
              ((Attacker_Clause p q),e)) \<in> spectroscopy_pos_order"
        using in_spec_order by fastforce
      show ?case
      proof(cases \<open>p = p'\<close>)
        case True
        hence "{q} \<Zsurj>S Q'"
          using g'_att_del local.pos_neg_clause move by presburger

        have "(\<exists>Q'. (spectroscopy_moves (Attacker_Clause p q) (Attacker_Delayed p Q') 
        = (Some min1_6)))"
          by auto
        hence "(the (spectroscopy_moves (Attacker_Clause p q) g') e) = min1_6 e"
          by (simp add: True \<open>{q} \<Zsurj>S Q'\<close> g'_att_del)
        have "(in_wina (min1_6 e) (Attacker_Delayed p Q'))"
          using \<open>g' = Attacker_Delayed p' Q'\<close> \<open>{q} \<Zsurj>S Q'\<close> move update_gets_smaller win_a_upwards_closure 
          by (simp add: True)
        from spec_order have \<phi>_ex:"(\<exists>\<phi>. strategy_formula (Attacker_Delayed p Q') (min1_6 e) \<phi> \<and> expressiveness_price \<phi> \<le> (min1_6 e)) \<or>
            (\<exists>\<phi>. strategy_formula_inner (Attacker_Delayed p Q') (min1_6 e) \<phi> \<and> expressiveness_price_inner \<phi> \<le> (min1_6 e)) \<or>
            (\<exists>\<phi>. strategy_formula_conjunct (Attacker_Delayed p Q') (min1_6 e) \<phi> \<and>
                  expressiveness_price_conjunct \<phi> \<le> (min1_6 e))"
          using Attacker_Clause \<open>in_wina (min1_6 e) (Attacker_Delayed p Q')\<close> 
          using \<open>{q} \<Zsurj>S Q'\<close> \<open>(the (spectroscopy_moves (Attacker_Clause p q) g') e) = min1_6 e\<close>
          using True by fastforce
        have \<phi>_not_\<phi>: "(\<nexists>\<phi>. strategy_formula (Attacker_Delayed p Q') (min1_6 e) \<phi> \<and> expressiveness_price \<phi> \<le> (min1_6 e))"
          using strategy_formula.simps spectroscopy_defender.simps spectroscopy_position.distinct(5)
          by blast
        have "(\<nexists>\<phi>. strategy_formula_conjunct (Attacker_Delayed p Q') e \<phi> \<and> expressiveness_price_conjunct \<phi> \<le> e)"
          using spectroscopy_defender.simps
          using strategy_formula_conjunct.simps by auto
        hence "(\<exists>\<phi>. strategy_formula_inner (Attacker_Delayed p Q') (min1_6 e) \<phi> \<and> expressiveness_price_inner \<phi> \<le> (min1_6 e))"
          using \<open>in_wina (min1_6 e) (Attacker_Delayed p Q')\<close> \<phi>_ex \<phi>_not_\<phi>
          using strategy_formula_conjunct.simps by blast
        then obtain \<chi> where "(strategy_formula_inner (Attacker_Delayed p Q') (min1_6 e) \<chi> \<and> expressiveness_price_inner \<chi> \<le> (min1_6 e))"
          by blast
        hence "((\<exists>Q'. (spectroscopy_moves (Attacker_Clause p q) (Attacker_Delayed p Q') 
        = (Some (min1_6))) \<and> (in_wina (min1_6 e) (Attacker_Delayed p Q')) 
          \<and> strategy_formula_inner (Attacker_Delayed p Q') (min1_6 e) \<chi>))"
          by (meson \<open>in_wina (min1_6 e) (Attacker_Delayed p Q')\<close> \<open>{q} \<Zsurj>S Q'\<close> local.pos_neg_clause)
hence "strategy_formula_conjunct (Attacker_Clause p q) e (Pos \<chi>)"
          using strategy_formula_strategy_formula_inner_strategy_formula_conjunct.delay
          using pos by blast

        have "expressiveness_price_conjunct (Pos \<chi>) \<le> e"
          using \<open>(strategy_formula_inner (Attacker_Delayed p Q') (min1_6 e) \<chi> \<and> expressiveness_price_inner \<chi> \<le> (min1_6 e))\<close> expr_pos 
          by blast 
        then show ?thesis 
          using \<open>strategy_formula_conjunct (Attacker_Clause p q) e (Pos \<chi>)\<close>
          by force
      next
        case False
        hence "{p} \<Zsurj>S Q'"
          using g'_att_del local.pos_neg_clause move by presburger

        have "p' = q"
          by (metis False Inhabited_Tau_LTS.spectroscopy_moves.simps(8) Inhabited_Tau_LTS_axioms g'_att_del move)

        have "(\<exists>Q'. (spectroscopy_moves (Attacker_Clause p q) (Attacker_Delayed p' Q') 
        = Some (min1_7 \<circ> (\<lambda>x. x- E 0 0 0 0 0 0 0 1))))"  
          using False \<open>p' = q\<close> by auto
        hence "(the (spectroscopy_moves (Attacker_Clause p q) g') e) = (min1_7 (e - E 0 0 0 0 0 0 0 1))"
          using False \<open>{p} \<Zsurj>S Q'\<close> g'_att_del \<open>p' = q\<close>
          by simp
        have "(in_wina ((min1_7 (e - E 0 0 0 0 0 0 0 1))) (Attacker_Delayed p' Q'))"
          using \<open>g' = Attacker_Delayed p' Q'\<close> \<open>{p} \<Zsurj>S Q'\<close> move update_gets_smaller win_a_upwards_closure False \<open>p' = q\<close>
          by auto
        
        from spec_order have \<phi>_ex:"(\<exists>\<phi>. strategy_formula (Attacker_Delayed p' Q') (min1_7 (e - E 0 0 0 0 0 0 0 1)) \<phi> \<and> expressiveness_price \<phi> \<le> (min1_7 (e - E 0 0 0 0 0 0 0 1))) \<or>
            (\<exists>\<phi>. strategy_formula_inner (Attacker_Delayed p' Q') (min1_7 (e - E 0 0 0 0 0 0 0 1)) \<phi> \<and> expressiveness_price_inner \<phi> \<le> (min1_7 (e - E 0 0 0 0 0 0 0 1))) \<or>
            (\<exists>\<phi>. strategy_formula_conjunct (Attacker_Delayed p' Q') (min1_7 (e - E 0 0 0 0 0 0 0 1)) \<phi> \<and>
                  expressiveness_price_conjunct \<phi> \<le> (min1_7 (e - E 0 0 0 0 0 0 0 1)))"
          using Attacker_Clause \<open>in_wina (min1_7 (e - E 0 0 0 0 0 0 0 1)) (Attacker_Delayed p' Q')\<close> 
          using \<open>{p} \<Zsurj>S Q'\<close> \<open>(the (spectroscopy_moves (Attacker_Clause p q) g') e) = (min1_7 (e - E 0 0 0 0 0 0 0 1))\<close> \<open>p' = q\<close>
          using False by fastforce
        have \<phi>_not_\<phi>: "(\<nexists>\<phi>. strategy_formula (Attacker_Delayed p Q') (min1_6 e) \<phi> \<and> expressiveness_price \<phi> \<le> (min1_6 e))"
          using strategy_formula.simps spectroscopy_defender.simps spectroscopy_position.distinct(5)
          by blast
        have "(\<nexists>\<phi>. strategy_formula_conjunct (Attacker_Delayed p Q') e \<phi> \<and> expressiveness_price_conjunct \<phi> \<le> e)"
          using spectroscopy_defender.simps
          using strategy_formula_conjunct.simps by auto
        hence "(\<exists>\<phi>. strategy_formula_inner (Attacker_Delayed p' Q') (min1_7 (e - E 0 0 0 0 0 0 0 1)) \<phi> \<and> expressiveness_price_inner \<phi> \<le> (min1_7 (e - E 0 0 0 0 0 0 0 1)))"
          using \<open>in_wina (min1_7 (e - E 0 0 0 0 0 0 0 1)) (Attacker_Delayed p' Q')\<close> \<phi>_ex \<phi>_not_\<phi>
          using strategy_formula_conjunct.simps 
          by (simp add: strategy_formula.simps) 
        then obtain \<chi> where "(strategy_formula_inner (Attacker_Delayed p' Q') (min1_7 (e - E 0 0 0 0 0 0 0 1)) \<chi> \<and> expressiveness_price_inner \<chi> \<le> (min1_7 (e - E 0 0 0 0 0 0 0 1)))"
          by blast
        hence "((\<exists>Q'. (spectroscopy_moves (Attacker_Clause p q) (Attacker_Delayed p' Q') 
        = (Some (min1_7 \<circ> (\<lambda>x. x- E 0 0 0 0 0 0 0 1)))) \<and> (in_wina (min1_7 (e - E 0 0 0 0 0 0 0 1)) (Attacker_Delayed p' Q')) 
          \<and> strategy_formula_inner (Attacker_Delayed p' Q') (min1_7 (e - E 0 0 0 0 0 0 0 1)) \<chi>))"
          using \<open>in_wina (min1_7 (e - E 0 0 0 0 0 0 0 1)) (Attacker_Delayed p' Q')\<close> local.pos_neg_clause
          using False \<open>{p} \<Zsurj>S Q'\<close> \<open>p' = q\<close> by fastforce

        hence "strategy_formula_conjunct (Attacker_Clause p q) e (Neg \<chi>)"
          using strategy_formula_strategy_formula_inner_strategy_formula_conjunct.delay
          using neg \<open>p' = q\<close> by blast

        have "expressiveness_price_conjunct (Neg \<chi>) \<le> e"
          using \<open>(strategy_formula_inner (Attacker_Delayed p' Q') (min1_7 (e - E 0 0 0 0 0 0 0 1)) \<chi> \<and> expressiveness_price_inner \<chi> \<le> (min1_7 (e - E 0 0 0 0 0 0 0 1)))\<close>
        proof
          have expr_neg: "expressiveness_price_conjunct (Neg \<chi>) =
E (modal_depth_srbb_conjunct (Neg \<chi>))
                              (branch_conj_depth_conjunct (Neg \<chi>))
                              (inst_conj_depth_conjunct (Neg \<chi>))
                              (st_conj_depth_conjunct (Neg \<chi>))
                              (imm_conj_depth_conjunct (Neg \<chi>))
                              (max_pos_conj_depth_conjunct (Neg \<chi>))
                              (max_neg_conj_depth_conjunct (Neg \<chi>))
                              (neg_depth_conjunct (Neg \<chi>))"
            using expressiveness_price_conjunct.simps by blast

          have neg_ups: "modal_depth_srbb_conjunct (Neg \<chi>) = modal_depth_srbb_inner \<chi>" 
"(branch_conj_depth_conjunct (Neg \<chi>)) = branch_conj_depth_inner \<chi>"
"inst_conj_depth_conjunct (Neg \<chi>) = inst_conj_depth_inner \<chi>" 
"st_conj_depth_conjunct (Neg \<chi>) = st_conj_depth_inner \<chi>"
"imm_conj_depth_conjunct (Neg \<chi>) = imm_conj_depth_inner \<chi>"
"max_pos_conj_depth_conjunct (Neg \<chi>) = max_pos_conj_depth_inner \<chi>"
"max_neg_conj_depth_conjunct (Neg \<chi>) = modal_depth_srbb_inner \<chi>"
"neg_depth_conjunct (Neg \<chi>) = 1 + neg_depth_inner \<chi>" 
            by simp+

          have "expressiveness_price_inner \<chi> \<le> (min1_7 (e - E 0 0 0 0 0 0 0 1))"
            using \<open>strategy_formula_inner (Attacker_Delayed p' Q') (min1_7 (e - E 0 0 0 0 0 0 0 1)) \<chi> \<and> expressiveness_price_inner \<chi> \<le> min1_7 (e - E 0 0 0 0 0 0 0 1)\<close>
            by blast
          obtain e1 e2 e3 e4 e5 e6 e7 e8 where "e = E e1 e2 e3 e4 e5 e6 e7 e8"
            by (metis "1"(2) energy.exhaust_sel in_wina.cases)
          hence "(e - (E 0 0 0 0 0 0 0 1)) = (E e1 e2 e3 e4 e5 e6 e7 (e8-1)) \<or> 
                  ((e - (E 0 0 0 0 0 0 0 1)) = eneg)"
            using minus_energy_def
            by simp
          then show ?thesis
          proof(rule disjE)
            assume "e - E 0 0 0 0 0 0 0 1 = eneg"
            hence "e = (E 0 0 0 0 0 0 0 0)"
              by (metis \<open>\<exists>Q'. spectroscopy_moves (Attacker_Clause p q) (Attacker_Delayed p' Q') = Some (min1_7 \<circ> (\<lambda>x. x - E 0 0 0 0 0 0 0 1)) \<and> in_wina (min1_7 (e - E 0 0 0 0 0 0 0 1)) (Attacker_Delayed p' Q') \<and> strategy_formula_inner (Attacker_Delayed p' Q') (min1_7 (e - E 0 0 0 0 0 0 0 1)) \<chi>\<close> eneg_leq gets_smaller_min_1_7 in_wina.cases order_class.order_eq_iff)
            then show ?thesis 
              using \<open>e - E 0 0 0 0 0 0 0 1 = eneg\<close> \<open>weight (Attacker_Clause p q) g' e = min1_7 (e - E 0 0 0 0 0 0 0 1)\<close> energy_game.in_wina.cases energy_game_axioms min_eneg(2) move 
              by fastforce
          next
            assume "e - E 0 0 0 0 0 0 0 1 = E e1 e2 e3 e4 e5 e6 e7 (e8 - 1)"
            hence "(min1_7 (e - E 0 0 0 0 0 0 0 1)) = (E (min e1 e7) e2 e3 e4 e5 e6 e7 (e8-1))"
            using min1_7_def
            by simp
            hence "modal_depth_srbb_inner \<chi> \<le> (min e1 e7)"
              using expressiveness_price_inner.simps
              using \<open>expressiveness_price_inner \<chi> \<le> min1_7 (e - E 0 0 0 0 0 0 0 1)\<close> leq_not_eneg by auto
            
            have "neg_depth_inner \<chi> \<le> (e8-1)"
              using \<open>(min1_7 (e - E 0 0 0 0 0 0 0 1)) = (E (min e1 e7) e2 e3 e4 e5 e6 e7 (e8-1))\<close>
\<open>e = E e1 e2 e3 e4 e5 e6 e7 e8\<close> \<open>expressiveness_price_inner \<chi> \<le> (min1_7 (e - E 0 0 0 0 0 0 0 1))\<close>
              using leq_not_eneg by force
            hence "neg_depth_conjunct (Neg \<chi>) \<le> e8"
              using \<open>neg_depth_conjunct (Neg \<chi>) = 1 + neg_depth_inner \<chi>\<close>
              by (metis \<open>e - E 0 0 0 0 0 0 0 1 = E e1 e2 e3 e4 e5 e6 e7 (e8 - 1)\<close> \<open>e = E e1 e2 e3 e4 e5 e6 e7 e8\<close> add_diff_cancel_enat enat_add_left_cancel_le energy.sel(8) energy.simps(3) le_iff_add leq_not_eneg minus_energy_def)
          thus "expressiveness_price_conjunct (Neg \<chi>) \<le> e"
            using expr_neg \<open>e = E e1 e2 e3 e4 e5 e6 e7 e8\<close> \<open>modal_depth_srbb_inner \<chi> \<le> (min e1 e7)\<close>
            using \<open>expressiveness_price_inner \<chi> \<le> min1_7 (e - E 0 0 0 0 0 0 0 1)\<close> \<open>(min1_7 (e - E 0 0 0 0 0 0 0 1)) = (E (min e1 e7) e2 e3 e4 e5 e6 e7 (e8-1))\<close> leq_not_eneg 
            by (simp add: \<open>e = E e1 e2 e3 e4 e5 e6 e7 e8\<close> neg_ups(7))
        qed
      qed
        then show ?thesis 
          using \<open>strategy_formula_conjunct (Attacker_Clause p q) e (hml_srbb_conjunct.Neg \<chi>)\<close> by force
      qed
    next
      case (Attacker_Delayed x41 x42)
      then show ?case sorry
    next
      case (Defender_Branch x51 x52 x53 x54 x55)
      then show ?case sorry
    next
      case (Defender_Conj p Q)
        from assms have A: "in_wina e (Defender_Conj p Q)"
          by (simp add: Defender_Conj)
        consider "in_wina e (Defender_Conj p Q) = (spectroscopy_defender g) \<and> (\<forall>g'. \<not>spectroscopy_moves g g' \<noteq> None)" | 
                 "in_wina e (Defender_Conj p Q) = (\<not>spectroscopy_defender g) \<and> (\<exists>g'. spectroscopy_moves g g' \<noteq>  None \<and> (in_wina (the (spectroscopy_moves g g') e) g'))" |
                 "in_wina e (Defender_Conj p Q) = (spectroscopy_defender g) \<and> (\<forall>g'. spectroscopy_moves g g' \<noteq>  None \<longrightarrow>  (in_wina (the (spectroscopy_moves g g') e) g'))"
          by (metis "1.prems" Defender_Conj.prems(2) in_wina.cases)        
          
        from A show ?case
        proof(cases)
          case 1
          from 1 have A: "\<forall>g'. \<not>spectroscopy_moves (Defender_Conj p Q) g' \<noteq>  None" using Defender_Conj by blast
          hence "\<forall>y'. (y',((Defender_Conj p Q),e)) \<notin> spectroscopy_pos_order" by (metis spectroscopy_pos_order.cases surj_pair)
          hence "False" using 1 sorry
          then show ?thesis by blast 
        next
          case 2
          then show ?thesis by simp 
        next
          case 3
          show ?thesis
          proof (cases "(spectroscopy_defender (Defender_Conj p Q)) \<and> (\<forall>g'. spectroscopy_moves (Defender_Conj p Q) g' \<noteq>  None)")
            case True
             hence "\<forall>y'. (y',((Defender_Conj p Q),e)) \<in> spectroscopy_pos_order " using Defender_Conj
               by (meson spectroscopy_moves.simps(95)) 
             then show ?thesis using Defender_Conj True spectroscopy_moves.simps(69) by blast
          next
            case False
            from False have "\<not>spectroscopy_defender (Defender_Conj p Q) \<or> (\<exists>g'. spectroscopy_moves (Defender_Conj p Q) g' = None)" using Defender_Conj by simp
            (*hence "\<forall>y'. (y',(g,e)) \<notin> spectroscopy_pos_order" by (metis spectroscopy_pos_order.cases surj_pair)
            hence "False" using 1 sorry*)
            from this show ?thesis
            proof (rule disjE)
              assume "\<not>spectroscopy_defender (Defender_Conj p Q)"
              then show ?thesis by (simp add: Defender_Conj)
            next
              assume "\<exists>g'. spectroscopy_moves (Defender_Conj p Q) g' = None"
              hence "\<exists>y'. (y',((Defender_Conj p Q),e)) \<notin> spectroscopy_pos_order"
                by (meson spectroscopy_pos_order.cases)
              hence "False" sorry
              then show ?thesis
                by auto 
            qed
          qed
        qed
    next
      case (Defender_Stable_Conj x71 x72)
      then show ?case sorry
    next
      case (Defender_Immediate_Conj x81 x82)
      then show ?case sorry
    qed
  qed

lemma strategy_formulas_distinguish:
  assumes "strategy_formula (Attacker_Immediate p Q) e \<phi>"
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
    have "\<exists>\<phi>. strategy_formula (Attacker_Immediate p Q) e \<phi> \<and> expressiveness_price \<phi> \<le> e" 
      by force
  hence "\<exists>\<phi>\<in>\<O> e. strategy_formula (Attacker_Immediate p Q) e \<phi>" unfolding \<O>_def by blast
  thus "\<exists>\<phi>\<in>\<O> e. distinguishes_from \<phi> p Q"
    using strategy_formulas_distinguish by blast
qed


end (* context full_spec_game *)

end
