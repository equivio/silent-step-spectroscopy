theory Silent_Step_Spectroscopy
  imports Spectroscopy_Game Expressiveness_Price HML_SRBB Weak_Traces
begin

context full_spec_game begin

lemma distinction_implies_winning_budgets:
  assumes "distinguishes_from \<phi> p Q"
  shows "in_wina (expressiveness_price \<phi>) (Attacker_Immediate p Q)"
  sorry

lemma winning_budget_implies_strategy_formula:
  assumes "in_wina e (Attacker_Immediate p Q)"
  shows "\<exists>\<phi>. strategy_formula (Attacker_Immediate p Q) e \<phi> \<and> expressiveness_price \<phi> \<le> e"
  sorry

thm strategy_formula_strategy_formula_inner_strategy_formula_conjunct.induct
thm strategy_formula.simps 
thm strategy_formula_inner.simps 
thm strategy_formula_conjunct.simps


lemma strategy_formulas_distinguish:
  shows "(strategy_formula g e \<phi> \<longrightarrow>
        (case g of
        Attacker_Immediate p Q \<Rightarrow>  distinguishes_from \<phi> p Q
      | Attacker_Delayed p Q \<Rightarrow> (Q \<Zsurj>S Q)\<longrightarrow>((strategy_formula_inner g e \<chi> \<and> Q \<Zsurj>S Q) \<longrightarrow> distinguishes_from (Internal \<chi>) p Q)
      | Attacker_Clause p q \<Rightarrow> True

      | Defender_Conj p Q \<Rightarrow> distinguishes_from \<phi> p Q
      | Defender_Stable_Conj p Q \<Rightarrow> True
      | Defender_Branch p \<alpha> p' Q Qa \<Rightarrow> True
      | Attacker_Branch p Q \<Rightarrow> True))
      \<and> 
      (strategy_formula_inner g e \<chi> \<longrightarrow>
        (case g of
        Attacker_Immediate p Q \<Rightarrow>  True
      | Attacker_Delayed p Q \<Rightarrow> (Q \<Zsurj>S Q) \<longrightarrow> distinguishes_from (Internal \<chi>) p Q
      | Attacker_Clause p q \<Rightarrow> True

      | Defender_Conj p Q \<Rightarrow> distinguishes_from_inner \<chi> p Q
      | Defender_Stable_Conj p Q \<Rightarrow> (\<forall>q. \<not> p \<mapsto> \<tau> q) \<longrightarrow> distinguishes_from_inner \<chi> p Q
      | Defender_Branch p \<alpha> p' Q Qa \<Rightarrow>((p \<mapsto> \<alpha> p') \<and> (Qa \<noteq> {})) \<longrightarrow> distinguishes_from_inner \<chi> p (Q\<union>Qa)
      | Attacker_Branch p Q \<Rightarrow> True))
      \<and>
      (strategy_formula_conjunct g e \<psi> \<longrightarrow>
        (case g of
        Attacker_Immediate p Q \<Rightarrow>  True
      | Attacker_Delayed p Q \<Rightarrow> True
      | Attacker_Clause p q \<Rightarrow> distinguishes_conjunct \<psi> p q

      | Defender_Conj p Q \<Rightarrow> True
      | Defender_Stable_Conj p Q \<Rightarrow> True
      | Defender_Branch p \<alpha> p' Q Qa \<Rightarrow> True
      | Attacker_Branch p Q \<Rightarrow> True))"
proof(induction rule: strategy_formula_strategy_formula_inner_strategy_formula_conjunct.induct)
  case (delay p Q e \<chi>)
  then show ?case
    by (smt (verit) distinguishes_from_def option.discI silent_reachable.intros(1) silent_reachable_trans spectroscopy_moves.simps(1) spectroscopy_position.simps(50) spectroscopy_position.simps(53))
next
  case (procrastination p Q e \<chi>)
  from this obtain p' where IH: "spectroscopy_moves (Attacker_Delayed p Q) (Attacker_Delayed p' Q) = Some id \<and>
       in_wina e (Attacker_Delayed p' Q) \<and>
       strategy_formula_inner (Attacker_Delayed p' Q) e \<chi> \<and>
       (case Attacker_Delayed p' Q of Attacker_Delayed p Q \<Rightarrow> Q \<Zsurj>S Q \<longrightarrow> distinguishes_from (hml_srbb.Internal \<chi>) p Q
        | Defender_Branch p \<alpha> p' Q Qa \<Rightarrow> distinguishes_from_inner \<chi> p (Q \<union> Qa)
        | Defender_Conj p Q \<Rightarrow> distinguishes_from_inner \<chi> p Q
        | Defender_Stable_Conj p Q \<Rightarrow> (\<forall>q. \<not> p \<mapsto>\<tau> q) \<longrightarrow> distinguishes_from_inner \<chi> p Q | _ \<Rightarrow> True)" by auto
  hence D: "Q \<Zsurj>S Q \<longrightarrow> distinguishes_from (hml_srbb.Internal \<chi>) p' Q"
    using spectroscopy_position.simps(53) by fastforce
  from IH have "spectroscopy_moves (Attacker_Delayed p Q) (Attacker_Delayed p' Q) = Some id" by auto
  hence "p \<Zsurj>p'"
    by (metis option.discI silent_reachable.intros(1) silent_reachable_append_\<tau> spectroscopy_moves.simps(2)) 
  hence "Q \<Zsurj>S Q \<longrightarrow> distinguishes_from (hml_srbb.Internal \<chi>) p Q" using D
    by (smt (verit, del_insts) distinguishes_def distinguishes_from_def hml_models.simps(3) hml_srbb_models.elims(2) hml_srbb_models.elims(3) hml_srbb_to_hml.simps(2) silent_reachable_trans)
  then show ?case by simp
next
  case (observation p Q e \<phi> \<alpha>)
  then obtain p' Q' where IH: "spectroscopy_moves (Attacker_Delayed p Q) (Attacker_Immediate p' Q') = subtract 1 0 0 0 0 0 0 0 \<and>
     in_wina (e - E 1 0 0 0 0 0 0 0) (Attacker_Immediate p' Q') \<and>
     (strategy_formula (Attacker_Immediate p' Q') (e - E 1 0 0 0 0 0 0 0) \<phi> \<and>
      (case Attacker_Immediate p' Q' of Attacker_Immediate p Q \<Rightarrow> distinguishes_from \<phi> p Q
       | Attacker_Delayed p Q \<Rightarrow>
           Q \<Zsurj>S Q \<longrightarrow>
           strategy_formula_inner (Attacker_Immediate p' Q') (e - E 1 0 0 0 0 0 0 0) \<chi> \<and> Q \<Zsurj>S Q \<longrightarrow>
           distinguishes_from (hml_srbb.Internal \<chi>) p Q
       | Defender_Conj p Q \<Rightarrow> distinguishes_from \<phi> p Q | _ \<Rightarrow> True)) \<and>
     p \<mapsto>\<alpha> p' \<and> Q \<mapsto>S \<alpha> Q' " by auto
  hence D: "distinguishes_from \<phi> p' Q'" by auto 
  hence "p' \<Turnstile>SRBB \<phi>" using distinguishes_from_def by auto


  from IH have "spectroscopy_moves (Attacker_Delayed p Q) (Attacker_Immediate p' Q') = subtract 1 0 0 0 0 0 0 0" by simp
  hence "(\<exists>a. p \<mapsto> a p' \<and> Q \<mapsto>S a Q' \<and> a \<noteq> \<tau>)"
    by (smt (verit) option.discI spectroscopy_moves.simps(3)) 


  from IH have "p \<mapsto>\<alpha> p'" and "Q \<mapsto>S \<alpha> Q'"  by auto
  hence P: "p \<Turnstile>SRBB (Internal (Obs \<alpha> \<phi>))" using \<open>p' \<Turnstile>SRBB \<phi>\<close>
    using silent_reachable.intros(1) by auto
  have "Q \<Zsurj>S Q \<longrightarrow> (\<forall>q\<in>Q. \<not>(q \<Turnstile>SRBB (Internal (Obs \<alpha> \<phi>))))" proof (rule impI)
    assume "Q \<Zsurj>S Q"
    show "\<forall>q\<in>Q. \<not> q \<Turnstile>SRBB Internal (Obs \<alpha> \<phi>)" proof 
      fix q 
      show "q \<in> Q \<Longrightarrow> \<not> q \<Turnstile>SRBB Internal (Obs \<alpha> \<phi>)" proof 
        assume "q \<in> Q" and "q \<Turnstile>SRBB Internal (Obs \<alpha> \<phi>)" 
        hence "\<exists>q'.  q \<Zsurj> q' \<and> hml_srbb_inner_models (Obs \<alpha> \<phi>) q'" by simp 
        then obtain q' where X: "q \<Zsurj> q' \<and> hml_srbb_inner_models (Obs \<alpha> \<phi>) q'" by auto
        hence "hml_srbb_inner_models (Obs \<alpha> \<phi>) q'" by simp
        hence "q' \<Turnstile> (HML_soft_poss \<alpha> (hml_srbb_to_hml \<phi>))"
          by simp
        then show "False" proof(cases "\<alpha>=\<tau>")
          case True
          then show ?thesis sorry
        next
          case False
          hence "q' \<Turnstile> (hml.Obs \<alpha> (hml_srbb_to_hml \<phi>))" using \<open>q' \<Turnstile> (HML_soft_poss \<alpha> (hml_srbb_to_hml \<phi>))\<close>
            by simp
          hence "\<exists>q''. q' \<mapsto> \<alpha> q'' \<and> q'' \<Turnstile> (hml_srbb_to_hml \<phi>)"
            by simp 
          hence "\<exists>q' q''. q \<Zsurj> q' \<and> q' \<mapsto> \<alpha> q'' \<and> q'' \<Turnstile>SRBB \<phi>" using X by auto
          then show "False" using \<open>Q \<Zsurj>S Q\<close>
            by (metis D \<open>Q \<mapsto>S \<alpha> Q'\<close> \<open>q \<in> Q\<close> distinguishes_from_def)
        qed 
      qed
    qed
  qed
  hence "Q \<Zsurj>S Q \<longrightarrow> distinguishes_from (hml_srbb.Internal (hml_srbb_inner.Obs \<alpha> \<phi>)) p Q" using P
    by (meson distinguishes_def distinguishes_from_def)
  then show ?case by simp
next
  case (early_conj Q p Q' e \<phi>)
  then show ?case
    by (smt (verit, del_insts) local.finishing_or_early_conj option.distinct(1) spectroscopy_position.simps(50) spectroscopy_position.simps(55))
next
  case (late_conj p Q e \<chi>)
  hence "distinguishes_from_inner \<chi> p Q" by simp
  hence "Q \<Zsurj>S Q \<longrightarrow> distinguishes_from (hml_srbb.Internal \<chi>) p Q"
    by (metis distinguishes_from_def distinguishes_from_inner_def hml_models.simps(3) hml_srbb_inner_models.elims(2) hml_srbb_inner_models.elims(3) hml_srbb_models.simps hml_srbb_to_hml.simps(2) silent_reachable.intros(1))
  then show ?case by simp 
next
  case (conj Q p e \<Phi>)
  hence A: "\<forall>q \<in> Q. distinguishes_conjunct (\<Phi> q) p q" by auto
  hence P: "\<forall>q \<in> Q. hml_srbb_conjunct_models (\<Phi> q) p" using distinguishes_conjunct_def by simp
  hence "\<forall>q\<in>Q. distinguishes_inner (hml_srbb_inner.Conj Q \<Phi>) p q" using A srbb_dist_conjunct_implies_dist_conjunction by simp
  hence "distinguishes_from_inner (hml_srbb_inner.Conj Q \<Phi>) p Q" using distinguishes_from_inner_def P
    by (metis dist_from_inner_srbb_eq_dist_from_hml distinguishes_from_hml_def distinguishes_from_inner'_def distinguishes_from_inner_prime empty_iff hml_models.simps(1) hml_srbb_inner_to_hml.simps(2) tt_eq_empty_conj) 
  then show ?case by simp 
next
  case (imm_conj Q p e \<Phi>)
  hence D: "\<forall>q \<in> Q. distinguishes_conjunct (\<Phi> q) p q" by auto
  hence "\<forall>q \<in> Q. hml_srbb_conjunct_models (\<Phi> q) p" using distinguishes_conjunct_def by simp
  hence "\<forall>q\<in>Q. distinguishes (ImmConj Q \<Phi>) p q" using D srbb_dist_conjunct_implies_dist_imm_conjunction by simp
  hence "distinguishes_from (ImmConj Q \<Phi>) p Q" using distinguishes_from_def
    by (metis distinguishes_from'_def distinguishes_from_prime empty_iff hml_models.simps(1) hml_srbb_models.elims(3) hml_srbb_to_hml.simps(3) tt_eq_empty_conj) 
  then show ?case by simp 
next
  case (pos p q e \<chi>)
  then obtain Q' where IH: "spectroscopy_moves (Attacker_Clause p q) (Attacker_Delayed p Q') = Some min1_6 \<and>
       in_wina (min1_6 e) (Attacker_Delayed p Q') \<and>
       strategy_formula_inner (Attacker_Delayed p Q') (min1_6 e) \<chi> \<and>
       (case Attacker_Delayed p Q' of Attacker_Delayed p Q \<Rightarrow> Q \<Zsurj>S Q \<longrightarrow> distinguishes_from (hml_srbb.Internal \<chi>) p Q
        | Defender_Branch p \<alpha> p' Q Qa \<Rightarrow> distinguishes_from_inner \<chi> p (Q \<union> Qa)
        | Defender_Conj p Q \<Rightarrow> distinguishes_from_inner \<chi> p Q
        | Defender_Stable_Conj p Q \<Rightarrow> (\<forall>q. \<not> p \<mapsto>\<tau> q) \<longrightarrow> distinguishes_from_inner \<chi> p Q | _ \<Rightarrow> True)" by auto
  hence D: "Q' \<Zsurj>S Q' \<longrightarrow> distinguishes_from (hml_srbb.Internal \<chi>) p Q'" by simp
  have "spectroscopy_moves (Attacker_Clause p q) (Attacker_Delayed p Q')= Some min1_6" using IH by simp
  hence "{q} \<Zsurj>S Q'" using spectroscopy_moves.simps
    by (metis (no_types, lifting) option.discI) 
  have "Q' \<Zsurj>S Q' \<longrightarrow> q \<in> Q'"
    by (simp add: \<open>{q} \<Zsurj>S Q'\<close> silent_reachable.intros(1)) 
  hence "distinguishes_conjunct (hml_srbb_conjunct.Pos \<chi>) p q" using D \<open>{q} \<Zsurj>S Q'\<close>
    by (smt (verit, ccfv_threshold) LTS_Tau.silent_reachable_trans distinguishes_conjunct_def distinguishes_def distinguishes_from_def hml_conjunct_models.simps(1) hml_srbb_conjunct_models.elims(2) hml_srbb_conjunct_models.elims(3) hml_srbb_conjunct_to_hml_conjunct.simps(1) hml_srbb_models.elims(1) hml_srbb_to_hml.simps(2) silent_reachable.intros(1)) 
  then show ?case by simp
next
  case (neg p q e \<chi>)
  then obtain P' where IH: "(spectroscopy_moves (Attacker_Clause p q) (Attacker_Delayed q P') = Some (min1_7 \<circ> (\<lambda>x. x - E 0 0 0 0 0 0 0 1)) \<and>
        in_wina (min1_7 (e - E 0 0 0 0 0 0 0 1)) (Attacker_Delayed q P')) \<and>
       strategy_formula_inner (Attacker_Delayed q P') (min1_7 (e - E 0 0 0 0 0 0 0 1)) \<chi> \<and>
       (case Attacker_Delayed q P' of Attacker_Delayed p Q \<Rightarrow> Q \<Zsurj>S Q \<longrightarrow> distinguishes_from (hml_srbb.Internal \<chi>) p Q
        | Defender_Branch p \<alpha> p' Q Qa \<Rightarrow> distinguishes_from_inner \<chi> p (Q \<union> Qa)
        | Defender_Conj p Q \<Rightarrow> distinguishes_from_inner \<chi> p Q
        | Defender_Stable_Conj p Q \<Rightarrow> (\<forall>q. \<not> p \<mapsto>\<tau> q) \<longrightarrow> distinguishes_from_inner \<chi> p Q | _ \<Rightarrow> True)" by auto
  hence D: "P' \<Zsurj>S P' \<longrightarrow> distinguishes_from (hml_srbb.Internal \<chi>) q P'" by simp
  from IH have "spectroscopy_moves (Attacker_Clause p q) (Attacker_Delayed q P') = Some (min1_7 \<circ> (\<lambda>x. x - E 0 0 0 0 0 0 0 1))" by auto
  hence "{p} \<Zsurj>S P'" using spectroscopy_moves.simps
    by (metis (no_types, lifting) not_Some_eq) 
  have "P' \<Zsurj>S P' \<longrightarrow> p \<in> P'" using \<open>{p} \<Zsurj>S P'\<close>  by (simp add: silent_reachable.intros(1)) 
  hence "distinguishes_conjunct (hml_srbb_conjunct.Neg \<chi>) p q" using D \<open>{p} \<Zsurj>S P'\<close>
    by (metis LTS_Tau.silent_reachable_trans distinguishes_conjunct_def distinguishes_from_def hml_conjunct_models.simps(2) hml_srbb_conjunct_models.elims(2) hml_srbb_conjunct_models.elims(3) hml_srbb_conjunct_to_hml_conjunct.simps(2) hml_srbb_models.elims(1) hml_srbb_to_hml.simps(2) silent_reachable.intros(1)) 
  then show ?case by simp
next
  case (stable p Q e \<chi>)
  then obtain Q' where IH: "spectroscopy_moves (Attacker_Delayed p Q) (Defender_Stable_Conj p Q') = Some id \<and>
       in_wina e (Defender_Stable_Conj p Q') \<and>
       strategy_formula_inner (Defender_Stable_Conj p Q') e \<chi> \<and>
       (case Defender_Stable_Conj p Q' of Attacker_Delayed p Q \<Rightarrow> Q \<Zsurj>S Q \<longrightarrow> distinguishes_from (hml_srbb.Internal \<chi>) p Q
        | Defender_Branch p \<alpha> p' Q Qa \<Rightarrow> p \<mapsto>\<alpha> p' \<and> Qa \<noteq> {} \<longrightarrow> distinguishes_from_inner \<chi> p (Q \<union> Qa)
        | Defender_Conj p Q \<Rightarrow> distinguishes_from_inner \<chi> p Q
        | Defender_Stable_Conj p Q \<Rightarrow> (\<forall>q. \<not> p \<mapsto>\<tau> q) \<longrightarrow> distinguishes_from_inner \<chi> p Q | _ \<Rightarrow> True)" by auto
  hence M:"spectroscopy_moves (Attacker_Delayed p Q) (Defender_Stable_Conj p Q') = Some id" by simp
  hence "(\<nexists>p''. p \<mapsto>\<tau> p'')"
    by (metis local.late_stbl_conj option.distinct(1)) 

  from IH have "(\<forall>q. \<not> p \<mapsto>\<tau> q) \<longrightarrow> distinguishes_from_inner \<chi> p Q'" by simp
  hence "distinguishes_from_inner \<chi> p Q'" using \<open>\<nexists>p''. p \<mapsto>\<tau> p''\<close> by auto
  hence "hml_srbb_inner_models \<chi> p"
    by (simp add: distinguishes_from_inner_def)
  hence "p \<Turnstile>SRBB (hml_srbb.Internal \<chi>)"
    using hml_impl_iffI pre_\<epsilon> by auto

  have "Q \<Zsurj>S Q \<longrightarrow> distinguishes_from (hml_srbb.Internal \<chi>) p Q" proof
    assume "Q \<Zsurj>S Q"
    have "(\<forall>q \<in> Q. \<not>(q \<Turnstile>SRBB (hml_srbb.Internal \<chi>)))" proof
      fix q
      assume "q \<in> Q"
      show "\<not>(q \<Turnstile>SRBB (hml_srbb.Internal \<chi>))" proof
        assume "(q \<Turnstile>SRBB (hml_srbb.Internal \<chi>))"
        hence "\<exists>q'. q \<Zsurj> q' \<and> (\<nexists>q''. q' \<mapsto>\<tau> q'') \<and> (hml_srbb_inner_models \<chi> q')" sorry
        then obtain q' where X: "q \<Zsurj> q' \<and> (\<nexists>q''. q' \<mapsto>\<tau> q'') \<and> (hml_srbb_inner_models \<chi> q')" by auto

        from M have "Q' = { q \<in> Q. (\<nexists>q'. q \<mapsto>\<tau> q')}"
          by (metis (full_types) local.late_stbl_conj option.distinct(1))
        hence "q' \<in> Q'" using X \<open>Q \<Zsurj>S Q\<close> \<open>q \<in> Q\<close> by blast
        thus "False" using X \<open>distinguishes_from_inner \<chi> p Q'\<close>
          by (simp add: distinguishes_from_inner_def)
      qed
    qed
    thus "distinguishes_from (hml_srbb.Internal \<chi>) p Q" using \<open>p \<Turnstile>SRBB (hml_srbb.Internal \<chi>)\<close>
      by (simp add: distinguishes_from_def)
  qed
  then show ?case by simp
next
  case (stable_conj Q p e \<Phi>)
  hence IH: "\<forall>q\<in> Q. distinguishes_conjunct (\<Phi> q) p q" by simp
  hence Q: "\<forall>q \<in> Q. hml_srbb_conjunct_models (\<Phi> q) p"
    by (simp add: distinguishes_conjunct_def) 
  have "(\<forall>q. \<not> p \<mapsto>\<tau> q) \<longrightarrow> distinguishes_from_inner (StableConj Q \<Phi>) p Q" proof
    assume "(\<forall>q. \<not> p \<mapsto>\<tau> q)"
    thus  "distinguishes_from_inner (StableConj Q \<Phi>) p Q" using IH Q srbb_dist_conjunct_or_stable_implies_dist_stable_conjunction
      by (smt (verit, ccfv_threshold) LTS_Tau.hml_models.simps(2) dist_from_inner_srbb_eq_dist_from_hml distinguishes_from_hml_def distinguishes_from_inner'_def distinguishes_from_inner_prime distinguishes_inner_def hml_conjunct_models.simps(1) hml_conjunct_models.simps(2) hml_models.simps(1) hml_models.simps(5) hml_srbb_inner_models.elims(3) hml_srbb_inner_to_hml.simps(3) tt_eq_empty_conj) 
  qed
  then show ?case by simp
next
  case (branch p Q e \<chi>)
  then obtain p' Q' \<alpha> Q\<alpha> where IH: "spectroscopy_moves (Attacker_Delayed p Q) (Defender_Branch p \<alpha> p' Q' Q\<alpha>) = Some id \<and>
     in_wina e (Defender_Branch p \<alpha> p' Q' Q\<alpha>) \<and>
     strategy_formula_inner (Defender_Branch p \<alpha> p' Q' Q\<alpha>) e \<chi> \<and>
     (case Defender_Branch p \<alpha> p' Q' Q\<alpha> of Attacker_Delayed p Q \<Rightarrow> Q \<Zsurj>S Q \<longrightarrow> distinguishes_from (hml_srbb.Internal \<chi>) p Q
      | Defender_Branch p \<alpha> p' Q Qa \<Rightarrow> p \<mapsto>\<alpha> p' \<and> Qa \<noteq> {} \<longrightarrow> distinguishes_from_inner \<chi> p (Q \<union> Qa)
      | Defender_Conj p Q \<Rightarrow> distinguishes_from_inner \<chi> p Q
      | Defender_Stable_Conj p Q \<Rightarrow> (\<forall>q. \<not> p \<mapsto>\<tau> q) \<longrightarrow> distinguishes_from_inner \<chi> p Q | _ \<Rightarrow> True)" by blast
  hence "spectroscopy_moves (Attacker_Delayed p Q) (Defender_Branch p \<alpha> p' Q' Q\<alpha>) = Some id" by simp
  hence "p \<mapsto>\<alpha> p' \<and> Q\<alpha> \<noteq> {}"
    by (metis local.br_conj option.distinct(1)) 
  from IH have "p \<mapsto>\<alpha> p' \<and> Q\<alpha> \<noteq> {} \<longrightarrow> distinguishes_from_inner \<chi> p (Q' \<union> Q\<alpha>)" by simp
  hence D: "distinguishes_from_inner \<chi> p (Q' \<union> Q\<alpha>)" using \<open>p \<mapsto>\<alpha> p' \<and> Q\<alpha> \<noteq> {}\<close> by auto

  from IH have "Q' = Q - Q\<alpha> \<and> p \<mapsto>\<alpha> p' \<and> Q\<alpha> \<noteq> {} \<and> Q\<alpha> \<subseteq> Q"
    by (metis local.br_conj option.distinct(1))
  hence "Q=(Q' \<union> Q\<alpha>)" by auto
  hence "distinguishes_from_inner \<chi> p Q" using D by auto
  hence " Q \<Zsurj>S Q \<longrightarrow> distinguishes_from (hml_srbb.Internal \<chi>) p Q"
    using dist_from_inner_srbb_eq_dist_from_hml dist_from_srbb_eq_dist_from_hml distinguishes_from_hml_def hml_impl_iffI pre_\<epsilon> by auto 
  then show ?case by simp
next
  case (branch_conj p \<alpha> p' Q1 Q\<alpha> e e' \<psi> \<Phi>)
  hence A1: "\<forall>q\<in>Q1. hml_srbb_conjunct_models (\<Phi> q) p" by (simp add: distinguishes_conjunct_def)

  from branch_conj obtain Q' where IH: "spectroscopy_moves (Defender_Branch p \<alpha> p' Q1 Q\<alpha>) (Attacker_Branch p' Q') =
         Some (min1_6 \<circ> (\<lambda>x. x - E 0 1 1 0 0 0 0 0)) \<and>
         spectroscopy_moves (Attacker_Branch p' Q') (Attacker_Immediate p' Q') = subtract 1 0 0 0 0 0 0 0 \<and>
         in_wina (min1_6 (e - E 0 1 1 0 0 0 0 0) - E 1 0 0 0 0 0 0 0) (Attacker_Immediate p' Q') \<and>
         strategy_formula (Attacker_Immediate p' Q') e' \<psi> \<and>
         (case Attacker_Immediate p' Q' of Attacker_Immediate p Q \<Rightarrow> distinguishes_from \<psi> p Q
          | Attacker_Delayed p Q \<Rightarrow>
              Q \<Zsurj>S Q \<longrightarrow>
              strategy_formula_inner (Attacker_Immediate p' Q') e' \<chi> \<and> Q \<Zsurj>S Q \<longrightarrow>
              distinguishes_from (hml_srbb.Internal \<chi>) p Q
          | Defender_Conj p Q \<Rightarrow> distinguishes_from \<psi> p Q | _ \<Rightarrow> True)" by auto
  hence " distinguishes_from \<psi> p' Q'" by simp
  hence X:"p' \<Turnstile>SRBB \<psi>" by (simp add: distinguishes_from_def) 
  have Y: "\<forall>q \<in> Q'. \<not>(q \<Turnstile>SRBB \<psi>)" using \<open>distinguishes_from \<psi> p' Q'\<close>  by (simp add: distinguishes_from_def) 

  have "(p \<mapsto> \<alpha> p' \<and> Q\<alpha> \<noteq> {}) \<longrightarrow> distinguishes_from_inner (BranchConj \<alpha> \<psi> Q1 \<Phi>) p (Q1 \<union> Q\<alpha>) " proof
    assume "p \<mapsto> \<alpha> p' \<and> Q\<alpha> \<noteq> {}"
    hence "p \<mapsto> \<alpha> p'" by simp
    from IH have "spectroscopy_moves (Defender_Branch p \<alpha> p' Q1 Q\<alpha>) (Attacker_Branch p' Q') =
         Some (min1_6 \<circ> (\<lambda>x. x - E 0 1 1 0 0 0 0 0))" by auto
    hence "Q\<alpha> \<mapsto>aS \<alpha> Q'"
      by (smt (verit) local.br_obsv option.distinct(1)) 
    hence A2: "hml_srbb_inner_models (Obs \<alpha> \<psi>) p" using X \<open>p \<mapsto> \<alpha> p' \<and> Q\<alpha> \<noteq> {}\<close>  by auto  

    have A3: "\<forall>q \<in> (Q1 \<union> Q\<alpha>). distinguishes_inner (BranchConj \<alpha> \<psi> Q1 \<Phi>) p q" proof
      fix q
      assume "q\<in>(Q1 \<union> Q\<alpha>)"     
      show "distinguishes_inner (BranchConj \<alpha> \<psi> Q1 \<Phi>) p q" proof (cases "q\<in>Q1")
        case True
        hence  "distinguishes_conjunct (\<Phi> q) p q" using branch_conj(2) by simp
        thus "distinguishes_inner (BranchConj \<alpha> \<psi> Q1 \<Phi>) p q" using A1 A2 srbb_dist_conjunct_or_branch_implies_dist_branch_conjunction True by blast
      next
        case False
        hence "q\<in> Q\<alpha>" using \<open>q\<in>(Q1 \<union> Q\<alpha>)\<close> by simp
        hence "\<not>(hml_srbb_inner_models (Obs \<alpha> \<psi>) q)"  using Y \<open>Q\<alpha> \<mapsto>aS \<alpha> Q'\<close> \<open>p \<mapsto> \<alpha> p'\<close> sorry
        hence "distinguishes_inner (Obs \<alpha> \<psi>) p q" using A2
          by (simp add: distinguishes_inner_def) 
        thus  "distinguishes_inner (BranchConj \<alpha> \<psi> Q1 \<Phi>) p q" using A1 A2 srbb_dist_conjunct_or_branch_implies_dist_branch_conjunction by blast    
      qed
    qed

    from \<open>p \<mapsto> \<alpha> p' \<and> Q\<alpha> \<noteq> {}\<close> have "\<exists>qa. qa \<in> Q\<alpha>" by auto
    then obtain qa where "qa \<in> Q\<alpha>" by auto
    hence A4: "hml_srbb_inner_models (BranchConj \<alpha> \<psi> Q1 \<Phi>) p" using A3
      by (meson Un_iff distinguishes_inner_def) 

    from A3 have "\<forall>q \<in> (Q1 \<union> Q\<alpha>). \<not>(hml_srbb_inner_models (BranchConj \<alpha> \<psi> Q1 \<Phi>) q)"
      using distinguishes_inner_def by blast 

    thus "distinguishes_from_inner (BranchConj \<alpha> \<psi> Q1 \<Phi>) p (Q1 \<union> Q\<alpha>)" using A4 distinguishes_from_inner_def by simp 
  qed 
 
  then show ?case by simp
qed

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
    have "\<exists>\<phi>. strategy_formula (Attacker_Immediate p Q) e \<phi> \<and> expressiveness_price \<phi> \<le> e" .
  hence "\<exists>\<phi>\<in>\<O> e. strategy_formula (Attacker_Immediate p Q) e \<phi>" unfolding \<O>_def by blast
  thus "\<exists>\<phi>\<in>\<O> e. distinguishes_from \<phi> p Q"
    using strategy_formulas_distinguish by fastforce 
qed


end (* context full_spec_game *)

end
