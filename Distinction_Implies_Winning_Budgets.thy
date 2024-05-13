text \<open>\newpage\<close>
section \<open>Distinction Implies Winning Budgets\<close>
theory Distinction_Implies_Winning_Budgets
  imports Spectroscopy_Game Expressiveness_Price
begin

context full_spec_game
begin

text \<open>In this section, we prove that if a formula distinguishes a process @{term "p"}
      from a set of process @{term "Q"}, then the price of this formula is in the attackers-winning
      budget. This is the same statement as that of lemma $1$ in the paper \cite[p. 20]{bisping2023lineartimebranchingtime}.
      We likewise also prove it in the same manner.
      
      First, we show that the statement holds if @{term "Q = {}"}. This is the case, as the
      attacker can move, at no cost, from the starting position, @{term "Attacker_Immediate p {}"}, 
      to the defender position @{term "Defender_Conj p {}"}. In this position the defender is then
      unable to make any further moves. Hence, the attacker wins the game with any budget.\<close>

lemma distinction_implies_winning_budgets_empty_Q:
  assumes "distinguishes_from \<phi> p {}"
  shows "in_wina (expressiveness_price \<phi>) (Attacker_Immediate p {})"
proof-
  have not_neg: "expressiveness_price \<phi> \<noteq> eneg" by auto
  moreover have is_last_move: "spectroscopy_moves (Defender_Conj p {}) p' = None" for p' 
    by(rule spectroscopy_moves.elims, auto)
  moreover have "spectroscopy_defender (Defender_Conj p {})" by simp
  ultimately have conj_win: "in_wina (expressiveness_price \<phi>) (Defender_Conj p {})" 
    by (simp add: in_wina.intros(1))

  from late_inst_conj[of p "{}" p "{}"] have next_move0: 
    "spectroscopy_moves (Attacker_Delayed p {}) (Defender_Conj p {}) = Some id" by force

  from delay[of p "{}" p "{}"] have next_move1: 
    "spectroscopy_moves (Attacker_Immediate p {}) (Attacker_Delayed p {}) = Some id" by force

  moreover have "attacker (Attacker_Immediate p {})" by simp
  ultimately show ?thesis using in_wina.intros(2)[of "Attacker_Immediate p {}" "expressiveness_price \<phi>"]
    using next_move0 next_move1
    by (metis conj_win id_apply in_wina.intros(2) not_neg option.distinct(1) option.sel spectroscopy_defender.simps(4))
qed

text \<open>Next, we show the statement for the case that @{term "Q \<noteq> {}"}. Following the proof of
      \cite[p. 20]{bisping2023lineartimebranchingtime}, we do this by induction on a more
      complex property. We formalize this property as follows (keeping the labels from the paper):
      \begin{itemize}
      \item [1.] \<open>\<forall>Q p. Q \<noteq> {} \<longrightarrow> distinguishes_from \<phi> p Q\<close>\\
      \<open>\<longrightarrow> in_wina (expressiveness_price \<phi>) (Attacker_Immediate p Q)\<close>
      
      \item[2.] \<open>\<forall>p Q. Q \<noteq> {} \<longrightarrow> distinguishes_from_inner \<chi> p Q \<longrightarrow> Q \<Zsurj>S Q\<close>\\
                \<open>\<longrightarrow> in_wina (expr_pr_inner \<chi>) (Attacker_Delayed p Q)\<close>
      
      \item [4.] \<open>\<forall>\<Psi>_I \<Psi> p Q. \<chi> = Conj \<Psi>_I \<Psi> \<longrightarrow> Q \<noteq> {}\<close>\\
            \<open>\<longrightarrow> distinguishes_from_inner \<chi> p Q\<close>\\
            \<open>\<longrightarrow> in_wina (expr_pr_inner \<chi>) (Defender_Conj p Q)\<close>
      
      \item[5.] \<open>\<forall>\<Psi>_I \<Psi> p Q. \<chi> = StableConj \<Psi>_I \<Psi> \<longrightarrow> Q \<noteq> {}\<close>\\
            \<open>\<longrightarrow> distinguishes_from_inner \<chi> p Q \<longrightarrow> (\<forall>q \<in> Q. \<nexists>q'. q \<mapsto> \<tau> q')\<close>\\
            \<open>\<longrightarrow> in_wina (expr_pr_inner \<chi>) (Defender_Stable_Conj p Q)\<close>
      
      \item[6.] \<open>\<forall>\<Psi>_I \<Psi> \<alpha> \<phi> p Q p' Q_\<alpha>. \<chi> = BranchConj \<alpha> \<phi> \<Psi>_I \<Psi>\<close>\\
             \<open>\<longrightarrow>distinguishes_from_inner \<chi> p Q \<longrightarrow> p \<mapsto>\<alpha> p' \<longrightarrow> p' \<Turnstile>SRBB \<phi>\<close>\\
             \<open>\<longrightarrow> Q_\<alpha> \<noteq> {} \<longrightarrow> Q \<inter> model_set_inner (Conj \<Psi>_I \<Psi>) \<subseteq> Q_\<alpha>\<close>\\
             \<open>\<longrightarrow> Q_\<alpha> \<subseteq> Q - model_set_inner (Obs \<alpha> \<phi>)\<close>\\
             \<open>\<longrightarrow> in_wina (expr_pr_inner \<chi>) (Defender_Branch p \<alpha> p' (Q - Q_\<alpha>) Q_\<alpha>)\<close>
      
      \item[3.] \<open>\<forall>p q. distinguishes_conjunct \<psi> p q\<close>\\
                \<open>\<longrightarrow> in_wina (expr_pr_conjunct \<psi>) (Attacker_Clause p q)\<close>
      \end{itemize}
    Note that the sixth case differs from the paper in the assumption that @{term "Q_\<alpha> \<noteq> {}"}.
    Strictly speaking this case is covered by the previous lemma, the case that @{term "Q = {}"},
    since using @{term "Q \<inter> model_set_inner (Conj \<Psi>_I \<Psi>) \<subseteq> Q_\<alpha>"} and @{term "Q_\<alpha> = {}"}
    we can conclude that @{term "Q = {}"}.
    But adding this assumption allows us to directly apply the induction hypothesis. Without
    further having to do this case distinction.\label{deviation:lemma1_Q_a}
    The induction itself is then done via the rule \<open>induct\<close> on \<open>hml_srbb_hml_srbb_inner_hml_srbb_conjunct\<close>.
    The parts of this proof that are completed work as described in the paper.
    A notable exception to this is that we also have to prove the statement for the 
    formula @{term "TT"}\label{deviation:lemma1TT}. This holds trivially as @{term "TT"} does not distinguishes any @{term "p"} from any
    non-empty @{term "Q"}. 
  \<close>
lemma distinction_implies_winning_budgets:
  assumes "distinguishes_from \<phi> p Q"
  shows "in_wina (expressiveness_price \<phi>) (Attacker_Immediate p Q)"
proof-
  have "\<And>\<phi> \<chi> \<psi>.
        (\<forall>Q p. Q \<noteq> {} \<longrightarrow> distinguishes_from \<phi> p Q
               \<longrightarrow> in_wina (expressiveness_price \<phi>) (Attacker_Immediate p Q))
      \<and>
        ((\<forall>p Q. Q \<noteq> {} \<longrightarrow> distinguishes_from_inner \<chi> p Q \<longrightarrow> Q \<Zsurj>S Q
            \<longrightarrow> in_wina (expr_pr_inner \<chi>) (Attacker_Delayed p Q))
        \<and> (\<forall>\<Psi>_I \<Psi> p Q. \<chi> = Conj \<Psi>_I \<Psi> \<longrightarrow>
            Q \<noteq> {} \<longrightarrow> distinguishes_from_inner \<chi> p Q
            \<longrightarrow> in_wina (expr_pr_inner \<chi>) (Defender_Conj p Q))
        \<and> (\<forall>\<Psi>_I \<Psi> p Q. \<chi> = StableConj \<Psi>_I \<Psi> \<longrightarrow>
            Q \<noteq> {} \<longrightarrow> distinguishes_from_inner \<chi> p Q \<longrightarrow> (\<forall>q \<in> Q. \<nexists>q'. q \<mapsto> \<tau> q')
            \<longrightarrow> in_wina (expr_pr_inner \<chi>) (Defender_Stable_Conj p Q))
        \<and> (\<forall>\<Psi>_I \<Psi> \<alpha> \<phi> p Q p' Q_\<alpha>. \<chi> = BranchConj \<alpha> \<phi> \<Psi>_I \<Psi> \<longrightarrow>
            distinguishes_from_inner \<chi> p Q \<longrightarrow> p \<mapsto>a \<alpha> p' \<longrightarrow> p' \<Turnstile>SRBB \<phi> \<longrightarrow>
            Q_\<alpha> \<noteq> {} \<longrightarrow> Q_\<alpha> = Q - model_set_inner (Obs \<alpha> \<phi>)
            \<longrightarrow> in_wina (expr_pr_inner \<chi>) (Defender_Branch p \<alpha> p' (Q - Q_\<alpha>) Q_\<alpha>)))
      \<and>
        (\<forall>p q. distinguishes_conjunct \<psi> p q
               \<longrightarrow> in_wina (expr_pr_conjunct \<psi>) (Attacker_Clause p q))"
  proof -
    fix \<phi> \<chi> \<psi>
    show "(\<forall>Q p. Q \<noteq> {} \<longrightarrow> distinguishes_from \<phi> p Q
               \<longrightarrow> in_wina (expressiveness_price \<phi>) (Attacker_Immediate p Q))
      \<and>
        ((\<forall>p Q. Q \<noteq> {} \<longrightarrow> distinguishes_from_inner \<chi> p Q \<longrightarrow> Q \<Zsurj>S Q
            \<longrightarrow> in_wina (expr_pr_inner \<chi>) (Attacker_Delayed p Q))
        \<and> (\<forall>\<Psi>_I \<Psi> p Q. \<chi> = Conj \<Psi>_I \<Psi> \<longrightarrow>
            Q \<noteq> {} \<longrightarrow> distinguishes_from_inner \<chi> p Q
            \<longrightarrow> in_wina (expr_pr_inner \<chi>) (Defender_Conj p Q))
        \<and> (\<forall>\<Psi>_I \<Psi> p Q. \<chi> = StableConj \<Psi>_I \<Psi> \<longrightarrow>
            Q \<noteq> {} \<longrightarrow> distinguishes_from_inner \<chi> p Q \<longrightarrow> (\<forall>q \<in> Q. \<nexists>q'. q \<mapsto> \<tau> q')
            \<longrightarrow> in_wina (expr_pr_inner \<chi>) (Defender_Stable_Conj p Q))
        \<and> (\<forall>\<Psi>_I \<Psi> \<alpha> \<phi> p Q p' Q_\<alpha>. \<chi> = BranchConj \<alpha> \<phi> \<Psi>_I \<Psi> \<longrightarrow>
            distinguishes_from_inner \<chi> p Q \<longrightarrow> p \<mapsto>a \<alpha> p' \<longrightarrow> p' \<Turnstile>SRBB \<phi> \<longrightarrow>
            Q_\<alpha> \<noteq> {} \<longrightarrow> Q_\<alpha> = Q - model_set_inner (Obs \<alpha> \<phi>)
            \<longrightarrow> in_wina (expr_pr_inner \<chi>) (Defender_Branch p \<alpha> p' (Q - Q_\<alpha>) Q_\<alpha>)))
      \<and>
        (\<forall>p q. distinguishes_conjunct \<psi> p q
               \<longrightarrow> in_wina (expr_pr_conjunct \<psi>) (Attacker_Clause p q))"
    proof (induct rule: hml_srbb_hml_srbb_inner_hml_srbb_conjunct.induct)
      case TT
      then show ?case
      proof (clarify)
        fix Q p
        assume "Q \<noteq> {}"
          and "distinguishes_from TT p Q"
        hence "\<exists>q. q \<in> Q" 
          by blast
        then obtain q where "q \<in> Q" by auto
  
        from \<open>distinguishes_from TT p Q\<close>
         and \<open>q \<in> Q\<close>
        have "distinguishes TT p q" 
          using distinguishes_from_def by auto
  
        with verum_never_distinguishes
        show "in_wina (expressiveness_price TT) (Attacker_Immediate p Q)" 
          by blast
      qed
    next
      case (Internal \<chi>)
      show ?case
      proof (clarify)
        fix Q p
        assume "Q \<noteq> {}"
           and "distinguishes_from (Internal \<chi>) p Q"
        hence "(\<exists>p'. p \<Zsurj> p' \<and> (p' \<Turnstile> hml_srbb_inner_to_hml \<chi>))
             \<and> (\<forall>q \<in> Q. (\<nexists>q'. q \<Zsurj> q' \<and> (q' \<Turnstile> hml_srbb_inner_to_hml \<chi>)))"
          unfolding distinguishes_from_def
                and distinguishes_def
                and hml_srbb_models.simps
                and hml_srbb_to_hml.simps
                and hml_models.simps
          by blast
        then have "\<exists>p'. p \<Zsurj> p' \<and> p' \<Turnstile> hml_srbb_inner_to_hml \<chi>"
              and "\<forall>q \<in> Q. (\<nexists>q'. q \<Zsurj> q' \<and> q' \<Turnstile> hml_srbb_inner_to_hml \<chi>)"
          by auto
        hence "\<forall>q \<in> Q. (\<forall>q'. q \<Zsurj> q' \<longrightarrow> \<not>(q' \<Turnstile> hml_srbb_inner_to_hml \<chi>))" by auto
        then have "\<forall>q \<in> Q. (\<forall>q'\<in>Q'. q \<Zsurj> q' \<longrightarrow> \<not>(q' \<Turnstile> hml_srbb_inner_to_hml \<chi>))" 
          for Q' by blast
        then have "Q \<Zsurj>S Q' \<longrightarrow> (\<forall>q' \<in> Q'. \<not>(q' \<Turnstile> hml_srbb_inner_to_hml \<chi>))"
          for Q' using \<open>Q \<noteq> {}\<close> by blast
  
        define Q\<tau> where "Q\<tau> \<equiv> silent_reachable_set Q"
        with \<open>\<And>Q'. Q \<Zsurj>S Q' \<longrightarrow> (\<forall>q' \<in> Q'. \<not>(q' \<Turnstile> hml_srbb_inner_to_hml \<chi>))\<close>
        have "\<forall>q' \<in> Q\<tau>. \<not>(q' \<Turnstile> hml_srbb_inner_to_hml \<chi>)" 
          using sreachable_set_is_sreachable by presburger
        have "Q\<tau> \<Zsurj>S Q\<tau>" unfolding Q\<tau>_def 
          by (metis silent_reachable_trans sreachable_set_is_sreachable 
              silent_reachable.intros(1))
  
        from \<open>\<exists>p'. p \<Zsurj> p' \<and> (p' \<Turnstile> hml_srbb_inner_to_hml \<chi>)\<close>
        obtain p' where "p \<Zsurj> p'" and "p' \<Turnstile> hml_srbb_inner_to_hml \<chi>" by auto
        from this(1) have "p \<Zsurj>L p'" by(rule silent_reachable_impl_loopless)
  
        have "Q\<tau> \<noteq> {}"
          using silent_reachable.intros(1) sreachable_set_is_sreachable Q\<tau>_def \<open>Q \<noteq> {}\<close> 
          by fastforce
  
        from \<open>p' \<Turnstile> hml_srbb_inner_to_hml \<chi>\<close>
         and \<open>\<forall>q' \<in> Q\<tau>. \<not>(q' \<Turnstile> hml_srbb_inner_to_hml \<chi>)\<close>
        have "distinguishes_from_inner \<chi> p' Q\<tau>" 
          by (simp add: distinguishes_from_inner_def distinguishes_inner_def)
  
        with \<open>Q\<tau> \<Zsurj>S Q\<tau>\<close> \<open>Q\<tau> \<noteq> {}\<close> Internal
        have "in_wina (expr_pr_inner \<chi>) (Attacker_Delayed p' Q\<tau>)" 
          by blast
  
        moreover have "expr_pr_inner \<chi> = expressiveness_price (Internal \<chi>)" by simp
        ultimately have "in_wina (expressiveness_price (Internal \<chi>)) 
            (Attacker_Delayed p' Q\<tau>)" by simp
  
        hence "in_wina (expressiveness_price (Internal \<chi>)) (Attacker_Delayed p Q\<tau>)"
        proof(induct rule: silent_reachable_loopless.induct[of "p" "p'", OF \<open>p \<Zsurj>L p'\<close>])
          case (1 p)
          thus ?case by simp
        next
          case (2 p p' p'')
          hence "in_wina (expressiveness_price (Internal \<chi>)) (Attacker_Delayed p' Q\<tau>)"
            by simp
          moreover have "spectroscopy_moves (Attacker_Delayed p Q\<tau>) (Attacker_Delayed p' Q\<tau>) 
            = Some id" using spectroscopy_moves.simps(2) \<open>p \<noteq> p'\<close> \<open>p \<mapsto>\<tau> p'\<close> by auto
          moreover have "attacker (Attacker_Delayed p Q\<tau>)" by simp
          ultimately show ?case using in_wina_Ga_with_id_step by auto
        qed
        have  "Q \<Zsurj>S Q\<tau>" 
          using Q\<tau>_def sreachable_set_is_sreachable by simp
        hence "spectroscopy_moves (Attacker_Immediate p Q) (Attacker_Delayed p Q\<tau>) = Some id"
          using spectroscopy_moves.simps(1) by simp
        with \<open>in_wina (expressiveness_price (Internal \<chi>)) (Attacker_Delayed p Q\<tau>)\<close>
        show "in_wina (expressiveness_price (Internal \<chi>)) (Attacker_Immediate p Q)" 
          using in_wina_Ga_with_id_step
          by (metis option.discI option.sel spectroscopy_defender.simps(1))
        qed

    next
      case (ImmConj I \<psi>s)
      show ?case
      proof (clarify)
        fix Q p
        assume "Q \<noteq> {}" and "distinguishes_from (ImmConj I \<psi>s) p Q"
        from this(2) have "\<forall>q\<in>Q. p \<Turnstile>SRBB ImmConj I \<psi>s \<and> \<not> q \<Turnstile>SRBB ImmConj I \<psi>s" 
          unfolding distinguishes_from_def distinguishes_def by blast
        hence "\<forall>q\<in>Q. \<exists>i\<in>I. hml_srbb_conjunct_models (\<psi>s i) p \<and> \<not>hml_srbb_conjunct_models (\<psi>s i) q"
          by simp
        hence "\<forall>q\<in>Q. \<exists>i\<in>I. distinguishes_conjunct (\<psi>s i) p q"
          using distinguishes_conjunct_def by simp
        hence "\<forall>q\<in>Q. \<exists>i\<in>I. ((\<psi>s i) \<in> range \<psi>s) \<and> distinguishes_conjunct (\<psi>s i) p q" by blast
        hence "\<forall>q\<in>Q. \<exists>i\<in>I. in_wina (expr_pr_conjunct (\<psi>s i)) (Attacker_Clause p q)" using ImmConj by blast
        hence a_clause_wina: "\<forall>q\<in>Q. \<exists>i\<in>I. in_wina (e3 (e5 (expressiveness_price (ImmConj I \<psi>s)))) 
          (Attacker_Clause p q)"
          using expressiveness_price_ImmConj_geq_parts' win_a_upwards_closure by fast
        from this \<open>Q \<noteq> {}\<close> have "I \<noteq> {}" by blast
        with expressiveness_price_ImmConj_geq_parts \<psi>_price_never_neg have
            "e5 (e3 (expressiveness_price (ImmConj I \<psi>s))) \<noteq> eneg"
          by (simp add: direct_minus_eq energy_leq_cases)
        hence "e5 (expressiveness_price (ImmConj I \<psi>s)) \<noteq> eneg"
          using leq_not_eneg minus_energy_def 
          by (metis \<open>Q \<noteq> {}\<close> a_clause_wina defender_win_level_not_in_wina
              energy.discI equals0I gets_smaller win_a_upwards_closure)
        have def_conj: "spectroscopy_defender (Defender_Conj p Q)" by simp
        have  "spectroscopy_moves (Defender_Conj p Q) N \<noteq> None 
              \<Longrightarrow> N = Attacker_Clause (attacker_state N) (defender_state N)" for N
          by (metis spectroscopy_moves.simps(34,35,36,38,64,74) spectroscopy_position.exhaust_sel)
        hence  move_kind: "spectroscopy_moves (Defender_Conj p Q) N \<noteq> None \<Longrightarrow> \<exists>q\<in>Q. N = Attacker_Clause p q" for N
          using conj_answer by metis   
        hence update: "\<And>g'. spectroscopy_moves (Defender_Conj p Q) g' \<noteq> None \<Longrightarrow> 
          weight (Defender_Conj p Q) g' = e3"
          by fastforce
        have move_wina: "\<And>g'. spectroscopy_moves (Defender_Conj p Q) g' \<noteq> None \<Longrightarrow>
          in_wina (e3 (e5 (expressiveness_price (ImmConj I \<psi>s)))) g'"
          using move_kind a_clause_wina by blast
        from in_wina_Gd[OF def_conj \<open>e5 (expressiveness_price (ImmConj I \<psi>s)) \<noteq> eneg\<close> update move_wina]
        have def_conj_wina: "in_wina (e5 (expressiveness_price (ImmConj I \<psi>s))) (Defender_Conj p Q)" by blast
  
        have imm_to_conj: "spectroscopy_moves (Attacker_Immediate p Q) (Defender_Conj p Q) \<noteq> None" 
          by (simp add: \<open>Q \<noteq> {}\<close>)
        have imm_to_conj_wgt: "weight (Attacker_Immediate p Q) (Defender_Conj p Q) = e5" 
          by (simp add: \<open>Q \<noteq> {}\<close>)
  
        from in_wina_Ga[of e5, OF def_conj_wina, of "Attacker_Immediate p Q"] imm_to_conj imm_to_conj_wgt
          show "in_wina (expressiveness_price (ImmConj I \<psi>s)) (Attacker_Immediate p Q)" by simp
      qed
    next
      case (Obs \<alpha> \<phi>)
      have "\<forall>p Q. Q \<noteq> {} \<longrightarrow> distinguishes_from_inner (hml_srbb_inner.Obs \<alpha> \<phi>) p Q \<longrightarrow> Q \<Zsurj>S Q
                \<longrightarrow> in_wina (expr_pr_inner (hml_srbb_inner.Obs \<alpha> \<phi>)) (Attacker_Delayed p Q)" 
      proof(clarify)
        fix p Q
        assume "Q \<noteq> {}" "distinguishes_from_inner (hml_srbb_inner.Obs \<alpha> \<phi>) p Q" " \<forall>p\<in>Q. \<forall>q. p \<Zsurj> q \<longrightarrow> q \<in> Q"
        have "\<exists>p' Q'. p \<mapsto>a \<alpha> p' \<and> Q \<mapsto>aS \<alpha> Q' \<and> in_wina (expressiveness_price \<phi>) (Attacker_Immediate p' Q')" 
        proof(cases "\<alpha> = \<tau>")
          case True
          with \<open>distinguishes_from_inner (hml_srbb_inner.Obs \<alpha> \<phi>) p Q\<close> have dist_unfold:
               "p \<Turnstile> Silent (hml_srbb_to_hml \<phi>) \<and> (\<forall>q\<in>Q. \<not> q \<Turnstile> Silent (hml_srbb_to_hml \<phi>))"
            unfolding True distinguishes_from_inner_def distinguishes_inner_def
            hml_srbb_inner_models.simps hml_srbb_inner_to_hml.simps hml_models.simps(4)
            by simp
          hence "((\<exists>p'. p \<mapsto>\<tau> p' \<and> p' \<Turnstile> hml_srbb_to_hml \<phi>) \<or> p \<Turnstile> hml_srbb_to_hml \<phi>)"
            unfolding True distinguishes_from_inner_def distinguishes_inner_def
            hml_srbb_inner_models.simps hml_srbb_inner_to_hml.simps hml_models.simps(4)
            by simp
          then obtain p' where "p' \<Turnstile> hml_srbb_to_hml \<phi>" "p \<mapsto>a \<alpha> p'" 
            unfolding True by blast
  
          from dist_unfold have
            "\<forall>q\<in>Q. (\<not> q \<Turnstile> hml_srbb_to_hml \<phi>) \<and> (\<nexists>q'. q \<mapsto>\<tau> q' \<and> q' \<Turnstile> hml_srbb_to_hml \<phi>)"
            by simp
          hence "\<forall>q\<in>Q. \<not>q \<Turnstile> hml_srbb_to_hml \<phi>" using \<open>\<forall>p\<in>Q. \<forall>q. p \<Zsurj> q \<longrightarrow> q \<in> Q\<close> by fastforce
  
          hence "distinguishes_from \<phi> p' Q"
            by (simp add: \<open>p' \<Turnstile> hml_srbb_to_hml \<phi>\<close> distinguishes_def distinguishes_from_def)
          with Obs have "in_wina (expressiveness_price \<phi>) (Attacker_Immediate p' Q)" 
            using \<open>Q \<noteq> {}\<close> by blast
          moreover have "Q \<mapsto>aS \<alpha> Q"
            unfolding True
            using \<open>\<forall>p\<in>Q. \<forall>q. p \<Zsurj> q \<longrightarrow> q \<in> Q\<close> silent_reachable_append_\<tau> silent_reachable.intros(1) by blast
          ultimately show ?thesis using \<open>p \<mapsto>a \<alpha> p'\<close> by blast
        next
          case False
          with \<open>distinguishes_from_inner (hml_srbb_inner.Obs \<alpha> \<phi>) p Q\<close> 
          obtain p'' where "(p \<mapsto>\<alpha> p'') \<and> (p'' \<Turnstile> (hml_srbb_to_hml \<phi>))" 
            unfolding distinguishes_from_inner_def distinguishes_inner_def
              hml_srbb_inner_models.simps hml_srbb_inner_to_hml.simps 
            using hml_models.simps \<open>Q \<noteq> {}\<close> by auto
  
          let ?Q' = "step_set Q \<alpha>"
          from \<open>distinguishes_from_inner (hml_srbb_inner.Obs \<alpha> \<phi>) p Q\<close> 
          have "\<forall>q\<in>Q. \<not> q \<Turnstile> hml.Obs \<alpha> (hml_srbb_to_hml \<phi>)" 
            unfolding distinguishes_from_inner_def distinguishes_inner_def
              hml_srbb_inner_models.simps hml_srbb_inner_to_hml.simps 
            using hml_models.simps \<open>Q \<noteq> {}\<close> by (metis (full_types))
          hence "\<forall>q\<in>?Q'. \<not> q \<Turnstile> hml_srbb_to_hml \<phi>"
            using step_set_is_step_set by fastforce
  
          from \<open>\<forall>q\<in>step_set Q \<alpha>. \<not> q \<Turnstile> hml_srbb_to_hml \<phi>\<close> \<open>p \<mapsto>\<alpha> p'' \<and> p'' \<Turnstile> hml_srbb_to_hml \<phi>\<close>
          have "distinguishes_from \<phi> p'' ?Q'"
            by (simp add: distinguishes_def distinguishes_from_def)
          hence "in_wina (expressiveness_price \<phi>) (Attacker_Immediate p'' ?Q')"
            by (metis Obs distinction_implies_winning_budgets_empty_Q)
          moreover have "p \<mapsto>\<alpha> p''" using \<open>p \<mapsto>\<alpha> p'' \<and> p'' \<Turnstile> hml_srbb_to_hml \<phi>\<close> by simp
          moreover have "Q \<mapsto>aS \<alpha> ?Q'" by (simp add: False LTS.step_set_is_step_set)
          ultimately show ?thesis by blast
        qed
        then obtain p' Q' where p'_Q': "p \<mapsto>a \<alpha> p'" "Q \<mapsto>aS \<alpha> Q'" and
          wina: "in_wina (expressiveness_price \<phi>) (Attacker_Immediate p' Q')" by blast
  
        have attacker: "attacker (Attacker_Delayed p Q)" by simp
  
        have "spectroscopy_moves (Attacker_Delayed p Q) (Attacker_Immediate p' Q') =
              (if (\<exists>a. p \<mapsto>a a p' \<and> Q \<mapsto>aS a Q') then Some e1 else None)"
          for p Q p' Q' by simp
        from this[of p Q p' Q'] have 
          "spectroscopy_moves (Attacker_Delayed p Q) (Attacker_Immediate p' Q') = 
               Some e1" using p'_Q' by auto
       
        with expr_obs_phi[of \<alpha> \<phi>] wina attacker show
          "in_wina (expr_pr_inner (hml_srbb_inner.Obs \<alpha> \<phi>)) (Attacker_Delayed p Q)"
          using in_wina_Ga by (metis option.discI option.sel)
      qed
      then show ?case by fastforce
    next
      case (Conj I \<psi>s)
      have main_case: \<open>\<forall>\<Psi>_I \<Psi> p Q. hml_srbb_inner.Conj I \<psi>s = hml_srbb_inner.Conj \<Psi>_I \<Psi> \<longrightarrow>
             Q \<noteq> {} \<longrightarrow> distinguishes_from_inner (hml_srbb_inner.Conj I \<psi>s) p Q
             \<longrightarrow> in_wina (expr_pr_inner (hml_srbb_inner.Conj I \<psi>s)) (Defender_Conj p Q)\<close>
      proof clarify
        fix p Q
        assume case_assms:
          \<open>Q \<noteq> {}\<close>
          \<open>distinguishes_from_inner (hml_srbb_inner.Conj I \<psi>s) p Q\<close>
        hence distinctions: \<open>\<forall>q\<in>Q. \<exists>i\<in>I. distinguishes_conjunct (\<psi>s i) p q\<close>
          using distinguishes_from_inner'_def distinguishes_from_inner_priming srbb_dist_conjunction_implies_dist_conjunct by auto
        hence inductive_wins: \<open>\<forall>q\<in>Q. \<exists>i\<in>I. distinguishes_conjunct (\<psi>s i) p q
            \<and> in_wina (expr_pr_conjunct (\<psi>s i)) (Attacker_Clause p q)\<close>
          using Conj by blast
        define \<psi>qs where
          \<open>\<psi>qs \<equiv> \<lambda>q. (SOME \<psi>. \<exists>i\<in>I. \<psi> = \<psi>s i \<and>  distinguishes_conjunct \<psi> p q
            \<and> in_wina (expr_pr_conjunct \<psi>) (Attacker_Clause p q))\<close>
        with inductive_wins someI have \<psi>qs_spec:
          \<open>\<forall>q\<in>Q. \<exists>i\<in>I. \<psi>qs q = \<psi>s i \<and> distinguishes_conjunct (\<psi>qs q ) p q
            \<and> in_wina (expr_pr_conjunct (\<psi>qs q)) (Attacker_Clause p q)\<close>
          by (smt (verit))
        have conjuncts_present: \<open>\<forall>q\<in>Q. expr_pr_conjunct (\<psi>qs q) \<in> expr_pr_conjunct ` (\<psi>qs ` Q)\<close>
          using \<open>Q \<noteq> {}\<close> by blast
        define e' where \<open>e' = E
          (Sup (one   ` (expr_pr_conjunct ` (\<psi>qs ` Q))))
          (Sup (two   ` (expr_pr_conjunct ` (\<psi>qs ` Q))))
          (Sup (three ` (expr_pr_conjunct ` (\<psi>qs ` Q))))
          (Sup (four  ` (expr_pr_conjunct ` (\<psi>qs ` Q))))
          (Sup (five  ` (expr_pr_conjunct ` (\<psi>qs ` Q))))
          (Sup (six   ` (expr_pr_conjunct ` (\<psi>qs ` Q))))
          (Sup (seven ` (expr_pr_conjunct ` (\<psi>qs ` Q))))
          (Sup (eight ` (expr_pr_conjunct ` (\<psi>qs ` Q))))\<close>
        from conjuncts_present have \<open>\<forall>q\<in>Q. (expr_pr_conjunct (\<psi>qs q)) \<le> e'\<close> unfolding e'_def
          by (auto, smt (verit, best) SUP_upper energy.sel energy.simps(3) energy_leq_cases image_iff)
        with \<psi>qs_spec win_a_upwards_closure have \<open>\<forall>q\<in>Q. in_wina e' (Attacker_Clause p q)\<close> by blast
        define eu' where \<open>eu' = E
          (Sup (one   ` (expr_pr_conjunct ` (\<psi>s ` I))))
          (Sup (two   ` (expr_pr_conjunct ` (\<psi>s ` I))))
          (Sup (three ` (expr_pr_conjunct ` (\<psi>s ` I))))
          (Sup (four  ` (expr_pr_conjunct ` (\<psi>s ` I))))
          (Sup (five  ` (expr_pr_conjunct ` (\<psi>s ` I))))
          (Sup (six   ` (expr_pr_conjunct ` (\<psi>s ` I))))
          (Sup (seven ` (expr_pr_conjunct ` (\<psi>s ` I))))
          (Sup (eight ` (expr_pr_conjunct ` (\<psi>s ` I))))\<close>
        have subset_form: \<open>\<psi>qs ` Q \<subseteq> \<psi>s ` I\<close>
          using \<psi>qs_spec by fastforce
        hence \<open>e' \<le> eu'\<close> unfolding e'_def eu'_def
          by (simp add: Sup_subset_mono image_mono leq_not_eneg)
        define e where \<open>e = E
          (one e')
          (two e')
          (1 + three e')
          (four e')
          (five e')
          (six e')
          (seven e')
          (eight e')\<close>
        have \<open>e' = direct_minus e (E 0 0 1 0 0 0 0 0)\<close> unfolding e_def e'_def by auto
        hence \<open>e' = e3 e\<close>
          by (auto, smt (verit) add_increasing2 direct_minus_eq e_def
            energy.distinct(1) energy.sel energy_leq_cases i0_lb le_numeral_extra(4))
        have expr_lower: \<open>(E 0 0 1 0 0 0 0 0) \<le> expr_pr_inner (Conj I \<psi>s)\<close>
          using case_assms(1) leq_not_eneg subset_form by force
        have \<open>eu' = direct_minus (expr_pr_inner (Conj I \<psi>s)) (E 0 0 1 0 0 0 0 0)\<close>
          unfolding eu'_def
          by (auto simp add: bot_enat_def) (metis (no_types, lifting) SUP_cong energy.sel image_image)+
        with expr_lower have eu'_characterization: \<open>eu' = e3 (expr_pr_inner (Conj I \<psi>s))\<close>
          using direct_minus_eq by presburger
        have \<open>\<forall>g'. spectroscopy_moves (Defender_Conj p Q) g' \<noteq> None
        \<longrightarrow> (\<exists>q\<in>Q. (Attacker_Clause p q) = g') \<and> spectroscopy_moves (Defender_Conj p Q) g' = Some e3\<close>
        proof safe
          fix g' y
          assume \<open>spectroscopy_moves (Defender_Conj p Q) g' = Some y\<close>
          thus \<open> \<exists>q\<in>Q. Attacker_Clause p q = g'\<close> \<open>spectroscopy_moves (Defender_Conj p Q) g' = Some e3\<close>
            by (induct, auto, metis option.discI option.inject)+
        qed
        hence "\<forall>g'. spectroscopy_moves (Defender_Conj p Q) g' \<noteq> None
          \<longrightarrow> in_wina ((the (spectroscopy_moves (Defender_Conj p Q) g')) e) g'"
          unfolding e_def
          using \<open>\<forall>q\<in>Q. in_wina e' (Attacker_Clause p q)\<close> \<open>e' = e3 e\<close> e_def by force
        hence \<open>in_wina e (Defender_Conj p Q)\<close>
          unfolding e_def
          by (auto simp add: in_wina.intros(3))
        moreover have \<open>e \<le> expr_pr_inner (Conj I \<psi>s)\<close>
          using \<open>e' \<le> eu'\<close> eu'_characterization \<open>e' = e3 e\<close> expr_lower case_assms(1) subset_form
          by (auto)
             (smt (z3) add_diff_cancel_enat comp_apply e'_def e_def empty_iff
               enat_add_left_cancel_le energy.distinct(1) energy.sel energy_minus idiff_0_right
               image_cong leq_not_eneg)
       ultimately show \<open>in_wina (expr_pr_inner (hml_srbb_inner.Conj I \<psi>s)) (Defender_Conj p Q)\<close>
          using win_a_upwards_closure by blast
      qed
      moreover have
        "\<forall>p Q. Q \<noteq> {} \<longrightarrow> distinguishes_from_inner (hml_srbb_inner.Conj I \<psi>s) p Q \<longrightarrow> Q \<Zsurj>S Q
             \<longrightarrow> in_wina (expr_pr_inner (hml_srbb_inner.Conj I \<psi>s)) (Attacker_Delayed p Q)"
      proof clarify
        fix p Q
        assume
          \<open>Q \<noteq> {}\<close>
          \<open>distinguishes_from_inner (hml_srbb_inner.Conj I \<psi>s) p Q\<close>
        hence \<open>in_wina (expr_pr_inner (hml_srbb_inner.Conj I \<psi>s)) (Defender_Conj p Q)\<close>
          using main_case by blast
        moreover have \<open>spectroscopy_moves (Attacker_Delayed p Q) (Defender_Conj p Q) = Some id\<close>
          by auto
        ultimately show \<open>in_wina (expr_pr_inner (hml_srbb_inner.Conj I \<psi>s)) (Attacker_Delayed p Q)\<close>
          by (metis in_wina_Ga_with_id_step option.discI option.sel spectroscopy_defender.simps(4))
      qed
      ultimately show ?case by fastforce
    next
      case (StableConj I \<psi>s)
      \<comment>\<open>The following proof is virtually the same as for (Conj I \<psi>s)\<close>
      have main_case: "(\<forall>\<Psi>_I \<Psi> p Q. StableConj I \<psi>s = StableConj \<Psi>_I \<Psi> \<longrightarrow>
             Q \<noteq> {} \<longrightarrow> distinguishes_from_inner (StableConj I \<psi>s) p Q \<longrightarrow> (\<forall>q\<in>Q. \<nexists>q'. q \<mapsto>\<tau> q')
             \<longrightarrow> in_wina (expr_pr_inner (StableConj I \<psi>s)) (Defender_Stable_Conj p Q))" 
      proof clarify
        fix p Q
        assume case_assms:
          \<open>Q \<noteq> {}\<close>
          \<open>distinguishes_from_inner (StableConj I \<psi>s) p Q\<close>
          \<open>\<forall>q\<in>Q. \<nexists>q'. q \<mapsto>\<tau> q'\<close>
        hence distinctions: \<open>\<forall>q\<in>Q. \<exists>i\<in>I. distinguishes_conjunct (\<psi>s i) p q\<close>
          using distinguishes_from_inner'_def distinguishes_from_inner_priming
           srbb_dist_stable_conjunction_implies_dist_conjunct_or_stable inverted_distinguishes
          unfolding distinguishes_hml_def by (auto, meson)
        hence inductive_wins: \<open>\<forall>q\<in>Q. \<exists>i\<in>I. distinguishes_conjunct (\<psi>s i) p q
            \<and> in_wina (expr_pr_conjunct (\<psi>s i)) (Attacker_Clause p q)\<close>
          using StableConj by blast
        define \<psi>qs where
          \<open>\<psi>qs \<equiv> \<lambda>q. (SOME \<psi>. \<exists>i\<in>I. \<psi> = \<psi>s i \<and>  distinguishes_conjunct \<psi> p q
            \<and> in_wina (expr_pr_conjunct \<psi>) (Attacker_Clause p q))\<close>
        with inductive_wins someI have \<psi>qs_spec:
          \<open>\<forall>q\<in>Q. \<exists>i\<in>I. \<psi>qs q = \<psi>s i \<and> distinguishes_conjunct (\<psi>qs q ) p q
            \<and> in_wina (expr_pr_conjunct (\<psi>qs q)) (Attacker_Clause p q)\<close>
          by (smt (verit))
        have conjuncts_present: \<open>\<forall>q\<in>Q. expr_pr_conjunct (\<psi>qs q) \<in> expr_pr_conjunct ` (\<psi>qs ` Q)\<close>
          using \<open>Q \<noteq> {}\<close> by blast
        define e' where \<open>e' = E
          (Sup (one   ` (expr_pr_conjunct ` (\<psi>qs ` Q))))
          (Sup (two   ` (expr_pr_conjunct ` (\<psi>qs ` Q))))
          (Sup (three ` (expr_pr_conjunct ` (\<psi>qs ` Q))))
          (Sup (four  ` (expr_pr_conjunct ` (\<psi>qs ` Q))))
          (Sup (five  ` (expr_pr_conjunct ` (\<psi>qs ` Q))))
          (Sup (six   ` (expr_pr_conjunct ` (\<psi>qs ` Q))))
          (Sup (seven ` (expr_pr_conjunct ` (\<psi>qs ` Q))))
          (Sup (eight ` (expr_pr_conjunct ` (\<psi>qs ` Q))))\<close>
        from conjuncts_present have \<open>\<forall>q\<in>Q. (expr_pr_conjunct (\<psi>qs q)) \<le> e'\<close> unfolding e'_def
          by (auto, smt (verit, best) SUP_upper energy.sel energy.simps(3) energy_leq_cases image_iff)
        with \<psi>qs_spec win_a_upwards_closure have \<open>\<forall>q\<in>Q. in_wina e' (Attacker_Clause p q)\<close> by blast
        define eu' where \<open>eu' = E
          (Sup (one   ` (expr_pr_conjunct ` (\<psi>s ` I))))
          (Sup (two   ` (expr_pr_conjunct ` (\<psi>s ` I))))
          (Sup (three ` (expr_pr_conjunct ` (\<psi>s ` I))))
          (Sup (four  ` (expr_pr_conjunct ` (\<psi>s ` I))))
          (Sup (five  ` (expr_pr_conjunct ` (\<psi>s ` I))))
          (Sup (six   ` (expr_pr_conjunct ` (\<psi>s ` I))))
          (Sup (seven ` (expr_pr_conjunct ` (\<psi>s ` I))))
          (Sup (eight ` (expr_pr_conjunct ` (\<psi>s ` I))))\<close>
        have subset_form: \<open>\<psi>qs ` Q \<subseteq> \<psi>s ` I\<close>
          using \<psi>qs_spec by fastforce
        hence \<open>e' \<le> eu'\<close> unfolding e'_def eu'_def
          by (simp add: Sup_subset_mono image_mono leq_not_eneg)
        define e where \<open>e = E
          (one e')
          (two e')
          (three e')
          (1 + four e')
          (five e')
          (six e')
          (seven e')
          (eight e')\<close>
        have \<open>e' = direct_minus e (E 0 0 0 1 0 0 0 0)\<close> unfolding e_def e'_def by auto
        hence \<open>e' = (subtract_fn 0 0 0 1 0 0 0 0) e\<close>
          by (auto, smt (verit) add_increasing2 direct_minus_eq e_def
            energy.distinct(1) energy.sel energy_leq_cases i0_lb le_numeral_extra(4))
        have expr_lower: \<open>(E 0 0 0 1 0 0 0 0) \<le> expr_pr_inner (StableConj I \<psi>s)\<close>
          using case_assms(1) leq_not_eneg subset_form by force
        have \<open>eu' = direct_minus (expr_pr_inner (StableConj I \<psi>s)) (E 0 0 0 1 0 0 0 0)\<close>
          unfolding eu'_def
          by (auto simp add: bot_enat_def) (metis (no_types, lifting) SUP_cong energy.sel image_image)+
        with expr_lower have eu'_characterization: \<open>eu' = (subtract_fn 0 0 0 1 0 0 0 0) (expr_pr_inner (StableConj I \<psi>s))\<close>
          using direct_minus_eq by presburger
        have \<open>\<forall>g'. spectroscopy_moves (Defender_Stable_Conj p Q) g' \<noteq> None
        \<longrightarrow> (\<exists>q\<in>Q. (Attacker_Clause p q) = g') \<and> spectroscopy_moves (Defender_Stable_Conj p Q) g' = (subtract 0 0 0 1 0 0 0 0)\<close>
        proof safe
          fix g' y
          assume \<open>spectroscopy_moves (Defender_Stable_Conj p Q) g' = Some y\<close>
          thus \<open> \<exists>q\<in>Q. Attacker_Clause p q = g'\<close>
            \<open>spectroscopy_moves (Defender_Stable_Conj p Q) g' = (subtract 0 0 0 1 0 0 0 0)\<close>
            using \<open>Q \<noteq> {}\<close>
            by (induct, auto) (metis option.discI option.inject)+
        qed
        hence "\<forall>g'. spectroscopy_moves (Defender_Stable_Conj p Q) g' \<noteq> None
          \<longrightarrow> in_wina ((the (spectroscopy_moves (Defender_Stable_Conj p Q) g')) e) g'"
          unfolding e_def
          using \<open>\<forall>q\<in>Q. in_wina e' (Attacker_Clause p q)\<close> \<open>e' = (subtract_fn 0 0 0 1 0 0 0 0) e\<close> e_def by force
        hence \<open>in_wina e (Defender_Stable_Conj p Q)\<close>
          unfolding e_def
          by (auto simp add: in_wina.intros(3))
        moreover have \<open>e \<le> expr_pr_inner (StableConj I \<psi>s)\<close>
          using \<open>e' \<le> eu'\<close> eu'_characterization \<open>e' = (subtract_fn 0 0 0 1 0 0 0 0) e\<close> expr_lower case_assms(1) subset_form
          by (auto)
             (smt (z3) add_diff_cancel_enat comp_apply e'_def e_def empty_iff
               enat_add_left_cancel_le energy.distinct(1) energy.sel energy_minus idiff_0_right
               image_cong leq_not_eneg)
       ultimately show \<open>in_wina (expr_pr_inner (StableConj I \<psi>s)) (Defender_Stable_Conj p Q)\<close>
          using win_a_upwards_closure by blast
      qed
      moreover have
        "(\<forall>p Q. Q \<noteq> {} \<longrightarrow> distinguishes_from_inner (StableConj I \<psi>s) p Q \<longrightarrow> Q \<Zsurj>S Q
           \<longrightarrow> in_wina (expr_pr_inner (StableConj I \<psi>s)) (Attacker_Delayed p Q))"
      proof clarify
        \<comment> \<open>This is where things are more complicated than in the Conj-case. (We have to differentiate
            situations where the stability requirement finishes the distinction.)\<close>
        fix p Q
        assume case_assms:
          "Q \<noteq> {}"
          "distinguishes_from_inner (StableConj I \<psi>s) p Q"
          "\<forall>q'\<in>Q. \<exists>q\<in>Q. q \<Zsurj> q'"
          "\<forall>q\<in>Q. \<forall>q'. q \<Zsurj> q' \<longrightarrow> q' \<in> Q"
        define Q' where \<open>Q' = { q \<in> Q. (\<nexists>q'. q \<mapsto>\<tau> q')}\<close>
        with case_assms(2) have Q'_spec: \<open>distinguishes_from_inner (StableConj I \<psi>s) p Q'\<close> \<open>\<nexists>p''. p \<mapsto>\<tau> p''\<close>
          unfolding distinguishes_from_inner_def by auto
        hence move: \<open>spectroscopy_moves (Attacker_Delayed p Q) (Defender_Stable_Conj p Q') = Some id\<close>
          unfolding Q'_def by auto
        show \<open>in_wina (expr_pr_inner (StableConj I \<psi>s)) (Attacker_Delayed p Q)\<close>
        proof (cases \<open>Q' = {}\<close>)
          case True
          hence
            \<open>spectroscopy_moves (Defender_Stable_Conj p Q') (Defender_Conj p {})
            = (subtract 0 0 0 1 0 0 0 0)\<close> by auto
          moreover have
            \<open>\<forall>g'. spectroscopy_moves (Defender_Stable_Conj p Q') g' \<noteq> None \<longrightarrow> g' = (Defender_Conj p {})\<close>
          proof clarify
            fix g' u
            assume
              \<open>spectroscopy_moves (Defender_Stable_Conj p Q') g' = Some u\<close>
            with True show \<open>g' = Defender_Conj p {}\<close>
              by (induct g', auto, metis option.discI, metis empty_iff option.discI)
          qed
          ultimately have win_transfer:
            \<open>\<forall>e. in_wina ((subtract_fn 0 0 0 1 0 0 0 0) e) (Defender_Conj p {}) \<longrightarrow> in_wina e (Defender_Stable_Conj p Q')\<close>
            using gets_smaller win_a_upwards_closure 
            by (metis energy.distinct(1) in_wina.cases in_wina.intros(3) option.sel spectroscopy_defender.simps(7))
          have \<open>\<forall>g'. spectroscopy_moves (Defender_Conj p {}) g' = None\<close>
          proof
            fix g'
            show \<open>spectroscopy_moves (Defender_Conj p {}) g' = None\<close> by (induct g', auto)
          qed
          hence \<open>\<forall>e. e \<noteq> eneg \<longrightarrow> in_wina e (Defender_Conj p {})\<close> using in_wina_Gd by fastforce
          moreover have \<open>\<forall>e. (subtract_fn 0 0 0 1 0 0 0 0) e \<noteq> eneg \<longrightarrow> e \<ge> (E 0 0 0 1 0 0 0 0)\<close>
            using minus_energy_def by presburger
          ultimately have \<open>\<forall>e. e \<ge> (E 0 0 0 1 0 0 0 0) \<longrightarrow> in_wina e (Defender_Stable_Conj p Q')\<close>
            using win_transfer
            using direct_minus_eq energy.distinct(1) by presburger
          moreover have \<open>expr_pr_inner (StableConj I \<psi>s) \<ge> (E 0 0 0 1 0 0 0 0)\<close>
            by (auto simp add: leq_not_eneg)
          ultimately show ?thesis
            by (metis move in_wina_Ga_with_id_step option.discI option.sel spectroscopy_defender.simps(4))
        next
          case False
          then show ?thesis using main_case Q'_spec Q'_def in_wina_Ga_with_id_step
            by (auto, metis (mono_tags, lifting) False mem_Collect_eq move option.sel
                spectroscopy_defender.simps(4))
        qed
      qed
      ultimately show ?case by blast
    next
      case (BranchConj \<alpha> \<phi> I \<psi>s)
      have main_case:
        "\<forall>p Q p' Q_\<alpha>.
             distinguishes_from_inner (BranchConj \<alpha> \<phi> I \<psi>s) p Q \<longrightarrow> p \<mapsto>a \<alpha> p' \<longrightarrow> p' \<Turnstile>SRBB \<phi> \<longrightarrow>
             Q_\<alpha> = Q - model_set_inner (Obs \<alpha> \<phi>)
             \<longrightarrow> in_wina (expr_pr_inner (BranchConj \<alpha> \<phi> I \<psi>s)) (Defender_Branch p \<alpha> p' (Q - Q_\<alpha>) Q_\<alpha>)"
      proof ((rule allI)+, (rule impI)+)
        fix p Q p' Q_\<alpha>
        assume case_assms:
          \<open>distinguishes_from_inner (BranchConj \<alpha> \<phi> I \<psi>s) p Q\<close>
          \<open>p \<mapsto>a \<alpha> p'\<close>
          \<open>p' \<Turnstile>SRBB \<phi>\<close>
          \<open>Q_\<alpha> = Q - model_set_inner (Obs \<alpha> \<phi>)\<close>
        from case_assms(1) have distinctions: \<open>\<forall>q\<in>(Q \<inter> model_set_inner (Obs \<alpha> \<phi>)). \<exists>i\<in>I. distinguishes_conjunct (\<psi>s i) p q\<close>
          using distinguishes_from_inner'_def distinguishes_from_inner_priming
            inverted_distinguishes srbb_dist_branch_conjunction_implies_dist_conjunct_or_branch
            dist_inner_srbb_eq_dist_hml distinguishes_hml_def distinguishes_inner_def
          by (smt (verit) Int_Collect)
        hence inductive_wins: \<open>\<forall>q\<in>(Q \<inter> model_set_inner (Obs \<alpha> \<phi>)). \<exists>i\<in>I. distinguishes_conjunct (\<psi>s i) p q
            \<and> in_wina (expr_pr_conjunct (\<psi>s i)) (Attacker_Clause p q)\<close>
          using BranchConj by blast
        define \<psi>qs where
          \<open>\<psi>qs \<equiv> \<lambda>q. (SOME \<psi>. \<exists>i\<in>I. \<psi> = \<psi>s i \<and>  distinguishes_conjunct \<psi> p q
            \<and> in_wina (expr_pr_conjunct \<psi>) (Attacker_Clause p q))\<close>
        with inductive_wins someI have \<psi>qs_spec:
          \<open>\<forall>q\<in>(Q \<inter> model_set_inner (Obs \<alpha> \<phi>)). \<exists>i\<in>I. \<psi>qs q = \<psi>s i \<and> distinguishes_conjunct (\<psi>qs q ) p q
            \<and> in_wina (expr_pr_conjunct (\<psi>qs q)) (Attacker_Clause p q)\<close>
          by (smt (verit))
        have conjuncts_present:
          \<open>\<forall>q\<in>(Q \<inter> model_set_inner (Obs \<alpha> \<phi>)). expr_pr_conjunct (\<psi>qs q)
            \<in> expr_pr_conjunct ` (\<psi>qs ` (Q \<inter> model_set_inner (Obs \<alpha> \<phi>)))\<close>
          by blast
        define e'0 where \<open>e'0 = E
          (Sup (one   ` (expr_pr_conjunct ` (\<psi>qs ` (Q \<inter> model_set_inner (Obs \<alpha> \<phi>))))))
          (Sup (two   ` (expr_pr_conjunct ` (\<psi>qs ` (Q \<inter> model_set_inner (Obs \<alpha> \<phi>))))))
          (Sup (three ` (expr_pr_conjunct ` (\<psi>qs ` (Q \<inter> model_set_inner (Obs \<alpha> \<phi>))))))
          (Sup (four  ` (expr_pr_conjunct ` (\<psi>qs ` (Q \<inter> model_set_inner (Obs \<alpha> \<phi>))))))
          (Sup (five  ` (expr_pr_conjunct ` (\<psi>qs ` (Q \<inter> model_set_inner (Obs \<alpha> \<phi>))))))
          (Sup (six   ` (expr_pr_conjunct ` (\<psi>qs ` (Q \<inter> model_set_inner (Obs \<alpha> \<phi>))))))
          (Sup (seven ` (expr_pr_conjunct ` (\<psi>qs ` (Q \<inter> model_set_inner (Obs \<alpha> \<phi>))))))
          (Sup (eight ` (expr_pr_conjunct ` (\<psi>qs ` (Q \<inter> model_set_inner (Obs \<alpha> \<phi>))))))\<close>
        from conjuncts_present have branch_answer_bound:
            \<open>\<forall>q\<in>(Q \<inter> model_set_inner (Obs \<alpha> \<phi>)). (expr_pr_conjunct (\<psi>qs q)) \<le> e'0\<close>
          unfolding e'0_def using SUP_upper energy.sel energy.simps(3) energy_leq_cases image_iff
          by (smt (z3))
        with \<psi>qs_spec win_a_upwards_closure have
          conj_wins: \<open>\<forall>q\<in>(Q \<inter> model_set_inner (Obs \<alpha> \<phi>)). in_wina e'0 (Attacker_Clause p q)\<close> by blast
        define eu'0 where \<open>eu'0 = E
          (Sup (one   ` (expr_pr_conjunct ` (\<psi>s ` I))))
          (Sup (two   ` (expr_pr_conjunct ` (\<psi>s ` I))))
          (Sup (three ` (expr_pr_conjunct ` (\<psi>s ` I))))
          (Sup (four  ` (expr_pr_conjunct ` (\<psi>s ` I))))
          (Sup (five  ` (expr_pr_conjunct ` (\<psi>s ` I))))
          (Sup (six   ` (expr_pr_conjunct ` (\<psi>s ` I))))
          (Sup (seven ` (expr_pr_conjunct ` (\<psi>s ` I))))
          (Sup (eight ` (expr_pr_conjunct ` (\<psi>s ` I))))\<close>
        have subset_form: \<open>\<psi>qs ` (Q \<inter> model_set_inner (Obs \<alpha> \<phi>)) \<subseteq> \<psi>s ` I\<close>
          using \<psi>qs_spec by fastforce
        hence \<open>e'0 \<le> eu'0\<close> unfolding e'0_def eu'0_def
          by (metis (mono_tags, lifting) Sup_subset_mono energy.distinct(1) energy.sel image_mono leq_not_eneg)

        have no_q_way: \<open>\<forall>q\<in>Q_\<alpha>. \<nexists>q'. q \<mapsto> \<alpha> q' \<and> hml_srbb_models q' \<phi>\<close>
          using case_assms(4)
          by fastforce
        define Q' where \<open>Q' \<equiv> (soft_step_set Q_\<alpha> \<alpha>)\<close>
        hence \<open>distinguishes_from \<phi> p' Q'\<close>
          using case_assms(2,3) no_q_way soft_step_set_is_soft_step_set mem_Collect_eq opt_\<tau>_is_or
          unfolding distinguishes_from_inner_def distinguishes_from_def case_assms(4)
          by (metis DiffD2 hml_srbb_inner_models.elims(3) hml_srbb_inner_to_hml.simps(1) hml_srbb_models.elims(2))
        with BranchConj have win_a_branch: \<open>in_wina (expressiveness_price \<phi>) (Attacker_Immediate p' Q')\<close>
          using distinction_implies_winning_budgets_empty_Q by (cases \<open>Q' = {}\<close>) auto
        have \<open>expr_pr_inner (Obs \<alpha> \<phi>) \<ge> (E 1 0 0 0 0 0 0 0)\<close> using leq_not_eneg by auto
        hence \<open>e1 (expr_pr_inner (Obs \<alpha> \<phi>)) = expressiveness_price \<phi>\<close>
          using expr_obs_phi by auto
        with win_a_branch have win_a_step:
          \<open>in_wina (e1 (expr_pr_inner (Obs \<alpha> \<phi>))) (Attacker_Immediate p' Q')\<close> by auto

        define e' where \<open>e' = E
          (Sup (one   ` ({expr_pr_inner (Obs \<alpha> \<phi>)} \<union> (expr_pr_conjunct ` (\<psi>s ` I)))))
          (Sup (two   ` ({expr_pr_inner (Obs \<alpha> \<phi>)} \<union> (expr_pr_conjunct ` (\<psi>s ` I)))))
          (Sup (three ` ({expr_pr_inner (Obs \<alpha> \<phi>)} \<union> (expr_pr_conjunct ` (\<psi>s ` I)))))
          (Sup (four  ` ({expr_pr_inner (Obs \<alpha> \<phi>)} \<union> (expr_pr_conjunct ` (\<psi>s ` I)))))
          (Sup (five  ` ({expr_pr_inner (Obs \<alpha> \<phi>)} \<union> (expr_pr_conjunct ` (\<psi>s ` I)))))
          (Sup ({1 + modal_depth_srbb \<phi>} 
             \<union> (six   ` ({expr_pr_inner (Obs \<alpha> \<phi>)} \<union> (expr_pr_conjunct ` (\<psi>s ` I))))))
          (Sup (seven ` ({expr_pr_inner (Obs \<alpha> \<phi>)} \<union> (expr_pr_conjunct ` (\<psi>s ` I)))))
          (Sup (eight ` ({expr_pr_inner (Obs \<alpha> \<phi>)} \<union> (expr_pr_conjunct ` (\<psi>s ` I)))))\<close>
        have \<open>eu'0 \<le> e'\<close> unfolding e'_def eu'0_def
          using leq_not_eneg
          by (auto, meson sup.cobounded2 sup.coboundedI2)

        have \<open>spectroscopy_moves (Attacker_Branch p' Q') (Attacker_Immediate p' Q') = Some e1\<close> by simp
        with win_a_step in_wina_Ga have \<open>in_wina (expr_pr_inner (Obs \<alpha> \<phi>)) (Attacker_Branch p' Q')\<close>
          by (metis option.distinct(1) option.sel spectroscopy_defender.simps(2))
        hence e'_win: \<open>in_wina e' (Attacker_Branch p' Q')\<close> 
          unfolding  e'_def
          using win_a_upwards_closure
          by (auto simp add: leq_not_eneg)
        have depths: \<open>1 + modal_depth_srbb \<phi> = one (expr_pr_inner (Obs \<alpha> \<phi>))\<close> by simp
        have \<open>e' \<noteq> eneg\<close>
          using e'_def by force
        have obs_win: \<open>in_wina (min1_6 e') (Attacker_Branch p' Q')\<close> sorry

        define e where \<open>e = E
          (one e')
          (1 + two e')
          (1 + three e')
          (four e')
          (five e')
          (six e')
          (seven e')
          (eight e')\<close>
        have \<open>e' = direct_minus e (E 0 1 1 0 0 0 0 0)\<close> unfolding e_def e'_def by auto
        hence \<open>e' = (subtract_fn 0 1 1 0 0 0 0 0) e\<close>
          by (auto, smt (verit) add_increasing2 direct_minus_eq e_def
            energy.distinct(1) energy.sel energy_leq_cases i0_lb le_numeral_extra(4))
        have expr_lower: \<open>(E 0 1 1 0 0 0 0 0) \<le> expr_pr_inner (BranchConj \<alpha> \<phi> I \<psi>s)\<close>
          using case_assms leq_not_eneg subset_form by auto
        have e'_minus: \<open>e' = direct_minus (expr_pr_inner (BranchConj \<alpha> \<phi> I \<psi>s)) (E 0 1 1 0 0 0 0 0)\<close>
          unfolding e'_def 
          by (auto simp add: bot_enat_def sup.left_commute)
             (metis (no_types, lifting) SUP_cong energy.sel image_image)+

        with expr_lower have e'_characterization:
            \<open>e' = (subtract_fn 0 1 1 0 0 0 0 0) (expr_pr_inner (BranchConj \<alpha> \<phi> I \<psi>s))\<close>
          using direct_minus_eq by presburger

        have moves: \<open>\<forall>g'. spectroscopy_moves (Defender_Branch p \<alpha> p' (Q - Q_\<alpha>) Q_\<alpha>) g' \<noteq> None
        \<longrightarrow> (((Attacker_Branch p' Q' = g')
            \<and> (spectroscopy_moves (Defender_Branch p \<alpha> p' (Q - Q_\<alpha>) Q_\<alpha>) g' = Some (min1_6 \<circ> (\<lambda>x. x - E 0 1 1 0 0 0 0 0))))
          \<or> ((\<exists>q\<in>(Q - Q_\<alpha>). Attacker_Clause p q = g'
            \<and> spectroscopy_moves (Defender_Branch p \<alpha> p' (Q - Q_\<alpha>) Q_\<alpha>) g' = (subtract 0 1 1 0 0 0 0 0))))\<close>
        proof clarify
          fix g' u
          assume
            \<open>spectroscopy_moves (Defender_Branch p \<alpha> p' (Q - Q_\<alpha>) Q_\<alpha>) g' = Some u\<close>
            \<open>\<not> (\<exists>q\<in>Q - Q_\<alpha>. Attacker_Clause p q = g' \<and> spectroscopy_moves (Defender_Branch p \<alpha> p' (Q - Q_\<alpha>) Q_\<alpha>) g' = subtract 0 1 1 0 0 0 0 0)\<close>
          thus \<open>Attacker_Branch p' Q' = g' \<and> spectroscopy_moves (Defender_Branch p \<alpha> p' (Q - Q_\<alpha>) Q_\<alpha>) g' = Some (min1_6 \<circ> subtract_fn 0 1 1 0 0 0 0 0)\<close>
            unfolding Q'_def using soft_step_set_is_soft_step_set
            by (induct g', auto) (metis option.discI option.inject)+
        qed

        have Q_subsets: \<open>Q - Q_\<alpha> \<subseteq> Q \<inter> model_set_inner (Obs \<alpha> \<phi>)\<close> using case_assms(4) by blast

        have obs_e: \<open>in_wina ((min1_6 \<circ> (\<lambda>x. x - E 0 1 1 0 0 0 0 0)) e) (Attacker_Branch p' Q')\<close>
          using obs_win \<open>e' = subtract_fn 0 1 1 0 0 0 0 0 e\<close> by force
        have \<open>\<forall>q\<in>(Q - Q_\<alpha>). spectroscopy_moves (Defender_Branch p \<alpha> p' (Q - Q_\<alpha>) Q_\<alpha>) (Attacker_Clause p q) = (subtract 0 1 1 0 0 0 0 0)
          \<longrightarrow> in_wina e'0 (Attacker_Clause p q)\<close>
          using conj_wins \<open>eu'0 \<le> e'\<close> Q_subsets by blast
        with obs_e moves have move_wins: "\<forall>g'. spectroscopy_moves (Defender_Branch p \<alpha> p' (Q - Q_\<alpha>) Q_\<alpha>) g' \<noteq> None
          \<longrightarrow> in_wina ((the (spectroscopy_moves (Defender_Branch p \<alpha> p' (Q - Q_\<alpha>) Q_\<alpha>) g')) e) g'"
          using  \<open>eu'0 \<le> e'\<close> \<open>e' = subtract_fn 0 1 1 0 0 0 0 0 e\<close> \<open>e'0 \<le> eu'0\<close> win_a_upwards_closure
          by (smt (verit, ccfv_SIG) option.sel)
        moreover have \<open>expr_pr_inner (BranchConj \<alpha> \<phi> I \<psi>s) = e\<close>
          using e'_characterization e'_minus unfolding e_def by force
        ultimately show \<open>in_wina (expr_pr_inner (BranchConj \<alpha> \<phi> I \<psi>s)) (Defender_Branch p \<alpha> p' (Q - Q_\<alpha>) Q_\<alpha>)\<close>
        using \<chi>_price_never_neg in_wina.intros(3) spectroscopy_defender.simps(5)
          by metis
      qed 
      moreover have
        "\<forall>p Q. Q \<noteq> {} \<longrightarrow> distinguishes_from_inner (BranchConj \<alpha> \<phi> I \<psi>s) p Q \<longrightarrow> Q \<Zsurj>S Q
             \<longrightarrow> in_wina (expr_pr_inner (BranchConj \<alpha> \<phi> I \<psi>s)) (Attacker_Delayed p Q)"
      proof clarify
        fix p Q
        assume case_assms:
          \<open>distinguishes_from_inner (BranchConj \<alpha> \<phi> I \<psi>s) p Q\<close>
          \<open>\<forall>q'\<in>Q. \<exists>q\<in>Q. q \<Zsurj> q'\<close>
          \<open>\<forall>p\<in>Q. \<forall>q. p \<Zsurj> q \<longrightarrow> q \<in> Q\<close>
        from case_assms(1) obtain p' where p'_spec: \<open>p \<mapsto>a \<alpha> p'\<close> \<open>p' \<Turnstile>SRBB \<phi>\<close> 
          unfolding distinguishes_from_inner_def
              and distinguishes_def
          using soft_poss_to_or hml_models.simps(2) by (auto) (blast)
        define Q_\<alpha> where \<open>Q_\<alpha> = Q - model_set_inner (hml_srbb_inner.Obs \<alpha> \<phi>)\<close>
        have \<open>in_wina (expr_pr_inner (BranchConj \<alpha> \<phi> I \<psi>s)) (Defender_Branch p \<alpha> p' (Q - Q_\<alpha>) Q_\<alpha>)\<close>
          using main_case case_assms(1) p'_spec Q_\<alpha>_def by blast
        moreover have \<open>spectroscopy_moves (Attacker_Delayed p Q) (Defender_Branch p \<alpha> p' (Q - Q_\<alpha>) Q_\<alpha>) = Some id\<close>
          using p'_spec Q_\<alpha>_def by auto
        ultimately show \<open>in_wina (expr_pr_inner (BranchConj \<alpha> \<phi> I \<psi>s)) (Attacker_Delayed p Q)\<close>
          using in_wina_Ga_with_id_step by auto
      qed
      ultimately show ?case by blast
    next
      case (Pos \<chi>)
      then show ?case sorry
    next
      case (Neg \<chi>)
      then show ?case sorry
    qed
  qed
  thus ?thesis
    by (metis assms distinction_implies_winning_budgets_empty_Q)
qed

end (* context full_spec_game *)

end