theory Spectroscopy_Game
  imports Energy_Games Energy LTS HML_SRBB
begin

text \<open>In this theory the full spectroscopy game is defined (as a locale). 
The definition corresponds to definition 16 in the paper. (Definition 16 is an extension of 
definition 14, which extends definition 12, which is a energy game depending on a LTS. We omit these 
steps and give a definition directly.) 

The full spectroscopy game is an energy game that can be constructed by adding stable and branching 
conjunctions to a delay bisimulation game, which is  depending on a LTS. In the following we 
differentiate the positions accordingly:\<close>

datatype ('s, 'a) spectroscopy_position = 
                          Attacker_Immediate (attacker_state: "'s") (defender_states: "'s set") |
                          Attacker_Branch (attacker_state: "'s") (defender_states: "'s set") |
                          Attacker_Clause (attacker_state: "'s") (defender_state: "'s") |
                          Attacker_Delayed (attacker_state: "'s") (defender_states: "'s set") |

                          Defender_Branch (attacker_state: "'s") (attack_action: "'a") (attacker_state_succ: "'s") (defender_states: "'s set") (defender_branch_states: "'s set") |
                          Defender_Conj (attacker_state: "'s") (defender_states: "'s set") |
                          Defender_Stable_Conj (attacker_state: "'s") (defender_states: "'s set")

context Inhabited_Tau_LTS begin

text \<open>Now we define the moves in a full spectroscopy game depending on a LTS:\<close>
fun spectroscopy_moves :: "('s, 'a) spectroscopy_position \<Rightarrow> ('s, 'a) spectroscopy_position \<Rightarrow> energy update option" where 
  delay: 
    "spectroscopy_moves (Attacker_Immediate p Q) (Attacker_Delayed p' Q') 
     = (if p' = p \<and> Q \<Zsurj>S Q' then Some id else None)" |

  procrastination: 
    "spectroscopy_moves (Attacker_Delayed p Q) (Attacker_Delayed p' Q')     
      = (if (Q' = Q \<and> p \<noteq> p' \<and> p \<mapsto> \<tau> p') then Some id else None)" |

  observation: 
    "spectroscopy_moves (Attacker_Delayed p Q) (Attacker_Immediate p' Q') 
      = (if (\<exists>a. p \<mapsto> a p' \<and> Q \<mapsto>S a Q' \<and> a \<noteq> \<tau>) then (subtract 1 0 0 0 0 0 0 0) else None)" |

  finishing_or_early_conj: 
    "spectroscopy_moves (Attacker_Immediate p Q) (Defender_Conj p' Q') 
      = (if Q = {} \<and> Q' = {} then 
          (if (p = p') then Some id else None) 
         else 
          (if (Q = Q' \<and> p = p') then (subtract 0 0 0 0 1 0 0 0) else None))" |

  late_inst_conj: 
    "spectroscopy_moves (Attacker_Delayed p Q) (Defender_Conj p' Q') 
      = (if p = p' \<and> Q = Q' then Some id else None)" |

  conj_answer: 
    "spectroscopy_moves (Defender_Conj p Q) (Attacker_Clause p' q) 
      = (if p = p' \<and> q \<in> Q then (subtract 0 0 1 0 0 0 0 0) else None)" |
  
  pos_neg_clause: 
    "spectroscopy_moves (Attacker_Clause p q) (Attacker_Delayed p' Q') 
      = (if (p = p') then 
          (if {q} \<Zsurj>S Q' then Some min1_6 else None) 
         else (if ({p} \<Zsurj>S Q'\<and> q=p')then Some (min1_7 \<circ> (\<lambda>x. x- E 0 0 0 0 0 0 0 1)) else None))" |

  late_stbl_conj: 
    "spectroscopy_moves (Attacker_Delayed p Q) (Defender_Stable_Conj p' Q') 
      = (if (p = p' \<and> Q' = { q \<in> Q. (\<nexists>q'. q \<mapsto>\<tau> q')} \<and> (\<nexists>p''. p \<mapsto>\<tau> p'')) then Some id else None)" |

  conj_s_answer: 
    "spectroscopy_moves (Defender_Stable_Conj p Q) (Attacker_Clause p' q) 
      = (if p = p' \<and> q \<in> Q then (subtract 0 0 0 1 0 0 0 0) else None)" |

  empty_stbl_conj_answer: "spectroscopy_moves (Defender_Stable_Conj p Q) (Defender_Conj p' Q') 
      = (if Q = {} \<and> Q = Q' \<and> p = p' then (subtract 0 0 0 1 0 0 0 0) else None)" |

  br_conj: 
    "spectroscopy_moves (Attacker_Delayed p Q) (Defender_Branch p' \<alpha> p'' Q' Q\<alpha>) 
      = (if (p = p' \<and> Q' = Q - Q\<alpha> \<and> p \<mapsto>\<alpha> p'' \<and> Q\<alpha> \<noteq> {} \<and> Q\<alpha> \<subseteq> Q)then Some id else None)" |

  br_answer: 
    "spectroscopy_moves (Defender_Branch p \<alpha> p' Q Q\<alpha>) (Attacker_Clause p'' q) 
      = (if (p = p'' \<and> q \<in> Q) then (subtract 0 1 1 0 0 0 0 0) else None)" |

  br_obsv: 
    "spectroscopy_moves (Defender_Branch p \<alpha> p' Q Q\<alpha>) (Attacker_Branch p'' Q') 
      = (if (p' = p'' \<and> Q\<alpha> \<mapsto>aS \<alpha> Q') then Some (min1_6 \<circ> (\<lambda>x. x- E 0 1 1 0 0 0 0 0)) else None)" |

  br_acct: 
    "spectroscopy_moves (Attacker_Branch p Q) (Attacker_Immediate p' Q') 
      = (if p = p' \<and> Q = Q' then subtract 1 0 0 0 0 0 0 0 else None)" |

  others: "spectroscopy_moves _ _ = None"

text \<open>The definition of defender positions in a full spectroscopy game is implicitly given by the 
possible positions. Now we make them explicit:\<close>
fun spectroscopy_defender where
  "spectroscopy_defender (Attacker_Immediate _ _) = False" |
  "spectroscopy_defender (Attacker_Branch _ _) = False" |
  "spectroscopy_defender (Attacker_Clause _ _) = False" |
  "spectroscopy_defender (Attacker_Delayed _ _) = False" |
  "spectroscopy_defender (Defender_Branch _ _ _ _ _) = True" |
  "spectroscopy_defender (Defender_Conj _ _) = True" |
  "spectroscopy_defender (Defender_Stable_Conj _ _) = True"

text \<open>To check whether these definitions are compatible with our definition of energy games we proof 
an interpretation. To do so we first provide lemmas showing monotonicity of updates and that updates 
only decline.\<close>

lemma update_monotonicity: 
  fixes g g' e e'
  assumes "(spectroscopy_moves g g') \<noteq> None" and "(e \<le> e')"
  shows "((the (spectroscopy_moves g g')e) \<le> (the (spectroscopy_moves g g')e'))"
using assms proof (cases g)
  case (Attacker_Immediate x11 x12)
  then have "(\<exists>p' Q'. g'=(Attacker_Delayed p' Q')) \<or> (\<exists> p' Q'. g'= (Defender_Conj p' Q'))" using assms
    using spectroscopy_defender.elims(2) spectroscopy_defender.elims(3) spectroscopy_moves.simps(45) spectroscopy_moves.simps(50) spectroscopy_moves.simps(56) spectroscopy_moves.simps(60) spectroscopy_moves.simps(71)
    by (metis spectroscopy_moves.simps(70))

  then consider (A_Delayed) "(\<exists>p' Q'. g'=(Attacker_Delayed p' Q'))" | (D_Conj) "(\<exists> p' Q'. g'= (Defender_Conj p' Q'))" by auto
  then show ?thesis proof (cases)
    case A_Delayed (*delay*)
    then have "spectroscopy_moves g g' = Some id"
      using Attacker_Immediate assms(1) local.delay
      by (smt (verit, best))
      
    then show ?thesis using assms(2) by simp
  next
    case D_Conj (*finishing_or_early_conj*)
    then have "spectroscopy_moves g g' = Some id \<or> spectroscopy_moves g g' = (subtract 0 0 0 0 1 0 0 0)" using assms(1)
      by (metis Attacker_Immediate local.finishing_or_early_conj)
    then show ?thesis using assms(2) gets_smaller
      using mono_subtract option.sel by auto
  qed
next
  case (Attacker_Branch x21 x22) (*br_acct*)
  then have "\<exists>p' Q'. g'= (Attacker_Immediate p' Q')" using assms(1) spectroscopy_moves.simps
    by (metis (no_types, lifting) spectroscopy_defender.elims(2) spectroscopy_defender.elims(3))
  then have "spectroscopy_moves g g' = subtract 1 0 0 0 0 0 0 0"
    by (metis Attacker_Branch assms(1) local.br_acct) 
  then show ?thesis using assms(2) mono_subtract by simp
next
  case (Attacker_Clause x31 x32) (*pos_neg_clause *)
  then have "\<exists>p' Q'. g'= (Attacker_Delayed p' Q')" using assms(1) spectroscopy_moves.simps
    by (metis (no_types, lifting) spectroscopy_defender.elims(2) spectroscopy_defender.elims(3))
  then have "spectroscopy_moves g g' = Some min1_6 \<or> spectroscopy_moves g g' = Some (min1_7 \<circ> (\<lambda>x. x- E 0 0 0 0 0 0 0 1))" using assms(1)
    by (smt (verit) Attacker_Clause local.pos_neg_clause)
  then show ?thesis using assms(2) mono_min_1_6 mono_min_1_7 mono_subtract
    by (metis (no_types, lifting) comp_apply monoE option.sel) 
next
  case (Attacker_Delayed x41 x42)
  then have "(\<exists>p' Q'. g'=(Attacker_Delayed p' Q')) \<or> (\<exists>p' Q'. g'=(Attacker_Immediate p' Q')) \<or> (\<exists>p' Q'. g'=(Defender_Conj p' Q')) \<or> (\<exists>p' Q'. g'=(Defender_Stable_Conj p' Q')) \<or> (\<exists>p' p'' Q' \<alpha> Q\<alpha> . g'= (Defender_Branch p' \<alpha> p'' Q' Q\<alpha>))"
    using assms spectroscopy_defender.cases spectroscopy_moves.simps(26) spectroscopy_moves.simps(27)
    by (metis spectroscopy_moves.simps(59))

  then consider (A_Delayed) "(\<exists>p' Q'. g'=(Attacker_Delayed p' Q'))" | (A_Immediate) "(\<exists>p' Q'. g'=(Attacker_Immediate p' Q'))" | (D_Conj) "(\<exists>p' Q'. g'=(Defender_Conj p' Q'))" | (D_Stable_Conj) "(\<exists>p' Q'. g'=(Defender_Stable_Conj p' Q'))" | (D_Branch) "(\<exists>p' p'' Q' \<alpha> Q\<alpha> . g'= (Defender_Branch p' \<alpha> p'' Q' Q\<alpha>))"
    by blast
  then show ?thesis proof (cases)
    case A_Delayed (* procrastination *)
    then show ?thesis using assms(2)
      by (metis Attacker_Delayed assms(1) id_apply local.procrastination option.sel)
  next
    case A_Immediate (* observation *)
    then have "spectroscopy_moves g g' = (subtract 1 0 0 0 0 0 0 0)"
      by (smt (verit) Attacker_Delayed assms(1) local.observation)
    then show ?thesis using assms(2) mono_subtract
      by simp
  next
    case D_Conj (* late_inst_conj *)
    then show ?thesis
      by (metis Attacker_Delayed assms(1) assms(2) id_apply local.late_inst_conj option.sel) 
  next
    case D_Stable_Conj (* late_stbl_conj *)
    then show ?thesis
      by (metis (mono_tags, lifting) Attacker_Delayed assms(1) assms(2) id_apply local.late_stbl_conj option.sel) 
  next
    case D_Branch (* br_conj *)
    then show ?thesis
      by (metis Attacker_Delayed assms(1) assms(2) id_apply local.br_conj option.sel) 
  qed
next
  case (Defender_Branch x51 x52 x53 x54 x55) (* br_answer or br_obsv *)
  then have "(\<exists>p'' q. g' = (Attacker_Clause p'' q)) \<or> (\<exists>p'' Q'. g'=(Attacker_Branch p'' Q'))" using assms(1)
    using spectroscopy_defender.cases spectroscopy_moves.simps(28) spectroscopy_moves.simps(29) spectroscopy_moves.simps(31) spectroscopy_moves.simps(32) spectroscopy_moves.simps(63)
    by (metis spectroscopy_moves.simps(30) spectroscopy_moves.simps(33))
  then have "spectroscopy_moves g g' = (subtract 0 1 1 0 0 0 0 0) \<or> spectroscopy_moves g g' = Some (min1_6 \<circ> (\<lambda>x. x- E 0 1 1 0 0 0 0 0))"
    by (smt (verit, del_insts) Defender_Branch assms(1) local.br_answer local.br_obsv) 
  then show ?thesis using assms(2) mono_subtract mono_min_1_6
    using comp_eq_dest_lhs monoD monoE mono_onI monotoneD option.sel by fastforce 
next
  case (Defender_Conj x61 x62) (* conj_answer *)
  then have "\<exists>p' q. g'=(Attacker_Clause p' q)" using assms(1)
    using spectroscopy_defender.cases spectroscopy_moves.simps(33) spectroscopy_moves.simps(34) spectroscopy_moves.simps(35) spectroscopy_moves.simps(36) spectroscopy_moves.simps(38) spectroscopy_moves.simps(69)
    by (metis spectroscopy_moves.simps(37) spectroscopy_moves.simps(39))
  then have "spectroscopy_moves g g' = (subtract 0 0 1 0 0 0 0 0)"
    by (metis Defender_Conj assms(1) local.conj_answer)
  then show ?thesis using assms(2) mono_subtract
    by simp
next
  case (Defender_Stable_Conj x71 x72) (* conj_s_answer *)
  then have "\<exists>p' q. g'=(Attacker_Clause p' q) \<or> (\<exists>p' Q'. g' = Defender_Conj p' Q')" using assms(1)
    using spectroscopy_defender.cases spectroscopy_moves.simps(39) spectroscopy_moves.simps(40) spectroscopy_moves.simps(41) spectroscopy_moves.simps(42) spectroscopy_moves.simps(43)
    by (smt (verit) spectroscopy_defender.elims(1) spectroscopy_moves.simps(40) spectroscopy_moves.simps(42) spectroscopy_moves.simps(43) spectroscopy_moves.simps(55) spectroscopy_moves.simps(75))

  then consider (A_Clause) "\<exists>p' q. g'=(Attacker_Clause p' q)" | (D_Conj) "(\<exists>p' Q'. g' = Defender_Conj p' Q')"
    by blast
  then show ?thesis proof (cases)
    case A_Clause
    then have "spectroscopy_moves g g' = (subtract 0 0 0 1 0 0 0 0)"
      using Defender_Stable_Conj assms(1) local.conj_s_answer
      by meson
    then show ?thesis using assms(2) mono_subtract by simp
  next
    case D_Conj
    then have "spectroscopy_moves g g' = (subtract 0 0 0 1 0 0 0 0)"
      by (metis Defender_Stable_Conj assms(1) local.empty_stbl_conj_answer)
    then show ?thesis using assms(2) mono_subtract by simp
  qed
qed
  
lemma update_gets_smaller: 
  fixes g g' e 
  assumes "(spectroscopy_moves g g') \<noteq> None"
  shows "(the (spectroscopy_moves g g')e)\<le> e"
using assms proof (cases g)
  case (Attacker_Immediate x11 x12)
  then have "(\<exists>p' Q'. g'=(Attacker_Delayed p' Q')) \<or> (\<exists> p' Q'. g'= (Defender_Conj p' Q'))" using assms
    using spectroscopy_defender.elims(2) spectroscopy_defender.elims(3) spectroscopy_moves.simps(45) spectroscopy_moves.simps(50) spectroscopy_moves.simps(56) spectroscopy_moves.simps(60) spectroscopy_moves.simps(71)
    by (metis spectroscopy_moves.simps(70))

  then consider (A_Delayed) "(\<exists>p' Q'. g'=(Attacker_Delayed p' Q'))" | (D_Conj) "(\<exists> p' Q'. g'= (Defender_Conj p' Q'))" by auto
  then show ?thesis proof (cases)
    case A_Delayed (*delay*)
    then have "spectroscopy_moves g g' = Some id"
      using Attacker_Immediate assms(1) local.delay
      by (smt (verit, del_insts))
    then show ?thesis by simp
  next
    case D_Conj (*finishing_or_early_conj*)
    then have "spectroscopy_moves g g' = Some id \<or> spectroscopy_moves g g' = (subtract 0 0 0 0 1 0 0 0)" using assms(1)
      by (metis Attacker_Immediate local.finishing_or_early_conj)
    then show ?thesis using gets_smaller by auto 
  qed
next
  case (Attacker_Branch x21 x22) (*br_acct*)
  then have "\<exists>p' Q'. g'= (Attacker_Immediate p' Q')" using assms(1) spectroscopy_moves.simps
    by (metis (no_types, lifting) spectroscopy_defender.elims(2) spectroscopy_defender.elims(3))
  then have "spectroscopy_moves g g' = subtract 1 0 0 0 0 0 0 0"
    by (metis Attacker_Branch assms(1) local.br_acct) 
  then show ?thesis using gets_smaller by auto 
next
  case (Attacker_Clause x31 x32) (*pos_neg_clause *)
  then have "\<exists>p' Q'. g'= (Attacker_Delayed p' Q')" using assms(1) spectroscopy_moves.simps
    by (metis (no_types, lifting) spectroscopy_defender.elims(2) spectroscopy_defender.elims(3))
  then have "spectroscopy_moves g g' = Some min1_6 \<or> spectroscopy_moves g g' = Some (min1_7 \<circ> (\<lambda>x. x- E 0 0 0 0 0 0 0 1))" using assms(1)
    by (smt (verit) Attacker_Clause local.pos_neg_clause) 
  then show ?thesis using gets_smaller
    using dual_order.trans gets_smaller_min_1_6 gets_smaller_min_1_7 option.sel by fastforce 
next
  case (Attacker_Delayed x41 x42)
  then have "(\<exists>p' Q'. g'=(Attacker_Delayed p' Q')) \<or> (\<exists>p' Q'. g'=(Attacker_Immediate p' Q')) \<or> (\<exists>p' Q'. g'=(Defender_Conj p' Q')) \<or> (\<exists>p' Q'. g'=(Defender_Stable_Conj p' Q')) \<or> (\<exists>p' p'' Q' \<alpha> Q\<alpha> . g'= (Defender_Branch p' \<alpha> p'' Q' Q\<alpha>))"
    using assms spectroscopy_defender.cases spectroscopy_moves.simps(26) spectroscopy_moves.simps(27)
    by (metis spectroscopy_moves.simps(28))

  then consider (A_Delayed) "(\<exists>p' Q'. g'=(Attacker_Delayed p' Q'))" | (A_Immediate) "(\<exists>p' Q'. g'=(Attacker_Immediate p' Q'))" | (D_Conj) "(\<exists>p' Q'. g'=(Defender_Conj p' Q'))" | (D_Stable_Conj) "(\<exists>p' Q'. g'=(Defender_Stable_Conj p' Q'))" | (D_Branch) "(\<exists>p' p'' Q' \<alpha> Q\<alpha> . g'= (Defender_Branch p' \<alpha> p'' Q' Q\<alpha>))"
    by blast
  then show ?thesis proof (cases)
    case A_Delayed (* procrastination *)
    then show ?thesis using assms
      by (metis Attacker_Delayed Orderings.order_eq_iff id_apply local.procrastination option.sel)
  next
    case A_Immediate (* observation *)
    then have "spectroscopy_moves g g' = (subtract 1 0 0 0 0 0 0 0)"
      by (smt (verit) Attacker_Delayed assms local.observation) 
    then show ?thesis using gets_smaller by simp
  next
    case D_Conj (* late_inst_conj *)
    then show ?thesis
      by (metis Attacker_Delayed assms eq_id_iff local.late_inst_conj option.sel order_refl)
  next
    case D_Stable_Conj (* late_stbl_conj *)
    then show ?thesis using assms
      by (metis (no_types, lifting) Attacker_Delayed Orderings.order_eq_iff id_apply local.late_stbl_conj option.sel)
  next
    case D_Branch (* br_conj *)
    then show ?thesis using assms
      by (metis Attacker_Delayed Orderings.order_eq_iff id_apply local.br_conj option.sel) 
  qed
next
  case (Defender_Branch x51 x52 x53 x54 x55) (* br_answer or br_obsv *)
  then have "(\<exists>p'' q. g' = (Attacker_Clause p'' q)) \<or> (\<exists>p'' Q'. g'=(Attacker_Branch p'' Q'))" using assms(1)
    using spectroscopy_defender.cases spectroscopy_moves.simps(28) spectroscopy_moves.simps(29) spectroscopy_moves.simps(31) spectroscopy_moves.simps(32) spectroscopy_moves.simps(63)
    by (metis spectroscopy_moves.simps(30) spectroscopy_moves.simps(33))
  then have "spectroscopy_moves g g' = (subtract 0 1 1 0 0 0 0 0) \<or> spectroscopy_moves g g' = Some (min1_6 \<circ> (\<lambda>x. x- E 0 1 1 0 0 0 0 0))"
    by (smt (verit, del_insts) Defender_Branch assms(1) local.br_answer local.br_obsv) 
  then show ?thesis using gets_smaller gets_smaller_min_1_6
    using dual_order.trans by fastforce
next
  case (Defender_Conj x61 x62) (* conj_answer *)
  then have "\<exists>p' q. g'=(Attacker_Clause p' q)" using assms(1)
    using spectroscopy_defender.cases spectroscopy_moves.simps(33) spectroscopy_moves.simps(34) spectroscopy_moves.simps(35) spectroscopy_moves.simps(36) spectroscopy_moves.simps(38) spectroscopy_moves.simps(69)
    by (metis spectroscopy_moves.simps(39) spectroscopy_moves.simps(64))
  then have "spectroscopy_moves g g' = (subtract 0 0 1 0 0 0 0 0)"
    by (metis Defender_Conj assms(1) local.conj_answer)
  then show ?thesis using gets_smaller by auto
next
  case (Defender_Stable_Conj x71 x72) (* conj_s_answer *)
  then have "\<exists>p' q. g'=(Attacker_Clause p' q) \<or> (\<exists>p' Q'. g' = (Defender_Conj p' Q'))" using assms(1)
    using spectroscopy_defender.cases spectroscopy_moves.simps(39) spectroscopy_moves.simps(40) spectroscopy_moves.simps(41) spectroscopy_moves.simps(42) spectroscopy_moves.simps(43)
    by (metis spectroscopy_moves.simps(44))
  then have "spectroscopy_moves g g' = (subtract 0 0 0 1 0 0 0 0)"
    using Defender_Stable_Conj assms(1) local.conj_s_answer 
    by (metis local.empty_stbl_conj_answer)
  then show ?thesis using gets_smaller by auto
qed

interpretation Game: energy_game "spectroscopy_moves" "spectroscopy_defender" "eneg" "less_eq" 
proof 
  fix e e' e''::energy
  show "e \<le> e' \<Longrightarrow> e' \<le> e'' \<Longrightarrow> e \<le> e''" unfolding less_eq_energy_def by (smt (z3) energy.case_eq_if order_trans)
  show "e \<le> e" unfolding less_eq_energy_def by (simp add: energy.case_eq_if)
  show "e \<le> e' \<Longrightarrow> e' \<le> e \<Longrightarrow> e = e'" unfolding less_eq_energy_def
    by (smt (z3) energy.case_eq_if energy.expand nle_le)
  show "eneg \<le> e" using eneg_leq .
  show "\<And>g g' e e'. spectroscopy_moves g g' \<noteq> None \<Longrightarrow> e \<le> e' \<Longrightarrow> the (spectroscopy_moves g g') e \<le> the (spectroscopy_moves g g') e'" using update_monotonicity by simp
  show "\<And>g g' e. spectroscopy_moves g g' \<noteq> None \<Longrightarrow> the (spectroscopy_moves g g') e \<le> e" using update_gets_smaller by simp
qed

end

text \<open>Now we can write down the full spectroscopy game depending on an arbitrary (but inhabitated) LTS:\<close>
locale full_spec_game =
  Inhabited_Tau_LTS step left right \<tau>
  + energy_game "spectroscopy_moves" "spectroscopy_defender" "eneg" "less_eq"
  for step :: \<open>'s \<Rightarrow> 'a \<Rightarrow> 's \<Rightarrow> bool\<close> (\<open>_ \<mapsto>_ _\<close> [70, 70, 70] 80) and
      left :: 's and
      right :: 's and
      \<tau> :: 'a
begin

inductive 
strategy_formula :: "('s, 'a) spectroscopy_position \<Rightarrow> energy \<Rightarrow> ('a, 's)hml_srbb \<Rightarrow> bool"
and strategy_formula_inner 
  :: "('s, 'a) spectroscopy_position \<Rightarrow> energy \<Rightarrow> ('a, 's)hml_srbb_inner \<Rightarrow> bool"
and strategy_formula_conjunct
  :: "('s, 'a) spectroscopy_position \<Rightarrow> energy \<Rightarrow> ('a, 's)hml_srbb_conjunct \<Rightarrow> bool"
where
  delay:
    "strategy_formula (Attacker_Immediate p Q) e (Internal \<chi>)"
      if "((\<exists>Q'. (spectroscopy_moves (Attacker_Immediate p Q) (Attacker_Delayed p Q') 
        = (Some (id:: energy \<Rightarrow> energy))) \<and> (in_wina e (Attacker_Delayed p Q')) 
          \<and> strategy_formula_inner (Attacker_Delayed p Q') e \<chi>))" |
  
  procrastination:
    "strategy_formula_inner (Attacker_Delayed p Q) e \<chi>"
      if "(\<exists>p'. spectroscopy_moves (Attacker_Delayed p Q) (Attacker_Delayed p' Q) 
         = (Some id) \<and> in_wina e (Attacker_Delayed p' Q)
          \<and> strategy_formula_inner (Attacker_Delayed p' Q) e \<chi>)"|
  
  observation: 
    "strategy_formula_inner (Attacker_Delayed p Q) e (Obs \<alpha> \<phi>)" 
      if "\<exists>p' Q'. spectroscopy_moves (Attacker_Delayed p Q) (Attacker_Immediate p' Q') 
         = (subtract 1 0 0 0 0 0 0 0) \<and> in_wina (e - (E 1 0 0 0 0 0 0 0)) (Attacker_Immediate p' Q')
          \<and> strategy_formula (Attacker_Immediate p' Q') (e - (E 1 0 0 0 0 0 0 0)) \<phi>
          \<and> p \<mapsto>\<alpha> p' \<and> Q \<mapsto>S \<alpha> Q'" |
  
  early_conj:
    "strategy_formula (Attacker_Immediate p Q) e \<phi>" 
      if "(if Q = {} then (\<exists>p'. spectroscopy_moves (Attacker_Immediate p Q) (Defender_Conj p' Q') 
                          = (Some id) \<and> in_wina e (Defender_Conj p' Q') 
                            \<and> strategy_formula (Defender_Conj p' Q') e \<phi>)

           else \<exists>p'. spectroscopy_moves (Attacker_Immediate p Q) (Defender_Conj p' Q') 
                = (subtract 0 0 0 0 1 0 0 0) \<and> in_wina (e - (E 0 0 0 0 1 0 0 0)) (Defender_Conj p' Q')
                  \<and> strategy_formula (Defender_Conj p' Q') (e - (E 0 0 0 0 1 0 0 0)) \<phi>)"|
  
  late_conj:
    "strategy_formula_inner (Attacker_Delayed p Q) e \<chi>"
      if "(spectroscopy_moves (Attacker_Delayed p Q) (Defender_Conj p Q) 
         = (Some id) \<and> (in_wina e (Defender_Conj p Q)) 
           \<and> strategy_formula_inner (Defender_Conj p Q) e \<chi>)"|
  
  conj:
  "strategy_formula_inner (Defender_Conj p Q) e (Conj Q \<Phi>)"
      if "\<forall>q \<in> Q. spectroscopy_moves (Defender_Conj p Q) (Attacker_Clause p q) 
          = (subtract 0 0 1 0 0 0 0 0) \<and> (in_wina (e - (E 0 0 1 0 0 0 0 0)) (Attacker_Clause p q)) 
            \<and> strategy_formula_conjunct (Attacker_Clause p q) (e - (E 0 0 1 0 0 0 0 0)) (\<Phi> q)"|

  imm_conj:
  "strategy_formula (Defender_Conj p Q) e (ImmConj Q \<Phi>)"
      if "\<forall>q \<in> Q. spectroscopy_moves (Defender_Conj p Q) (Attacker_Clause p q) 
          = (subtract 0 0 1 0 0 0 0 0) \<and> (in_wina (e - (E 0 0 1 0 0 0 0 0)) (Attacker_Clause p q)) 
            \<and> strategy_formula_conjunct (Attacker_Clause p q) (e - (E 0 0 1 0 0 0 0 0)) (\<Phi> q)"|
  
  pos:
  "strategy_formula_conjunct (Attacker_Clause p q) e (Pos \<chi>)"
    if "(\<exists>Q'. spectroscopy_moves (Attacker_Clause p q) (Attacker_Delayed p Q') 
      = Some min1_6 \<and> in_wina (min1_6 e) (Attacker_Delayed p Q')
        \<and> strategy_formula_inner (Attacker_Delayed p Q') (min1_6 e) \<chi>)"|
  
  neg:
  "strategy_formula_conjunct (Attacker_Clause p q) e (Neg \<chi>)" 
    if "\<exists>P'. (spectroscopy_moves (Attacker_Clause p q) (Attacker_Delayed q P') 
      = Some (min1_7 \<circ> (\<lambda>x. x- E 0 0 0 0 0 0 0 1))
        \<and> in_wina ((min1_7 (e - (E 0 0 0 0 0 0 0 1)))) (Attacker_Delayed q P'))
        \<and> strategy_formula_inner (Attacker_Delayed q P') ((min1_7 (e - (E 0 0 0 0 0 0 0 1)))) \<chi>" |
  
  stable:
  "strategy_formula_inner (Attacker_Delayed p Q) e \<chi>" 
    if "(\<exists>Q'. spectroscopy_moves (Attacker_Delayed p Q) (Defender_Stable_Conj p Q') 
      = (Some id) \<and> in_wina e (Defender_Stable_Conj p Q') 
        \<and> strategy_formula_inner (Defender_Stable_Conj p Q') e \<chi>)"|

  stable_conj:
    "strategy_formula_inner (Defender_Stable_Conj p Q) e (StableConj Q \<Phi>)"
      if "\<forall>q \<in> Q. spectroscopy_moves (Defender_Stable_Conj p Q) (Attacker_Clause p q) 
        = (subtract 0 0 0 1 0 0 0 0) \<and> in_wina (e - (E 0 0 0 1 0 0 0 0)) (Attacker_Clause p q)
          \<and> strategy_formula_conjunct (Attacker_Clause p q) (e - (E 0 0 0 1 0 0 0 0)) (\<Phi> q)"|
  
  branch:
  "strategy_formula_inner (Attacker_Delayed p Q) e \<chi>" 
    if "\<exists>p' Q' \<alpha> Q\<alpha>. spectroscopy_moves (Attacker_Delayed p Q) (Defender_Branch p \<alpha> p' Q' Q\<alpha>) 
      = (Some id) \<and> in_wina e (Defender_Branch p \<alpha> p' Q' Q\<alpha>) 
        \<and> strategy_formula_inner (Defender_Branch p \<alpha> p' Q' Q\<alpha>) e \<chi>"|

  branch_conj:
  "strategy_formula_inner (Defender_Branch p \<alpha> p' Q Q\<alpha>) e (BranchConj \<alpha> \<psi> Q \<Phi>)"
    if "\<exists>Q'. spectroscopy_moves (Defender_Branch p \<alpha> p' Q Q\<alpha>) (Attacker_Branch p' Q') 
          = Some (min1_6 \<circ> (\<lambda>x. x- E 0 1 1 0 0 0 0 0)) 
            \<and> spectroscopy_moves (Attacker_Branch p' Q') (Attacker_Immediate p' Q')
            = subtract 1 0 0 0 0 0 0 0 
            \<and> (in_wina ((min1_6 (e - E 0 1 1 0 0 0 0 0)) - (E 1 0 0 0 0 0 0 0)) 
                  (Attacker_Immediate p' Q'))
            \<and> strategy_formula (Attacker_Immediate p' Q') e' \<psi>"
        
        "\<forall>q \<in> Q. spectroscopy_moves (Defender_Branch p \<alpha> p' Q Q\<alpha>) (Attacker_Clause p q) 
          = (subtract 0 1 1 0 0 0 0 0)
          \<and> in_wina (e - (E 0 1 1 0 0 0 0 0)) (Attacker_Clause p q)
          \<and> strategy_formula_conjunct (Attacker_Clause p q) (e - (E 0 1 1 0 0 0 0 0)) (\<Phi> q)"

end

end