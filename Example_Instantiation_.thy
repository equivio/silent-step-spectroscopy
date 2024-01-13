theory Example_Instantiation_
  imports Energy_Games "HOL-Library.Extended_Nat"
begin
text \<open>In this theory we create an instantiation of energy game to test our definitions.\<close>
text \<open>Based on our definition of energy  with eight dimensions, we first define energy..\<close>
datatype energy = E (one: "enat") (two: "enat") | eneg

text \<open>We define the following definitions and abbreviations to update our energy levels.
Note that we always use "eneg" when the energy level is equal to or lower than the "defender win level".\<close>
instantiation energy :: minus
begin
abbreviation "direct_minus e1 e2 \<equiv> E ((one e1) - (one e2)) ((two e1) - (two e2))"

fun order:: "energy \<Rightarrow> energy \<Rightarrow> bool" where 
  "order eneg _ = True" |
  "order (E e1 e2) (E e1' e2') = (e1 \<le> e1' \<and> e2 \<le> e2')" |
  "order _ _ = False"

definition minus_energy_def: "e1 - e2 \<equiv> if (\<not> order e2 e1) then eneg
                                             else direct_minus e1 e2"
instance ..
lemma energy_minus[simp]:
  assumes "(order (E c d) (E a b))"
  shows "E a b - E c d = E (a - c) (b - d)" using assms minus_energy_def by auto
end

definition "min_update e1 \<equiv> if (e1 = eneg) then eneg else  E (min (one e1) (two e1)) (two e1)" 

lemma min_update[simp]:
  shows "min_update (E a b) = E (min a b) b" unfolding min_update_def using energy.sel by fastforce

text \<open>In preparation for our instantiation we define our states, the updates for our energy levels and which states are defender positions.\<close>
datatype state = a | b1 | b2 | c | d1 | d2 | e

fun weight_opt :: "state \<Rightarrow> state \<Rightarrow> energy update option" where
  "weight_opt a b1 = Some (\<lambda>x. x - (E 1 0))" |
  "weight_opt a b2 = Some (\<lambda>x. x - (E 0 1))" |
  "weight_opt b1 c = Some id" |
  "weight_opt b2 c = Some min_update" |
  "weight_opt c d1 = Some (\<lambda>x. x - (E 0 1))" |
  "weight_opt c d2 = Some (\<lambda>x. x - (E 1 0))" |
  "weight_opt d1 e = Some id" |
  "weight_opt d2 e = Some id" |
  "weight_opt _ _ = None"

find_theorems weight_opt

fun defender :: "state \<Rightarrow> bool" where
  "defender b1 = True" |
  "defender b2 = True" |
  "defender c = True" |
  "defender e = True" |
  "defender _ = False"

interpretation Game: energy_game "weight_opt" "defender" "eneg" "order" 
proof
  fix g g' e e' e''
  show "order e e' \<Longrightarrow> order e' e'' \<Longrightarrow> order e e''"
    by (smt (verit) dual_order.trans energy.discI energy.inject order.elims(1))
  show "order e e"
    using order.elims(3) by blast
  show "order e e' \<Longrightarrow> order e' e \<Longrightarrow> e = e'"
    by (smt (verit) antisym energy.distinct(1) energy.inject order.elims(1))
  show "order eneg e" by simp 

  assume "weight_opt g g' \<noteq> None"
  hence Y: "weight_opt g g' = Some id \<or> weight_opt g g' = Some min_update \<or> weight_opt g g' = Some (\<lambda>x. x - (E 1 0)) \<or> weight_opt g g' = Some (\<lambda>x. x - (E 0 1))"
    using weight_opt.simps by (smt (verit, del_insts) defender.cases) 
  then consider (id) "weight_opt g g' = Some id" | (min) "weight_opt g g' = Some min_update" |(10) " weight_opt g g' = Some (\<lambda>x. x - (E 1 0))" | (01) " weight_opt g g' = Some (\<lambda>x. x - (E 0 1))" by auto

  thus "order (the (weight_opt g g') e) e" proof (cases)
    case id
    then show ?thesis
      by (simp add: \<open>order e e\<close>) 
  next
    case min
    then show ?thesis
      by (smt (verit, del_insts) antisym_conv3 dual_order.refl energy.case_eq_if energy.discI energy.distinct(1) energy.exhaust energy.inject energy.sel(1) energy.sel(2) energy.simps(4) min.absorb3 min.absorb_iff2 min.commute min.idem min_update_def minus_energy_def option.sel order.elims(2) order.elims(3) order.simps(3) order_less_imp_le verit_comp_simplify1(3)) 
  next
    case 10
    then show ?thesis proof (cases "order (E 1 0) e")
      case True
      from this \<open>weight_opt g g' = Some (\<lambda>x. x - E 1 0)\<close> have "the (weight_opt g g') e = e - E 1 0" by auto
      hence X: "the (weight_opt g g') e = E ((one e) - 1) ((two e) - 0)" by (simp add: True minus_energy_def) 
      have "((one e) - 1) \<le> (one e) \<and> ((two e) - 0) \<le> (two e)"
        by (metis True add.commute add.right_neutral eSuc_minus_1 eSuc_plus_1 energy.distinct(1) energy.sel(1) idiff_0_right le_iff_add order.elims(2))
      from this X show ?thesis
        by (metis True energy.exhaust_sel order.simps(2) order.simps(3)) 
    next
      case False
      from this \<open>weight_opt g g' = Some (\<lambda>x. x - E 1 0)\<close> show ?thesis using minus_energy_def by simp 
    qed
  next
    case 01
     then show ?thesis proof (cases "order (E 0 1) e")
      case True
      from this \<open>weight_opt g g' = Some (\<lambda>x. x - E 0 1)\<close> have "the (weight_opt g g') e = e - E 0 1" by auto
      hence X: "the (weight_opt g g') e = E ((one e) - 0) ((two e) - 1)" by (simp add: True minus_energy_def) 
      have "((one e) - 0) \<le> (one e) \<and> ((two e) - 1) \<le> (two e)"
        by (metis True add.commute add.right_neutral eSuc_minus_1 eSuc_plus_1 energy.distinct(1) energy.exhaust_sel idiff_0_right le_iff_add order.elims(2) order.simps(2))
      from this X show ?thesis
        by (metis True energy.exhaust_sel order.simps(2) order.simps(3)) 
    next
      case False
      from this \<open>weight_opt g g' = Some (\<lambda>x. x - E 0 1)\<close> show ?thesis using minus_energy_def by simp 
    qed
  qed

  assume "order e e'"
  from Y consider (id) "weight_opt g g' = Some id" | (min) "weight_opt g g' = Some min_update" |(10) " weight_opt g g' = Some (\<lambda>x. x - (E 1 0))" | (01) " weight_opt g g' = Some (\<lambda>x. x - (E 0 1))" by auto
  then show "order (the (weight_opt g g') e) (the (weight_opt g g') e')" proof (cases)
    case id
    then show ?thesis using \<open>order e e'\<close> by auto
  next
    case min
    then show ?thesis proof (cases "e =eneg")
      case True
      then show ?thesis using \<open>order e e'\<close> min
        by (simp add: min_update_def)
    next
      case False
      then show ?thesis using \<open>order e e'\<close> min
        by (smt (verit) energy.sel(1) energy.sel(2) min.mono min_update_def option.sel order.elims(2) order.elims(3) order.simps(1) order.simps(3))
    qed 
  next
    case 10
    then show ?thesis proof (cases "order (E 1 0) e")
      case True
      hence E: "the (weight_opt g g') e = E ((one e) - 1) ((two e) - 0)" using 10
        by (simp add: minus_energy_def)
      from True 10 have E': "the (weight_opt g g') e' = E ((one e') - 1) ((two e') - 0)" using \<open>order e e'\<close>
        by (smt (verit) energy.sel(1) energy.sel(2) minus_energy_def option.sel order.elims(2) order.simps(2) order.simps(3) order.trans) 
      have "order  (E ((one e) - 1) ((two e) - 0)) (E ((one e') - 1) ((two e') - 0))" using True \<open>order e e'\<close>
        by (metis add.commute add_diff_assoc_enat energy.distinct(1) energy.exhaust energy.sel(1) energy.sel(2) idiff_0_right le_iff_add order.elims(2) order.simps(2))
      thus ?thesis using E E' by simp
    next
      case False
      then show ?thesis using 10 \<open>order e e'\<close>
        by (simp add: minus_energy_def)
    qed
  next
    case 01
    then show ?thesis proof (cases "order (E 0 1) e")
      case True
      hence E: "the (weight_opt g g') e = E ((one e) - 0) ((two e) - 1)" using 01
        by (simp add: minus_energy_def)
      from True 01 have E': "the (weight_opt g g') e' = E ((one e') - 0) ((two e') - 1)" using \<open>order e e'\<close>
        by (smt (verit) energy.sel(1) energy.sel(2) minus_energy_def option.sel order.elims(2) order.simps(2) order.simps(3) order.trans) 
      have "order  (E ((one e) - 0) ((two e) - 1)) (E ((one e') - 0) ((two e') - 1))" using True \<open>order e e'\<close>
        by (metis add.commute add_diff_assoc_enat energy.distinct(1) energy.exhaust energy.sel(1) energy.sel(2) idiff_0_right le_iff_add order.elims(2) order.simps(2))
      thus ?thesis using E E' by simp
    next
      case False
      then show ?thesis using 01 \<open>order e e'\<close>
        by (simp add: minus_energy_def)
    qed
  qed
qed

notation Game.moves (infix "\<Zinj>" 70)
abbreviation "finite_play \<equiv> Game.finite_play"

lemma moves:
  shows "a \<Zinj> b1" "a \<Zinj> b2"
       "b1 \<Zinj> c" "b2 \<Zinj> c"
       "c \<Zinj> d1" "c \<Zinj> d2"
       "d1 \<Zinj> e" "d2 \<Zinj> e"
       "\<not>(c \<Zinj> e)" "\<not>(e \<Zinj> d1)"
  by simp+

text\<open>In the following we check our definition of finite play with two examples: one that is a finite play and one that is not.
We also look at the "behavior" of our finite game definition if we change the starting position.\<close>
lemma Game_finite_play_example:
  shows "finite_play a [a, b2, c, d1, e]"
proof-
  have "finite_play a [a]" by (rule Game.finite_play.intros(1))
  hence "finite_play a [a, b2]" using Game.finite_play.intros(2) by fastforce
  hence "finite_play a [a, b2, c]" using Game.finite_play.intros(2) by fastforce
  hence "finite_play a [a, b2, c, d1]" using Game.finite_play.intros(2) by fastforce
  thus "finite_play a [a, b2, c, d1, e]" using  Game.finite_play.intros(2) by fastforce
qed

lemma Game_finite_play_counterexample:
  shows "\<not>finite_play a [a, b2, e, d1, e]"
  using Game.finite_play.intros Game.finite_play_is_path
  by (metis append_Cons append_Nil last_snoc list.distinct(1) weight_opt.simps(20)) 

lemma Game_finite_play_check:
  shows "\<not>finite_play b2 [a, b2, c, d1, e]"
  by (metis Game.finite_play.cases Game.finite_play_prefix append.left_neutral append_Cons last_ConsL last_appendR not_Cons_self2 state.distinct(3) weight_opt.simps(39))

lemma Game_finite_play_check_2:
  assumes "x\<noteq>a"
  shows "\<not>finite_play x [a, b2, c, d1, e]" 
proof (rule notI)
  assume A1: "finite_play x [a, b2, c, d1, e]"
  from A1 have A2: "finite_play x ([a] @ [b2, c, d1, e])"
    by simp
  from A2 have A3: "\<not>finite_play x ([a] @ [b2, c, d1, e])"
    by (metis Game.finite_play.cases Game.finite_play_prefix append1_eq_conv append_Nil assms neq_Nil_conv weight_opt.simps(39)) 
  from A1 A3 show "False" by simp
qed

abbreviation "energy_level \<equiv> Game.energy_level"
text \<open>To check our calculation of energy levels, we look at different games and their energy levels using the following lemmas.\<close>
lemma energy_level_example:
  shows "energy_level a (E 10 10) [a, b2, c, d1, e] = E 9 8"
proof-
  have "energy_level a (E 10 10) [a, b2, c, d1, e] =id ((min_update (E 10 10 - E 0 1)) - E 0 1)" by simp
  also have "... = id ((min_update (E 10 9)) - E 0 1)" by (simp add: numeral_eq_enat one_enat_def)
  also have "... = id (E 9 9 - E 0 1)" by simp
  also have "... = id (E 9 8)" by (simp add: numeral_eq_enat one_enat_def)
  also have "... = E 9 8" by simp
  finally show ?thesis .
qed

lemma energy_level_example_1:
  shows "energy_level a (E 10 10) [a, b2, c] = E 9 9"
proof-
  have "energy_level a (E 10 10) [a, b2, c] = min_update (E 10 10 - E 0 1)" by simp
  also have "... = E 9 9" by (simp add: numeral_eq_enat one_enat_def)
  finally show "energy_level a (E 10 10) [a, b2, c] = E 9 9".
qed

lemma energy_level_example_2:
  shows "energy_level a (E 10 10) [a, b2, d1] = undefined"
  using Game.energy_level.elims Game.energy_level.pelims by simp

lemma energy_level_example_3:
  shows "energy_level a (E 10 10) [a, b2, b1] = undefined"
  using Game.energy_level.elims Game.energy_level.pelims by simp

lemma energy_level_example_4:
  shows "energy_level a (E 10 10) [c] = undefined"
  using Game.energy_level.elims Game.energy_level.pelims by simp

text \<open>We also take a look at our definition of play stuck using different examples of plays.
In particular we check our definition regarding invalid games.\<close>
lemma play_stuck_example:
  shows "Game.play_stuck a [a, b2, c, d1, e]"
  by (metis Game.finite_play_is_path Game.finite_play_suffix2 Game_finite_play_example append_Cons append_Nil last_ConsL list.distinct(1) weight_opt.simps(38))
 
lemma play_not_stuck_example:
  shows "\<not>(Game.play_stuck a [a, b2, c])"
proof (-) 
  have "finite_play a ([a, b2, c] @ [d1])"
    by (metis Game.finite_play_suffix Game_finite_play_example append_Cons append_Nil list.distinct(1))
  thus "\<not>(Game.play_stuck a [a, b2, c])" by auto
qed
text \<open>\<close>
lemma play_stuck_invalid_game: 
  shows "\<not>(Game.play_stuck a [a, b2, d1])"
  by (smt (verit, best) Game.finite_play.simps butlast.simps(2) butlast_snoc distinct_adj_Cons distinct_adj_Cons_Cons last.simps last_snoc weight_opt.simps(18))

lemma play_stuck_invalid_game_1: 
  shows "\<not>Game.play_stuck a [a, b2, b1]"
  by (metis Game.finite_play.cases butlast.simps(2) butlast_snoc last.simps last_snoc list.discI weight_opt.simps(16))

text \<open>In the following we look at play examples and check who wins the corresponding game.\<close>
lemma attacker_wins_example:
  shows "Game.won_by_attacker a (E 10 10) [a, b2, c, d1, e]"
  using play_stuck_example energy_level_example
  by (simp add: Game.won_by_attacker_def)

lemma no_winner_example: 
  shows "Game.no_winner a (E 10 10) [a, b2, c]"
  using play_not_stuck_example energy_level_example_1 by simp

lemma attacker_turn_not_stuck:
  assumes "finite_play a p" and "Game.is_attacker_turn p"
  shows "\<not>Game.play_stuck a p"
using assms proof - 
  from assms have "last p = a \<or> last p = d1 \<or> last p = d2"
    using defender.elims(3) by blast
  hence "(last p)\<Zinj> b1 \<or> (last p) \<Zinj> e" by auto
  hence "(\<exists>gn. finite_play a (p @ [gn]))" using assms(1) Game.finite_play.intros(2) by blast 
  thus "\<not>Game.play_stuck a p" by simp
qed
text \<open>Finally, we verify our definition of win_a using scenarios where we expect the attacker to have a winning strategy (or not).\<close>

lemma attackers_winas_defender_stuck:
  shows "Game.in_wina (E 9 8) e"
  by (simp add: Game.in_wina.intros(1))

lemma attacker_has_wina_example:
  shows "\<exists>e1. Game.in_wina e1 e" 
  using attackers_winas_defender_stuck by blast

lemma attackers_winas_defender_stuck_gen: 
  shows "\<forall>e'. e' \<noteq> eneg \<longrightarrow> Game.in_wina e' e"
  by (simp add: Game.in_wina.intros(1))

lemma attacker_winas_example_attacker:
  shows "Game.in_wina (E 9 8) d1" 
proof -
  have A1: "\<not>(defender d1)" by simp
  have A2: "d1 \<Zinj> e" by simp
  have A3: "Game.in_wina (E 9 8) e" by (rule attackers_winas_defender_stuck)
  have "Game.weight d1 e = id"by simp
  hence "(Game.weight d1 e (E 9 8)) = E 9 8 " by simp
  hence "(Game.in_wina (((Game.weight d1 e (E 9 8)))) e)" using A3 by simp
  from this A3 have A4: "\<not>(defender d1) \<and> (\<exists>g'. ((d1 \<Zinj> g') \<and> (Game.in_wina (((Game.weight d1 g' (E 9 8)))) g')))"
  by (meson A1 A2 Game.in_wina.intros(1,3) defender.simps(4) weight_opt.simps(38))
  thus "Game.in_wina (E 9 8) d1" using Game.in_wina.intros(2) by blast 
qed

lemma attacker_winas_example_attacker_2:
  shows "Game.in_wina (E 8 9) d2" 
proof -
  have A1: "\<not>(defender d2)" by simp
  have A2: "d2 \<Zinj> e" by simp
  have A3: "Game.in_wina (E 8 9) e" by (simp add: attackers_winas_defender_stuck_gen)
  have "Game.weight d2 e = id"by simp
  hence "(Game.weight d2 e (E 8 9)) = E 8 9 " by simp
  hence "(Game.in_wina (((Game.weight d2 e (E 8 9)))) e)" using A3 by simp
  from this A3 have A4: "\<not>(defender d2) \<and> (\<exists>g'. ((d2 \<Zinj> g') \<and> (Game.in_wina (((Game.weight d2 g' (E 8 9)))) g')))"
  by (meson A1 A2 Game.in_wina.intros(1,3) defender.simps(4) weight_opt.simps(38))
  thus "Game.in_wina (E 8 9) d2" using Game.in_wina.intros(2) by blast 
qed

lemma defender_not_stuck_wina:
  shows "Game.in_wina (E 9 9) c"
proof -
  have A1: "defender c" by auto
  have A2: "\<forall>g'. (c \<Zinj> g') \<longrightarrow> (g' = d1 \<or> g' = d2)"
    by (metis moves(9) state.exhaust weight_opt.simps(21) weight_opt.simps(22) weight_opt.simps(23) weight_opt.simps(24))
  have A3: "Game.in_wina (E 9 8) d1" using attacker_winas_example_attacker by blast
  have A4: "Game.in_wina (E 8 9) d2" using attacker_winas_example_attacker_2 by blast

  have "\<not>order (E 9 9) (E 0 1)" by simp
  hence "(E 9 9 - (E 0 1)) = E ((one (E 9 9)) - (one (E 0 1))) ((two (E 9 9)) - (two (E 0 1)))" using minus_energy_def
    by simp
  hence "(E 9 9 - (E 0 1)) = E 9 (9 -1)" by simp
  hence A5: "(E 9 9 - (E 0 1)) = E 9 8" using numeral_eq_enat one_enat_def
    by (metis add_diff_cancel_right' idiff_enat_enat inc.simps(2) numeral_inc) 

  have "(Game.weight c d1) (E 9 9) = (E 9 9) - (E 0 1)" using weight_opt.simps(5)by simp
  hence "(Game.weight c d1) (E 9 9) = E 9 8" using A5 by simp
  hence A6: "Game.in_wina ((Game.weight c d1) (E 9 9)) d1" using A3 by simp

    have "\<not>order (E 9 9) (E 1 0)" by simp
  hence "(E 9 9 - (E 1 0)) = E ((one (E 9 9)) - (one (E 1 0))) ((two (E 9 9)) - (two (E 1 0)))" using minus_energy_def
    by simp
  hence "(E 9 9 - (E 1 0)) = E (9 -1) 9" by simp
  hence A7: "(E 9 9 - (E 1 0)) = E 8 9" using numeral_eq_enat one_enat_def
    by (metis add_diff_cancel_right' idiff_enat_enat inc.simps(2) numeral_inc) 

  have "(Game.weight c d2) (E 9 9) = (E 9 9) - (E 1 0)" using weight_opt.simps(6)by simp
  hence "(Game.weight c d2) (E 9 9) = E 8 9" using A7 by simp
  hence A8: "Game.in_wina ((Game.weight c d2) (E 9 9)) d2" using A4 by simp

  thus "Game.in_wina (E 9 9) c" using A7 Game.in_wina.intros(3) energy.distinct(1) A2 A1 A6 by blast  
qed


lemma attacker_does_not_win_example:
  shows "\<not>Game.in_wina (E 0 0) c"
proof -
  have "order (E 0 0) (E 0 1)" by simp
  hence "((E 0 0) - (E 0 1)) = eneg" using minus_energy_def by auto
  hence "(Game.weight c d1)(E 0 0) = eneg" by simp
  hence A1: "\<not>(Game.in_wina ((Game.weight c d1)(E 0 0)) d1)" by (metis Game.in_wina.cases)

  have "order (E 0 0) (E 1 0)" by simp
  hence "((E 0 0) - (E 1 0)) = eneg" using minus_energy_def by auto
  hence "(Game.weight c d2)(E 0 0) = eneg" by simp
  hence A2: "\<not>(Game.in_wina ((Game.weight c d2)(E 0 0)) d2)" by (metis Game.in_wina.cases)

  have "\<forall>g'. (c \<Zinj> g') \<longrightarrow> (g' = d1 \<or> g' = d2)"
    by (metis moves(9) state.exhaust weight_opt.simps(21) weight_opt.simps(22) weight_opt.simps(23) weight_opt.simps(24))
  hence "(\<forall>g'. ((c \<Zinj> g') \<longrightarrow> \<not>(Game.in_wina ((Game.weight c g') (E 0 0)) g')))" using A1 A2 by blast
  hence "\<not>((defender c) \<and>(\<forall>g'. ((c \<Zinj> g') \<longrightarrow> (Game.in_wina ((Game.weight c g') (E 0 0)) g'))) \<and> ((E 0 0) \<noteq> eneg))"
    using moves(6) by blast
  thus "\<not>Game.in_wina (E 0 0) c" using Game.in_wina.intros by (metis Game.in_wina.cases defender.simps(3))
qed


end