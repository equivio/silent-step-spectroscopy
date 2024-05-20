section\<open>Instantiation of an Energy Game\<close>

theory Example_Instantiation
  imports Energy_Games "HOL-Library.Extended_Nat"
begin
text \<open>In this theory, we create an instantiation of a two-dimensional energy game to test our definitions.\<close>

subsection\<open>Two-Dimensional Energies\<close>

text \<open>We first define energies in a similar manner to our definition of energies with eight dimensions.
We use \<open>eneg\<close> when the energy level is equal to or lower than the \<open>defender_win_level\<close>. We define 
component-wise subtraction and the update \<open>min_update\<close> where the first component is replaced by the minimum of both entries.\<close>

datatype energy = E (one: "enat") (two: "enat")

abbreviation "direct_minus e1 e2 \<equiv> E ((one e1) - (one e2)) ((two e1) - (two e2))"


instantiation energy :: order
begin

fun less_eq_energy:: "energy \<Rightarrow> energy \<Rightarrow> bool" where 
  "less_eq_energy (E ea1 ea2) (E eb1 eb2) = (ea1 \<le> eb1 \<and> ea2 \<le> eb2)"

fun less_energy:: "energy \<Rightarrow> energy \<Rightarrow> bool" where 
  "less_energy eA eB = (eA \<le> eB \<and> \<not> eB \<le> eA)"

instance proof standard
  fix eA eB :: energy
  show \<open>(eA < eB) = (eA \<le> eB \<and> \<not> eB \<le> eA)\<close> by auto
next
  fix e :: energy
  show \<open>e \<le> e\<close> 
    using less_eq_energy.elims(3) by fastforce
next
  fix eA eB eC:: energy
  assume \<open>eA \<le> eB\<close> \<open>eB \<le> eC\<close>
  thus \<open>eA \<le> eC\<close>
    by (smt (verit, del_insts) energy.inject less_eq_energy.elims order.trans)
next
  fix eA eB :: energy
  assume \<open>eA \<le> eB\<close> \<open>eB \<le> eA\<close>
  thus \<open>eA = eB\<close>
    using less_eq_energy.elims(2) by fastforce
qed
end

fun order_opt:: "energy option \<Rightarrow> energy option \<Rightarrow> bool" where 
  "order_opt (Some eA) (Some eB) = (eA \<le> eB)" |
  "order_opt None _ = True" |
  "order_opt (Some eA) None = False"

definition minus_energy_def[simp]: "minus_energy e1 e2 \<equiv> if (\<not>e2 \<le> e1) then None
                                             else Some (direct_minus e1 e2)"
lemma energy_minus[simp]:
  assumes "E c d \<le> E a b"
  shows "minus_energy (E a b) (E c d) = Some (E (a - c) (b - d))" using assms by auto

definition min_update_def[simp]: "min_update e1 \<equiv> Some (E (min (one e1) (two e1)) (two e1))"

subsection\<open>Energy Game Example\<close>

text \<open>In preparation for our instantiation, we define our states, the updates for our energy levels and which states are defender positions.\<close>
datatype state = a | b1 | b2 | c | d1 | d2 | e

fun weight_opt :: "state \<Rightarrow> state \<Rightarrow> energy update option" where
  "weight_opt a b1 = Some (\<lambda>x. minus_energy x (E 1 0))" |
  "weight_opt a b2 = Some (\<lambda>x. minus_energy x (E 0 1))" |
  "weight_opt b1 c = Some Some" |
  "weight_opt b2 c = Some min_update" |
  "weight_opt c d1 = Some (\<lambda>x. minus_energy x (E 0 1))" |
  "weight_opt c d2 = Some (\<lambda>x. minus_energy x (E 1 0))" |
  "weight_opt d1 e = Some Some" |
  "weight_opt d2 e = Some Some" |
  "weight_opt _ _ = None"

find_theorems weight_opt

fun defender :: "state \<Rightarrow> bool" where
  "defender b1 = True" |
  "defender b2 = True" |
  "defender c = True" |
  "defender e = True" |
  "defender _ = False"

text\<open>Now, we can state our energy game example.\<close>

interpretation Game: energy_game "weight_opt" "defender" "(\<le>)" 
proof
  fix g g' and e e' eu eu' :: energy
  show "e \<le> e' \<Longrightarrow> e' \<le> e \<Longrightarrow> e = e'" by auto

  assume case_assms: "e \<le> e'"
   "the (weight_opt g g') e = Some eu" "the (weight_opt g g') e' = Some eu'"
   "weight_opt g g' \<noteq> None"
  hence Y: "weight_opt g g' = Some Some \<or> weight_opt g g' = Some min_update \<or> weight_opt g g' = Some (\<lambda>x. minus_energy x (E 1 0)) \<or> weight_opt g g' = Some (\<lambda>x. minus_energy x (E 0 1))"
    using weight_opt.simps by (smt (verit, del_insts) defender.cases) 
  then consider (id) "weight_opt g g' = Some Some" | (min) "weight_opt g g' = Some min_update" |(10) " weight_opt g g' = Some (\<lambda>x. minus_energy x (E 1 0))" | (01) " weight_opt g g' = Some (\<lambda>x. minus_energy x (E 0 1))" by auto

  (*from Y consider (id) "weight_opt g g' = Some Some" | (min) "weight_opt g g' = Some min_update" |(10) " weight_opt g g' = Some (\<lambda>x. minus_energy x (E 1 0))" | (01) " weight_opt g g' = Some (\<lambda>x. minus_energy x (E 0 1))" by auto*)
  then show "eu \<le> eu'"
  proof (cases)
    case id
    then show ?thesis
      using case_assms by auto 
  next
    case min
    hence \<open>min_update e = Some eu\<close> \<open>min_update e' = Some eu'\<close> using case_assms by auto 
    then show ?thesis
      using case_assms(1) by (cases e, cases e', auto simp add: min_le_iff_disj)
  next
    case 10
    hence \<open>minus_energy e (E 1 0) = Some eu\<close> \<open>minus_energy e' (E 1 0) = Some eu'\<close> using case_assms by auto 
    then show ?thesis using case_assms(1)
      by (cases e, cases e', auto,
         metis add.commute add_diff_assoc_enat energy.sel idiff_0_right le_iff_add less_eq_energy.simps option.distinct(1) option.inject)
  next
    case 01
    hence \<open>minus_energy e (E 0 1) = Some eu\<close> \<open>minus_energy e' (E 0 1) = Some eu'\<close> using case_assms by auto 
    then show ?thesis  using case_assms(1)
      by (cases e, cases e', auto,
         metis add.commute add_diff_assoc_enat energy.sel idiff_0_right le_iff_add less_eq_energy.simps option.distinct(1) option.inject)
  qed
next
  fix g g' e e'
  assume \<open>e \<le> e'\<close> \<open>weight_opt g g' \<noteq> None\<close> \<open>the (weight_opt g g') e' = None\<close>
  thus \<open>the (weight_opt g g') e = None\<close>
    by (induct g) (induct g', auto simp add: order.trans)+
qed

notation Game.moves (infix "\<Zinj>" 70)

lemma moves:
  shows "a \<Zinj> b1" "a \<Zinj> b2"
       "b1 \<Zinj> c" "b2 \<Zinj> c"
       "c \<Zinj> d1" "c \<Zinj> d2"
       "d1 \<Zinj> e" "d2 \<Zinj> e"
       "\<not>(c \<Zinj> e)" "\<not>(e \<Zinj> d1)"
  by simp+

subsection\<open>Checking Definitions\<close>

text \<open>Our definition of winning budgets.\<close>

lemma wina_of_e:
  shows "Game.attacker_wins (E 9 8) e"
  by (simp add: Game.attacker_wins.Defense)

lemma wina_of_e_exist:
  shows "\<exists>e1. Game.attacker_wins e1 e" 
  using wina_of_e by blast

lemma attacker_wins_at_e: 
  shows "\<forall>e'. Game.attacker_wins e' e"
  by (simp add: Game.attacker_wins.Defense)

lemma wina_of_d1:
  shows "Game.attacker_wins (E 9 8) d1" 
proof -
  have A1: "\<not>(defender d1)" by simp
  have A2: "d1 \<Zinj> e" by simp
  have A3: "Game.attacker_wins (E 9 8) e" by (rule wina_of_e)
  have Aid: "Game.weight d1 e = Some" by simp
  hence "(Game.weight d1 e (E 9 8)) = Some (E 9 8) " by simp
  hence "(Game.attacker_wins (the ((Game.weight d1 e (E 9 8)))) e)" using A3 by simp
  from this A3 have A4: "\<not>(defender d1) \<and> (\<exists>g'. ((d1 \<Zinj> g') \<and> (Game.attacker_wins (the ((Game.weight d1 g' (E 9 8)))) g')))"
    by (meson A1 A2 Game.attacker_wins.Defense defender.simps(4) weight_opt.simps(38))
  thus "Game.attacker_wins (E 9 8) d1" using Game.attacker_wins.Attack A2 Aid wina_of_e by presburger
qed

lemma wina_of_d2:
  shows "Game.attacker_wins (E 8 9) d2" 
proof -
  have A1: "\<not>(defender d2)" by simp
  have A2: "d2 \<Zinj> e" by simp
  have A3: "Game.attacker_wins (E 8 9) e" by (simp add: attacker_wins_at_e)
  have Aid: "Game.weight d2 e = Some" by simp
  hence "(Game.weight d2 e (E 8 9)) = Some (E 8 9) " by simp
  hence "(Game.attacker_wins (the ((Game.weight d2 e (E 8 9)))) e)" using A3 by simp
  from this A3 have A4: "\<not>(defender d2) \<and> (\<exists>g'. ((d2 \<Zinj> g') \<and> (Game.attacker_wins (the ((Game.weight d2 g' (E 8 9)))) g')))"
    by (meson A1 A2 Game.attacker_wins.Defense defender.simps(4) weight_opt.simps(38))
  thus "Game.attacker_wins (E 8 9) d2" using Game.attacker_wins.Attack A2 A3 Aid wina_of_e by presburger
qed

lemma wina_of_c:
  shows "Game.attacker_wins (E 9 9) c"
proof -
  have A1: "defender c" by auto
  have A2: "\<forall>g'. (c \<Zinj> g') \<longrightarrow> (g' = d1 \<or> g' = d2)"
    by (metis moves(9) state.exhaust weight_opt.simps(21) weight_opt.simps(22) weight_opt.simps(23) weight_opt.simps(24))
  have A3: "Game.attacker_wins (E 9 8) d1" using wina_of_d1 by blast
  have A4: "Game.attacker_wins (E 8 9) d2" using wina_of_d2 by blast

  have "\<not>(E 9 9) \<le> (E 0 1)" by simp
  hence "minus_energy (E 9 9) (E 0 1) = Some (E ((one (E 9 9)) - (one (E 0 1))) ((two (E 9 9)) - (two (E 0 1))))"
    by simp
  hence A5: "minus_energy (E 9 9) (E 0 1) = Some (E 9 8)"
    using numeral_eq_enat one_enat_def
    by (auto, metis diff_Suc_1 eval_nat_numeral(3) idiff_enat_enat)

  have "(Game.weight c d1) (E 9 9) = minus_energy (E 9 9) (E 0 1)" using weight_opt.simps(5) by simp
  hence A56: "(Game.weight c d1) (E 9 9) = Some (E 9 8)" using A5 by simp
  hence A6: "Game.attacker_wins (the ((Game.weight c d1) (E 9 9))) d1" using A3 by simp

  have "\<not>(E 9 9) \<le> (E 1 0)" by simp
  hence "minus_energy (E 9 9) (E 1 0) = Some (E ((one (E 9 9)) - (one (E 1 0))) ((two (E 9 9)) - (two (E 1 0))))"
    by simp
  hence A7: "minus_energy (E 9 9) (E 1 0) = Some (E 8 9)"
    using numeral_eq_enat one_enat_def
    by (simp, metis add_diff_cancel_right' idiff_enat_enat inc.simps(2) numeral_inc) 

  have "(Game.weight c d2) (E 9 9) = minus_energy (E 9 9) (E 1 0)"
    using weight_opt.simps(6)by simp
  moreover hence "(Game.weight c d2) (E 9 9) = Some (E 8 9)"
    using A7 by simp
  moreover hence "Game.attacker_wins (the ((Game.weight c d2) (E 9 9))) d2"
    using A4 by simp
  ultimately show "Game.attacker_wins (E 9 9) c"
    using A7 Game.attacker_wins.Defense A2 A1 A6  wina_of_d1 wina_of_d2 A56  by blast    
qed

lemma not_wina_of_c:
  shows "\<not>Game.attacker_wins (E 0 0) c"
proof -
  have "E 0 0 \<le> E 0 1" by simp
  hence "minus_energy (E 0 0) (E 0 1) = None" by auto
  hence no_win_a: "(Game.weight c d1) (E 0 0) = None" by simp
  have "(E 0 0) \<le> (E 1 0)" by simp
  hence "minus_energy (E 0 0) (E 1 0) = None" by auto
  hence no_win_b: "(Game.weight c d2)(E 0 0) = None" by simp
  have "\<forall>g'. (c \<Zinj> g') \<longrightarrow> (g' = d1 \<or> g' = d2)"
    by (metis moves(9) state.exhaust weight_opt.simps(21) weight_opt.simps(22) weight_opt.simps(23) weight_opt.simps(24))
  thus "\<not>Game.attacker_wins (E 0 0) c"
    using no_win_a no_win_b Game.attacker_wins.intros Game.attacker_wins.cases
    by (metis moves(5) option.distinct(1))
qed

end