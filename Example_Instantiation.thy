subsection \<open>Instantiation of an Energy Game\<close>

theory Example_Instantiation
  imports Energy_Games "HOL-Library.Extended_Nat"
begin

text \<open>In this theory, we create an instantiation of a two-dimensional energy game to test our definitions.\<close>

text \<open>We first define energies in a similar manner to our definition of energies with two dimensions. We define component-wise subtraction.\<close>

datatype energy = E (one: \<open>enat\<close>) (two: \<open>enat\<close>)

abbreviation \<open>direct_minus e1 e2 \<equiv> E ((one e1) - (one e2)) ((two e1) - (two e2))\<close>

instantiation energy :: order
begin

fun less_eq_energy:: \<open>energy \<Rightarrow> energy \<Rightarrow> bool\<close> where
  \<open>less_eq_energy (E ea1 ea2) (E eb1 eb2) = (ea1 \<le> eb1 \<and> ea2 \<le> eb2)\<close>

fun less_energy:: \<open>energy \<Rightarrow> energy \<Rightarrow> bool\<close> where
  \<open>less_energy eA eB = (eA \<le> eB \<and> \<not> eB \<le> eA)\<close>

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

fun order_opt:: \<open>energy option \<Rightarrow> energy option \<Rightarrow> bool\<close> where
  \<open>order_opt (Some eA) (Some eB) = (eA \<le> eB)\<close> |
  \<open>order_opt None _ = True\<close> |
  \<open>order_opt (Some eA) None = False\<close>

definition minus_energy_def[simp]: \<open>minus_energy e1 e2 \<equiv> if (\<not>e2 \<le> e1) then None
                                             else Some (direct_minus e1 e2)\<close>
lemma energy_minus[simp]:
  assumes \<open>E c d \<le> E a b\<close>
  shows \<open>minus_energy (E a b) (E c d) = Some (E (a - c) (b - d))\<close> using assms by auto

definition min_update_def[simp]: \<open>min_update e1 \<equiv> Some (E (min (one e1) (two e1)) (two e1))\<close>

text \<open>In preparation for our instantiation, we define our states, the updates for our energy levels and which states are defender positions.\<close>
datatype state = a | b1 | b2 | c | d1 | d2 | e

fun weight_opt :: \<open>state \<Rightarrow> state \<Rightarrow> energy update option\<close> where
  \<open>weight_opt a b1 = Some (\<lambda>x. minus_energy x (E 1 0))\<close> |
  \<open>weight_opt a b2 = Some (\<lambda>x. minus_energy x (E 0 1))\<close> |
  \<open>weight_opt a _  = None\<close>  |
  \<open>weight_opt b1 c = Some Some\<close> |
  \<open>weight_opt b1 _  = None\<close>  |
  \<open>weight_opt b2 c = Some min_update\<close> |
  \<open>weight_opt b2 _  = None\<close>  |
  \<open>weight_opt c d1 = Some (\<lambda>x. minus_energy x (E 0 1))\<close> |
  \<open>weight_opt c d2 = Some (\<lambda>x. minus_energy x (E 1 0))\<close> |
  \<open>weight_opt c _  = None\<close>  |
  \<open>weight_opt d1 e = Some Some\<close> |
  \<open>weight_opt d1 _  = None\<close>  |
  \<open>weight_opt d2 e = Some Some\<close> |
  \<open>weight_opt d2 _  = None\<close> |
  \<open>weight_opt e _  = None\<close>

find_theorems weight_opt

fun defender :: \<open>state \<Rightarrow> bool\<close> where
  \<open>defender b1 = True\<close> |
  \<open>defender b2 = True\<close> |
  \<open>defender c = True\<close> |
  \<open>defender e = True\<close> |
  \<open>defender _ = False\<close>

text\<open>Now, we can state our energy game example.\<close>

interpretation Game: energy_game \<open>weight_opt\<close> \<open>defender\<close> \<open>(\<le>)\<close>
proof
  fix g g' and e e' eu eu' :: energy
  show \<open>e \<le> e' \<Longrightarrow> e' \<le> e \<Longrightarrow> e = e'\<close> by auto

  assume case_assms: \<open>e \<le> e'\<close>
   \<open>the (weight_opt g g') e = Some eu\<close> \<open>the (weight_opt g g') e' = Some eu'\<close>
   \<open>weight_opt g g' \<noteq> None\<close>
  hence Y: \<open>weight_opt g g' = Some Some \<or> weight_opt g g' = Some min_update \<or> weight_opt g g' = Some (\<lambda>x. minus_energy x (E 1 0)) \<or> weight_opt g g' = Some (\<lambda>x. minus_energy x (E 0 1))\<close>
    using weight_opt.simps by (smt (verit, del_insts) defender.cases)
  then consider (id) \<open>weight_opt g g' = Some Some\<close> | (min) \<open>weight_opt g g' = Some min_update\<close> |(10) \<open> weight_opt g g' = Some (\<lambda>x. minus_energy x (E 1 0))\<close> | (01) \<open> weight_opt g g' = Some (\<lambda>x. minus_energy x (E 0 1))\<close> by auto

  (*from Y consider (id) \<open>weight_opt g g' = Some Some\<close> | (min) \<open>weight_opt g g' = Some min_update\<close> |(10) \<open> weight_opt g g' = Some (\<lambda>x. minus_energy x (E 1 0))\<close> | (01) \<open> weight_opt g g' = Some (\<lambda>x. minus_energy x (E 0 1))\<close> by auto*)
  then show \<open>eu \<le> eu'\<close>
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

notation Game.moves (infix \<open>\<Zinj>\<close> 70)

lemma moves:
  shows \<open>a \<Zinj> b1\<close> \<open>a \<Zinj> b2\<close>
       \<open>b1 \<Zinj> c\<close> \<open>b2 \<Zinj> c\<close>
       \<open>c \<Zinj> d1\<close> \<open>c \<Zinj> d2\<close>
       \<open>d1 \<Zinj> e\<close> \<open>d2 \<Zinj> e\<close>
       \<open>\<not>(c \<Zinj> e)\<close> \<open>\<not>(e \<Zinj> d1)\<close>
  by simp+

text \<open>Our definition of winning budgets.\<close>

lemma wina_of_e:
  shows \<open>Game.attacker_wins (E 9 8) e\<close>
  by (simp add: Game.attacker_wins.Defense)

lemma wina_of_e_exist:
  shows \<open>\<exists>e1. Game.attacker_wins e1 e\<close>
  using wina_of_e by blast

lemma attacker_wins_at_e:
  shows \<open>\<forall>e'. Game.attacker_wins e' e\<close>
  by (simp add: Game.attacker_wins.Defense)

lemma wina_of_d1:
  shows \<open>Game.attacker_wins (E 9 8) d1\<close>
proof -
  have A1: \<open>\<not>(defender d1)\<close> by simp
  have A2: \<open>d1 \<Zinj> e\<close> by simp
  have A3: \<open>Game.attacker_wins (E 9 8) e\<close> by (rule wina_of_e)
  have Aid: \<open>Game.weight d1 e = Some\<close> by simp
  hence \<open>(Game.weight d1 e (E 9 8)) = Some (E 9 8)\<close> by simp
  hence \<open>(Game.attacker_wins (the ((Game.weight d1 e (E 9 8)))) e)\<close> using A3 by simp
  from this A3 have A4: \<open>\<not>(defender d1) \<and> (\<exists>g'. ((d1 \<Zinj> g') \<and> (Game.attacker_wins (the ((Game.weight d1 g' (E 9 8)))) g')))\<close>
    by (meson A1 A2 Game.attacker_wins.Defense defender.simps(4) weight_opt.simps(38))
  thus \<open>Game.attacker_wins (E 9 8) d1\<close> using Game.attacker_wins.Attack A2 Aid wina_of_e by presburger
qed

lemma wina_of_d2:
  shows \<open>Game.attacker_wins (E 8 9) d2\<close>
proof -
  have A1: \<open>\<not>(defender d2)\<close> by simp
  have A2: \<open>d2 \<Zinj> e\<close> by simp
  have A3: \<open>Game.attacker_wins (E 8 9) e\<close> by (simp add: attacker_wins_at_e)
  have Aid: \<open>Game.weight d2 e = Some\<close> by simp
  hence \<open>(Game.weight d2 e (E 8 9)) = Some (E 8 9)\<close> by simp
  hence \<open>(Game.attacker_wins (the ((Game.weight d2 e (E 8 9)))) e)\<close> using A3 by simp
  from this A3 have A4: \<open>\<not>(defender d2) \<and> (\<exists>g'. ((d2 \<Zinj> g') \<and> (Game.attacker_wins (the ((Game.weight d2 g' (E 8 9)))) g')))\<close>
    by (meson A1 A2 Game.attacker_wins.Defense defender.simps(4) weight_opt.simps(38))
  thus \<open>Game.attacker_wins (E 8 9) d2\<close> using Game.attacker_wins.Attack A2 A3 Aid wina_of_e by presburger
qed

lemma wina_of_c:
  shows \<open>Game.attacker_wins (E 9 9) c\<close>
proof -
  have A1: \<open>defender c\<close> by auto
  have A2: \<open>\<forall>g'. (c \<Zinj> g') \<longrightarrow> (g' = d1 \<or> g' = d2)\<close>
    by (metis moves(9) state.exhaust weight_opt.simps(24,25,26,27))
  have A3: \<open>Game.attacker_wins (E 9 8) d1\<close> using wina_of_d1 by blast
  have A4: \<open>Game.attacker_wins (E 8 9) d2\<close> using wina_of_d2 by blast

  have \<open>\<not>(E 9 9) \<le> (E 0 1)\<close> by simp
  hence \<open>minus_energy (E 9 9) (E 0 1) = Some (E ((one (E 9 9)) - (one (E 0 1))) ((two (E 9 9)) - (two (E 0 1))))\<close>
    by simp
  hence A5: \<open>minus_energy (E 9 9) (E 0 1) = Some (E 9 8)\<close>
    using numeral_eq_enat one_enat_def
    by (auto, metis diff_Suc_1 eval_nat_numeral(3) idiff_enat_enat)

  have \<open>(Game.weight c d1) (E 9 9) = minus_energy (E 9 9) (E 0 1)\<close> using weight_opt.simps(5) by simp
  hence A56: \<open>(Game.weight c d1) (E 9 9) = Some (E 9 8)\<close> using A5 by simp
  hence A6: \<open>Game.attacker_wins (the ((Game.weight c d1) (E 9 9))) d1\<close> using A3 by simp

  have \<open>\<not>(E 9 9) \<le> (E 1 0)\<close> by simp
  hence \<open>minus_energy (E 9 9) (E 1 0) = Some (E ((one (E 9 9)) - (one (E 1 0))) ((two (E 9 9)) - (two (E 1 0))))\<close>
    by simp
  hence A7: \<open>minus_energy (E 9 9) (E 1 0) = Some (E 8 9)\<close>
    using numeral_eq_enat one_enat_def
    by (simp, metis add_diff_cancel_right' idiff_enat_enat inc.simps(2) numeral_inc)

  have \<open>(Game.weight c d2) (E 9 9) = minus_energy (E 9 9) (E 1 0)\<close>
    using weight_opt.simps(6)by simp
  moreover hence \<open>(Game.weight c d2) (E 9 9) = Some (E 8 9)\<close>
    using A7 by simp
  moreover hence \<open>Game.attacker_wins (the ((Game.weight c d2) (E 9 9))) d2\<close>
    using A4 by simp
  ultimately show \<open>Game.attacker_wins (E 9 9) c\<close>
    using A7 Game.attacker_wins.Defense A2 A1 A6  wina_of_d1 wina_of_d2 A56 by blast
qed

lemma not_wina_of_c:
  shows \<open>\<not>Game.attacker_wins (E 0 0) c\<close>
proof -
  have \<open>E 0 0 \<le> E 0 1\<close> by simp
  hence \<open>minus_energy (E 0 0) (E 0 1) = None\<close> by auto
  hence no_win_a: \<open>(Game.weight c d1) (E 0 0) = None\<close> by simp
  have \<open>(E 0 0) \<le> (E 1 0)\<close> by simp
  hence \<open>minus_energy (E 0 0) (E 1 0) = None\<close> by auto
  hence no_win_b: \<open>(Game.weight c d2)(E 0 0) = None\<close> by simp
  have \<open>\<forall>g'. (c \<Zinj> g') \<longrightarrow> (g' = d1 \<or> g' = d2)\<close>
    by (metis defender.cases moves(9) weight_opt.simps(24,25,26,27))
  thus \<open>\<not>Game.attacker_wins (E 0 0) c\<close>
    using no_win_a no_win_b Game.attacker_wins.intros Game.attacker_wins.cases
    by (metis moves(5) option.distinct(1))
qed

end