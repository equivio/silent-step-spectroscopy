theory ExampleInstantiation      
  imports EnergyGames "HOL-Library.Extended_Nat"
begin

datatype energy = E (one: "enat") (two: "enat")

instantiation energy :: minus
begin
definition minus_energy_def: "e1 - e2 \<equiv> E ((one e1) - (one e2)) ((two e1) - (two e2))"

instance ..

lemma energy_minus[simp]:
  shows "E a b - E c d = E (a - c) (b - d)" using minus_energy_def by simp
end

definition "min_update e1 \<equiv> E (min (one e1) (two e1)) (two e1)" 

lemma min_update[simp]:
  shows "min_update (E a b) = E (min a b) b" unfolding min_update_def using energy.sel by fastforce

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

fun defender :: "state \<Rightarrow> bool" where
  "defender b1 = True" |
  "defender b2 = True" |
  "defender c = True" |
  "defender e = True" |
  "defender _ = False"

interpretation Game: energy_game "a" "E 10 10" "weight_opt" "defender" "E 0 0" .

notation Game.moves (infix "\<Zinj>" 70)
abbreviation "finite_play \<equiv> Game.finite_play"

lemma moves:
  shows "a \<Zinj> b1" "a \<Zinj> b2"
       "b1 \<Zinj> c" "b2 \<Zinj> c"
       "c \<Zinj> d1" "c \<Zinj> d2"
       "d1 \<Zinj> e" "d2 \<Zinj> e"
  by simp+

lemma Game_finite_play_example:
  shows "finite_play [a, b2, c, d1, e]"
proof-
  have "finite_play [a]" by (rule Game.finite_play.intros(1))
  hence "finite_play [a, b2]" using Game.finite_play.intros(2) by fastforce
  hence "finite_play [a, b2, c]" using Game.finite_play.intros(2) by fastforce
  hence "finite_play [a, b2, c, d1]" using Game.finite_play.intros(2) by fastforce
  thus "finite_play [a, b2, c, d1, e]" using  Game.finite_play.intros(2) by fastforce
qed

abbreviation "energy_level \<equiv> Game.energy_level"

lemma energy_level_example:
  shows "energy_level [a, b2, c, d1, e] = E 9 8"
proof-
  let ?p="[a, b2, c, d1, e]"
  from Game_finite_play_example Game.energy_level_fold_eq[of "?p"] have "energy_level ?p = 
    id ((min_update (E 10 10 - E 0 1)) - E 0 1)" by simp
  also have "... = id ((min_update (E 10 9)) - E 0 1)" by (simp add: numeral_eq_enat one_enat_def)
  also have "... = id (E 9 9 - E 0 1)" by simp
  also have "... = id (E 9 8)" by (simp add: numeral_eq_enat one_enat_def)
  also have "... = E 9 8" by simp
  finally show ?thesis .
qed

end