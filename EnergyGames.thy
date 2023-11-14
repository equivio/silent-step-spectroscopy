section "Energy Games"

theory EnergyGames
  imports Main
begin

section \<open>Energy Games\<close>

type_synonym 'gstate move = "'gstate \<times> 'gstate"
type_synonym 'energy update = "'energy \<Rightarrow> 'energy"
(******************Basic Game Definitions******************************************)
locale energy_game =
  fixes g0 :: "'gstate" and
        e0 :: "'energy" and
        moves :: "'gstate move set" and
        weight :: "'gstate \<Rightarrow> 'gstate \<Rightarrow> 'energy update" ("w") and
        defender :: "'gstate \<Rightarrow> bool" ("Gd") and 
        defender_win_level :: "'energy"
begin

abbreviation attacker :: "'gstate \<Rightarrow> bool" ("Ga") where "Ga p \<equiv> \<not> Gd p" 

abbreviation move (infix "\<Zinj>" 70) where "g1 \<Zinj> g2 \<equiv> (g1, g2) \<in> moves"

abbreviation weighted_move :: "'gstate \<Rightarrow> 'energy update \<Rightarrow> 'gstate \<Rightarrow>  bool" ("_ \<Zinj>w _ _" [60,60,60] 70) where
  "weighted_move g1 u g2 \<equiv> g1 \<Zinj> g2 \<and> (weight g1 g2 = u)"

subsection \<open>Finite Plays\<close>
(*Definition of a finite_play as (finite) paths*)
inductive finite_play :: "'gstate list \<Rightarrow> bool" where
  "finite_play [g0]" |
  "finite_play ([gn] @ p)" if "finite_play p" and "last p \<Zinj> gn" (*missing: dealing with weight*)

(*Definition of Round*)
inductive round:: "'gstate  \<Rightarrow> 'gstate \<Rightarrow> nat \<Rightarrow> bool" where
  "round g0 g0 0" |
  "round g gs (Suc n)" if "\<exists>gp. round gp g n \<and> gp \<Zinj> g"  (*missing: dealing with weight*)

(*Definition of Energy Level of a round i*)

(*fun energy_level:: "'gstate \<Rightarrow> 'gstate \<Rightarrow> 'energy"
  where
    "energy_level g0 g0 = e0" | 
    "energy_level g gs= weight g gs" *)
    (*"energy_level g gs = undefined" if "u < defender_win_level"*) (*ordering of energy level necessary*)

(*abbreviation "finite_energy_level p \<equiv> round_finite_energy_level p (length p)" 

abbreviation "play_stuck p \<equiv> \<nexists>ps. finite_play (p @ ps)" 

abbreviation "is_defender_turn p \<equiv> Gd (last p)"
abbreviation "is_attacker_turn p \<equiv> Ga (last p)"

definition defender_won :: "'gstate list \<Rightarrow> bool" where
  "defender_won \<equiv> \<exists>n. finite_energy_level p n "
definition attacker_won :: "'gstate list \<Rightarrow> bool" where 
  "attacker_won p \<equiv> \<forall>n. finite_energy_level p n \<noteq> defender_win_level \<and> is_defender_turn p \<and> play_stuck p" 
*)
(*****************Strategies and Winning Budgets******************************************)
end \<comment> \<open>end of context energy_game\<close>

end
