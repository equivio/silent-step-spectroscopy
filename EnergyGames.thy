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
      assumes win_is_stuck: "(weight g1 g2) defender_win_level = defender_win_level" and
              weight_well_def: "(weight g1 g2) e1 \<noteq> undefined" and
              e0: "e0 \<noteq> undefined"
begin

abbreviation attacker :: "'gstate \<Rightarrow> bool" ("Ga") where "Ga p \<equiv> \<not> Gd p" 

abbreviation move (infix "\<Zinj>" 70) where "g1 \<Zinj> g2 \<equiv> (g1, g2) \<in> moves"

abbreviation weighted_move :: "'gstate \<Rightarrow> 'energy update \<Rightarrow> 'gstate \<Rightarrow>  bool" ("_ \<Zinj>w _ _" [60,60,60] 70) where
  "weighted_move g1 u g2 \<equiv> g1 \<Zinj> g2 \<and> (weight g1 g2 = u)"

fun energy_level :: "'gstate list \<Rightarrow> 'energy" where
  "energy_level p = (if p = [g0] then e0 else (
    if (\<exists>gn p'. p' @ [gn] = p) then ((weight (last (THE p'. \<exists>gn. p' @ [gn] = p)) (THE gn. \<exists>p'. p' @ [gn] = p)) 
      (energy_level (THE p'. \<exists>gn. p' @ [gn] = p))) 
    else undefined))"

lemma energy_level_def1:
  shows "energy_level [g0] = e0"
  by simp

lemma energy_level_def2:
  assumes "p' \<noteq> []"
  shows "energy_level (p' @ [gn]) = weight (last p') gn (energy_level p')"
proof-
  define p where p_def: "p \<equiv> p' @ [gn]"
  have p'_eq: "(THE p'. \<exists>gn. p' @ [gn] = p) = p'" unfolding p_def by simp
  have gn_eq: "(THE gn. \<exists>p'. p' @ [gn] = p) = gn" unfolding p_def by simp

  thus ?thesis unfolding p_def using p'_eq gn_eq assms p_def by simp
qed

lemma energy_level_def3:
  shows "energy_level [] = undefined"
  by simp

lemma energy_level_def4:
  assumes "p \<noteq> []" "hd p = g0"  
  shows "energy_level p \<noteq> undefined"
using assms proof(induct p rule: rev_induct)
  case Nil
  thus ?case by simp
next
  case (snoc x xs)
  thus ?case proof(cases "xs = []")
    case True
    hence "xs @ [x] = [x]" by simp
    with snoc(3) have "x = g0" by simp
    hence "energy_level [x] = e0" by simp
    thus ?thesis unfolding \<open>xs @ [x] = [x]\<close> using e0 by simp
  next
    case False
    then show ?thesis 
      using energy_level_def2 weight_well_def by simp
  qed
qed

subsection \<open>Finite Plays\<close>
inductive finite_play :: "'gstate list \<Rightarrow> bool" where
  "finite_play [g0]" |
  "finite_play (p @ [gn])" if "finite_play p" and "last p \<Zinj> gn" and "(w (last p) gn) (energy_level p) \<noteq> defender_win_level"

lemma finite_play_prefix:
  assumes "finite_play (a @ b)" "a \<noteq> []"
  shows "finite_play a"
using assms proof(induct "a @ b" arbitrary: b rule: finite_play.induct)
  case 1
  thus ?case
    by (metis Nil_is_append_conv butlast_append butlast_snoc finite_play.simps)
next
  case (2 p gn)
  thus ?case
    by (metis butlast_append butlast_snoc finite_play.intros(2))
qed

corollary finite_play_suffix:
  assumes "finite_play (p @ [gn])" and "p \<noteq> []"
  shows "finite_play p"
  using assms finite_play_prefix by fast

fun pairs :: "'a list \<Rightarrow> ('a \<times> 'a) list" where
  "pairs p = (if length p \<le> 1 then [] else (hd p, hd (tl p)) # pairs (tl p))"

(* some intuiton on this definition*)
lemma "pairs [1,2,3] = [(1,2), (2,3)]" by simp
lemma empty_pair: "pairs [] = []" by simp
lemma single_pair: "pairs [x] = []" by simp
lemma pairs_append_single: "pairs (p @ [gn]) = (if length p \<ge> 1 then (pairs p) @ [((last p), gn)] else [])" oops

lemma energy_level_fold_eq:
  assumes "finite_play p"
  shows "energy_level p = fold (\<lambda>g e. (weight (fst g) (snd g)) e) (pairs p) e0"
using assms proof (induct "p" rule: finite_play.induct)
  case 1
  thus ?case unfolding single_pair[of "g0"] fold_Nil by simp
next
  case (2 p gn)
  then show ?case sorry
qed

abbreviation "play_stuck p \<equiv>  \<nexists>ps. finite_play (p @ ps)" (*only check wheter p is currently stucked*)

abbreviation "is_defender_turn p \<equiv> Gd (last p)"
abbreviation "is_attacker_turn p \<equiv> Ga (last p)"

lemma next_turn:
  fixes p
  shows "is_defender_turn p \<or> is_attacker_turn p"
by simp

definition won_by_defender:: "'gstate list \<Rightarrow> bool" where
  "won_by_defender p \<equiv> play_stuck p \<and> is_attacker_turn p"

definition won_by_attacker:: "'gstate list \<Rightarrow> bool" where
  "won_by_attacker p \<equiv> play_stuck p \<and> is_defender_turn p"

definition no_winner:: "'gstate list \<Rightarrow> bool" where
  "no_winner p \<equiv> \<not>play_stuck p"

lemma winner:
  fixes p
  shows "won_by_defender p \<or> won_by_attacker p \<or> no_winner p"
  using no_winner_def won_by_attacker_def won_by_defender_def by auto
end \<comment> \<open>end of context energy_game\<close>

end
