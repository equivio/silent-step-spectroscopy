section "Energy Games"

theory EnergyGames
  imports Main Misc
begin

section \<open>Energy Games\<close>

type_synonym 'energy update = "'energy \<Rightarrow> 'energy"
type_synonym 'gstate strategy = "'gstate \<Rightarrow> 'gstate \<Rightarrow> bool"
type_synonym 'gstate fplay = "'gstate list"

locale energy_game =
  fixes g0 :: "'gstate" and
        e0 :: "'energy" and
        weight_opt :: "'gstate \<Rightarrow> 'gstate \<Rightarrow> 'energy update option" and
        defender :: "'gstate \<Rightarrow> bool" ("Gd") and 
        defender_win_level :: "'energy"
begin

abbreviation attacker :: "'gstate \<Rightarrow> bool" ("Ga") where "Ga p \<equiv> \<not> Gd p" 

abbreviation moves :: "'gstate \<Rightarrow> 'gstate \<Rightarrow> bool" (infix "\<Zinj>" 70) where "g1 \<Zinj> g2 \<equiv> weight_opt g1 g2 \<noteq> None"

abbreviation weighted_move :: "'gstate \<Rightarrow> 'energy update \<Rightarrow> 'gstate \<Rightarrow>  bool" ("_ \<Zinj>wgt _ _" [60,60,60] 70) where
  "weighted_move g1 u g2 \<equiv> g1 \<Zinj> g2 \<and> (the (weight_opt g1 g2) = u)"

abbreviation "weight g1 g2 \<equiv> the (weight_opt g1 g2)"

fun energy_level :: "'gstate fplay \<Rightarrow> 'energy" where
  "energy_level p = (
    if p = [g0] then 
      e0 
    else 
      (if (p \<noteq> [] \<and> ((weight_opt (last (butlast p))(last p)) \<noteq> None)) then 
        ((weight (last (butlast p)) (last p)) (energy_level (butlast p))) 
       else 
        undefined))"

lemma %invisible energy_level_def1:
  shows "energy_level [g0] = e0"
  by simp

lemma %invisible energy_level_def2:
  assumes "p' \<noteq> []" and "energy_level p' \<noteq> undefined" and "weight_opt (last p') gn \<noteq> None"  
  shows "energy_level (p' @ [gn]) = weight (last p') gn (energy_level p')"
  using assms by simp

lemma %invisible energy_level_def3:
  shows "energy_level [] = undefined"
  by simp

lemma %invisible energy_level_def4:
  assumes "p \<noteq> []" "hd p = g0" and e0: "e0 \<noteq> undefined" and weight_well_def: "\<And>g1 g2 e1.((weight_opt g1 g2)\<noteq> None \<and> (weight g1 g2) e1 \<noteq> undefined)"
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
inductive finite_play :: "'gstate fplay \<Rightarrow> bool" where
  "finite_play [g0]" |
  "finite_play (p @ [gn])" if "finite_play p" and "last p \<Zinj> gn"

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

lemma finite_play_min_len: "finite_play p \<Longrightarrow> length p \<ge> 1"
  by (metis One_nat_def Suc_le_eq energy_game.finite_play.simps length_greater_0_conv not_Cons_self snoc_eq_iff_butlast)

lemma finite_play_is_trace:
  fixes p
  assumes "finite_play p"
  shows "((p = ((a @ [g]) @ b)) \<and> a \<noteq>[]) \<longrightarrow> ((last a) \<Zinj> g)"
  by (metis assms butlast.simps(2) finite_play.simps finite_play_prefix snoc_eq_iff_butlast)

lemma energy_level_fold_eq:
  assumes "finite_play p"
  shows "energy_level p = fold (\<lambda>(g1, g2) e. (weight g1 g2) e) (pairs p) e0"
using assms proof (induct "p" rule: finite_play.induct)
  case 1
  thus ?case unfolding single_pair[of "g0"] fold_Nil by simp
next
  case (2 p gn)
  have "length p \<ge> 1" using 2(1) finite_play_min_len by auto
  hence pred_eq: "(pairs (p @ [gn])) = (pairs p) @ [(last p, gn)]" using pairs_append_single by metis

  have "fold (\<lambda>(g1, g2). weight g1 g2) [(last p, gn)] = weight (last p) gn" by simp
  hence "fold (\<lambda>(g1, g2). weight g1 g2) ((pairs p) @ [(last p, gn)]) = (weight (last p) gn) \<circ> (fold (\<lambda>(g1, g2). weight g1 g2) (pairs p))" 
    using fold_append by simp
  with 2 show ?case using pred_eq by fastforce
qed

subsection \<open>Winning\<close>
abbreviation "play_stuck p \<equiv> (finite_play p) \<and> (\<nexists>gn. finite_play (p @ [gn]))"

lemma play_stuck_def:
  shows "play_stuck p \<longleftrightarrow> ((finite_play p) \<and> (\<nexists>ps. ps \<noteq> [] \<and> finite_play (p @ ps)))"
proof
  assume asm: "(finite_play p) \<and> (\<nexists>gn. finite_play (p @ [gn]))"
  show "((finite_play p) \<and> (\<nexists>ps. ps \<noteq> [] \<and> finite_play (p @ ps)))" 
  proof(rule ccontr)
    assume "\<not>( (finite_play p) \<and> (\<nexists>ps. ps \<noteq> [] \<and> finite_play (p @ ps)))"
    hence "\<exists>gn ps. finite_play (p @ [gn] @ ps)"
      by (metis Cons_eq_appendI append_self_conv2 asm list.exhaust_sel)
    hence "\<exists>gn. finite_play (p @ [gn])" using finite_play_prefix by (metis append.assoc snoc_eq_iff_butlast)
    with asm show "False" by simp
  qed
next
  show "(finite_play p) \<and> (\<nexists>ps. ps \<noteq> [] \<and> finite_play (p @ ps)) \<Longrightarrow> play_stuck p" using finite_play_suffix
    by blast
qed

abbreviation "is_defender_turn p \<equiv> Gd (last p)"
abbreviation "is_attacker_turn p \<equiv> Ga (last p)"

definition won_by_defender:: "'gstate fplay \<Rightarrow> bool" where
  "won_by_defender p \<equiv> (play_stuck p \<and> is_attacker_turn p) \<or> (energy_level p = defender_win_level)"

definition won_by_attacker:: "'gstate fplay \<Rightarrow> bool" where
  "won_by_attacker p \<equiv> play_stuck p \<and> is_defender_turn p \<and> (energy_level p \<noteq> defender_win_level)"

abbreviation no_winner:: "'gstate fplay \<Rightarrow> bool" where
  "no_winner p \<equiv> \<not>play_stuck p \<and> (energy_level p \<noteq> defender_win_level)"

lemma play_won_cases:
  shows "won_by_defender p \<or> won_by_attacker p \<or> no_winner p"
  unfolding won_by_attacker_def won_by_defender_def by blast

lemma play_won_unique:
  shows"won_by_defender p  \<longleftrightarrow>  \<not> (won_by_attacker p \<or> no_winner p)"
  and  "won_by_attacker p  \<longleftrightarrow>  \<not> (won_by_defender p \<or> no_winner p)"
  and  "no_winner p  \<longleftrightarrow>  \<not> (won_by_defender p \<or> won_by_attacker p)"
  using  won_by_attacker_def won_by_defender_def by blast+

subsection \<open>Winning Budgets\<close>

inductive in_wina:: "'energy \<Rightarrow> 'gstate \<Rightarrow> bool " where
 "in_wina e g" if "(Gd g) \<and> (\<forall>g'. \<not>(g \<Zinj> g')) \<and> (e \<noteq> defender_win_level)" |
 "in_wina e g" if "(Ga g) \<and> (\<exists>g'. ((g \<Zinj> g') \<and> (in_wina ((weight g g') e) g')))\<and> (e \<noteq> defender_win_level)" |
 "in_wina e g" if "(Gd g) \<and>(\<forall>g'. ((g \<Zinj> g') \<longrightarrow> (in_wina ((weight g g') e) g'))) \<and> (e \<noteq> defender_win_level)" 

lemma defender_win_level_not_in_wina:
  shows "\<forall>g. \<not>in_wina defender_win_level g"
  by (metis in_wina.cases)

lemma attacker_wins_last_wina_notempty:
  fixes p
  assumes "(finite_play p) \<and> (won_by_attacker p)"
  shows "\<exists>e. in_wina e (last p)"
  using assms won_by_attacker_def finite_play.intros(2) in_wina.intros(1) by meson


end (*End of context energy_game*)
end
