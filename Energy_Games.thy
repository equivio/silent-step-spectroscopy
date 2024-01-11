section "Energy Games"

theory Energy_Games
  imports Main Misc
begin

text \<open>In this theory energy games are introduced and basic definitions such as (winning) plays are 
given. This creates the foundation for the later introduced full spectroscopy game, which is an 
energy game itself, characterizing equivalence problems.\<close>

section \<open>Energy Games\<close>

text\<open>Later on we will consider 8-dimensional energy games. For now energies will not be typed.\<close>

type_synonym 'energy update = "'energy \<Rightarrow> 'energy"

text\<open>When only finite plays are considered these can be represented as a list of states. To stay 
aware of this limitation to finite cases a corresponding type synonym is introduced.\<close>

type_synonym 'gstate fplay = "'gstate list"

text\<open>An energy games is played on a directed graph labeled by energy updates. We limit ourselves to 
the case where only the attacker can run out of energy if the energy level reaches the 
\<open>defender_win_level\<close>.\<close>

locale energy_game =
  fixes weight_opt :: "'gstate \<Rightarrow> 'gstate \<Rightarrow> 'energy update option" and
        defender :: "'gstate \<Rightarrow> bool" ("Gd") and 
        defender_win_level :: "'energy" and
        ord::"'energy \<Rightarrow> 'energy \<Rightarrow> bool"
  assumes transitivity: "\<And>e e' e''. (ord e e') \<Longrightarrow> (ord e' e'') \<Longrightarrow> (ord e e'')" and
          reflexivity: "\<And>e. (ord e e)" and
          antysim: "\<And>e e'. (ord e e') \<Longrightarrow> (ord e' e) \<Longrightarrow> e=e'" and
          dwl_min: "\<And>e. ord defender_win_level e" and 
          monotonicity:"\<And>g g' e e'. (weight_opt g g') \<noteq> None \<Longrightarrow> (ord e e')  \<Longrightarrow> (ord (the (weight_opt g g')e) (the (weight_opt g g')e'))" and
          update_gets_smaller: "\<And>g g' e. ((weight_opt g g') \<noteq> None) \<Longrightarrow> (ord (the (weight_opt g g')e) e)"
begin

text\<open>Some natural abbreviations follow:\<close>

abbreviation attacker :: "'gstate \<Rightarrow> bool" ("Ga") where "Ga p \<equiv> \<not> Gd p" 

abbreviation moves :: "'gstate \<Rightarrow> 'gstate \<Rightarrow> bool" (infix "\<Zinj>" 70) where "g1 \<Zinj> g2 \<equiv> weight_opt g1 g2 \<noteq> None"

abbreviation weighted_move :: "'gstate \<Rightarrow> 'energy update \<Rightarrow> 'gstate \<Rightarrow>  bool" ("_ \<Zinj>wgt _ _" [60,60,60] 70) where
  "weighted_move g1 u g2 \<equiv> g1 \<Zinj> g2 \<and> (the (weight_opt g1 g2) = u)"

abbreviation "weight g1 g2 \<equiv> the (weight_opt g1 g2)"

text\<open>Starting with some energy at some state the resulting energy level after a valid play can be 
calculated as follows:\<close>

fun energy_level :: "'gstate \<Rightarrow> 'energy \<Rightarrow>'gstate fplay \<Rightarrow> 'energy" where
  "energy_level g0 e0 p = (
    if p = [g0] then 
      e0 
    else ( if (length p \<ge> 2) then ( if ((weight_opt (last (butlast p))(last p)) \<noteq> None) then ((weight (last (butlast p)) (last p)) (energy_level g0 e0 (butlast p)))
                                    else undefined)
          else undefined))"

lemma %invisible energy_level_def1:
  shows "energy_level g0 e0 [g0] = e0"
  by simp

lemma %invisible energy_level_def2:
  assumes "p' \<noteq> []" and "energy_level g0 e0 p' \<noteq> undefined" and "weight_opt (last p') gn \<noteq> None"  
  shows "energy_level g0 e0 (p' @ [gn]) = weight (last p') gn (energy_level g0 e0 p')"
  using assms by (simp add: not_less_eq_eq) 

lemma %invisible energy_level_def3:
  shows "energy_level g0 e0 [] = undefined"
  by simp

lemma %invisible energy_level_def4:
  assumes "p \<noteq> []" "hd p = g0" and e0: "e0 \<noteq> undefined" and weight_well_def: "\<And>g1 g2 e1.((weight_opt g1 g2)\<noteq> None \<and> (weight g1 g2) e1 \<noteq> undefined)"
  shows "energy_level g0 e0 p \<noteq> undefined"
using assms proof(induct p rule: rev_induct)
  case Nil
  thus ?case by simp
next
  case (snoc x xs)
  thus ?case proof(cases "xs = []")
    case True
    hence "xs @ [x] = [x]" by simp
    with snoc(3) have "x = g0" by simp
    hence "energy_level g0 e0 [x] = e0" by simp
    thus ?thesis unfolding \<open>xs @ [x] = [x]\<close> using e0 by simp
  next
    case False
    then show ?thesis 
      using energy_level_def2 weight_well_def e0 snoc.hyps snoc.prems(2) by auto 
  qed
qed

subsection \<open>Finite Plays\<close>

text\<open>We already spoke of "valid games". By this we mean lists of states where an edge from one 
state to the next in the list exists. In the finite case this is represented as \<open>finite_play\<close>.\<close>

inductive finite_play :: "'gstate \<Rightarrow> 'gstate fplay \<Rightarrow> bool" where
  "finite_play g0 [g0]" |
  "finite_play g0 (p @ [gn])" if "finite_play g0 p" and "last p \<Zinj> gn"

text\<open>Some potentially helpful lemmas follow:\<close>

lemma finite_play_prefix:
  assumes "finite_play g0 (a @ b)" "a \<noteq> []"
  shows "finite_play g0 a"
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
  assumes "finite_play g0 (p @ [gn])" and "p \<noteq> []"
  shows "finite_play g0 p"
  using assms finite_play_prefix by fast

lemma finite_play_suffix2:
  assumes "finite_play g0 ([g0] @ ([g1]@p))"
  shows "finite_play g1 ([g1]@p)"
using assms proof (induct p rule: rev_induct)
  case Nil
  then show ?case by (simp add: finite_play.intros(1)) 
next
  case (snoc x xs)
  then show ?case
    by (smt (verit) Cons_eq_appendI append_assoc append_same_eq distinct_adj_Cons distinct_adj_Cons_Cons eq_Nil_appendI finite_play.simps last.simps last_appendR)
qed

lemma finite_play_check_gen:
   assumes "x \<noteq> p1" and
           "p = p1 # [pn]"
   shows "\<not>finite_play x (p @ [gn])"
proof (rule notI)
  assume A1: "finite_play x (p @ [gn])"
  from assms A1 have A2: "finite_play x p"
    using finite_play_prefix by blast 
  from assms(2) A2 have A3: "finite_play x ( p1 # [pn])"
    by meson
  from A3 have A4: "finite_play x ([p1] @ [pn])"
    by simp
  from A4 have A5: "finite_play x [p1]"
    using finite_play_prefix by blast 
  have A6: "\<not>finite_play x [p1]"
    by (metis assms(1) butlast.simps(2) finite_play.simps list.distinct(1) snoc_eq_iff_butlast)
  show "False"
    using A5 A6 by auto 
qed

lemma finite_play_min_len: "finite_play g0 p \<Longrightarrow> length p \<ge> 1"
  using add_leE finite_play.cases not_Cons_self2 not_less_eq_eq by fastforce

lemma finite_play_is_path:
  fixes p
  assumes "finite_play g0 p"
  shows "((p = ((a @ [g]) @ b)) \<and> a \<noteq>[]) \<longrightarrow> ((last a) \<Zinj> g)"
  by (metis assms butlast.simps(2) finite_play.simps finite_play_prefix snoc_eq_iff_butlast)

lemma energy_level_fold_eq:
  assumes "finite_play g0 p"
  shows "energy_level g0 e0 p = fold (\<lambda>(g1, g2) e. (weight g1 g2) e) (pairs p) e0"
using assms proof (induct "p" rule: finite_play.induct)
  case 1
  thus ?case unfolding single_pair[of "g0"] fold_Nil by simp
next
  case (2 g0 p gn)
  have "length p \<ge> 1" using 2(1) finite_play_min_len by auto
  hence pred_eq: "(pairs (p @ [gn])) = (pairs p) @ [(last p, gn)]" using pairs_append_single by metis
  have L: "length (p @ [gn]) \<ge> 2" using \<open>1 \<le> length p\<close> by auto 

  have "fold (\<lambda>(g1, g2). weight g1 g2) [(last p, gn)] = weight (last p) gn" by simp
  hence "fold (\<lambda>(g1, g2). weight g1 g2) ((pairs p) @ [(last p, gn)]) = (weight (last p) gn) \<circ> (fold (\<lambda>(g1, g2). weight g1 g2) (pairs p))" 
    using fold_append by simp
  with 2 show ?case using pred_eq L energy_level_def2 energy_level_def3 energy_level_def4 comp_apply energy_level.simps snoc_eq_iff_butlast by auto
qed

subsection \<open>Winning\<close>

text\<open>Energy games can be won. An infinite game is won by the defender. A finite play is won if it's 
stuck (i.e. there are no more possible moves) and it is the other players turn. Since we for now
only consider finite plays we will need to define stuckness.\<close>

abbreviation "play_stuck g0 p \<equiv> (finite_play g0 p) \<and> (\<nexists>gn. finite_play g0 (p @ [gn]))"

lemma play_stuck_def:
  shows "play_stuck g0 p \<longleftrightarrow> ((finite_play g0 p) \<and> (\<nexists>ps. ps \<noteq> [] \<and> finite_play g0 (p @ ps)))"
proof
  assume asm: "(finite_play g0 p) \<and> (\<nexists>gn. finite_play g0 (p @ [gn]))"
  show "((finite_play g0 p) \<and> (\<nexists>ps. ps \<noteq> [] \<and> finite_play g0 (p @ ps)))" 
  proof(rule ccontr)
    assume "\<not>( (finite_play g0 p) \<and> (\<nexists>ps. ps \<noteq> [] \<and> finite_play g0 (p @ ps)))"
    hence "\<exists>gn ps. finite_play g0 (p @ [gn] @ ps)"
      by (metis Cons_eq_appendI append_self_conv2 asm list.exhaust_sel)
    hence "\<exists>gn. finite_play g0 (p @ [gn])" using finite_play_prefix by (metis append.assoc snoc_eq_iff_butlast)
    with asm show "False" by simp
  qed
next
  show "(finite_play g0 p) \<and> (\<nexists>ps. ps \<noteq> [] \<and> finite_play g0 (p @ ps)) \<Longrightarrow> play_stuck g0 p" using finite_play_suffix
    by blast
qed

abbreviation "is_defender_turn p \<equiv> Gd (last p)"
abbreviation "is_attacker_turn p \<equiv> Ga (last p)"

text\<open>Now the winning conditions for finite plays can be formalized and we can show that each finite 
play is either won by the defender, won by the attacker or not yet stuck. We need to consider the 
energy levels of plays. The attacker should be understood as truly not stuck only if the energy 
level does not equal the defender win level - otherwise the defender wins.\<close>

definition won_by_defender:: "'gstate \<Rightarrow> 'energy \<Rightarrow> 'gstate fplay \<Rightarrow> bool" where
  "won_by_defender g0 e0 p \<equiv> (play_stuck g0 p \<and> is_attacker_turn p) \<or> (energy_level g0 e0 p = defender_win_level)"

definition won_by_attacker:: "'gstate \<Rightarrow> 'energy \<Rightarrow> 'gstate fplay \<Rightarrow> bool" where
  "won_by_attacker g0 e0 p \<equiv> play_stuck g0 p \<and> is_defender_turn p \<and> (energy_level g0 e0 p \<noteq> defender_win_level)"

abbreviation no_winner:: "'gstate \<Rightarrow> 'energy \<Rightarrow> 'gstate fplay \<Rightarrow> bool" where
  "no_winner g0 e0 p \<equiv> \<not>play_stuck g0 p \<and> (energy_level g0 e0 p \<noteq> defender_win_level)"

lemma play_won_cases:
  shows "won_by_defender g0 e0 p \<or> won_by_attacker g0 e0 p \<or> no_winner g0 e0 p"
  unfolding won_by_attacker_def won_by_defender_def by blast

lemma play_won_unique:
  shows"won_by_defender g0 e0 p  \<longleftrightarrow>  \<not> (won_by_attacker g0 e0 p \<or> no_winner g0 e0 p)"
  and  "won_by_attacker g0 e0 p  \<longleftrightarrow>  \<not> (won_by_defender g0 e0 p \<or> no_winner g0 e0 p)"
  and  "no_winner g0 e0 p  \<longleftrightarrow>  \<not> (won_by_defender g0 e0 p \<or> won_by_attacker g0 e0 p)"
  using  won_by_attacker_def won_by_defender_def by blast+

subsubsection \<open>Winning Budgets\<close>

text\<open>The attacker wins a game from some starting position if they can force the defender to get 
stuck before running out of energy themselves. How much energy is needed can be characterized by 
winning budgets: \<close>

inductive in_wina:: "'energy \<Rightarrow> 'gstate \<Rightarrow> bool " where
 "in_wina e g" if "(Gd g) \<and> (\<forall>g'. \<not>(g \<Zinj> g')) \<and> (e \<noteq> defender_win_level)" |
 "in_wina e g" if "(Ga g) \<and> (\<exists>g'. ((g \<Zinj> g') \<and> (in_wina ((weight g g') e) g')))\<and> (e \<noteq> defender_win_level)" |
 "in_wina e g" if "(Gd g) \<and> (\<forall>g'. ((g \<Zinj> g') \<longrightarrow> (in_wina ((weight g g') e) g'))) \<and> (e \<noteq> defender_win_level)"

definition wina_set
  where
"wina_set g = {e. in_wina e g}"

lemma defender_win_level_not_in_wina:
  shows "\<forall>g. \<not>in_wina defender_win_level g" 
  by (metis in_wina.cases)

lemma attacker_wins_last_wina_notempty:
  assumes "won_by_attacker g0 e0 p"
  shows "\<exists>e. in_wina e (last p)"
  using assms won_by_attacker_def finite_play.intros(2) in_wina.intros(1) by meson

lemma in_wina_Ga:
  assumes "in_wina e g" and "Ga g" 
  shows "\<exists>g'. ((g \<Zinj> g') \<and> (in_wina ((weight g g') e) g'))"
  using assms(1) assms(2) in_wina.simps by blast

text\<open>The intuitively true statement "with more energy the attacker will win at least as much as 
before" can be proven when given a partial order on energies such that the \<open>defender_win_leve\<close>l is 
the minimal energy, updates are monotonic and \<open>e \<ge> Upd(e)\<close> holds for all energies and updates:\<close>

lemma win_a_upwards_closure: 
  assumes "in_wina e g"
        shows "(\<forall>e'.((ord e e')\<longrightarrow> (in_wina e' g)))"
using assms proof (induct rule: in_wina.induct)
  case (1 g e)
  then show ?case using antysim dwl_min local.reflexivity local.transitivity update_gets_smaller
    by (metis in_wina.intros(1))
next
  case (2 g e)
  then show ?case
    using antysim dwl_min in_wina.intros(2) monotonicity by blast 
next
  case (3 g e)
  then show ?case
    using antysim dwl_min in_wina.intros(3) monotonicity by blast 
qed

end (*End of context energy_game*)
end
