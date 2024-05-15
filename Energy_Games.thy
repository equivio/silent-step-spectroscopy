text \<open>\newpage\<close>
section \<open>Energy Games\<close>

theory Energy_Games
  imports Main Misc
begin

text\<open>In this theory, we introduce energy games and give basic definitions such as winning budgets.
Energy games are the foundation for the later introduced weak spectroscopy game, which is an 
energy game itself, characterizing equivalence problems. \label{energy games}\<close>

subsection \<open>Fundamentals\<close>
text\<open>We use an abstract concept of energies and only later consider eight-dimensional energy games. 
Through our later given definition of energies as a data type, we obtain certain 
properties that we enforce for all energy games. We therefore assume that an energy game 
has a partial order on energies such that all updates are monotonic and never increase.\<close>

type_synonym 'energy update = "'energy \<Rightarrow> 'energy"

text\<open>An energy game is played by two players on a directed graph labelled by energy updates. 
These updates represent the costs of choosing a certain move.
Since we will only consider cases in which the attacker's moves may actually have non-zero costs, only they can run 
out of energy. This is the case when the energy level reaches the \<open>defender_win_level\<close>.
In contrast to other definitions of games, we do not fix a starting position.\<close>
locale energy_game =
  fixes weight_opt :: "'gstate \<Rightarrow> 'gstate \<Rightarrow> 'energy update option" and
        defender :: "'gstate \<Rightarrow> bool" ("Gd") and 
        defender_win_level :: "'energy" and
        ord::"'energy \<Rightarrow> 'energy \<Rightarrow> bool"
  assumes transitivity: "\<And>e e' e''. (ord e e') \<Longrightarrow> (ord e' e'') \<Longrightarrow> (ord e e'')" and
          reflexivity: "\<And>e. (ord e e)" and
          antisim: "\<And>e e'. (ord e e') \<Longrightarrow> (ord e' e) \<Longrightarrow> e=e'" and
          dwl_min: "\<And>e. ord defender_win_level e" and 
          monotonicity:"\<And>g g' e e'. (weight_opt g g') \<noteq> None \<Longrightarrow> (ord e e')  \<Longrightarrow> (ord (the (weight_opt g g')e) (the (weight_opt g g')e'))" and
          update_gets_smaller: "\<And>g g' e. ((weight_opt g g') \<noteq> None) \<Longrightarrow> (ord (the (weight_opt g g')e) e)"
begin

text\<open>In the following, we introduce some abbreviations for attacker positions and moves.\<close>

abbreviation attacker :: "'gstate \<Rightarrow> bool" ("Ga") where "Ga p \<equiv> \<not> Gd p" 

abbreviation moves :: "'gstate \<Rightarrow> 'gstate \<Rightarrow> bool" (infix "\<Zinj>" 70) where "g1 \<Zinj> g2 \<equiv> weight_opt g1 g2 \<noteq> None"

abbreviation weighted_move :: "'gstate \<Rightarrow> 'energy update \<Rightarrow> 'gstate \<Rightarrow>  bool" ("_ \<Zinj>wgt _ _" [60,60,60] 70) where
  "weighted_move g1 u g2 \<equiv> g1 \<Zinj> g2 \<and> (the (weight_opt g1 g2) = u)"

abbreviation "weight g1 g2 \<equiv> the (weight_opt g1 g2)"

subsubsection \<open>Winning Budgets\<close>

text\<open>The attacker wins a game if and only if they manage to force the defender to get stuck before 
running out of energy. The needed amount of energy is described by winning budgets: \<open>e\<close> is in the 
winning budget of \<open>g\<close> if and only if there exists a winning strategy for the attacker when starting in \<open>g\<close> 
with energy \<open>e\<close>. In more detail, this yields the following definition: 

\begin{itemize}
  \item If \<open>g\<close> is an attacker position and \<open>e\<close> is not the \<open>defender_win_level\<close> then \<open>e\<close> is in the winning budget 
  of \<open>g\<close> if and only if there exists a position \<open>g'\<close> the attacker can move to. In other words, if the updated energy 
  level is in the winning budget of \<open>g'\<close>. (This corresponds to the second case of the following definition.)
  \item  If \<open>g\<close> is a defender position and \<open>e\<close> is not the \<open>defender_win_level\<close> then \<open>e\<close> is in the winning budget 
   of \<open>g\<close> if and only if for all successors \<open>g'\<close> the accordingly updated energy is in the winning 
   budget of \<open>g'\<close>. In other words, if the attacker will win from every successor the defender can move to.
\end{itemize}
\<close>

inductive in_wina:: "'energy \<Rightarrow> 'gstate \<Rightarrow> bool " where
 Attack: "in_wina e g" if \<open>Ga g\<close> \<open>g \<Zinj> g'\<close> \<open>in_wina ((weight g g') e) g'\<close> \<open>e \<noteq> defender_win_level\<close> |
 Defense: "in_wina e g" if \<open>Gd g\<close> \<open>\<forall>g'. ((g \<Zinj> g') \<longrightarrow> (in_wina ((weight g g') e) g'))\<close> \<open>e \<noteq> defender_win_level\<close>

lemma %invisible defender_win_level_not_in_wina:
  shows "\<forall>g. \<not>in_wina defender_win_level g" 
  by (metis in_wina.cases)

lemma %invisible in_wina_GaE:
  assumes "in_wina e g" and "Ga g" 
  shows "\<exists>g'. ((g \<Zinj> g') \<and> (in_wina ((weight g g') e) g'))"
  using assms(1) assms(2) in_wina.simps by blast

lemma %invisible in_wina_Ga:
  assumes "in_wina (u e) g'" "g \<Zinj>wgt u g'" "Ga g"
  shows "in_wina e g"
  using assms in_wina.simps by (metis antisim dwl_min update_gets_smaller)

lemma %invisible in_wina_Ga_with_id_step:
  assumes "in_wina e g'" "g \<Zinj>wgt id g'" "Ga g"
  shows "in_wina e g"
  using assms by (metis id_apply in_wina.simps)

lemma %invisible in_wina_Gd:
  fixes update
  assumes "Gd g"
  "e \<noteq> defender_win_level"
  "\<And>g'. g \<Zinj> g' \<Longrightarrow>  weight g g' = update"
  "\<And>g'. g \<Zinj> g' \<Longrightarrow> in_wina (update e) g'"
shows "in_wina e g" using assms in_wina.intros(2) by blast

text\<open>If from a certain starting position \<open>g\<close> a game is won by the attacker with some energy \<open>e\<close> (i.e.
\<open>e\<close> is in the winning budget of \<open>g\<close>), then the game is also won by the attacker with more energy. 
This is proven using the inductive definition of winning budgets and the given properties of the partial order \<open>ord\<close>.\<close>

lemma win_a_upwards_closure: 
  assumes
    "in_wina e g"
    "ord e e'"
  shows
    "in_wina e' g"
using assms proof (induct arbitrary: e' rule: in_wina.induct)
  case (Attack g g' e)
  then show ?case
    using antisim dwl_min in_wina.intros(1) monotonicity by blast 
next
  case (Defense g e)
  then show ?case
    using antisim dwl_min in_wina.intros(2) monotonicity by blast 
qed

end (*End of context energy_game*)

end
