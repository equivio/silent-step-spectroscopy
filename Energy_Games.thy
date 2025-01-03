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
has a partial order on energies such that all updates are monotonic and have sink where the defender wins.\<close>

type_synonym 'energy update = \<open>'energy \<Rightarrow> 'energy option\<close>

text\<open>An energy game is played by two players on a directed graph labelled by energy updates.
These updates represent the costs of choosing a certain move.
Since we will only consider cases in which the attacker's moves may actually have non-zero costs, only they can run
out of energy. This is the case when the energy level reaches the \<open>defender_win_level\<close>.
In contrast to other definitions of games, we do not fix a starting position.\<close>
locale energy_game =
fixes
  weight_opt :: \<open>'gstate \<Rightarrow> 'gstate \<Rightarrow> 'energy update option\<close> and
  defender :: \<open>'gstate \<Rightarrow> bool\<close> (\<open>Gd\<close>) and
  ord:: \<open>'energy \<Rightarrow> 'energy \<Rightarrow> bool\<close>
assumes
  antisim: \<open>\<And>e e'. (ord e e') \<Longrightarrow> (ord e' e) \<Longrightarrow> e = e'\<close> and
  monotonicity: \<open>\<And>g g' e e' eu eu'.
    weight_opt g g' \<noteq> None \<Longrightarrow> the (weight_opt g g') e = Some eu \<Longrightarrow> the (weight_opt g g') e' = Some eu'
    \<Longrightarrow> ord e e' \<Longrightarrow> ord eu eu'\<close> and
  defender_win_min: \<open>\<And>g g' e e'. ord e e' \<Longrightarrow> weight_opt g g' \<noteq> None \<Longrightarrow> the (weight_opt g g') e' = None \<Longrightarrow> the (weight_opt g g') e = None\<close>
begin

text\<open>In the following, we introduce some abbreviations for attacker positions and moves.\<close>

abbreviation attacker :: \<open>'gstate \<Rightarrow> bool\<close> (\<open>Ga\<close>) where \<open>Ga p \<equiv> \<not> Gd p\<close>

abbreviation moves :: \<open>'gstate \<Rightarrow> 'gstate \<Rightarrow> bool\<close> (infix \<open>\<Zinj>\<close> 70) where \<open>g1 \<Zinj> g2 \<equiv> weight_opt g1 g2 \<noteq> None\<close>

abbreviation weighted_move :: \<open>'gstate \<Rightarrow> 'energy update \<Rightarrow> 'gstate \<Rightarrow>  bool\<close> (\<open>_ \<Zinj>wgt _ _\<close> [60,60,60] 70) where
  \<open>weighted_move g1 u g2 \<equiv> g1 \<Zinj> g2 \<and> (the (weight_opt g1 g2) = u)\<close>

abbreviation \<open>weight g1 g2 \<equiv> the (weight_opt g1 g2)\<close>

abbreviation \<open>updated g g' e \<equiv> the (weight g g' e)\<close>

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

inductive attacker_wins:: \<open>'energy \<Rightarrow> 'gstate \<Rightarrow> bool\<close> where
  Attack: \<open>attacker_wins e g\<close> if
    \<open>Ga g\<close> \<open>g \<Zinj> g'\<close> \<open>weight g g' e = Some e'\<close> \<open>attacker_wins e' g'\<close> |
  Defense: \<open>attacker_wins e g\<close> if
    \<open>Gd g\<close> \<open>\<forall>g'. (g \<Zinj> g') \<longrightarrow> (\<exists>e'. weight g g' e = Some e' \<and> attacker_wins e' g')\<close>

lemma %invisible attacker_wins_GaE:
  assumes \<open>attacker_wins e g\<close> and \<open>Ga g\<close>
  shows \<open>\<exists>g'. ((g \<Zinj> g') \<and> (attacker_wins (the (weight g g' e)) g'))\<close>
  using assms attacker_wins.simps option.sel by metis

lemma %invisible attacker_wins_Ga:
  assumes \<open>u e = Some e'\<close> \<open>attacker_wins e' g'\<close> \<open>g \<Zinj>wgt u g'\<close> \<open>Ga g\<close>
  shows \<open>attacker_wins e g\<close>
  using assms attacker_wins.simps by blast

lemma %invisible attacker_wins_Ga_with_id_step:
  assumes \<open>attacker_wins e g'\<close> \<open>g \<Zinj>wgt Some g'\<close> \<open>Ga g\<close>
  shows \<open>attacker_wins e g\<close>
  using assms by (metis attacker_wins.simps)

lemma %invisible attacker_wins_Gd:
  fixes update
  assumes \<open>Gd g\<close>
  \<open>\<And>g'. g \<Zinj> g' \<Longrightarrow> weight g g' = update\<close>
  \<open>\<And>g'. g \<Zinj> g' \<Longrightarrow> \<exists>e'. update e = Some e' \<and> attacker_wins e' g'\<close>
shows \<open>attacker_wins e g\<close> using assms attacker_wins.Defense by metis

text\<open>If from a certain starting position \<open>g\<close> a game is won by the attacker with some energy \<open>e\<close> (i.e.
\<open>e\<close> is in the winning budget of \<open>g\<close>), then the game is also won by the attacker with more energy.
This is proven using the inductive definition of winning budgets and the given properties of the partial order \<open>ord\<close>.\<close>

lemma win_a_upwards_closure:
  assumes
    \<open>attacker_wins e g\<close>
    \<open>ord e e'\<close>
  shows
    \<open>attacker_wins e' g\<close>
using assms proof (induct arbitrary: e' rule: attacker_wins.induct)
  case (Attack g g' e eu e')
  with defender_win_min obtain eu' where \<open>weight g g' e' = Some eu'\<close> by fastforce
  then show ?case
    using Attack monotonicity attacker_wins_Ga by blast
next
  case (Defense g e)
  with defender_win_min have \<open>\<forall>g'. g \<Zinj> g' \<longrightarrow> (\<exists>eu'. weight g g' e' = Some eu')\<close> by fastforce
  then show ?case
    using Defense attacker_wins.Defense monotonicity by meson
qed

end (*End of context energy_game*)

end
