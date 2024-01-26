theory Expressiveness_Price
  imports Main HML_SRBB "HOL-Library.Extended_Nat" Energy
begin

section \<open>The expressiveness price function\<close>

text \<open>
The expressiveness price function assigns a price - an eight element tuple - to a \<open>hml_srbb\<close> formula.
It may be defined as a single function:
\begin{align*}
  expr(\top) := expr^\varepsilon(\top) :=& 0 \\
  expr(\langle\varepsilon\rangle\chi) :=& expr^\varepsilon(\chi) \\
  expr(\bigwedge\Psi) :=& \hat{e}_5 + expr^\varepsilon(\bigwedge\Psi) \\
  expr^\varepsilon((\alpha)\varphi) :=& \hat{e}_1 + expr(\varphi) \\
  expr^\varepsilon(\bigwedge(\{(\alpha)\varphi\} \cup \Psi)) :=& \hat{e}_2 + expr^\varepsilon(\bigwedge(\{\langle\varepsilon\rangle(\alpha)\varphi\} \cup \Psi \setminus \{(\alpha)\varphi\})) \\
  expr^\varepsilon(\bigwedge\Psi) :=& \sup \{expr^\wedge(\psi) | \psi \in \Psi\} + 
    \begin{cases}
      \hat{e}_4 & \text{if} \neg\langle\tau\rangle\top \in \Psi \\
      \hat{e}_3 & \text{otherwise}
    \end{cases} \\
  expr^\wedge(\neg\langle\tau\rangle\top) :=&  0 \\
  expr^\wedge(\neg\varphi) :=& \sup \{\hat{e}_8 + expr(\varphi), (0,0,0,0,0,0,expr_1(\varphi),0)\} \\
  expr^\wedge(\varphi) :=& \sup \{expr(\varphi), (0,0,0,0,0,expr_1(\varphi),0,0)\}
\end{align*}

The eight dimensions are intended to measure the following properties of formulas:
\begin{enumerate}
  \item Modal depth (of observations $\langle\alpha\rangle$, $(\alpha)$),
  \item Depth of branching conjunctions (with one observation clause not starting with $\langle\varepsilon\rangle$),
  \item Depth of instable conjunctions (that do not enforce stability by a $\neg\langle\tau\rangle\top$-conjunct),
  \item Depth of stable conjunctions (that do enforce stability by a $\neg\langle\tau\rangle\top$-conjunct),
  \item Depth of immediate conjunctions (that are not preceded by $\langle\varepsilon\rangle$),
  \item Maximal modal depth of positive clauses in conjunctions,
  \item Maximal modal depth of negative clauses in conjunctions,
  \item Depth of negations
\end{enumerate}

Instead of defining the expressiveness price function in one go, we instead define eight functions (one for each dimension)
and then use them in combination to build the result tupel.\\

Note that, since all these functions stem from the above singular function, they all look very similar,
and differ mostly in where the $1+$ is placed.
\<close>

subsection \<open>Modal depth\<close>

text \<open>
(Maximal) Modal depth (of observations $\langle\alpha\rangle$, $(\alpha)$)\\

This counter is increased on each:
\begin{itemize}
  \item \<open>Obs\<close>
  \item \<open>BranchConj\<close>
\end{itemize}
\<close>

primrec
      modal_depth_srbb :: "('act, 'i) hml_srbb \<Rightarrow> enat"
  and modal_depth_srbb_inner :: "('act, 'i) hml_srbb_inner \<Rightarrow> enat"
  and modal_depth_srbb_conjunct :: "('act, 'i) hml_srbb_conjunct \<Rightarrow> enat" where
"modal_depth_srbb TT = 0" |
 "modal_depth_srbb (Internal \<chi>) = modal_depth_srbb_inner \<chi>" |
 "modal_depth_srbb (ImmConj I \<psi>s) = Sup ((modal_depth_srbb_conjunct \<circ> \<psi>s) ` I)" |

 "modal_depth_srbb_inner (Obs \<alpha> \<phi>) = 1 + modal_depth_srbb \<phi>" |
 "modal_depth_srbb_inner (Conj I \<psi>s) =
    Sup ((modal_depth_srbb_conjunct \<circ> \<psi>s) ` I)" |
 "modal_depth_srbb_inner (StableConj I \<psi>s) = 
    Sup ((modal_depth_srbb_conjunct \<circ> \<psi>s) ` I)" |
 "modal_depth_srbb_inner (BranchConj a \<phi> I \<psi>s) =
    Sup ({1 + modal_depth_srbb \<phi>} \<union> ((modal_depth_srbb_conjunct \<circ> \<psi>s) ` I))" |

 "modal_depth_srbb_conjunct (Pos \<chi>) = modal_depth_srbb_inner \<chi>" |
 "modal_depth_srbb_conjunct (Neg \<chi>) = modal_depth_srbb_inner \<chi>" 

lemma "modal_depth_srbb TT = 0"
  using Sup_enat_def by simp

lemma "modal_depth_srbb (Internal (Obs \<alpha> (Internal (BranchConj \<beta> TT {} \<psi>s2)))) = 2"
  using Sup_enat_def by simp

fun observe_n_alphas :: "'a \<Rightarrow> nat \<Rightarrow> ('a, nat) hml_srbb" where
  "observe_n_alphas \<alpha> 0 = TT" |
  "observe_n_alphas \<alpha> (Suc n) = Internal (Obs \<alpha> (observe_n_alphas \<alpha> n))"

lemma obs_n_\<alpha>_depth_n: "modal_depth_srbb (observe_n_alphas \<alpha> n) = n"
proof (induct n)
  case 0
  show ?case unfolding observe_n_alphas.simps(1) and modal_depth_srbb.simps(2)
    using zero_enat_def and Sup_enat_def by force
next
  case (Suc n)
  then show ?case 
    using eSuc_enat plus_1_eSuc(1) by auto
qed

lemma sup_nats_in_enats_infinite: "(SUP x\<in>\<nat>. enat x) = \<infinity>"
  by (metis Nats_infinite Sup_enat_def enat.inject finite.emptyI finite_imageD inj_on_def)

lemma sucs_of_nats_in_enats_sup_infinite: "(SUP x\<in>\<nat>. 1 + enat x) = \<infinity>"
  using sup_nats_in_enats_infinite
  by (metis Sup.SUP_cong eSuc_Sup eSuc_infinity image_image image_is_empty plus_1_eSuc(1))

lemma "modal_depth_srbb (ImmConj \<nat> (\<lambda>n. Pos (Obs \<alpha> (observe_n_alphas \<alpha> n)))) = \<infinity>"
  unfolding modal_depth_srbb.simps(3)
        and o_def
        and modal_depth_srbb_conjunct.simps(1)
        and modal_depth_srbb_inner.simps(1)
        and obs_n_\<alpha>_depth_n
  by (metis sucs_of_nats_in_enats_sup_infinite) 


subsection \<open>Depth of branching conjunctions\<close>

text \<open>
Depth of branching conjunctions (with one observation clause not starting with $\langle\varepsilon\rangle$)\\

This counter is increased on each:
\begin{itemize}
  \item \<open>BranchConj\<close> if there are other conjuncts besides the branching conjunct
\end{itemize}

Note that if the \<open>BranchConj\<close> is empty (i.e. has no other conjuncts),
then it is treated like a simple \<open>Obs\<close>.
\<close>

primrec
      branching_conjunction_depth :: "('a, 's) hml_srbb \<Rightarrow> enat"
  and branch_conj_depth_inner :: "('a, 's) hml_srbb_inner \<Rightarrow> enat"
  and branch_conj_depth_conjunct :: "('a, 's) hml_srbb_conjunct \<Rightarrow> enat" where
  "branching_conjunction_depth TT = 0" |
  "branching_conjunction_depth (Internal \<chi>) = branch_conj_depth_inner \<chi>" |
  "branching_conjunction_depth (ImmConj I \<psi>s) = Sup ((branch_conj_depth_conjunct \<circ> \<psi>s) ` I)" |

  "branch_conj_depth_inner (Obs _ \<phi>) = branching_conjunction_depth \<phi>" |
  "branch_conj_depth_inner (Conj I \<psi>s) = Sup ((branch_conj_depth_conjunct \<circ> \<psi>s) ` I)" |
  "branch_conj_depth_inner (StableConj I \<psi>s) = Sup ((branch_conj_depth_conjunct \<circ> \<psi>s) ` I)" |
  "branch_conj_depth_inner (BranchConj _ \<phi> I \<psi>s) =
    (if I = {}
     then branching_conjunction_depth \<phi>
     else 1 + Sup ({branching_conjunction_depth \<phi>} \<union> ((branch_conj_depth_conjunct \<circ> \<psi>s) ` I)))" |

  "branch_conj_depth_conjunct (Pos \<chi>) = branch_conj_depth_inner \<chi>" |
  "branch_conj_depth_conjunct (Neg \<chi>) = branch_conj_depth_inner \<chi>" 


subsection \<open>Depth of instable conjunctions\<close>

text \<open>
Depth of instable conjunctions (that do not enforce stability by a $\neg\langle\tau\rangle\top$-conjunct)

This counter is increased on each:
\begin{itemize}
  \item \<open>ImmConj\<close> if there are conjuncts (i.e. $\bigwedge\{\}$ is not counted)
  \item \<open>Conj\<close> if there are conjuncts, (i.e. the conjunction is not empty)
  \item \<open>BranchConj\<close> if there are other conjuncts besides the branching conjunct
\end{itemize}

Note that if the \<open>BranchConj\<close> is empty (i.e. has no other conjuncts),
then it is treated like a simple \<open>Obs\<close>.
\<close>

primrec
      instable_conjunction_depth :: "('a, 's) hml_srbb \<Rightarrow> enat"
  and inst_conj_depth_inner :: "('a, 's) hml_srbb_inner \<Rightarrow> enat"
  and inst_conj_depth_conjunct :: "('a, 's) hml_srbb_conjunct \<Rightarrow> enat" where
  "instable_conjunction_depth TT = 0" |
  "instable_conjunction_depth (Internal \<chi>) = inst_conj_depth_inner \<chi>" |
  "instable_conjunction_depth (ImmConj I \<psi>s) =
    (if I = {}
     then 0
     else 1 + Sup ((inst_conj_depth_conjunct \<circ> \<psi>s) ` I))" |

  "inst_conj_depth_inner (Obs _ \<phi>) = instable_conjunction_depth \<phi>" |
  "inst_conj_depth_inner (Conj I \<psi>s) =
    (if I = {} 
     then 0
     else 1 + Sup ((inst_conj_depth_conjunct \<circ> \<psi>s) ` I))" |
  "inst_conj_depth_inner (StableConj I \<psi>s) = Sup ((inst_conj_depth_conjunct \<circ> \<psi>s) ` I)" |
  "inst_conj_depth_inner (BranchConj _ \<phi> I \<psi>s) =
    (if I = {}
     then instable_conjunction_depth \<phi>
     else 1 + Sup ({instable_conjunction_depth \<phi>} \<union> ((inst_conj_depth_conjunct \<circ> \<psi>s) ` I)))" |

  "inst_conj_depth_conjunct (Pos \<chi>) = inst_conj_depth_inner \<chi>" |
  "inst_conj_depth_conjunct (Neg \<chi>) = inst_conj_depth_inner \<chi>" 


subsection \<open>Depth of stable conjunctions\<close>

text \<open>
Depth of stable conjunctions (that do enforce stability by a $\neg\langle\tau\rangle\top$-conjunct)

This counter is increased on each:
\begin{itemize}
  \item \<open>StableConj\<close>
\end{itemize}

Note that if the \<open>StableConj\<close> is empty (i.e. has no other conjuncts),
it is still counted!
\<close>

primrec
      stable_conjunction_depth :: "('a, 's) hml_srbb \<Rightarrow> enat"
  and st_conj_depth_inner :: "('a, 's) hml_srbb_inner \<Rightarrow> enat"
  and st_conj_depth_conjunct :: "('a, 's) hml_srbb_conjunct \<Rightarrow> enat" where
  "stable_conjunction_depth TT = 0" |
  "stable_conjunction_depth (Internal \<chi>) = st_conj_depth_inner \<chi>" |
  "stable_conjunction_depth (ImmConj I \<psi>s) = Sup ((st_conj_depth_conjunct \<circ> \<psi>s) ` I)" |

  "st_conj_depth_inner (Obs _ \<phi>) = stable_conjunction_depth \<phi>" |
  "st_conj_depth_inner (Conj I \<psi>s) = Sup ((st_conj_depth_conjunct \<circ> \<psi>s) ` I)" |
  "st_conj_depth_inner (StableConj I \<psi>s) = 1 + Sup ((st_conj_depth_conjunct \<circ> \<psi>s) ` I)" |
  "st_conj_depth_inner (BranchConj _ \<phi> I \<psi>s) = Sup ({stable_conjunction_depth \<phi>} \<union> ((st_conj_depth_conjunct \<circ> \<psi>s) ` I))" |

  "st_conj_depth_conjunct (Pos \<chi>) = st_conj_depth_inner \<chi>" |
  "st_conj_depth_conjunct (Neg \<chi>) = st_conj_depth_inner \<chi>" 


subsection \<open>Depth of immediate conjunctions\<close>

text \<open>
Depth of immediate conjunctions (that are not preceded by $\langle\varepsilon\rangle$)

This counter is increased on each:
\begin{itemize}
  \item \<open>ImmConj\<close> if there are conjuncts (i.e. $\bigwedge\{\}$ is not counted)
\end{itemize}
\<close>

primrec
      immediate_conjunction_depth :: "('a, 's) hml_srbb \<Rightarrow> enat"
  and imm_conj_depth_inner :: "('a, 's) hml_srbb_inner \<Rightarrow> enat"
  and imm_conj_depth_conjunct :: "('a, 's) hml_srbb_conjunct \<Rightarrow> enat" where 
  "immediate_conjunction_depth TT = 0" |
  "immediate_conjunction_depth (Internal \<chi>) = imm_conj_depth_inner \<chi>" |
  "immediate_conjunction_depth (ImmConj I \<psi>s) =
    (if I = {}
     then 0
     else 1 + Sup ((imm_conj_depth_conjunct \<circ> \<psi>s) ` I))" |

  "imm_conj_depth_inner (Obs _ \<phi>) = immediate_conjunction_depth \<phi>" |
  "imm_conj_depth_inner (Conj I \<psi>s) = Sup ((imm_conj_depth_conjunct \<circ> \<psi>s) ` I)" |
  "imm_conj_depth_inner (StableConj I \<psi>s) = Sup ((imm_conj_depth_conjunct \<circ> \<psi>s) ` I)" |
  "imm_conj_depth_inner (BranchConj _ \<phi> I \<psi>s) = Sup ({immediate_conjunction_depth \<phi>} \<union> ((imm_conj_depth_conjunct \<circ> \<psi>s) ` I))" |

  "imm_conj_depth_conjunct (Pos \<chi>) = imm_conj_depth_inner \<chi>" |
  "imm_conj_depth_conjunct (Neg \<chi>) = imm_conj_depth_inner \<chi>"


section \<open>Maximal modal depth of positive clauses in conjunctions\<close>

primrec
      max_positive_conjunct_depth :: "('a, 's) hml_srbb \<Rightarrow> enat"
  and max_pos_conj_depth_inner :: "('a, 's) hml_srbb_inner \<Rightarrow> enat"
  and max_pos_conj_depth_conjunct :: "('a, 's) hml_srbb_conjunct \<Rightarrow> enat" where
  "max_positive_conjunct_depth TT = 0"|
  "max_positive_conjunct_depth (Internal \<chi>) = max_pos_conj_depth_inner \<chi>" |
  "max_positive_conjunct_depth (ImmConj I \<psi>s) = Sup ((max_pos_conj_depth_conjunct \<circ> \<psi>s) ` I)" |

  "max_pos_conj_depth_inner (Obs _ \<phi>) = max_positive_conjunct_depth \<phi>" |
  "max_pos_conj_depth_inner (Conj I \<psi>s) = Sup ((max_pos_conj_depth_conjunct \<circ> \<psi>s) ` I)" |
  "max_pos_conj_depth_inner (StableConj I \<psi>s) = Sup ((max_pos_conj_depth_conjunct \<circ> \<psi>s) ` I)" |
  "max_pos_conj_depth_inner (BranchConj _ \<phi> I \<psi>s) = Sup ({max_positive_conjunct_depth \<phi>} \<union> ((max_pos_conj_depth_conjunct \<circ> \<psi>s) ` I))" |

  "max_pos_conj_depth_conjunct (Pos \<chi>) = modal_depth_srbb_inner \<chi>" |
  "max_pos_conj_depth_conjunct (Neg \<chi>) = max_pos_conj_depth_inner \<chi>"

subsection \<open>Maximal modal depth of negative clauses in conjunctions\<close>

primrec
      max_negative_conjunct_depth :: "('a, 's) hml_srbb \<Rightarrow> enat"
  and max_neg_conj_depth_inner :: "('a, 's) hml_srbb_inner \<Rightarrow> enat"
  and max_neg_conj_depth_conjunct :: "('a, 's) hml_srbb_conjunct \<Rightarrow> enat" where
  "max_negative_conjunct_depth TT = 0" |
  "max_negative_conjunct_depth (Internal \<chi>) = max_neg_conj_depth_inner \<chi>" |
  "max_negative_conjunct_depth (ImmConj I \<psi>s) = Sup ((max_neg_conj_depth_conjunct \<circ> \<psi>s) ` I)" |

  "max_neg_conj_depth_inner (Obs _ \<phi>) = max_negative_conjunct_depth \<phi>" |
  "max_neg_conj_depth_inner (Conj I \<psi>s) = Sup ((max_neg_conj_depth_conjunct \<circ> \<psi>s) ` I)" |
  "max_neg_conj_depth_inner (StableConj I \<psi>s) = Sup ((max_neg_conj_depth_conjunct \<circ> \<psi>s) ` I)" |
  "max_neg_conj_depth_inner (BranchConj _ \<phi> I \<psi>s) = Sup ({max_negative_conjunct_depth \<phi>} \<union> ((max_neg_conj_depth_conjunct \<circ> \<psi>s) ` I))" |

  "max_neg_conj_depth_conjunct (Pos \<chi>) = max_neg_conj_depth_inner \<chi>" |
  "max_neg_conj_depth_conjunct (Neg \<chi>) = modal_depth_srbb_inner \<chi>"

subsection \<open>Depth of negations\<close>

primrec
      negation_depth :: "('a, 's) hml_srbb \<Rightarrow> enat"
  and neg_depth_inner :: "('a, 's) hml_srbb_inner \<Rightarrow> enat"
  and neg_depth_conjunct :: "('a, 's) hml_srbb_conjunct \<Rightarrow> enat" where
  "negation_depth TT = 0" |
  "negation_depth (Internal \<chi>) = neg_depth_inner \<chi>" |
  "negation_depth (ImmConj I \<psi>s) = Sup ((neg_depth_conjunct \<circ> \<psi>s) ` I)" |

  "neg_depth_inner (Obs _ \<phi>) = negation_depth \<phi>" |
  "neg_depth_inner (Conj I \<psi>s) = Sup ((neg_depth_conjunct \<circ> \<psi>s) ` I)" |
  "neg_depth_inner (StableConj I \<psi>s) = Sup ((neg_depth_conjunct \<circ> \<psi>s) ` I)" |
  "neg_depth_inner (BranchConj _ \<phi> I \<psi>s) = Sup ({negation_depth \<phi>} \<union> ((neg_depth_conjunct \<circ> \<psi>s) ` I))" |

  "neg_depth_conjunct (Pos \<chi>) = neg_depth_inner \<chi>" |
  "neg_depth_conjunct (Neg \<chi>) = 1 + neg_depth_inner \<chi>" 

subsection \<open>Expressiveness price function\<close>

fun expressiveness_price :: "('a, 's) hml_srbb \<Rightarrow> energy" where
  "expressiveness_price \<phi> = E (modal_depth_srbb            \<phi>)
                              (branching_conjunction_depth \<phi>)
                              (instable_conjunction_depth  \<phi>)
                              (stable_conjunction_depth    \<phi>)
                              (immediate_conjunction_depth \<phi>)
                              (max_positive_conjunct_depth \<phi>)
                              (max_negative_conjunct_depth \<phi>)
                              (negation_depth              \<phi>)"

lemma expressiveness_price_ImmConj_def:
  shows "expressiveness_price (ImmConj I \<psi>s) = E 
    (Sup ((modal_depth_srbb_conjunct \<circ> \<psi>s) ` I))
    (Sup ((branch_conj_depth_conjunct \<circ> \<psi>s) ` I))
    (if I = {} then 0 else 1 + Sup ((inst_conj_depth_conjunct \<circ> \<psi>s) ` I))
    (Sup ((st_conj_depth_conjunct \<circ> \<psi>s) ` I))
    (if I = {} then 0 else 1 + Sup ((imm_conj_depth_conjunct \<circ> \<psi>s) ` I))
    (Sup ((max_pos_conj_depth_conjunct \<circ> \<psi>s) ` I))
    (Sup ((max_neg_conj_depth_conjunct \<circ> \<psi>s) ` I))
    (Sup ((neg_depth_conjunct \<circ> \<psi>s) ` I))" by simp

lemma expressiveness_price_ImmConj_non_empty_def:
  assumes "I \<noteq> {}"
  shows "expressiveness_price (ImmConj I \<psi>s) = E 
    (Sup ((modal_depth_srbb_conjunct \<circ> \<psi>s) ` I))
    (Sup ((branch_conj_depth_conjunct \<circ> \<psi>s) ` I))
    (1 + Sup ((inst_conj_depth_conjunct \<circ> \<psi>s) ` I))
    (Sup ((st_conj_depth_conjunct \<circ> \<psi>s) ` I))
    (1 + Sup ((imm_conj_depth_conjunct \<circ> \<psi>s) ` I))
    (Sup ((max_pos_conj_depth_conjunct \<circ> \<psi>s) ` I))
    (Sup ((max_neg_conj_depth_conjunct \<circ> \<psi>s) ` I))
    (Sup ((neg_depth_conjunct \<circ> \<psi>s) ` I))" using assms  by simp

lemma expressiveness_price_ImmConj_empty_def:
  assumes "I = {}"
  shows "expressiveness_price (ImmConj I \<psi>s) = E 0 0 0 0 0 0 0 0" using assms 
  unfolding expressiveness_price_ImmConj_def by (simp add: bot_enat_def)

lemma srbb_price_never_neg : "expressiveness_price \<phi> \<noteq> eneg"
  by simp

definition \<O> :: "energy \<Rightarrow> (('a, 's) hml_srbb) set" where
  "\<O> energy \<equiv> {\<phi> . expressiveness_price \<phi> \<le> energy}"

fun expr_pr_inner :: "('a, 's) hml_srbb_inner \<Rightarrow> energy" where
  "expr_pr_inner \<chi> = E (modal_depth_srbb_inner \<chi>)
                 (branch_conj_depth_inner \<chi>)
                 (inst_conj_depth_inner \<chi>)
                 (st_conj_depth_inner \<chi>)
                 (imm_conj_depth_inner \<chi>)
                 (max_pos_conj_depth_inner \<chi>)
                 (max_neg_conj_depth_inner \<chi>)
                 (neg_depth_inner \<chi>)"

lemma \<chi>_price_never_neg: "expr_pr_inner \<chi> \<noteq> eneg"
  by simp

definition \<O>_inner :: "energy \<Rightarrow> (('a, 's) hml_srbb_inner) set" where
  "\<O>_inner energy \<equiv> {\<chi> . expr_pr_inner \<chi> \<le> energy}"

fun expr_pr_conjunct :: "('a, 's) hml_srbb_conjunct \<Rightarrow> energy" where
  "expr_pr_conjunct \<psi> = E (modal_depth_srbb_conjunct \<psi>)
                 (branch_conj_depth_conjunct \<psi>)
                 (inst_conj_depth_conjunct \<psi>)
                 (st_conj_depth_conjunct \<psi>)
                 (imm_conj_depth_conjunct \<psi>)
                 (max_pos_conj_depth_conjunct \<psi>)
                 (max_neg_conj_depth_conjunct \<psi>)
                 (neg_depth_conjunct \<psi>)"

definition \<O>_conjunct :: "energy \<Rightarrow> (('a, 's) hml_srbb_conjunct) set" where
  "\<O>_conjunct energy \<equiv> {\<chi> . expr_pr_conjunct \<chi> \<le> energy}"

lemma \<psi>_price_never_neg:
  shows "expr_pr_conjunct \<psi> \<noteq> eneg"
  by simp

lemma expressiveness_price_ImmConj_geq_parts:
  assumes "i \<in> I" "I \<noteq> {}"
  shows "expressiveness_price (ImmConj I \<psi>s) - E 0 0 1 0 1 0 0 0 \<ge> expr_pr_conjunct (\<psi>s i)"
proof-
  from expressiveness_price_ImmConj_non_empty_def[OF assms(2)] 
  have "expressiveness_price (ImmConj I \<psi>s) \<ge> E 0 0 1 0 1 0 0 0"
    using energy_leq_cases by force
  from direct_minus_eq[OF this] have
  "expressiveness_price (ImmConj I \<psi>s) - E 0 0 1 0 1 0 0 0 = E
    (Sup ((modal_depth_srbb_conjunct \<circ> \<psi>s) ` I))
    (Sup ((branch_conj_depth_conjunct \<circ> \<psi>s) ` I))
    (Sup ((inst_conj_depth_conjunct \<circ> \<psi>s) ` I))
    (Sup ((st_conj_depth_conjunct \<circ> \<psi>s) ` I))
    (Sup ((imm_conj_depth_conjunct \<circ> \<psi>s) ` I))
    (Sup ((max_pos_conj_depth_conjunct \<circ> \<psi>s) ` I))
    (Sup ((max_neg_conj_depth_conjunct \<circ> \<psi>s) ` I))
    (Sup ((neg_depth_conjunct \<circ> \<psi>s) ` I))" unfolding expressiveness_price_ImmConj_non_empty_def[OF assms(2)] by auto
  also have "... \<ge> expr_pr_conjunct (\<psi>s i)" using assms using SUP_upper leq_not_eneg by fastforce
  finally show ?thesis .
qed

lemma expressiveness_price_ImmConj_geq_parts':
  assumes "i \<in> I" "I \<noteq> {}"
  shows "(expressiveness_price (ImmConj I \<psi>s) - E 0 0 0 0 1 0 0 0) - E 0 0 1 0 0 0 0 0 \<ge> expr_pr_conjunct (\<psi>s i)"
  using expressiveness_price_ImmConj_geq_parts[OF assms]
  less_eq_energy_def minus_energy_def
  by (smt (z3) assms(2) energy.case_eq_if energy.simps(4)
      energy_minus expressiveness_price_ImmConj_non_empty_def
      idiff_0_right linorder_le_less_linear not_less_zero)

subsection \<open>characterizing equivalence by energy coordinates\<close>

context Inhabited_Tau_LTS
begin

definition expr_preord :: "'s \<Rightarrow> energy \<Rightarrow> 's \<Rightarrow> bool" ("_ \<preceq> _ _" 60) where
  "(p \<preceq> e q) \<equiv> hml_preordered (\<O> e) p q"

definition expr_equiv :: "'s \<Rightarrow> energy \<Rightarrow> 's \<Rightarrow> bool" ("_ \<sim> _ _" 60) where
  "(p \<sim> e q) \<equiv> hml_equivalent (\<O> e) p q"

end


context Inhabited_LTS
begin

lemma example_\<phi>_cp:
  fixes op::"'a" and a:: "'a" and b::"'a"
  defines \<phi>: "\<phi> \<equiv> 
    (Internal
      (Obs op 
        (Internal 
          (Conj {left, right} 
                (\<lambda>i. (if i = left
                      then (Pos (Obs a TT))
                      else if i = right
                           then (Pos (Obs b TT))
                           else undefined))))))"
  shows
      "modal_depth_srbb            \<phi> = 2"
  and "branching_conjunction_depth \<phi> = 0"
  and "instable_conjunction_depth  \<phi> = 1"
  and "stable_conjunction_depth    \<phi> = 0"
  and "immediate_conjunction_depth \<phi> = 0"
  and "max_positive_conjunct_depth \<phi> = 1"
  and "max_negative_conjunct_depth \<phi> = 0"
  and "negation_depth              \<phi> = 0"
  unfolding \<phi>
  by simp+

lemma "expressiveness_price (Internal
      (Obs op 
        (Internal 
          (Conj {left, right} 
                (\<lambda>i. (if i = left
                      then (Pos (Obs a TT))
                      else if i = right
                           then (Pos (Obs b TT))
                           else undefined)))))) = E 2 0 1 0 0 1 0 0"
  by simp

lemma "expressiveness_price TT = E 0 0 0 0 0 0 0 0"
  by simp

lemma "expressiveness_price (ImmConj {} \<psi>s) = E 0 0 0 0 0 0 0 0"
  by (simp add: Sup_enat_def)

lemma "expressiveness_price (Internal (Conj {} \<psi>s)) = E 0 0 0 0 0 0 0 0"
  by (simp add: Sup_enat_def)

lemma "expressiveness_price (Internal (BranchConj \<alpha> TT {} \<psi>s)) = E 1 0 0 0 0 0 0 0"
  by (simp add: Sup_enat_def)

lemma expr_obs:
  assumes "expressiveness_price \<phi> \<le> (e - E 1 0 0 0 0 0 0 0)"
  shows "expr_pr_inner (Obs \<alpha> \<phi>) \<le> e"
proof-
  have expr_pr_obs: "expr_pr_inner (Obs \<alpha> \<phi>) = 
                  (E (modal_depth_srbb_inner (Obs \<alpha> \<phi>))
                 (branch_conj_depth_inner (Obs \<alpha> \<phi>))
                 (inst_conj_depth_inner (Obs \<alpha> \<phi>))
                 (st_conj_depth_inner (Obs \<alpha> \<phi>))
                 (imm_conj_depth_inner (Obs \<alpha> \<phi>))
                 (max_pos_conj_depth_inner (Obs \<alpha> \<phi>))
                 (max_neg_conj_depth_inner (Obs \<alpha> \<phi>))
                 (neg_depth_inner (Obs \<alpha> \<phi>)))"
    using expr_pr_inner.simps by blast
  have obs_upds: "modal_depth_srbb_inner (Obs \<alpha> \<phi>) = 1 + modal_depth_srbb \<phi>" 
  "branch_conj_depth_inner (Obs \<alpha> \<phi>) = branching_conjunction_depth \<phi>"
  "inst_conj_depth_inner (Obs \<alpha> \<phi>) = instable_conjunction_depth \<phi>"
  "st_conj_depth_inner (Obs \<alpha> \<phi>) = stable_conjunction_depth \<phi>"
  "imm_conj_depth_inner (Obs \<alpha> \<phi>) = immediate_conjunction_depth \<phi>"
  "max_pos_conj_depth_inner (Obs \<alpha> \<phi>) = max_positive_conjunct_depth \<phi>"
  "max_neg_conj_depth_inner (Obs \<alpha> \<phi>) = max_negative_conjunct_depth \<phi>"
  "neg_depth_inner (Obs \<alpha> \<phi>) = negation_depth \<phi>"
    by simp+

  obtain e1 e2 e3 e4 e5 e6 e7 e8 where "e = E e1 e2 e3 e4 e5 e6 e7 e8"
    by (metis antisym assms eneg_leq energy.exhaust_sel gets_smaller srbb_price_never_neg)
  hence "(e - (E 1 0 0 0 0 0 0 0)) = (E (e1-1) e2 e3 e4 e5 e6 e7 e8) \<or> 
                  ((e - (E 1 0 0 0 0 0 0 0)) = eneg)"
            using minus_energy_def
            by simp
  then show ?thesis
  proof(rule disjE)
  assume "e - E 1 0 0 0 0 0 0 0 = eneg"
  hence "e = (E 0 0 0 0 0 0 0 0)"
    using assms
    using antisym eneg_leq min_eneg(2) by fastforce
  then show ?thesis 
    using \<open>e - E 1 0 0 0 0 0 0 0 = eneg\<close> assms 
    using eneg_leq order_class.order_eq_iff by auto
next
  assume "e - E 1 0 0 0 0 0 0 0 = E (e1 - 1) e2 e3 e4 e5 e6 e7 e8"
  hence "modal_depth_srbb \<phi> \<le> (e1 - 1)"
    using assms leq_not_eneg by force
  hence "modal_depth_srbb_inner (Obs \<alpha> \<phi>) \<le> e1"
    using obs_upds
    by (metis \<open>e - E 1 0 0 0 0 0 0 0 = E (e1 - 1) e2 e3 e4 e5 e6 e7 e8\<close> \<open>e = E e1 e2 e3 e4 e5 e6 e7 e8\<close> add_diff_assoc_enat add_diff_cancel_enat add_mono_thms_linordered_semiring(1) enat.simps(3) energy.distinct(1) energy.sel(1) le_numeral_extra(4) leq_not_eneg minus_energy_def one_enat_def)
  then show ?thesis
    using expr_pr_obs obs_upds 
    using \<open>e - E 1 0 0 0 0 0 0 0 = E (e1 - 1) e2 e3 e4 e5 e6 e7 e8\<close> \<open>e = E e1 e2 e3 e4 e5 e6 e7 e8\<close> assms leq_not_eneg by fastforce 
qed
qed

lemma expr_obs_phi:
  shows "e1 (expr_pr_inner (Obs \<alpha> \<phi>)) = expressiveness_price \<phi>"
  by (simp add: direct_minus_eq energy_leq_cases le_iff_add)

end

end
