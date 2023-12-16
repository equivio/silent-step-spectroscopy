theory HML_SRBB
  imports Main HML
begin

datatype 
  ('act, 'i) hml_srbb =
    TT |
    Internal "('act, 'i) hml_srbb_conjunction" |
    ImmConj "'i set" "'i \<Rightarrow> ('act, 'i) hml_srbb_conjunct"
and
  ('act, 'i) hml_srbb_conjunction =
    Obs 'act "('act, 'i) hml_srbb" |
    Conj "'i set" "'i \<Rightarrow> ('act, 'i) hml_srbb_conjunct" |
    StableConj "'i set" "'i \<Rightarrow> ('act, 'i) hml_srbb_conjunct" |
    BranchConj 'act "('act, 'i) hml_srbb"
               "'i set" "'i \<Rightarrow> ('act, 'i) hml_srbb_conjunct"
and
  ('act, 'i) hml_srbb_conjunct =
    Pos "('act, 'i) hml_srbb_conjunction" |
    Neg "('act, 'i) hml_srbb_conjunction"


context Inhabited_Tau_LTS
begin

primrec
      hml_srbb_to_hml :: "('a, 's) hml_srbb \<Rightarrow> ('a, 's) hml"
  and hml_srbb_conjunction_to_hml :: "('a, 's) hml_srbb_conjunction \<Rightarrow> ('a, 's) hml"
  and hml_srbb_conjunct_to_hml_conjunct :: "('a, 's) hml_srbb_conjunct \<Rightarrow> ('a, 's) hml_conjunct" where
  "hml_srbb_to_hml TT = hml.TT" |
  "hml_srbb_to_hml (Internal \<chi>) = hml.Internal (hml_srbb_conjunction_to_hml \<chi>)" |
  "hml_srbb_to_hml (ImmConj I \<psi>s) = hml.Conj I (hml_srbb_conjunct_to_hml_conjunct \<circ> \<psi>s)" |

  "hml_srbb_conjunction_to_hml (Obs a \<phi>) = hml.Obs a (hml_srbb_to_hml \<phi>)" |
  "hml_srbb_conjunction_to_hml (Conj I \<psi>s) = hml.Conj I (hml_srbb_conjunct_to_hml_conjunct \<circ> \<psi>s)" |

  "hml_srbb_conjunction_to_hml (StableConj I \<psi>s) =
    (hml_conjunct.Neg (hml.Obs \<tau> hml.TT)
     \<and>hml hml_conjunct.Pos (hml.Conj I (hml_srbb_conjunct_to_hml_conjunct \<circ> \<psi>s)))" |

  "hml_srbb_conjunction_to_hml (BranchConj a \<phi> I \<psi>s) = 
     (hml_conjunct.Pos (HML_soft_poss a (hml_srbb_to_hml \<phi>))
      \<and>hml hml_conjunct.Pos (hml.Conj I (hml_srbb_conjunct_to_hml_conjunct \<circ> \<psi>s)))" |

  "hml_srbb_conjunct_to_hml_conjunct (Pos \<chi>) = hml_conjunct.Pos (hml.Internal (hml_srbb_conjunction_to_hml \<chi>))" |
  "hml_srbb_conjunct_to_hml_conjunct (Neg \<chi>) = hml_conjunct.Neg (hml.Internal (hml_srbb_conjunction_to_hml \<chi>))"

fun hml_srbb_models :: "'s \<Rightarrow> ('a, 's) hml_srbb \<Rightarrow> bool" (infix "\<Turnstile>SRBB" 60)where
  "hml_srbb_models state formula = (state \<Turnstile> (hml_srbb_to_hml formula))"

(*Some sanity checks*)

lemma "(state \<Turnstile>SRBB TT) = (state \<Turnstile>SRBB ImmConj {} \<psi>s)"
  by simp

lemma "(state \<Turnstile>SRBB Internal \<chi>) = (state \<Turnstile>SRBB ImmConj {left} (\<lambda>i. if i = left then Pos \<chi> else undefined))"
  by simp

definition hml_preordered :: "(('a, 's) hml_srbb) set \<Rightarrow> 's \<Rightarrow> 's \<Rightarrow> bool" where
  "hml_preordered \<phi>s p q \<equiv> \<forall>\<phi> \<in> \<phi>s. p \<Turnstile>SRBB \<phi> \<longrightarrow> q \<Turnstile>SRBB \<phi>"

definition distinguishes :: "('a, 's) hml_srbb \<Rightarrow> 's \<Rightarrow> 's \<Rightarrow> bool" where
  "distinguishes \<phi> p q \<equiv> p \<Turnstile>SRBB \<phi> \<and> \<not>(q \<Turnstile>SRBB \<phi>)"

definition hml_equivalent :: "(('a, 's) hml_srbb) set \<Rightarrow> 's \<Rightarrow> 's \<Rightarrow> bool" where
  "hml_equivalent \<phi>s l r \<equiv> hml_preordered \<phi>s l r \<and> hml_preordered \<phi>s r l"


lemma "hml_preordered \<phi>s l r = (\<forall>\<phi> \<in> \<phi>s. \<not>(distinguishes \<phi> l r))"
  by (simp add: distinguishes_def hml_preordered_def)

lemma "hml_equivalent \<phi>s l r = (\<forall>\<phi> \<in> \<phi>s. \<not>(distinguishes \<phi> l r) \<and> \<not>(distinguishes \<phi> r l))"
  using distinguishes_def hml_equivalent_def hml_preordered_def by auto

lemma "equivp (hml_equivalent \<phi>s)"
proof (rule equivpI)
  show "reflp (hml_equivalent \<phi>s)" 
    by (simp add: hml_equivalent_def hml_preordered_def reflpI)
next
  show "symp (hml_equivalent \<phi>s)" 
    by (metis hml_equivalent_def sympI)
next
  show "transp (hml_equivalent \<phi>s)" 
    by (smt (verit) hml_equivalent_def hml_preordered_def transpI)
qed

lemma "reflp (hml_preordered \<phi>s) \<and> transp (hml_preordered \<phi>s)"
proof (rule conjI)
  show "reflp (hml_preordered \<phi>s)" 
    by (simp add: hml_preordered_def reflpI)
next
  show "transp (hml_preordered \<phi>s)" 
    by (smt (verit, best) hml_preordered_def transpI)
qed

lemma "\<phi>s \<subseteq> \<phi>s' \<Longrightarrow> hml_equivalent \<phi>s' l r \<Longrightarrow> hml_equivalent \<phi>s l r"
  by (meson hml_equivalent_def hml_preordered_def subsetD)

lemma "hml_preordered \<phi>s l r = (\<forall>\<phi> \<in> \<phi>s. \<not>(distinguishes \<phi> l r))"
  using distinguishes_def hml_preordered_def by auto

lemma "hml_equivalent \<phi>s l r = (\<forall>\<phi> \<in> \<phi>s. \<not>(distinguishes \<phi> l r) \<and> \<not>(distinguishes \<phi> r l))"
  using distinguishes_def hml_equivalent_def hml_preordered_def by auto

end (* Inhabited_Tau_LTS *)

context LTS_Tau
begin

inductive tau_obs_free :: "('a, 's) hml_srbb \<Rightarrow> bool"
  and tau_obs_free_\<chi> :: "('a, 's) hml_srbb_conjunction \<Rightarrow> bool"
  and tau_obs_free_\<psi> :: "('a, 's) hml_srbb_conjunct \<Rightarrow> bool" where
  "tau_obs_free TT" |
  "tau_obs_free (Internal \<chi>)" if "tau_obs_free_\<chi> \<chi>" |
  "tau_obs_free (ImmConj I \<psi>s)" if "\<forall>i \<in> I. tau_obs_free_\<psi> (\<psi>s i)" |

  "tau_obs_free_\<chi> (Obs \<alpha> \<phi>)" if "\<alpha> \<noteq> \<tau>" and "tau_obs_free \<phi>" |
  "tau_obs_free_\<chi> (Conj I \<psi>s)" if "\<forall>i \<in> I. tau_obs_free_\<psi> (\<psi>s i)" |
  "tau_obs_free_\<chi> (StableConj I \<psi>s)" if "\<forall>i \<in> I. tau_obs_free_\<psi> (\<psi>s i)" |
  "tau_obs_free_\<chi> (BranchConj _ \<phi> I \<psi>s)" if "tau_obs_free \<phi>" and "\<forall>i \<in> I. tau_obs_free_\<psi> (\<psi>s i)" |

  "tau_obs_free_\<psi> (Pos \<chi>)" if "tau_obs_free_\<chi> \<chi>" |
  "tau_obs_free_\<psi> (Neg \<chi>)" if "tau_obs_free_\<chi> \<chi>"

lemma tau_free_so_\<alpha>_not_\<tau>: "tau_obs_free_\<chi> (Obs \<alpha> \<phi>) \<Longrightarrow> \<alpha> \<noteq> \<tau>"
  using hml_srbb_conjunction.distinct(5) tau_obs_free_\<chi>.cases by auto

end
  

context Inhabited_Tau_LTS
begin

primrec
      hml_srbb_to_hml' :: "('a, 's) hml_srbb \<Rightarrow> ('a, 's) hml"
  and hml_srbb_conjunction_to_hml' :: "('a, 's) hml_srbb_conjunction \<Rightarrow> ('a, 's) hml"
  and hml_srbb_conjunct_to_hml_conjunct' :: "('a, 's) hml_srbb_conjunct \<Rightarrow> ('a, 's) hml_conjunct" where
  "hml_srbb_to_hml' TT = hml.TT" |
  "hml_srbb_to_hml' (Internal \<chi>) = hml.Internal (hml_srbb_conjunction_to_hml' \<chi>)" |
  "hml_srbb_to_hml' (ImmConj I \<psi>s) = hml.Conj I (hml_srbb_conjunct_to_hml_conjunct' \<circ> \<psi>s)" |

  "hml_srbb_conjunction_to_hml' (Obs a \<phi>) = HML_soft_poss a (hml_srbb_to_hml' \<phi>)" |
  "hml_srbb_conjunction_to_hml' (Conj I \<psi>s) = hml.Conj I (hml_srbb_conjunct_to_hml_conjunct' \<circ> \<psi>s)" |

  "hml_srbb_conjunction_to_hml' (StableConj I \<psi>s) =
    (hml_conjunct.Neg (hml.Obs \<tau> hml.TT)
     \<and>hml hml_conjunct.Pos (hml.Conj I (hml_srbb_conjunct_to_hml_conjunct' \<circ> \<psi>s)))" |

  "hml_srbb_conjunction_to_hml' (BranchConj a \<phi> I \<psi>s) = 
     (hml_conjunct.Pos (HML_soft_poss a (hml_srbb_to_hml' \<phi>))
      \<and>hml hml_conjunct.Pos (hml.Conj I (hml_srbb_conjunct_to_hml_conjunct' \<circ> \<psi>s)))" |

  "hml_srbb_conjunct_to_hml_conjunct' (Pos \<chi>) = hml_conjunct.Pos (hml.Internal (hml_srbb_conjunction_to_hml' \<chi>))" |
  "hml_srbb_conjunct_to_hml_conjunct' (Neg \<chi>) = hml_conjunct.Neg (hml.Internal (hml_srbb_conjunction_to_hml' \<chi>))"


lemma
  fixes \<phi> :: "('a, 's) hml_srbb"
    and \<chi> :: "('a, 's) hml_srbb_conjunction"
    and \<psi> :: "('a, 's) hml_srbb_conjunct"
  shows "(\<forall>state. tau_obs_free \<phi> \<longrightarrow> ((state \<Turnstile> (hml_srbb_to_hml \<phi>)) \<longleftrightarrow> (state \<Turnstile> (hml_srbb_to_hml' \<phi>))))
        \<and> (\<forall>state'. tau_obs_free_\<chi> \<chi> \<longrightarrow> ((state' \<Turnstile> (hml_srbb_conjunction_to_hml \<chi>)) \<longleftrightarrow> (state' \<Turnstile> (hml_srbb_conjunction_to_hml' \<chi>))))
        \<and> (\<forall>state''. tau_obs_free_\<psi> \<psi> \<longrightarrow> ((hml_conjunct_models state'' (hml_srbb_conjunct_to_hml_conjunct \<psi>)) \<longleftrightarrow> (hml_conjunct_models state'' (hml_srbb_conjunct_to_hml_conjunct' \<psi>))))"
  apply (rule hml_srbb_hml_srbb_conjunction_hml_srbb_conjunct.induct)
  apply simp 
  apply (metis LTS_Tau.hml_models.simps(3) hml_srbb.distinct(1) hml_srbb.distinct(5) hml_srbb.inject(1) hml_srbb_to_hml'.simps(2) hml_srbb_to_hml.simps(2) tau_obs_free.cases)
  apply (smt (verit) comp_apply hml_models.simps(5) hml_srbb.distinct(3) hml_srbb.distinct(5) hml_srbb.inject(2) hml_srbb_to_hml'.simps(3) hml_srbb_to_hml.simps(3) range_eqI tau_obs_free.cases)
  apply (smt (verit) hml_models.simps(2) hml_srbb_conjunction.distinct(1) hml_srbb_conjunction.distinct(3) hml_srbb_conjunction.distinct(5) hml_srbb_conjunction.inject(1) hml_srbb_conjunction_to_hml'.simps(1) hml_srbb_conjunction_to_hml.simps(1) tau_obs_free_\<chi>.cases)
  apply (smt (verit) comp_apply hml_models.simps(5) hml_srbb_conjunction.distinct(1) hml_srbb_conjunction.distinct(7) hml_srbb_conjunction.distinct(9) hml_srbb_conjunction.inject(2) hml_srbb_conjunction_to_hml'.simps(2) hml_srbb_conjunction_to_hml.simps(2) range_eqI tau_obs_free_\<chi>.cases)
  apply (smt (verit) comp_def hml_conjunct_models.simps(1) hml_models.simps(5) hml_srbb_conjunction.distinct(11) hml_srbb_conjunction.distinct(3) hml_srbb_conjunction.distinct(7) hml_srbb_conjunction.inject(3) hml_srbb_conjunction_to_hml'.simps(3) hml_srbb_conjunction_to_hml.simps(3) range_eqI tau_obs_free_\<chi>.cases)
proof -
  fix \<alpha> :: 'a 
    and \<phi> :: "('a, 's) hml_srbb" 
    and I :: "'s set"
    and \<psi>s :: "'s \<Rightarrow> ('a, 's) hml_srbb_conjunct"
  assume IH1: "\<forall>state. tau_obs_free \<phi> \<longrightarrow> state \<Turnstile> hml_srbb_to_hml \<phi> = state \<Turnstile> hml_srbb_to_hml' \<phi>"
    and IH2: "(\<And>\<psi>. \<psi> \<in> range \<psi>s \<Longrightarrow>
               \<forall>state''.
                  tau_obs_free_\<psi> \<psi> \<longrightarrow>
                  hml_conjunct_models state'' (hml_srbb_conjunct_to_hml_conjunct \<psi>) =
                  hml_conjunct_models state'' (hml_srbb_conjunct_to_hml_conjunct' \<psi>))"
  show "\<forall>state'.
          tau_obs_free_\<chi> (BranchConj \<alpha> \<phi> I \<psi>s) \<longrightarrow>
          (state' \<Turnstile> hml_srbb_conjunction_to_hml (BranchConj \<alpha> \<phi> I \<psi>s)) =
          (state' \<Turnstile> hml_srbb_conjunction_to_hml' (BranchConj \<alpha> \<phi> I \<psi>s))"
  proof (rule allI, rule impI, cases \<open>\<alpha> = \<tau>\<close>)
    fix state'
    assume "tau_obs_free_\<chi> (BranchConj \<alpha> \<phi> I \<psi>s)"
      and "\<alpha> = \<tau>"
    show "state' \<Turnstile> hml_srbb_conjunction_to_hml (BranchConj \<alpha> \<phi> I \<psi>s) =
       state' \<Turnstile> hml_srbb_conjunction_to_hml' (BranchConj \<alpha> \<phi> I \<psi>s)"
    proof (rule iffI)
      assume "state' \<Turnstile> hml_srbb_conjunction_to_hml (BranchConj \<alpha> \<phi> I \<psi>s)"
      hence "hml_conjunct_models state' (hml_conjunct.Pos (HML_soft_poss \<alpha> (hml_srbb_to_hml \<phi>)))"
        and "hml_conjunct_models state' (hml_conjunct.Pos (hml.Conj I (hml_srbb_conjunct_to_hml_conjunct \<circ> \<psi>s)))"
        unfolding hml_srbb_conjunction_to_hml.simps
        using HML_and_logic_and 
        by blast+

      show "state' \<Turnstile> hml_srbb_conjunction_to_hml' (BranchConj \<alpha> \<phi> I \<psi>s)" 
        unfolding hml_srbb_conjunction_to_hml'.simps
        unfolding HML_and_logic_and
      proof (rule conjI)
        show "hml_conjunct_models state' (hml_conjunct.Pos (HML_soft_poss \<alpha> (hml_srbb_to_hml' \<phi>)))"
          using \<open>hml_conjunct_models state' (hml_conjunct.Pos (HML_soft_poss \<alpha> (hml_srbb_to_hml \<phi>)))\<close>
            and IH1 
          using \<open>\<alpha> = \<tau>\<close> \<open>tau_obs_free_\<chi> (BranchConj \<alpha> \<phi> I \<psi>s)\<close> hml_conjunct_models.simps(1) hml_models.simps(4) hml_srbb_conjunction.distinct(11) hml_srbb_conjunction.inject(4) tau_obs_free_\<chi>.simps by auto
      next
        show "hml_conjunct_models state' (hml_conjunct.Pos (hml.Conj I (hml_srbb_conjunct_to_hml_conjunct' \<circ> \<psi>s)))"
          using \<open>hml_conjunct_models state' (hml_conjunct.Pos (hml.Conj I (hml_srbb_conjunct_to_hml_conjunct \<circ> \<psi>s)))\<close>
            and IH2 rangeI 
          by (smt (verit) \<open>tau_obs_free_\<chi> (BranchConj \<alpha> \<phi> I \<psi>s)\<close> comp_def hml_conjunct_models.simps(1) hml_models.simps(5) hml_srbb_conjunction.distinct(11) hml_srbb_conjunction.distinct(5) hml_srbb_conjunction.distinct(9) hml_srbb_conjunction.inject(4) tau_obs_free_\<chi>.cases)
      qed        
    next
      assume "state' \<Turnstile> hml_srbb_conjunction_to_hml' (BranchConj \<alpha> \<phi> I \<psi>s)"
      hence "hml_conjunct_models state' (hml_conjunct.Pos (HML_soft_poss \<alpha> (hml_srbb_to_hml' \<phi>)))"
         and "hml_conjunct_models state' (hml_conjunct.Pos (hml.Conj I (hml_srbb_conjunct_to_hml_conjunct' \<circ> \<psi>s)))"
        unfolding hml_srbb_conjunction_to_hml'.simps
        unfolding HML_and_logic_and by blast+
      show "state' \<Turnstile> hml_srbb_conjunction_to_hml (BranchConj \<alpha> \<phi> I \<psi>s)"
        unfolding hml_srbb_conjunction_to_hml.simps
        unfolding HML_and_logic_and
      proof (rule conjI)
        show "hml_conjunct_models state' (hml_conjunct.Pos (HML_soft_poss \<alpha> (hml_srbb_to_hml \<phi>)))"
          using \<open>hml_conjunct_models state' (hml_conjunct.Pos (HML_soft_poss \<alpha> (hml_srbb_to_hml' \<phi>)))\<close>
            and IH1 
            and \<open>\<alpha> = \<tau>\<close>
            and \<open>tau_obs_free_\<chi> (BranchConj \<alpha> \<phi> I \<psi>s)\<close> 
          using hml_srbb_conjunction.distinct(11) hml_srbb_conjunction.distinct(5) hml_srbb_conjunction.distinct(9) tau_obs_free_\<chi>.cases by fastforce
      next
        show "hml_conjunct_models state' (hml_conjunct.Pos (hml.Conj I (hml_srbb_conjunct_to_hml_conjunct \<circ> \<psi>s)))"
          using \<open>hml_conjunct_models state' (hml_conjunct.Pos (hml.Conj I (hml_srbb_conjunct_to_hml_conjunct' \<circ> \<psi>s)))\<close>
            and IH2 
            and \<open>tau_obs_free_\<chi> (BranchConj \<alpha> \<phi> I \<psi>s)\<close> 
          by (smt (verit) comp_apply hml_conjunct_models.simps(1) hml_models.simps(5) hml_srbb_conjunction.distinct(11) hml_srbb_conjunction.distinct(5) hml_srbb_conjunction.distinct(9) hml_srbb_conjunction.inject(4) rangeI tau_obs_free_\<chi>.cases)
      qed
    qed
  next
    fix state'
    assume "tau_obs_free_\<chi> (BranchConj \<alpha> \<phi> I \<psi>s)"
      and "\<alpha> \<noteq> \<tau>"
    hence "tau_obs_free \<phi>"
      and "\<forall>i \<in> I. tau_obs_free_\<psi> (\<psi>s i)"   
      using tau_obs_free_\<chi>.cases by blast+

    show "state' \<Turnstile> hml_srbb_conjunction_to_hml (BranchConj \<alpha> \<phi> I \<psi>s) =
       state' \<Turnstile> hml_srbb_conjunction_to_hml' (BranchConj \<alpha> \<phi> I \<psi>s)"
    proof (rule iffI)
      assume "state' \<Turnstile> hml_srbb_conjunction_to_hml (BranchConj \<alpha> \<phi> I \<psi>s)"
      hence "hml_conjunct_models state' (hml_conjunct.Pos (HML_soft_poss \<alpha> (hml_srbb_to_hml \<phi>)))"
        and "hml_conjunct_models state' (hml_conjunct.Pos (hml.Conj I (hml_srbb_conjunct_to_hml_conjunct \<circ> \<psi>s)))"
        using hml_srbb_conjunction_to_hml.simps and HML_and_logic_and apply simp
        using hml_srbb_conjunction_to_hml.simps and HML_and_logic_and 
          and \<open>state' \<Turnstile> hml_srbb_conjunction_to_hml (BranchConj \<alpha> \<phi> I \<psi>s)\<close> by presburger

      show "state' \<Turnstile> hml_srbb_conjunction_to_hml' (BranchConj \<alpha> \<phi> I \<psi>s)"
        unfolding hml_srbb_conjunction_to_hml'.simps
              and HML_and_logic_and
      proof (rule conjI)
        show "hml_conjunct_models state' (hml_conjunct.Pos (HML_soft_poss \<alpha> (hml_srbb_to_hml' \<phi>)))"
          using \<open>hml_conjunct_models state' (hml_conjunct.Pos (HML_soft_poss \<alpha> (hml_srbb_to_hml \<phi>)))\<close>
            and IH1 and \<open>\<alpha> \<noteq> \<tau>\<close>
            and \<open>tau_obs_free \<phi>\<close> 
          by simp
      next
        show "hml_conjunct_models state' (hml_conjunct.Pos (hml.Conj I (hml_srbb_conjunct_to_hml_conjunct' \<circ> \<psi>s)))"
          using \<open>hml_conjunct_models state' (hml_conjunct.Pos (hml.Conj I (hml_srbb_conjunct_to_hml_conjunct \<circ> \<psi>s)))\<close>
            and IH2
            and \<open>\<forall>i \<in> I. tau_obs_free_\<psi> (\<psi>s i)\<close> 
          by simp
      qed
    next
      assume "state' \<Turnstile> hml_srbb_conjunction_to_hml' (BranchConj \<alpha> \<phi> I \<psi>s)"
      then show "state' \<Turnstile> hml_srbb_conjunction_to_hml (BranchConj \<alpha> \<phi> I \<psi>s)" 
        using IH1 IH2 \<open>\<alpha> \<noteq> \<tau>\<close> \<open>\<forall>i\<in>I. tau_obs_free_\<psi> (\<psi>s i)\<close> \<open>tau_obs_free \<phi>\<close> comp_apply hml_conjunct_models.simps(1) hml_models.simps(2) hml_models.simps(5) hml_srbb_conjunction_to_hml'.simps(4) hml_srbb_conjunction_to_hml.simps(4) rangeI by auto
    qed
  qed
next
  show "\<And>x. \<forall>state'. tau_obs_free_\<chi> x \<longrightarrow> state' \<Turnstile> hml_srbb_conjunction_to_hml x = state' \<Turnstile> hml_srbb_conjunction_to_hml' x \<Longrightarrow>
         \<forall>state''.
            tau_obs_free_\<psi> (hml_srbb_conjunct.Pos x) \<longrightarrow>
            hml_conjunct_models state'' (hml_srbb_conjunct_to_hml_conjunct (hml_srbb_conjunct.Pos x)) =
            hml_conjunct_models state'' (hml_srbb_conjunct_to_hml_conjunct' (hml_srbb_conjunct.Pos x))"
    
    by (metis LTS_Tau.hml_conjunct_models.simps(1) LTS_Tau.hml_models.simps(3) hml_srbb_conjunct.inject(1) hml_srbb_conjunct.simps(4) hml_srbb_conjunct_to_hml_conjunct'.simps(1) hml_srbb_conjunct_to_hml_conjunct.simps(1) tau_obs_free_\<psi>.cases)
next
  show "\<And>x. \<forall>state'. tau_obs_free_\<chi> x \<longrightarrow> state' \<Turnstile> hml_srbb_conjunction_to_hml x = state' \<Turnstile> hml_srbb_conjunction_to_hml' x \<Longrightarrow>
         \<forall>state''.
            tau_obs_free_\<psi> (hml_srbb_conjunct.Neg x) \<longrightarrow>
            hml_conjunct_models state'' (hml_srbb_conjunct_to_hml_conjunct (hml_srbb_conjunct.Neg x)) =
            hml_conjunct_models state'' (hml_srbb_conjunct_to_hml_conjunct' (hml_srbb_conjunct.Neg x))"
    by (simp add: tau_obs_free_\<psi>.simps)
qed



  
end

end
