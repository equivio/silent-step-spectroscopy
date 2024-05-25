section \<open>HML Contexts\<close>
theory HML_Context
  imports Main HML
begin
text \<open>
This section contains definitions for context based definitions of substitution and congruence.
These are not used in the project, since handing a set of lemmas which handle
substitution or congruence under a single prefix to automatic proof search proved to be more convenient
then manually specifying where exactly in the formula substitution ought to occur.
The added control provided by the mechanisms in this section was never needed and thereby never justified
manually constructing a context term.
We keep this section for the amusement of the interested reader.
\<close>

text \<open> The data type @{term "hml_precontext"} specifies where within a formula one may substitute
an implication leading to a new implication. \<close>

datatype 
  ('act, 'i) hml_precontext =
    PCHole |
    ObsPC 'act "('act, 'i) hml_precontext" |
    InternalPC "('act, 'i) hml_precontext" |
    SilentPC "('act, 'i) hml_precontext" |
    ConjPC "'i set" "'i \<Rightarrow> ('act, 'i) hml_conjunct" "'i set" "'i \<Rightarrow> ('act, 'i) hml_precontext"

text \<open> Given a context and a formula, one may place the formula into the hole of the context to
generate a new formula. Usually, the resulting formula is the one in which one want to substitute
a subformula, while the argument formula is the formula to be substituted.

Note that this definition of data type and filling function ensures that one can never substitute under a negated
conjunct.\<close>

primrec 
      fill_pre :: "('act, 'i) hml \<Rightarrow> ('act, 'i) hml_precontext \<Rightarrow> ('act, 'i) hml" where
  "fill_pre \<phi> PCHole = \<phi>" |
  "fill_pre \<phi> (ObsPC \<alpha> \<phi>') = (Obs \<alpha> (fill_pre \<phi> \<phi>'))" |
  "fill_pre \<phi> (InternalPC \<phi>') = (Internal (fill_pre \<phi> \<phi>'))" |
  "fill_pre \<phi> (SilentPC \<phi>') = (Silent (fill_pre \<phi> \<phi>'))" |
  "fill_pre \<phi> (ConjPC I \<psi>s I' \<psi>s') = (Conj (I \<union> I') (\<lambda>i. if i \<in> I'
                                                     then (Pos (fill_pre \<phi> (\<psi>s' i)))
                                                     else \<psi>s i))"

context LTS_Tau
begin

lemma pre_subst:
  assumes "\<phi>l \<Rrightarrow> \<phi>r"
      and "\<phi> \<Rrightarrow> fill_pre \<phi>l C" 
  shows "\<phi> \<Rrightarrow> fill_pre \<phi>r C"
    oops

lemma pre_cong:
  assumes "\<phi>l \<Rrightarrow> \<phi>r"
  shows "fill_pre \<phi>l C \<Rrightarrow> fill_pre \<phi>r C"
  using assms and hml_impl_def by (induct C) auto[5]

end (* LTS_Tau *)

text \<open> The data type @{term "hml_context"} specifies where within a formula one may substitute
an equivalence leading to a new equivalence. \<close>

datatype 
  ('act, 'i) hml_context =
    Hole |
    ObsC 'act "('act, 'i) hml_context" |
    InternalC "('act, 'i) hml_context" |
    SilentC "('act, 'i) hml_context" |
    ConjC "'i set" "'i \<Rightarrow> ('act, 'i) hml_conjunct" "'i set" "'i 
    \<Rightarrow> ('act, 'i) hml_conjunct_context"
and
  ('act, 'i) hml_conjunct_context =
    PosC "('act, 'i) hml_context" |
    NegC "('act, 'i) hml_context"

text \<open> The function @{term "fill"} serves the same purpose as @{term "fill_pre"}, i.e filling the
hole in a context with a formula, resulting in a formula.\<close>

primrec 
      fill :: "('act, 'i) hml \<Rightarrow> ('act, 'i) hml_context \<Rightarrow> ('act, 'i) hml"
  and fill_conjunct :: "('act, 'i) hml \<Rightarrow> ('act, 'i) hml_conjunct_context \<Rightarrow> ('act, 'i) hml_conjunct" where
  "fill \<phi> Hole = \<phi>" |
  "fill \<phi> (ObsC \<alpha> \<phi>') = (Obs \<alpha> (fill \<phi> \<phi>'))" |
  "fill \<phi> (InternalC \<phi>') = (Internal (fill \<phi> \<phi>'))" |
  "fill \<phi> (SilentC \<phi>') = (Silent (fill \<phi> \<phi>'))" |
  "fill \<phi> (ConjC I \<psi>s I' \<psi>s') = (Conj (I \<union> I') (\<lambda>i. if i \<in> I'
                                                     then fill_conjunct \<phi> (\<psi>s' i)
                                                     else \<psi>s i))" |

  "fill_conjunct \<phi> (PosC \<phi>') = (Pos (fill \<phi> \<phi>'))" |
  "fill_conjunct \<phi> (NegC \<phi>') = (Neg (fill \<phi> \<phi>'))"

text \<open> One may note that here both the context definition as well as the filling function mirror the
structure of the underlying formula data type exactly. \<close>


context LTS_Tau
begin

text \<open> One may substitute an equivalence on one side of another equivalence, which will yield a
new equivalence. \<close>
lemma hml_subst: "\<phi>l \<Lleftarrow>\<Rrightarrow> \<phi>r \<Longrightarrow> (fill \<phi>l C) \<Lleftarrow>\<Rrightarrow> \<phi> \<Longrightarrow> (fill \<phi>r C) \<Lleftarrow>\<Rrightarrow> \<phi>"
             and "\<phi>l \<Lleftarrow>\<Rrightarrow> \<phi>r \<Longrightarrow> (fill_conjunct \<phi>l C') \<Lleftarrow>\<and>\<Rrightarrow> \<psi> \<Longrightarrow> (fill_conjunct \<phi>r C') \<Lleftarrow>\<and>\<Rrightarrow> \<psi>"
  apply (induct C and C' arbitrary: \<phi> and \<psi>)
  using hml_eq_equality apply force
  using LTS_Tau.hml_eq_equiv LTS_Tau.obs_subst equivp_reflp equivp_symp apply fastforce
  using LTS_Tau.hml_eq_equiv LTS_Tau.internal_subst equivp_reflp equivp_symp apply fastforce
  using hml_eq_equality apply fastforce
  defer
  apply (metis equivp_reflp fill_conjunct.simps(1) hml_eq_def hml_eq_equiv pos_subst)
  apply (metis LTS_Tau.neg_subst fill_conjunct.simps(2) hml_eq_equality)
proof -
  fix I \<psi>s I' \<psi>s' \<phi>
  assume IH: "\<And>\<psi>' \<psi>. \<psi>' \<in> range \<psi>s' \<Longrightarrow> \<phi>l \<Lleftarrow>\<Rrightarrow> \<phi>r \<Longrightarrow> fill_conjunct \<phi>l \<psi>' \<Lleftarrow>\<and>\<Rrightarrow> \<psi> \<Longrightarrow> fill_conjunct \<phi>r \<psi>' \<Lleftarrow>\<and>\<Rrightarrow> \<psi>"
        and "\<phi>l \<Lleftarrow>\<Rrightarrow> \<phi>r" 
        and "fill \<phi>l (ConjC I \<psi>s I' \<psi>s') \<Lleftarrow>\<Rrightarrow> \<phi>"
  then have "(\<forall>p. p \<Turnstile> \<phi>l \<longleftrightarrow> p \<Turnstile> \<phi>r)
           \<and> (\<forall>p. p \<Turnstile> Conj (I \<union> I') (\<lambda>i. if i \<in> I' then fill_conjunct \<phi>l (\<psi>s' i) else \<psi>s i) \<longleftrightarrow> p \<Turnstile> \<phi>)"
    unfolding fill.simps and hml_eq_equality
    by force
  then have "\<forall>p. p \<Turnstile> \<phi>l \<longleftrightarrow> p \<Turnstile> \<phi>r"
        and thing: "\<forall>p. p \<Turnstile> Conj (I \<union> I') (\<lambda>i. if i \<in> I' then fill_conjunct \<phi>l (\<psi>s' i) else \<psi>s i) \<longleftrightarrow> p \<Turnstile> \<phi>"
    by auto

  from IH
  have IH2: "\<forall>i \<in> I'. \<phi>l \<Lleftarrow>\<Rrightarrow> \<phi>r \<longrightarrow> fill_conjunct \<phi>l (\<psi>s' i) \<Lleftarrow>\<and>\<Rrightarrow> \<psi> \<longrightarrow> fill_conjunct \<phi>r (\<psi>s' i) \<Lleftarrow>\<and>\<Rrightarrow> \<psi>"
    by blast

  show "fill \<phi>r (ConjC I \<psi>s I' \<psi>s') \<Lleftarrow>\<Rrightarrow> \<phi>"
    unfolding fill.simps and hml_eq_equality
  proof (rule allI)
    fix p
    show "p \<Turnstile> Conj (I \<union> I') (\<lambda>i. if i \<in> I' then fill_conjunct \<phi>r (\<psi>s' i) else \<psi>s i) \<longleftrightarrow> p \<Turnstile> \<phi>"
    proof (rule iffI)
      assume "p \<Turnstile> Conj (I \<union> I') (\<lambda>i. if i \<in> I' then fill_conjunct \<phi>r (\<psi>s' i) else \<psi>s i)"
      then have "(p \<Turnstile> Conj (I - I') \<psi>s)
               \<and> (p \<Turnstile> Conj I' (\<lambda>i. fill_conjunct \<phi>r (\<psi>s' i)))" 
        by (smt (verit, ccfv_threshold) Diff_iff UnI1 UnI2 hml_models.simps(5))
      then have "p \<Turnstile> Conj (I - I') \<psi>s"
            and "p \<Turnstile> Conj I' ((fill_conjunct \<phi>r) \<circ> \<psi>s')" by auto

      from thing
      have "p \<Turnstile> Conj (I \<union> I') (\<lambda>i. if i \<in> I' then fill_conjunct \<phi>l (\<psi>s' i) else \<psi>s i) \<longleftrightarrow> p \<Turnstile> \<phi>" by (rule spec)
      then have "((p \<Turnstile> Conj (I - I') \<psi>s) \<and> (p \<Turnstile> Conj I' (\<lambda>i. fill_conjunct \<phi>l (\<psi>s' i)))) \<longleftrightarrow> p \<Turnstile> \<phi>"  
        by (smt (z3) Un_iff \<open>p \<Turnstile> Conj (I - I') \<psi>s\<close> \<open>p \<Turnstile> Conj (I \<union> I') (\<lambda>i. if i \<in> I' then fill_conjunct \<phi>r (\<psi>s' i) else \<psi>s i)\<close> hml_models.simps(5))
      then have nthing: "((p \<Turnstile> Conj (I - I') \<psi>s) \<and> (p \<Turnstile> Conj I' ((fill_conjunct \<phi>l) \<circ> \<psi>s'))) \<longleftrightarrow> p \<Turnstile> \<phi>"
        by auto

      from \<open>p \<Turnstile> Conj I' ((fill_conjunct \<phi>r) \<circ> \<psi>s')\<close>
       and \<open>\<phi>l \<Lleftarrow>\<Rrightarrow> \<phi>r\<close>
       and IH2
      have "p \<Turnstile> Conj I' ((fill_conjunct \<phi>l) \<circ> \<psi>s')" 
        by (smt (verit) IH LTS_Tau.hml_conjunct_eq_def hml_conjunct_impl_def hml_models.simps(5) o_def rangeI)

      from \<open>((p \<Turnstile> Conj (I - I') \<psi>s) \<and> (p \<Turnstile> Conj I' ((fill_conjunct \<phi>l) \<circ> \<psi>s'))) \<longleftrightarrow> p \<Turnstile> \<phi>\<close>
       and \<open>p \<Turnstile> Conj (I - I') \<psi>s\<close>
       and \<open>p \<Turnstile> Conj I' ((fill_conjunct \<phi>l) \<circ> \<psi>s')\<close>
      show "p \<Turnstile> \<phi>" 
        by blast
    next
      assume "p \<Turnstile> \<phi>"

      with thing
      have "p \<Turnstile> Conj (I \<union> I') (\<lambda>i. if i \<in> I' then fill_conjunct \<phi>l (\<psi>s' i) else \<psi>s i)"
        by blast
      then have "(p \<Turnstile> Conj (I - I') \<psi>s)
               \<and> (p \<Turnstile> Conj I' (\<lambda>i. fill_conjunct \<phi>l (\<psi>s' i)))" 
        by (smt (verit, ccfv_threshold) Diff_iff UnI1 UnI2 hml_models.simps(5))
      then have "p \<Turnstile> Conj (I - I') \<psi>s"
            and "p \<Turnstile> Conj I' (\<lambda>i. fill_conjunct \<phi>l (\<psi>s' i))" by auto
      then have "p \<Turnstile> Conj I' ((fill_conjunct \<phi>l) \<circ> \<psi>s')" by simp
      hence "\<forall>i\<in>I'. hml_conjunct_models p ((fill_conjunct \<phi>l \<circ> \<psi>s') i)"
        unfolding hml_models.simps.

      have "p \<Turnstile> Conj I' ((fill_conjunct \<phi>r) \<circ> \<psi>s')"
        unfolding hml_models.simps
      proof (rule ballI)
        fix i
        assume "i \<in> I'"
        with \<open>\<forall>i\<in>I'. hml_conjunct_models p ((fill_conjunct \<phi>l \<circ> \<psi>s') i)\<close>
          and IH2
          and \<open>\<phi>l \<Lleftarrow>\<Rrightarrow> \<phi>r\<close>
        show "hml_conjunct_models p ((fill_conjunct \<phi>r \<circ> \<psi>s') i)" 
          by (metis IH comp_def hml_conjunct_eq_def hml_conjunct_impl_def rangeI)
      qed

      with \<open>p \<Turnstile> Conj (I - I') \<psi>s\<close>
      show "p \<Turnstile> Conj (I \<union> I') (\<lambda>i. if i \<in> I' then fill_conjunct \<phi>r (\<psi>s' i) else \<psi>s i)" 
        by auto
    qed
  qed
qed

text \<open> If you substitute an equivalence somewhere in a formula, the equivalence is preserved. \<close>
lemma hml_cong: "\<forall>\<phi>l \<phi>r. \<phi>l \<Lleftarrow>\<Rrightarrow> \<phi>r \<longrightarrow> fill \<phi>l C \<Lleftarrow>\<Rrightarrow> fill \<phi>r C"
  and hml_conj_cong: "\<forall>\<phi>l \<phi>r. \<phi>l \<Lleftarrow>\<Rrightarrow> \<phi>r \<longrightarrow> fill_conjunct \<phi>l C' \<Lleftarrow>\<and>\<Rrightarrow> fill_conjunct \<phi>r C'"
  apply (induct C and C')
  prefer 6 prefer 7
  using obs_cong
    and internal_cong
    and silent_cong
    and pos_cong
    and neg_cong
  apply auto[6]
proof -
  fix I :: "'s set"
  and \<psi>s :: "'s \<Rightarrow> ('a, 's) hml_conjunct"
  and I' :: "'s set"
  and \<psi>s' :: "'s \<Rightarrow> ('a, 's) hml_conjunct_context"
  assume "\<And>\<psi>'. \<psi>' \<in> range \<psi>s' \<Longrightarrow> \<forall>\<phi>l \<phi>r. \<phi>l \<Lleftarrow>\<Rrightarrow> \<phi>r \<longrightarrow> fill_conjunct \<phi>l \<psi>' \<Lleftarrow>\<and>\<Rrightarrow> fill_conjunct \<phi>r \<psi>'"
  hence IH: "\<forall>i\<in>I'. \<forall>\<phi>l \<phi>r. \<phi>l \<Lleftarrow>\<Rrightarrow> \<phi>r \<longrightarrow> fill_conjunct \<phi>l (\<psi>s' i) \<Lleftarrow>\<and>\<Rrightarrow> fill_conjunct \<phi>r (\<psi>s' i)" 
    by simp
  show "\<forall>\<phi>l \<phi>r. \<phi>l \<Lleftarrow>\<Rrightarrow> \<phi>r \<longrightarrow> fill \<phi>l (ConjC I \<psi>s I' \<psi>s') \<Lleftarrow>\<Rrightarrow> fill \<phi>r (ConjC I \<psi>s I' \<psi>s')"
  proof (rule allI, rule allI, rule impI)
    fix \<phi>l \<phi>r
    assume "\<phi>l \<Lleftarrow>\<Rrightarrow> \<phi>r"

    show "fill \<phi>l (ConjC I \<psi>s I' \<psi>s') \<Lleftarrow>\<Rrightarrow> fill \<phi>r (ConjC I \<psi>s I' \<psi>s')"
      unfolding hml_eq_def and hml_impl_def
    proof (rule conjI)
      show "\<forall>p. p \<Turnstile> fill \<phi>l (ConjC I \<psi>s I' \<psi>s') \<longrightarrow> p \<Turnstile> fill \<phi>r (ConjC I \<psi>s I' \<psi>s')"
      proof (rule allI, rule impI)
        fix p
        assume "p \<Turnstile> fill \<phi>l (ConjC I \<psi>s I' \<psi>s')"
        hence "\<forall>i\<in>I \<union> I'. hml_conjunct_models p (if i \<in> I' then fill_conjunct \<phi>l (\<psi>s' i) else \<psi>s i)"
          unfolding fill.simps and hml_models.simps.
        then have "(\<forall>i\<in>I'. hml_conjunct_models p (fill_conjunct \<phi>l (\<psi>s' i)))
                 \<and> (\<forall>i\<in>I - I'. hml_conjunct_models p (\<psi>s i))" 
          by (metis (full_types) DiffD1 DiffD2 Un_iff)
        then have "\<forall>i\<in>I'. hml_conjunct_models p (fill_conjunct \<phi>l (\<psi>s' i))"
              and "\<forall>i\<in>I - I'. hml_conjunct_models p (\<psi>s i)" by auto

        from \<open>\<forall>i\<in>I'. hml_conjunct_models p (fill_conjunct \<phi>l (\<psi>s' i))\<close>
         and \<open>\<phi>l \<Lleftarrow>\<Rrightarrow> \<phi>r\<close>
         and IH
        have "\<forall>i\<in>I'. hml_conjunct_models p (fill_conjunct \<phi>r (\<psi>s' i))" 
          using hml_conjunct_eq_def hml_conjunct_impl_def by blast

        from \<open>\<forall>i\<in>I - I'. hml_conjunct_models p (\<psi>s i)\<close>
        have "\<forall>i\<in>I - I'. hml_conjunct_models p (\<psi>s i)".

        from \<open>\<forall>i\<in>I'. hml_conjunct_models p (fill_conjunct \<phi>r (\<psi>s' i))\<close>
         and \<open>\<forall>i\<in>I - I'. hml_conjunct_models p (\<psi>s i)\<close>
        have "\<forall>i\<in>I \<union> I'. hml_conjunct_models p (if i \<in> I' then fill_conjunct \<phi>r (\<psi>s' i) else \<psi>s i)" 
          by auto

        then show "p \<Turnstile> fill \<phi>r (ConjC I \<psi>s I' \<psi>s')"
          unfolding fill.simps and hml_models.simps.
      qed
    next
      show " \<forall>p. p \<Turnstile> fill \<phi>r (ConjC I \<psi>s I' \<psi>s') \<longrightarrow> p \<Turnstile> fill \<phi>l (ConjC I \<psi>s I' \<psi>s')"
      proof (rule allI, rule impI)
        fix p
        assume "p \<Turnstile> fill \<phi>r (ConjC I \<psi>s I' \<psi>s')"
        hence "\<forall>i\<in>I \<union> I'. hml_conjunct_models p (if i \<in> I' then fill_conjunct \<phi>r (\<psi>s' i) else \<psi>s i)"
          unfolding fill.simps and hml_models.simps.
        then have "(\<forall>i\<in>I'. hml_conjunct_models p (fill_conjunct \<phi>r (\<psi>s' i)))
                 \<and> (\<forall>i\<in>I - I'. hml_conjunct_models p (\<psi>s i))" 
          by (metis (full_types) DiffD1 DiffD2 Un_iff)
        hence "\<forall>i\<in>I'. hml_conjunct_models p (fill_conjunct \<phi>r (\<psi>s' i))"
          and "\<forall>i\<in>I - I'. hml_conjunct_models p (\<psi>s i)" by auto

        from \<open>\<forall>i\<in>I'. hml_conjunct_models p (fill_conjunct \<phi>r (\<psi>s' i))\<close>
         and \<open>\<phi>l \<Lleftarrow>\<Rrightarrow> \<phi>r\<close>
         and IH
        have "\<forall>i\<in>I'. hml_conjunct_models p (fill_conjunct \<phi>l (\<psi>s' i))" 
          using hml_conjunct_eq_def hml_conjunct_impl_def by blast

        from \<open>\<forall>i\<in>I - I'. hml_conjunct_models p (\<psi>s i)\<close>
        have "\<forall>i\<in>I - I'. hml_conjunct_models p (\<psi>s i)".

        from \<open>\<forall>i\<in>I'. hml_conjunct_models p (fill_conjunct \<phi>l (\<psi>s' i))\<close>
         and \<open>\<forall>i\<in>I - I'. hml_conjunct_models p (\<psi>s i)\<close>
        have "\<forall>i\<in>I \<union> I'. hml_conjunct_models p (if i \<in> I' then fill_conjunct \<phi>l (\<psi>s' i) else \<psi>s i)" 
          by auto

        then show "p \<Turnstile> fill \<phi>l (ConjC I \<psi>s I' \<psi>s')"
          unfolding fill.simps and hml_models.simps.
      qed
    qed
  qed
qed

end (* LTS_Tau *)

end (* HML_Context *)