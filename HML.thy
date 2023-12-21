theory HML
  imports Main LTS
begin

datatype 
  ('act, 'i) hml =
    TT |
    Obs 'act "('act, 'i) hml" |
    Internal "('act, 'i) hml" |
    Silent "('act, 'i) hml" |
    Conj "'i set" "'i \<Rightarrow> ('act, 'i) hml_conjunct"
and
  ('act, 'i) hml_conjunct =
    Pos "('act, 'i) hml" |
    Neg "('act, 'i) hml"


context Inhabited_LTS
begin

abbreviation HML_and :: "('a, 's) hml_conjunct \<Rightarrow> ('a, 's) hml_conjunct \<Rightarrow> ('a, 's) hml" ("_ \<and>hml _" 70) where
  "HML_and left_conjunct right_conjunct \<equiv> Conj {left, right} (\<lambda>i. if i = left
                                          then left_conjunct
                                          else if i = right
                                               then right_conjunct
                                               else Pos TT)"

end (* context Inhabited_LTS *)


context LTS_Tau
begin

abbreviation HML_soft_poss :: "'a \<Rightarrow> ('a, 'i) hml \<Rightarrow> ('a, 'i) hml" where
  "HML_soft_poss \<alpha> \<phi> \<equiv> if \<alpha> = \<tau> then Silent \<phi> else Obs \<alpha> \<phi>"

primrec
      hml_models          :: "'s \<Rightarrow> ('a, 's) hml          \<Rightarrow> bool" ("_ \<Turnstile> _" 60) 
  and hml_conjunct_models :: "'s \<Rightarrow> ('a, 's) hml_conjunct \<Rightarrow> bool"
where
  "(_ \<Turnstile> TT) = True" |
  "(p \<Turnstile> (Obs a \<phi>)) = (\<exists>p'. p \<mapsto> a p' \<and> (p' \<Turnstile> \<phi>))" |
  "(p \<Turnstile> (Internal \<phi>)) = (\<exists>p'. p \<Zsurj> p' \<and> (p' \<Turnstile> \<phi>))" |
  "(p \<Turnstile> (Silent \<phi>)) = ((\<exists>p'. p \<mapsto> \<tau> p' \<and> (p' \<Turnstile> \<phi>)) \<or> (p \<Turnstile> \<phi>))" |
  "(p \<Turnstile> (Conj I \<psi>s)) = (\<forall>i \<in> I. hml_conjunct_models p (\<psi>s i))" |

  "(hml_conjunct_models p (Pos \<phi>)) = (p \<Turnstile> \<phi>)" |
  "(hml_conjunct_models p (Neg \<phi>)) = (\<not>(p \<Turnstile> \<phi>))"


lemma "(state \<Turnstile> TT) = (state \<Turnstile> Conj {} \<psi>)"
  by simp

lemma opt_\<tau>_is_or: "(p \<Turnstile> (Silent \<phi>)) = ((p \<Turnstile> (Obs \<tau> \<phi>)) \<or> (p \<Turnstile> \<phi>))"
  by simp

end (* context LTS_Tau *)


context Inhabited_Tau_LTS
begin

abbreviation HML_not :: "('a, 's) hml \<Rightarrow> ('a, 's) hml" where
  "HML_not \<phi> \<equiv> Conj {left} (\<lambda>i. if i = left then (Neg \<phi>) else (Pos TT))"

lemma "(state \<Turnstile> \<phi>) = (state \<Turnstile>Conj {left}
                            (\<lambda>i. if i = left
                                 then (Pos \<phi>)
                                 else (Pos TT)))"
  by simp

lemma "(state \<Turnstile> \<phi>) = (state \<Turnstile> HML_not (HML_not \<phi>))"
  by simp

end (* context Inhabited_Tau_LTS *)

datatype 
  ('act, 'i) hml_precontext =
    PCHole |
    ObsPC 'act "('act, 'i) hml_precontext" |
    InternalPC "('act, 'i) hml_precontext" |
    SilentPC "('act, 'i) hml_precontext" |
    ConjPC "'i set" "'i \<Rightarrow> ('act, 'i) hml_conjunct" "'i set" "'i \<Rightarrow> ('act, 'i) hml_precontext"


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

\<comment> \<open> Pre-Order \<close>

definition hml_impl :: "('a, 's) hml \<Rightarrow> ('a, 's) hml \<Rightarrow> bool" (infix "\<Rrightarrow>" 60)  where
  "\<phi>l \<Rrightarrow> \<phi>r \<equiv> (\<forall>p. (p \<Turnstile> \<phi>l) \<longrightarrow> (p \<Turnstile> \<phi>r))"

lemma hml_impl_iffI: "\<phi>l \<Rrightarrow> \<phi>r = (\<forall>p. (p \<Turnstile> \<phi>l) \<longrightarrow> (p \<Turnstile> \<phi>r))"
  using hml_impl_def by force

lemma hml_impl_preord: "reflp (\<Rrightarrow>) \<and> transp (\<Rrightarrow>)"
  by (metis hml_impl_def reflpI transpI)

definition hml_conjunct_impl :: "('a, 's) hml_conjunct \<Rightarrow> ('a, 's) hml_conjunct \<Rightarrow> bool" (infix "\<and>\<Rrightarrow>" 60)  where
  "\<psi>l \<and>\<Rrightarrow> \<psi>r \<equiv> (\<forall>p. (hml_conjunct_models p \<psi>l) \<longrightarrow> (hml_conjunct_models p \<psi>r))"

lemma hml_conjunct_impl_preord: "reflp (\<and>\<Rrightarrow>) \<and> transp (\<and>\<Rrightarrow>)"
  by (metis hml_conjunct_impl_def reflpI transpI)

\<comment> \<open> Pre-Congruence \<close>

lemma obs_pre_cong: "\<phi>l \<Rrightarrow> \<phi>r \<Longrightarrow> (Obs \<alpha> \<phi>l) \<Rrightarrow> (Obs \<alpha> \<phi>r)"
  using hml_impl_iffI by auto

lemma internal_pre_cong: "\<phi>l \<Rrightarrow> \<phi>r \<Longrightarrow> (Internal \<phi>l) \<Rrightarrow> (Internal \<phi>r)"
  using hml_impl_iffI by auto

lemma silent_pre_cong: "\<phi>l \<Rrightarrow> \<phi>r \<Longrightarrow> (Silent \<phi>l) \<Rrightarrow> (Silent \<phi>r)"
  using hml_impl_iffI by auto

lemma conj_pre_cong: "\<psi>sl ` I = \<psi>sr ` I \<Longrightarrow> \<psi>sl l \<and>\<Rrightarrow> \<psi>sr r \<Longrightarrow> (Conj (I \<union> {l}) \<psi>sl) \<Rrightarrow> (Conj (I \<union> {r}) \<psi>sr)"
  by (smt (verit) Un_insert_right hml_conjunct_impl_def hml_impl_def hml_models.simps(5) image_iff insert_iff sup_bot.right_neutral)

lemma conj_pre_congs: "\<psi>sl ` I = \<psi>sr ` I \<Longrightarrow> \<forall>i \<in> I'. \<psi>sl i \<and>\<Rrightarrow> \<psi>sr i \<Longrightarrow> (Conj (I \<union> I') \<psi>sl) \<Rrightarrow> (Conj (I \<union> I') \<psi>sr)"
  by (smt (verit, ccfv_threshold) LTS_Tau.hml_conjunct_impl_def UnE UnI1 hml_impl_iffI hml_models.simps(5) imageE imageI)

lemma pos_pre_cong: "\<phi>l \<Rrightarrow> \<phi>r \<Longrightarrow> Pos \<phi>l \<and>\<Rrightarrow> Pos \<phi>r"
  by (simp add: hml_conjunct_impl_def hml_impl_iffI)

lemma neg_pre_cong: "\<phi>l \<Rrightarrow> \<phi>r \<Longrightarrow> Neg \<phi>r \<and>\<Rrightarrow> Neg \<phi>l"
  using hml_conjunct_impl_def hml_impl_def by auto

lemma pre_cong: "\<phi>l \<Rrightarrow> \<phi>r \<Longrightarrow> fill_pre \<phi>l C \<Rrightarrow> fill_pre \<phi>r C"
  using hml_impl_def by (induct C) auto[5]

\<comment> \<open> Know Pre-Order Elements\<close>

lemma pre_\<epsilon>: "\<phi> \<Rrightarrow> (Internal \<phi>)"
  using silent_reachable.intros(1) hml_impl_def by fastforce

lemma pre_\<tau>: "\<phi> \<Rrightarrow> (Silent \<phi>)"
  using hml_impl_def by fastforce

lemma \<epsilon>_eats_\<tau>: "(Internal (Obs \<tau> \<phi>)) \<Rrightarrow> (Internal \<phi>)"
  using silent_reachable_append_\<tau> hml_impl_def by fastforce

\<comment> \<open> Equivalence \<close>

definition hml_eq :: "('a, 's) hml \<Rightarrow> ('a, 's) hml \<Rightarrow> bool" (infix "\<Lleftarrow>\<Rrightarrow>" 60)  where
  "\<phi>l \<Lleftarrow>\<Rrightarrow> \<phi>r \<equiv> \<phi>l \<Rrightarrow> \<phi>r \<and> \<phi>r \<Rrightarrow> \<phi>l"

lemma hml_eq_equiv: "equivp (\<Lleftarrow>\<Rrightarrow>)"
  by (smt (verit, del_insts) equivpI hml_eq_def hml_impl_def reflpI sympI transpI)

definition hml_conjunct_eq :: "('a, 's) hml_conjunct \<Rightarrow> ('a, 's) hml_conjunct \<Rightarrow> bool" (infix "\<Lleftarrow>\<and>\<Rrightarrow>" 60)  where
  "\<psi>l \<Lleftarrow>\<and>\<Rrightarrow> \<psi>r \<equiv> \<psi>l \<and>\<Rrightarrow> \<psi>r \<and> \<psi>r \<and>\<Rrightarrow> \<psi>l"

lemma hml_conjunct_eq_equiv: "equivp (\<Lleftarrow>\<and>\<Rrightarrow>)"
  by (smt (verit, best) equivpI hml_conjunct_eq_def hml_conjunct_impl_def reflpI sympI transpI)

end

\<comment> \<open> Congruence Properties\<close>

datatype 
  ('act, 'i) hml_context =
    Hole |
    ObsC 'act "('act, 'i) hml_context" |
    InternalC "('act, 'i) hml_context" |
    SilentC "('act, 'i) hml_context" |
    ConjC "'i set" "'i \<Rightarrow> ('act, 'i) hml_conjunct" "'i set" "'i \<Rightarrow> ('act, 'i) hml_conjunct_context"
and
  ('act, 'i) hml_conjunct_context =
    PosC "('act, 'i) hml_context" |
    NegC "('act, 'i) hml_context"

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

context LTS_Tau
begin

lemma obs_cong: "\<phi>l \<Lleftarrow>\<Rrightarrow> \<phi>r \<Longrightarrow> (Obs \<alpha> \<phi>l) \<Lleftarrow>\<Rrightarrow> (Obs \<alpha> \<phi>r)"
  by (meson hml_eq_def hml_impl_def hml_models.simps(2))

lemma internal_cong: "\<phi>l \<Lleftarrow>\<Rrightarrow> \<phi>r \<Longrightarrow> (Internal \<phi>l) \<Lleftarrow>\<Rrightarrow> (Internal \<phi>r)"
  using hml_eq_def hml_impl_def by auto

lemma silent_cong: "\<phi>l \<Lleftarrow>\<Rrightarrow> \<phi>r \<Longrightarrow> (Silent \<phi>l) \<Lleftarrow>\<Rrightarrow> (Silent \<phi>r)"
  using hml_eq_def hml_impl_def by auto

lemma conj_cong: "\<psi>sl ` I = \<psi>sr ` I \<Longrightarrow> (\<psi>sl l) \<Lleftarrow>\<and>\<Rrightarrow> (\<psi>sr r) \<Longrightarrow> (Conj (I \<union> {l}) \<psi>sl) \<Lleftarrow>\<Rrightarrow> (Conj (I \<union> {r}) \<psi>sr)"
proof -
  assume "\<psi>sl ` I = \<psi>sr ` I"
     and "(\<psi>sl l) \<Lleftarrow>\<and>\<Rrightarrow> (\<psi>sr r)"
  hence "(\<forall>p. hml_conjunct_models p (\<psi>sl l) \<longrightarrow> hml_conjunct_models p (\<psi>sr r))
       \<and> (\<forall>p. hml_conjunct_models p (\<psi>sr r) \<longrightarrow> hml_conjunct_models p (\<psi>sl l))"
    unfolding hml_conjunct_eq_def
          and hml_conjunct_impl_def by auto
  then have
        IHL: "\<forall>p. hml_conjunct_models p (\<psi>sl l) \<longrightarrow> hml_conjunct_models p (\<psi>sr r)"
    and IHR: "\<forall>p. hml_conjunct_models p (\<psi>sr r) \<longrightarrow> hml_conjunct_models p (\<psi>sl l)" 
    apply blast 
    using \<open>(\<forall>p. hml_conjunct_models p (\<psi>sl l) \<longrightarrow> hml_conjunct_models p (\<psi>sr r)) \<and> (\<forall>p. hml_conjunct_models p (\<psi>sr r) \<longrightarrow> hml_conjunct_models p (\<psi>sl l))\<close> by blast
  
  show "(Conj (I \<union> {l}) \<psi>sl) \<Lleftarrow>\<Rrightarrow> (Conj (I \<union> {r}) \<psi>sr)"
    unfolding hml_eq_def
          and hml_impl_def
  proof (rule conjI)
    show "\<forall>p. p \<Turnstile> Conj (I \<union> {l}) \<psi>sl \<longrightarrow> p \<Turnstile> Conj (I \<union> {r}) \<psi>sr"
    proof (rule allI, rule impI)
      fix p
      assume "p \<Turnstile> Conj (I \<union> {l}) \<psi>sl"
      hence "\<forall>i\<in>I \<union> {l}. hml_conjunct_models p (\<psi>sl i)"
        unfolding hml_models.simps.
      then have "hml_conjunct_models p (\<psi>sl l)"
        by blast
      then have "hml_conjunct_models p (\<psi>sr r)"
        using IHL by simp
      then show "p \<Turnstile> Conj (I \<union> {r}) \<psi>sr"
        using \<open>\<psi>sl ` I = \<psi>sr ` I\<close> 
        by (smt (verit) Un_insert_right \<open>\<forall>i\<in>I \<union> {l}. hml_conjunct_models p (\<psi>sl i)\<close> hml_models.simps(5) image_iff insert_iff sup_bot.right_neutral)
    qed
  next
    show "\<forall>p. p \<Turnstile> Conj (I \<union> {r}) \<psi>sr \<longrightarrow> p \<Turnstile> Conj (I \<union> {l}) \<psi>sl"
    proof (rule allI, rule impI)
      fix p
      assume "p \<Turnstile> Conj (I \<union> {r}) \<psi>sr"
      hence "\<forall>i\<in>I \<union> {r}. hml_conjunct_models p (\<psi>sr i)"
        unfolding hml_models.simps.
      then have "hml_conjunct_models p (\<psi>sr r)"
        by blast
      then have "hml_conjunct_models p (\<psi>sl l)"
        using IHR by simp
      then show " p \<Turnstile> Conj (I \<union> {l}) \<psi>sl" 
        by (smt (verit, best) Un_empty_right Un_insert_right \<open>\<forall>i\<in>I \<union> {r}. hml_conjunct_models p (\<psi>sr i)\<close> \<open>\<psi>sl ` I = \<psi>sr ` I\<close> hml_models.simps(5) image_iff insert_iff)
    qed
  qed
qed

lemma conj_congs: "\<forall>i \<in> I. \<psi>sl i = \<psi>sr i \<Longrightarrow> \<forall>i \<in> I'. (\<psi>sl i) \<Lleftarrow>\<and>\<Rrightarrow> (\<psi>sr i) \<Longrightarrow> (Conj (I \<union> I') \<psi>sl) \<Lleftarrow>\<Rrightarrow> (Conj (I \<union> I') \<psi>sr)"
proof -
  assume "\<forall>i \<in> I. \<psi>sl i = \<psi>sr i"
     and "\<forall>i \<in> I'. (\<psi>sl i) \<Lleftarrow>\<and>\<Rrightarrow> (\<psi>sr i)"
  hence conjunct_eq: "\<forall>i\<in>I'. (\<forall>p. hml_conjunct_models p (\<psi>sl i) \<longrightarrow> hml_conjunct_models p (\<psi>sr i))
                   \<and> (\<forall>p. hml_conjunct_models p (\<psi>sr i) \<longrightarrow> hml_conjunct_models p (\<psi>sl i))"
    unfolding hml_conjunct_eq_def and hml_conjunct_impl_def by auto
  show "(Conj (I \<union> I') \<psi>sl) \<Lleftarrow>\<Rrightarrow> (Conj (I \<union> I') \<psi>sr)"
    unfolding hml_eq_def and hml_impl_def
  proof (rule conjI)
    show "\<forall>p. p \<Turnstile> Conj (I \<union> I') \<psi>sl \<longrightarrow> p \<Turnstile> Conj (I \<union> I') \<psi>sr"
    proof (rule allI, rule impI)
      fix p
      assume "p \<Turnstile> Conj (I \<union> I') \<psi>sl"
      hence "(\<forall>i\<in>I. hml_conjunct_models p (\<psi>sl i))
           \<and> (\<forall>i\<in>I'. hml_conjunct_models p (\<psi>sl i))" 
        by simp
      then have "\<forall>i\<in>I. hml_conjunct_models p (\<psi>sl i)"
            and "\<forall>i\<in>I'. hml_conjunct_models p (\<psi>sl i)" by blast+

      from \<open>\<forall>i\<in>I. hml_conjunct_models p (\<psi>sl i)\<close>
       and \<open>\<forall>i\<in>I. \<psi>sl i = \<psi>sr i\<close>
      have "\<forall>i\<in>I. hml_conjunct_models p (\<psi>sr i)" 
        by force

      from conjunct_eq
       and \<open>\<forall>i\<in>I'. hml_conjunct_models p (\<psi>sl i)\<close>
      have "\<forall>i\<in>I'. hml_conjunct_models p (\<psi>sr i)" 
        by blast

      from \<open>\<forall>i\<in>I. hml_conjunct_models p (\<psi>sr i)\<close>
       and \<open>\<forall>i\<in>I'. hml_conjunct_models p (\<psi>sr i)\<close>
      show "p \<Turnstile> Conj (I \<union> I') \<psi>sr"
        unfolding hml_models.simps 
        by blast
    qed
  next
    show "\<forall>p. p \<Turnstile> Conj (I \<union> I') \<psi>sr \<longrightarrow> p \<Turnstile> Conj (I \<union> I') \<psi>sl" 
      using Un_iff \<open>\<forall>i\<in>I. \<psi>sl i = \<psi>sr i\<close> conjunct_eq by auto
  qed
qed

lemma pos_cong: "\<phi>l \<Lleftarrow>\<Rrightarrow> \<phi>r \<Longrightarrow> (Pos \<phi>l) \<Lleftarrow>\<and>\<Rrightarrow> (Pos \<phi>r)"
  by (simp add: hml_conjunct_eq_def hml_conjunct_impl_def hml_eq_def hml_impl_def)

lemma neg_cong: "\<phi>l \<Lleftarrow>\<Rrightarrow> \<phi>r \<Longrightarrow> (Neg \<phi>l) \<Lleftarrow>\<and>\<Rrightarrow> (Neg \<phi>r)"
  by (meson hml_conjunct_eq_def hml_conjunct_impl_def hml_conjunct_models.simps(2) hml_eq_def hml_impl_def)

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
          by (metis DiffD1 DiffD2 Un_iff)
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
          by (metis DiffD1 DiffD2 Un_iff)
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

\<comment> \<open> Know Equivalence Elements\<close>

lemma "(Internal (Silent \<phi>)) \<Lleftarrow>\<Rrightarrow> (Internal \<phi>)"
  unfolding hml_eq_def
proof (rule conjI)
  from pre_\<tau>
  have "\<phi> \<Rrightarrow> (Silent \<phi>)".
  then have "fill_pre \<phi> (InternalPC PCHole) \<Rrightarrow> fill_pre (Silent \<phi>) (InternalPC PCHole)"
    by (rule pre_cong)
  then show "Internal \<phi> \<Rrightarrow> Internal (Silent \<phi>)"
    unfolding fill_pre.simps.
next
  show "Internal (Silent \<phi>) \<Rrightarrow> Internal \<phi>"
    unfolding hml_impl_def
  proof (rule allI, rule impI)
    fix p
    assume "p \<Turnstile> Internal (Silent \<phi>)"
    hence "p \<Turnstile> Internal \<phi> \<or> p \<Turnstile> Internal (Obs \<tau> \<phi>)" by auto
    then show "p \<Turnstile> Internal \<phi>"
      apply (rule disjE) apply assumption
    proof -
      assume "p \<Turnstile> Internal (Obs \<tau> \<phi>)"
      then show "p \<Turnstile> Internal \<phi>"
        using \<epsilon>_eats_\<tau> and hml_impl_iffI by simp
    qed
  qed
qed

end

end
