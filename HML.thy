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


lemma tt_eq_empty_conj: "(state \<Turnstile> TT) = (state \<Turnstile> Conj {} \<psi>)"
  by simp

lemma opt_\<tau>_is_or: "(p \<Turnstile> (Silent \<phi>)) = ((p \<Turnstile> (Obs \<tau> \<phi>)) \<or> (p \<Turnstile> \<phi>))"
  by simp

end (* context LTS_Tau *)

context Inhabited_Tau_LTS
begin

lemma hml_and_and: "(p \<Turnstile> (\<psi>l \<and>hml \<psi>r)) = (hml_conjunct_models p \<psi>l \<and> hml_conjunct_models p \<psi>r)"
  unfolding hml_models.simps and hml_conjunct_models.simps
proof (rule iffI)
  assume "\<forall>i\<in>{left, right}. hml_conjunct_models p (if i = left then \<psi>l else if i = right then \<psi>r else Pos TT)"
  then have for_all_l_and_r: "\<forall>i\<in>{left, right}. (if i = left then hml_conjunct_models p \<psi>l else if i = right then hml_conjunct_models p \<psi>r else hml_conjunct_models p (Pos TT))"
    by presburger
  then show "hml_conjunct_models p \<psi>l \<and> hml_conjunct_models p \<psi>r"
    by (metis Inhabited_LTS_axioms Inhabited_LTS_def insertCI)
next
  assume "hml_conjunct_models p \<psi>l \<and> hml_conjunct_models p \<psi>r"
  then show "\<forall>i\<in>{left, right}. hml_conjunct_models p (if i = left then \<psi>l else if i = right then \<psi>r else Pos TT)"
    by auto
qed

end (* Inhabited_Tau_LTS *)


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

\<comment> \<open> Pre-Substitution \<close>

lemma obs_pre_subst:
  assumes "\<phi>l \<Rrightarrow> \<phi>r"
      and "\<phi> \<Rrightarrow> (Obs \<alpha> \<phi>l)"
  shows "\<phi> \<Rrightarrow> (Obs \<alpha> \<phi>r)"
  using assms and hml_impl_def by force

lemma internal_pre_subst:
  assumes "\<phi>l \<Rrightarrow> \<phi>r"
      and "\<phi> \<Rrightarrow> (Internal \<phi>l)"
  shows "\<phi> \<Rrightarrow> (Internal \<phi>r)"
  using assms and hml_impl_iffI by force

lemma silent_pre_subst: 
  assumes "\<phi>l \<Rrightarrow> \<phi>r"
      and "\<phi> \<Rrightarrow> (Silent \<phi>l)"
  shows "\<phi> \<Rrightarrow> (Silent \<phi>r)"
  using assms and hml_impl_iffI by force

lemma conj_pre_subst: 
  assumes "\<phi>l \<Rrightarrow> \<phi>r"
      and "\<phi> \<Rrightarrow> (Conj (I \<union> {s}) (\<lambda>i. if i = s then Pos \<phi>l else \<psi>s i))"
  shows "\<phi> \<Rrightarrow> (Conj (I \<union> {s}) (\<lambda>i. if i = s then Pos \<phi>r else \<psi>s i))"
  using assms and hml_impl_iffI by fastforce

lemma pos_pre_subst:
  assumes "\<phi>l \<Rrightarrow> \<phi>r"
      and "\<psi> \<and>\<Rrightarrow> (Pos \<phi>l)" 
  shows "\<psi> \<and>\<Rrightarrow> (Pos \<phi>r)" 
  using assms by (simp add: hml_conjunct_impl_def hml_impl_iffI)

lemma neg_pre_subst: 
  assumes "\<phi>l \<Rrightarrow> \<phi>r"
      and "(Neg \<phi>l) \<and>\<Rrightarrow> \<psi>" 
  shows "(Neg \<phi>r) \<and>\<Rrightarrow> \<psi>"
  using assms and hml_conjunct_impl_def hml_impl_iffI by auto

\<comment> \<open> Pre-Congruence \<close>

lemma obs_pre_cong:
  assumes "\<phi>l \<Rrightarrow> \<phi>r"
  shows "(Obs \<alpha> \<phi>l) \<Rrightarrow> (Obs \<alpha> \<phi>r)"
  using assms and hml_impl_iffI by auto

lemma internal_pre_cong: 
  assumes "\<phi>l \<Rrightarrow> \<phi>r"
  shows "(Internal \<phi>l) \<Rrightarrow> (Internal \<phi>r)"
  using assms and hml_impl_iffI by auto

lemma silent_pre_cong: 
  assumes "\<phi>l \<Rrightarrow> \<phi>r"
  shows "(Silent \<phi>l) \<Rrightarrow> (Silent \<phi>r)"
  using assms and hml_impl_iffI by auto

lemma conj_pre_cong: 
  assumes "\<psi>sl ` I = \<psi>sr ` I"
      and "\<psi>sl l \<and>\<Rrightarrow> \<psi>sr r" 
  shows "(Conj (I \<union> {l}) \<psi>sl) \<Rrightarrow> (Conj (I \<union> {r}) \<psi>sr)"
  using assms
  by (smt (verit) Un_insert_right hml_conjunct_impl_def hml_impl_def hml_models.simps(5) image_iff insert_iff sup_bot.right_neutral)

lemma conj_pre_congs:
  assumes "\<psi>sl ` I = \<psi>sr ` I"
      and "\<forall>i \<in> I'. \<psi>sl i \<and>\<Rrightarrow> \<psi>sr i"
  shows "(Conj (I \<union> I') \<psi>sl) \<Rrightarrow> (Conj (I \<union> I') \<psi>sr)"
  using assms
  by (smt (verit, ccfv_threshold) LTS_Tau.hml_conjunct_impl_def UnE UnI1 hml_impl_iffI hml_models.simps(5) imageE imageI)

lemma pos_pre_cong:
  assumes "\<phi>l \<Rrightarrow> \<phi>r"
  shows "Pos \<phi>l \<and>\<Rrightarrow> Pos \<phi>r"
  using assms
  by (simp add: hml_conjunct_impl_def hml_impl_iffI)

lemma neg_pre_cong:
  assumes "\<phi>l \<Rrightarrow> \<phi>r"
  shows "Neg \<phi>r \<and>\<Rrightarrow> Neg \<phi>l"
  using assms and hml_conjunct_impl_def hml_impl_def by auto

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

lemma hml_eq_equality: "(\<phi>l \<Lleftarrow>\<Rrightarrow> \<phi>r) = (\<forall>p.( p \<Turnstile> \<phi>l) = (p \<Turnstile> \<phi>r))"
  using hml_eq_def hml_impl_iffI by blast

definition hml_conjunct_eq :: "('a, 's) hml_conjunct \<Rightarrow> ('a, 's) hml_conjunct \<Rightarrow> bool" (infix "\<Lleftarrow>\<and>\<Rrightarrow>" 60)  where
  "\<psi>l \<Lleftarrow>\<and>\<Rrightarrow> \<psi>r \<equiv> \<psi>l \<and>\<Rrightarrow> \<psi>r \<and> \<psi>r \<and>\<Rrightarrow> \<psi>l"

lemma hml_conjunct_eq_equiv: "equivp (\<Lleftarrow>\<and>\<Rrightarrow>)"
  by (smt (verit, best) equivpI hml_conjunct_eq_def hml_conjunct_impl_def reflpI sympI transpI)

end


\<comment> \<open> Substitution \<close>

context LTS_Tau
begin

lemma obs_subst:
  assumes "\<phi>l \<Lleftarrow>\<Rrightarrow> \<phi>r"
      and "(Obs \<alpha> \<phi>l) \<Lleftarrow>\<Rrightarrow> \<phi>"
  shows "(Obs \<alpha> \<phi>r) \<Lleftarrow>\<Rrightarrow> \<phi>"
  using assms
  by (meson hml_eq_def hml_impl_iffI obs_pre_cong)

lemma internal_subst:
  assumes "\<phi>l \<Lleftarrow>\<Rrightarrow> \<phi>r"
      and "(Internal \<phi>l) \<Lleftarrow>\<Rrightarrow> \<phi>"
  shows "(Internal \<phi>r) \<Lleftarrow>\<Rrightarrow> \<phi>"
  using assms
  by (simp add: hml_eq_equality)

lemma silent_subst:
  assumes "\<phi>l \<Lleftarrow>\<Rrightarrow> \<phi>r"
      and "(Silent \<phi>l) \<Lleftarrow>\<Rrightarrow> \<phi>"
  shows "(Silent \<phi>r) \<Lleftarrow>\<Rrightarrow> \<phi>"
  using assms
  by (meson LTS_Tau.hml_impl_def LTS_Tau.silent_pre_cong hml_eq_def)

lemma conj_subst:
  assumes "\<psi>l \<Lleftarrow>\<and>\<Rrightarrow> \<psi>r"
      and "(Conj (I \<union> {s}) (\<lambda>i. if i = s then \<psi>l else \<psi>s i)) \<Lleftarrow>\<Rrightarrow> \<phi>"
  shows "(Conj (I \<union> {s}) (\<lambda>i. if i = s then \<psi>r else \<psi>s i)) \<Lleftarrow>\<Rrightarrow> \<phi>"
  using assms
  by (smt (verit) LTS_Tau.hml_impl_iffI hml_conjunct_eq_def hml_conjunct_impl_def hml_eq_def hml_models.simps(5))

lemma pos_subst:
  assumes "\<phi>l \<Lleftarrow>\<Rrightarrow> \<phi>r"
      and "(Pos \<phi>l) \<Lleftarrow>\<and>\<Rrightarrow> \<psi>"
  shows "(Pos \<phi>r) \<Lleftarrow>\<and>\<Rrightarrow> \<psi>"
  using assms
  by (meson LTS_Tau.hml_conjunct_eq_def LTS_Tau.hml_eq_def LTS_Tau.pos_pre_cong hml_conjunct_impl_preord transpE)

lemma neg_subst:
  assumes "\<phi>l \<Lleftarrow>\<Rrightarrow> \<phi>r"
      and "(Neg \<phi>l) \<Lleftarrow>\<and>\<Rrightarrow> \<psi>"
  shows "(Neg \<phi>r) \<Lleftarrow>\<and>\<Rrightarrow> \<psi>"
  using assms
  by (meson LTS_Tau.neg_pre_subst hml_conjunct_eq_def hml_conjunct_impl_def hml_eq_def)


\<comment> \<open> Congruence Properties\<close>

lemma obs_cong:
  assumes "\<phi>l \<Lleftarrow>\<Rrightarrow> \<phi>r"
  shows "(Obs \<alpha> \<phi>l) \<Lleftarrow>\<Rrightarrow> (Obs \<alpha> \<phi>r)"
  using assms
  by (meson hml_eq_def hml_impl_def hml_models.simps(2))

lemma internal_cong:
  assumes "\<phi>l \<Lleftarrow>\<Rrightarrow> \<phi>r"
  shows "(Internal \<phi>l) \<Lleftarrow>\<Rrightarrow> (Internal \<phi>r)"
  using assms and hml_eq_def and hml_impl_def by auto

lemma silent_cong:
  assumes "\<phi>l \<Lleftarrow>\<Rrightarrow> \<phi>r"
  shows "(Silent \<phi>l) \<Lleftarrow>\<Rrightarrow> (Silent \<phi>r)"
  using assms and hml_eq_def and hml_impl_def by auto

lemma conj_cong:
  assumes "\<psi>sl ` I = \<psi>sr ` I"
      and "(\<psi>sl l) \<Lleftarrow>\<and>\<Rrightarrow> (\<psi>sr r)"
  shows "(Conj (I \<union> {l}) \<psi>sl) \<Lleftarrow>\<Rrightarrow> (Conj (I \<union> {r}) \<psi>sr)"
  using assms
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

lemma conj_cong':
  assumes "s \<notin> I"
      and "\<psi>sl ` I = \<psi>sr ` I"
      and "(\<psi>sl s) \<Lleftarrow>\<and>\<Rrightarrow> (\<psi>sr s)"
  shows "(Conj (I \<union> {s}) \<psi>sl) \<Lleftarrow>\<Rrightarrow> (Conj (I \<union> {s}) \<psi>sr)"
  using assms and conj_cong by presburger

lemma conj_congs:
  assumes "\<forall>i \<in> I. \<psi>sl i = \<psi>sr i"
      and "\<forall>i \<in> I'. (\<psi>sl i) \<Lleftarrow>\<and>\<Rrightarrow> (\<psi>sr i)"
  shows "(Conj (I \<union> I') \<psi>sl) \<Lleftarrow>\<Rrightarrow> (Conj (I \<union> I') \<psi>sr)"
  using assms
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

lemma conj_congs':
  assumes "I \<inter> I' = {}"
      and "\<forall>i \<in> I. \<psi>sl i = \<psi>sr i"
      and "\<forall>i \<in> I'. (\<psi>sl i) \<Lleftarrow>\<and>\<Rrightarrow> (\<psi>sr i)"
  shows "(Conj (I \<union> I') \<psi>sl) \<Lleftarrow>\<Rrightarrow> (Conj (I \<union> I') \<psi>sr)"
  using assms and conj_congs by presburger

lemma pos_cong:
  assumes "\<phi>l \<Lleftarrow>\<Rrightarrow> \<phi>r"
  shows "(Pos \<phi>l) \<Lleftarrow>\<and>\<Rrightarrow> (Pos \<phi>r)"
  using assms
  by (simp add: hml_conjunct_eq_def hml_conjunct_impl_def hml_eq_def hml_impl_def)

lemma neg_cong:
  assumes "\<phi>l \<Lleftarrow>\<Rrightarrow> \<phi>r"
  shows "(Neg \<phi>l) \<Lleftarrow>\<and>\<Rrightarrow> (Neg \<phi>r)"
  using assms
  by (meson hml_conjunct_eq_def hml_conjunct_impl_def hml_conjunct_models.simps(2) hml_eq_def hml_impl_def)


\<comment> \<open> Know Equivalence Elements\<close>

lemma \<epsilon>\<tau>_is_\<tau>: "(Internal (Silent \<phi>)) \<Lleftarrow>\<Rrightarrow> (Internal \<phi>)"
  unfolding hml_eq_def
proof (rule conjI)
  from pre_\<tau>
  have "\<phi> \<Rrightarrow> (Silent \<phi>)".
  then show "Internal \<phi> \<Rrightarrow> Internal (Silent \<phi>)"
    using internal_pre_cong by simp
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

lemma \<epsilon>T_is_T: "(Internal TT) \<Lleftarrow>\<Rrightarrow> TT"
  by (simp add: LTS_Tau.pre_\<epsilon> hml_eq_def hml_impl_def)

fun n_\<epsilon>\<tau>s_then :: "nat \<Rightarrow> ('a, 's) hml \<Rightarrow> ('a, 's) hml" where
  "n_\<epsilon>\<tau>s_then 0 cont = cont" |
  "n_\<epsilon>\<tau>s_then (Suc n) cont = (Internal (Silent (n_\<epsilon>\<tau>s_then n cont)))"

lemma \<epsilon>\<tau>_stack_reduces: "n_\<epsilon>\<tau>s_then n (Internal \<phi>) \<Lleftarrow>\<Rrightarrow> (Internal \<phi>)"
  apply (induct n)
  apply (simp add: LTS_Tau.hml_impl_iffI hml_eq_def)
  unfolding n_\<epsilon>\<tau>s_then.simps(2)
  using \<epsilon>\<tau>_is_\<tau>
  by (smt (verit, del_insts) hml_eq_def hml_impl_iffI hml_models.simps(3) pre_\<epsilon> silent_reachable_trans)

lemma n_\<epsilon>\<tau>s_then_cong:
  assumes "\<phi>l \<Lleftarrow>\<Rrightarrow> \<phi>r"
  shows "n_\<epsilon>\<tau>s_then n \<phi>l \<Lleftarrow>\<Rrightarrow> n_\<epsilon>\<tau>s_then n \<phi>r"
  using assms
  by (induct n) (simp add: internal_cong silent_cong)+

lemma "n_\<epsilon>\<tau>s_then n TT \<Lleftarrow>\<Rrightarrow> TT"
  using n_\<epsilon>\<tau>s_then_cong
    and \<epsilon>\<tau>_stack_reduces
    and \<epsilon>T_is_T
    and equivp_def
    and hml_eq_equiv
  by metis

lemma T_is_empty_conj: "TT \<Lleftarrow>\<Rrightarrow> Conj {} \<psi>s"
  using tt_eq_empty_conj
    and hml_eq_equality
  by blast

lemma T_is_\<epsilon>_empty_conj: "TT \<Lleftarrow>\<Rrightarrow> Internal (Conj {} \<psi>s)"
  using \<epsilon>T_is_T
     and T_is_empty_conj
  by (meson LTS_Tau.internal_subst equivp_symp hml_eq_equiv)

end

context Inhabited_Tau_LTS
begin

lemma hml_and_commutative: "(\<phi>l \<and>hml \<phi>r) \<Lleftarrow>\<Rrightarrow> (\<phi>r \<and>hml \<phi>l)"
  using Inhabited_LTS_axioms Inhabited_LTS_def hml_eq_equality by fastforce

lemma hml_and_left_tt: "(Pos TT \<and>hml Pos \<phi>) \<Lleftarrow>\<Rrightarrow> \<phi>"
  using Inhabited_LTS_axioms Inhabited_LTS_def hml_eq_equality by fastforce

lemma hml_and_right_tt: "(Pos \<phi> \<and>hml Pos TT) \<Lleftarrow>\<Rrightarrow> \<phi>"
  using hml_and_commutative and hml_and_left_tt
  by (simp add: hml_eq_equality)

lemma hml_and_same_no_and: "(Pos \<phi> \<and>hml Pos \<phi>) \<Lleftarrow>\<Rrightarrow> \<phi>"
  by (simp add: hml_eq_equality)

lemma conj_extract_conjunct:
  assumes "s \<notin> I"
  shows "Conj (I \<union> {s}) (\<lambda>i. if i = s then \<psi> else \<psi>s i) \<Lleftarrow>\<Rrightarrow> (\<psi> \<and>hml Pos (Conj I \<psi>s))"
  using assms
proof -
  assume "s \<notin> I"
  show "Conj (I \<union> {s}) (\<lambda>i. if i = s then \<psi> else \<psi>s i) \<Lleftarrow>\<Rrightarrow> (\<psi> \<and>hml Pos (Conj I \<psi>s))"
    unfolding hml_eq_def and hml_impl_def
  proof (rule conjI)
    show "\<forall>p. p \<Turnstile> Conj (I \<union> {s}) (\<lambda>i. if i = s then \<psi> else \<psi>s i) \<longrightarrow> p \<Turnstile> \<psi> \<and>hml Pos (Conj I \<psi>s)"
    proof (rule allI, rule impI)
      fix p
      assume "p \<Turnstile> Conj (I \<union> {s}) (\<lambda>i. if i = s then \<psi> else \<psi>s i)"
      with \<open>s \<notin> I\<close>
      have "p \<Turnstile> Conj I \<psi>s \<and> hml_conjunct_models p \<psi>"
        by (smt (verit, ccfv_threshold) IntE Un_Int_eq(3) Un_upper2 hml_models.simps(5) singletonI subsetD)
      then have "p \<Turnstile> Conj I \<psi>s" and "hml_conjunct_models p \<psi>"
        by auto

      show "p \<Turnstile> \<psi> \<and>hml Pos (Conj I \<psi>s)"
        unfolding hml_and_and
      proof (rule conjI)
        from \<open>hml_conjunct_models p \<psi>\<close>
        show "hml_conjunct_models p \<psi>".
      next
        from \<open>p \<Turnstile> Conj I \<psi>s\<close>
        show "hml_conjunct_models p (Pos (Conj I \<psi>s))"
          unfolding hml_conjunct_models.simps.
      qed
    qed
  next
    show "\<forall>p. p \<Turnstile> \<psi> \<and>hml Pos (Conj I \<psi>s) \<longrightarrow> p \<Turnstile> Conj (I \<union> {s}) (\<lambda>i. if i = s then \<psi> else \<psi>s i)"
    proof (rule allI, rule impI)
      fix p
      assume "p \<Turnstile> \<psi> \<and>hml Pos (Conj I \<psi>s)"
      then have "hml_conjunct_models p \<psi> \<and> hml_conjunct_models p (Pos (Conj I \<psi>s))"
        using hml_and_and by simp
      then show "p \<Turnstile> Conj (I \<union> {s}) (\<lambda>i. if i = s then \<psi> else \<psi>s i)" 
        by simp
    qed
  qed
qed

lemma
  assumes "s \<notin> I"
  shows "Conj (I \<union> {s}) (\<lambda>i. if i = s then Pos TT else \<psi>s i) \<Lleftarrow>\<Rrightarrow> Conj I \<psi>s"
  using assms
proof -
  assume "s \<notin> I"
  then have "Conj (I \<union> {s}) (\<lambda>i. if i = s then Pos TT else \<psi>s i) \<Lleftarrow>\<Rrightarrow> (Pos TT \<and>hml Pos (Conj I \<psi>s))"
    by (rule conj_extract_conjunct)
  with hml_and_left_tt
  show "Conj (I \<union> {s}) (\<lambda>i. if i = s then Pos TT else \<psi>s i) \<Lleftarrow>\<Rrightarrow> Conj I \<psi>s"
    by (meson equivp_transp hml_eq_equiv)
qed

end (* Inhabited_Tau_LTS *)

\<comment> \<open> Distinguishing Formulas \<close>

context LTS_Tau
begin

definition dist :: "'s \<Rightarrow> ('a, 's) hml \<Rightarrow> 's \<Rightarrow> bool" ("_ <> _ _" [70, 70, 70] 80) where
  "(p <> \<phi> q) \<equiv> (p \<Turnstile> \<phi>) \<and> \<not>(q \<Turnstile> \<phi>)"

definition distFrom :: "'s \<Rightarrow> ('a, 's) hml \<Rightarrow> 's set \<Rightarrow> bool" ("_ <> _ _" [70, 70, 70] 80) where
  "(p <> \<phi> Q) \<equiv> (\<forall>q \<in> Q. p <> \<phi> q)"


lemma
  fixes Q :: "'s set"
  assumes "p <> (Conj I \<psi>s) Q"
  shows "\<exists>\<psi>s'. p <> (Conj Q \<psi>s') Q"
  using assms
  unfolding distFrom_def and dist_def
proof -
  assume "\<forall>q\<in>Q. (p \<Turnstile> Conj I \<psi>s \<and> \<not> q \<Turnstile> Conj I \<psi>s)"

  define \<psi>s' :: "'s \<Rightarrow> ('a, 's) hml_conjunct" where
    "\<psi>s' \<equiv> (\<lambda>_. Pos (Conj I \<psi>s))"

  from \<open>\<forall>q\<in>Q. (p \<Turnstile> Conj I \<psi>s \<and> \<not> q \<Turnstile> Conj I \<psi>s)\<close>
  have "\<forall>q\<in>Q. (p \<Turnstile> Conj Q \<psi>s' \<and> \<not> q \<Turnstile> Conj Q \<psi>s')"
    by (simp add: \<psi>s'_def)

  then show "\<exists>\<psi>s'. \<forall>q\<in>Q. p \<Turnstile> Conj Q \<psi>s' \<and> \<not> q \<Turnstile> Conj Q \<psi>s'" by auto
qed

lemma dist_conj_thinning:
  fixes Q :: "'s set"
  assumes "p <> (Conj I \<psi>s) Q"
  shows "p <> (Conj Q (\<lambda>q. \<psi>s (SOME i. i \<in> I \<and> \<not>(hml_conjunct_models q (\<psi>s i))))) Q"
  using assms
proof -
  assume "p <> Conj I \<psi>s Q"
  hence conj_dist_from_Q: "\<forall>q\<in>Q. p \<Turnstile> Conj I \<psi>s \<and> \<not> q \<Turnstile> Conj I \<psi>s"
    unfolding distFrom_def and dist_def.

  show "p <> (Conj Q (\<lambda>q. \<psi>s (SOME i. i \<in> I \<and> \<not>(hml_conjunct_models q (\<psi>s i))))) Q"
    unfolding distFrom_def and dist_def
  proof (rule ballI, rule conjI)
    fix q
    assume "q \<in> Q"
    with conj_dist_from_Q
    have "p \<Turnstile> Conj I \<psi>s" and "\<not> q \<Turnstile> Conj I \<psi>s" by auto

    from \<open>\<not> q \<Turnstile> Conj I \<psi>s\<close>
    have "\<exists>i. i \<in> I \<and> \<not> hml_conjunct_models q (\<psi>s i)"
      using hml_models.simps(5) by blast

    from \<open>p \<Turnstile> Conj I \<psi>s\<close>
    have "\<forall>i\<in>I. hml_conjunct_models p (\<psi>s i)"
      unfolding hml_models.simps.

    have "\<forall>q'\<in>Q. hml_conjunct_models p (\<psi>s (SOME i. i \<in> I \<and> \<not> hml_conjunct_models q' (\<psi>s i)))"
    proof (rule ballI)
      fix q'
      assume "q' \<in> Q"
      with \<open>\<forall>i\<in>I. hml_conjunct_models p (\<psi>s i)\<close>
       and \<open>\<exists>i. i \<in> I \<and> \<not> hml_conjunct_models q (\<psi>s i)\<close>
      show "hml_conjunct_models p (\<psi>s (SOME i. i \<in> I \<and> \<not> hml_conjunct_models q' (\<psi>s i)))" 
        by (metis (no_types, lifting) LTS_Tau.hml_models.simps(5) conj_dist_from_Q tfl_some)
    qed

    then show "p \<Turnstile> Conj Q (\<lambda>q. \<psi>s (SOME i. i \<in> I \<and> \<not> hml_conjunct_models q (\<psi>s i)))"
      unfolding hml_models.simps.
  next
    fix q
    assume "q \<in> Q"
    with conj_dist_from_Q
    have "p \<Turnstile> Conj I \<psi>s" and "\<not> q \<Turnstile> Conj I \<psi>s" by auto

    from \<open>\<not> q \<Turnstile> Conj I \<psi>s\<close>
    have "\<exists>i. i \<in> I \<and> \<not> hml_conjunct_models q (\<psi>s i)"
      using hml_models.simps(5) by blast

    then have "\<not>(hml_conjunct_models q (\<psi>s (SOME i. i \<in> I \<and> \<not> hml_conjunct_models q (\<psi>s i))))"
      by (metis (no_types, lifting) tfl_some)

    then have "\<exists>q'\<in>Q. \<not>(hml_conjunct_models q (\<psi>s (SOME i. i \<in> I \<and> \<not> hml_conjunct_models q' (\<psi>s i))))"
      using \<open>q \<in> Q\<close> by auto

    then show "\<not> q \<Turnstile> Conj Q (\<lambda>q. \<psi>s (SOME i. i \<in> I \<and> \<not> hml_conjunct_models q (\<psi>s i)))"
      unfolding hml_models.simps by auto
  qed
qed


lemma dist_conjunct_image_subset_all_conjuncts:
  defines 
    "distinguishing_conjunct \<equiv> (\<lambda>I.\<lambda>\<psi>s.
       \<lambda>q. if I = {}
           then Pos TT
           else if \<exists>i \<in> I. \<not>(hml_conjunct_models q (\<psi>s i))
                then \<psi>s (SOME i. i \<in> I \<and> \<not>(hml_conjunct_models q (\<psi>s i)))
                else \<psi>s (SOME i. i \<in> I))"
  shows "(distinguishing_conjunct I \<psi>s) ` Q \<subseteq> (\<psi>s ` I) \<union> {Pos TT}"
proof (cases "I = {}")
  assume "I = {}"
  then show "distinguishing_conjunct I \<psi>s ` Q \<subseteq> \<psi>s ` I \<union> {Pos TT}"
    by (simp add: assms image_subsetI)
next
  assume "I \<noteq> {}"

  then have "(\<lambda>q. if \<exists>i \<in> I. \<not>(hml_conjunct_models q (\<psi>s i))
             then \<psi>s (SOME i. i \<in> I \<and> \<not>(hml_conjunct_models q (\<psi>s i)))
             else \<psi>s (SOME i. i \<in> I)) ` Q \<subseteq> \<psi>s ` I"
    by (smt (verit, ccfv_threshold) empty_subsetI image_eqI image_is_empty image_subsetI subset_antisym tfl_some)

  then show "distinguishing_conjunct I \<psi>s ` Q \<subseteq> \<psi>s ` I \<union> {Pos TT}"
    using \<open>I \<noteq> {}\<close> and distinguishing_conjunct_def
    by auto
qed

lemma models_full_models_dist_subset:
  defines 
    "distinguishing_conjunct \<equiv> (\<lambda>I.\<lambda>\<psi>s.
       \<lambda>q. if I = {}
           then Pos TT
           else if \<exists>i \<in> I. \<not>(hml_conjunct_models q (\<psi>s i))
                then \<psi>s (SOME i. i \<in> I \<and> \<not>(hml_conjunct_models q (\<psi>s i)))
                else \<psi>s (SOME i. i \<in> I))"
  assumes "p \<Turnstile> (Conj I \<psi>s)"
  shows "p \<Turnstile> (Conj Q (distinguishing_conjunct I \<psi>s))"
  using assms(2)
  unfolding hml_models.simps
proof -
  assume "\<forall>i\<in>I. hml_conjunct_models p (\<psi>s i)"

  from dist_conjunct_image_subset_all_conjuncts
  have "\<forall>q\<in>Q. (\<exists>i\<in>I. distinguishing_conjunct I \<psi>s q = \<psi>s i) \<or> (distinguishing_conjunct I \<psi>s q = Pos TT)"
    unfolding distinguishing_conjunct_def
    apply (cases "I = {}")
    apply simp
    using some_in_eq some_eq_ex by (smt (z3))

  with \<open>\<forall>i\<in>I. hml_conjunct_models p (\<psi>s i)\<close>
  show "\<forall>q\<in>Q. hml_conjunct_models p (distinguishing_conjunct I \<psi>s q)"
    using distinguishing_conjunct_def by fastforce
qed

lemma models_full_models_dist_subset':
  fixes \<psi>s'
  defines 
    "distinguishing_conjunct \<equiv> (\<lambda>I.\<lambda>\<psi>s.
       \<lambda>q. if I = {}
           then Pos (Internal (Conj {} \<psi>s'))
           else if \<exists>i \<in> I. \<not>(hml_conjunct_models q (\<psi>s i))
                then \<psi>s (SOME i. i \<in> I \<and> \<not>(hml_conjunct_models q (\<psi>s i)))
                else \<psi>s (SOME i. i \<in> I))"
  assumes "p \<Turnstile> (Conj I \<psi>s)"
  shows "p \<Turnstile> (Conj Q (distinguishing_conjunct I \<psi>s))"
  using assms(2)
proof (cases "I = {}")
  assume "I = {}"
  then have "distinguishing_conjunct I \<psi>s = (\<lambda>q. Pos (Internal (Conj {} \<psi>s')))"
    unfolding distinguishing_conjunct_def by simp
  then show "p \<Turnstile> Conj Q (distinguishing_conjunct I \<psi>s)"
    using silent_reachable.intros(1) by auto
next
  assume "p \<Turnstile> Conj I \<psi>s"
      and "I \<noteq> {}"
  then show "p \<Turnstile> Conj Q (distinguishing_conjunct I \<psi>s)"
    using models_full_models_dist_subset
      and distinguishing_conjunct_def
    by (smt (verit, ccfv_threshold) hml_models.simps(5))
qed


lemma dist_conj_non_empty_conj:
  fixes p :: 's and q :: 's
  assumes "p <> (Conj I \<psi>s) q"
  shows "I \<noteq> {}"
  by (metis dist_def assms empty_iff hml_models.simps(5))

end (* LTS_Tau *)

context Inhabited_Tau_LTS
begin

lemma hml_and_dist_disj: "p <> (\<psi>l \<and>hml \<psi>r) q = (p \<Turnstile> (\<psi>l \<and>hml \<psi>r) \<and> (\<not>hml_conjunct_models q \<psi>l \<or> \<not>hml_conjunct_models q \<psi>r))"
  using Inhabited_Tau_LTS.hml_and_and Inhabited_Tau_LTS_axioms LTS_Tau.dist_def by fastforce

end

end
