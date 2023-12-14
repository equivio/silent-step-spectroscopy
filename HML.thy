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

context LTS_Tau
begin

lemma "(state \<Turnstile> (Internal \<phi>)) \<Longrightarrow> (state \<Turnstile> (Internal (Silent \<phi>)))"
  by auto

lemma "\<exists>state. \<exists>\<phi>.(state \<Turnstile> (Internal (Silent \<phi>))) \<and> \<not>(state \<Turnstile> (Internal \<phi>))"
  unfolding hml_models.simps
  sorry

lemma "(state \<Turnstile> (Internal \<phi>)) \<longleftrightarrow> (state \<Turnstile> (Internal (Silent \<phi>)))"
proof (rule iffI)
  assume "state \<Turnstile> Internal \<phi>"
  hence "\<exists>p'. state \<Zsurj> p' \<and> (p' \<Turnstile> \<phi>)" unfolding hml_models.simps.
  then obtain p' where
        "state \<Zsurj> p'" 
    and "(p' \<Turnstile> \<phi>)" by auto

  then have "\<exists>p'. state \<Zsurj> p' \<and>
      ((\<exists>p'a. p' \<mapsto> \<tau> p'a \<and> (p'a \<Turnstile> \<phi>)) \<or> (p' \<Turnstile> \<phi>))" 
    by blast

  then show "state \<Turnstile> Internal (Silent \<phi>)"
    unfolding hml_models.simps.
next
  assume "state \<Turnstile> Internal (Silent \<phi>)"
  hence "\<exists>p'. state \<Zsurj> p' \<and> ((\<exists>p'a. p' \<mapsto> \<tau> p'a \<and> (p'a \<Turnstile> \<phi>)) \<or> (p' \<Turnstile> \<phi>))"
    unfolding hml_models.simps.
  then obtain p' where
        "state \<Zsurj> p'" 
    and "(\<exists>p'a. p' \<mapsto> \<tau> p'a \<and> (p'a \<Turnstile> \<phi>)) \<or> (p' \<Turnstile> \<phi>)" by auto

  from \<open>(\<exists>p'a. p' \<mapsto> \<tau> p'a \<and> (p'a \<Turnstile> \<phi>)) \<or> (p' \<Turnstile> \<phi>)\<close>
  have "\<exists>p'. state \<Zsurj> p' \<and> (p' \<Turnstile> \<phi>)"
  proof (rule disjE)
    assume "\<exists>p'a. p' \<mapsto> \<tau> p'a \<and> (p'a \<Turnstile> \<phi>)"
    then obtain p'' where
          "p' \<mapsto> \<tau> p''"
      and "p'' \<Turnstile> \<phi>" by auto

    \<comment> \<open>
    from \<open>state \<Zsurj> p'\<close> and \<open>p' \<mapsto> \<tau> p''\<close>
    have "state \<Zsurj> p''" sorry
    \<close>

    then show "\<exists>p'. state \<Zsurj> p' \<and> (p' \<Turnstile> \<phi>)" sorry
  next
    assume "p' \<Turnstile> \<phi>"
    with \<open>state \<Zsurj> p'\<close>
     show "\<exists>p'. state \<Zsurj> p' \<and> (p' \<Turnstile> \<phi>)" 
       by auto
  qed

  then show "state \<Turnstile> Internal \<phi>"
    unfolding hml_models.simps.
qed

end

end
