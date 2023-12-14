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

lemma \<epsilon>\<tau>\<phi>_eq_\<epsilon>\<phi>: "(state \<Turnstile> (Internal \<phi>)) = (state \<Turnstile> (Internal (Silent \<phi>)))"
  apply (rule iffI)
  apply auto[1]
  unfolding hml_models.simps
proof -
  assume "\<exists>p'. state \<Zsurj> p' \<and>
             ((\<exists>p'a. p' \<mapsto> \<tau> p'a \<and> (p'a \<Turnstile> \<phi>)) \<or>
             (p' \<Turnstile> \<phi>))"
  hence "(\<exists>p'. state \<Zsurj> p' \<and> (\<exists>p'a. p' \<mapsto> \<tau> p'a \<and> (p'a \<Turnstile> \<phi>)))
             \<or> (\<exists>p'. state \<Zsurj> p' \<and> (p' \<Turnstile> \<phi>))" by auto
  then show "\<exists>p'. state \<Zsurj> p' \<and> (p' \<Turnstile> \<phi>)"
  proof (rule disjE)
    assume "\<exists>p'. state \<Zsurj> p' \<and> (\<exists>p'a. p' \<mapsto> \<tau> p'a \<and> (p'a \<Turnstile> \<phi>))"
    then obtain p' where "state \<Zsurj> p'" and "(\<exists>p'a. p' \<mapsto> \<tau> p'a \<and> (p'a \<Turnstile> \<phi>))" by auto
    then obtain p'' where "p' \<mapsto> \<tau> p''" and "p'' \<Turnstile> \<phi>" by auto

    from \<open>state \<Zsurj> p'\<close> and \<open>p' \<mapsto> \<tau> p''\<close>
    have "state \<Zsurj> p''" using silend_reachable_append by auto
    with \<open>p'' \<Turnstile> \<phi>\<close> 
    show "\<exists>p'. state \<Zsurj> p' \<and> (p' \<Turnstile> \<phi>)" by auto
  next
    assume "\<exists>p'. state \<Zsurj> p' \<and> (p' \<Turnstile> \<phi>)"
    then show "\<exists>p'. state \<Zsurj> p' \<and> (p' \<Turnstile> \<phi>)".
  qed
qed

end

end
