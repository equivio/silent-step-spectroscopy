theory Stability_Respecting_Branching_Bisimilarity
  imports Main HML_SRBB Expressiveness_Price
begin

context LTS_Tau
begin

inductive stability_respecting_branching_bisimilar :: "'s \<Rightarrow> 's \<Rightarrow> bool" (infix "\<approx>SRBB" 70) where
  "p \<approx>SRBB p" |
  "p \<approx>SRBB q" if "\<forall>p' \<alpha>. p \<mapsto> \<alpha> p' \<longrightarrow> ((\<alpha> = \<tau> \<and> p' \<approx>SRBB q)
                                    \<or> (\<exists>q' q''. q \<Zsurj> q' \<and> q' \<mapsto> \<alpha> q'' \<and> p \<approx>SRBB q' \<and> p' \<approx>SRBB q''))"
             and "\<not>(\<exists>p'. p \<mapsto> \<tau> p') \<longrightarrow> (\<exists>q'. q \<Zsurj> q' \<and> \<not>(\<exists>q''. q' \<mapsto> \<tau> q'') \<and> p \<approx>SRBB q')"
             and "\<forall>q' \<alpha>. q \<mapsto> \<alpha> q' \<longrightarrow> ((\<alpha> = \<tau> \<and> p \<approx>SRBB q')
                                    \<or> (\<exists>p' p''. p \<Zsurj> p' \<and> p' \<mapsto> \<alpha> p'' \<and> p' \<approx>SRBB q \<and> p'' \<approx>SRBB q'))"
             and "\<not>(\<exists>q'. q \<mapsto> \<tau> q') \<longrightarrow> (\<exists>p'. p \<Zsurj> p' \<and> \<not>(\<exists>p''. p' \<mapsto> \<tau> p'') \<and> p' \<approx>SRBB q)"

lemma srbb_equiv: "equivp (\<approx>SRBB)"
proof (rule equivpI)
  show "reflp (\<approx>SRBB)" 
    by (simp add: reflpI stability_respecting_branching_bisimilar.intros(1))
next
  show "symp (\<approx>SRBB)"
  proof (rule sympI)
    fix p q
    assume "p \<approx>SRBB q"
    then show "q \<approx>SRBB p"
    proof (induct)
      case (1 p)
      then show ?case 
        using stability_respecting_branching_bisimilar.intros(1) by auto
    next
      case (2 p q)
      assume
        "\<forall>p' \<alpha>. p \<mapsto> \<alpha> p' \<longrightarrow>
             \<alpha> = \<tau> \<and> p' \<approx>SRBB q \<and> q \<approx>SRBB p'
          \<or> (\<exists>q' q''. q \<Zsurj> q' \<and> q' \<mapsto> \<alpha> q'' \<and> (p \<approx>SRBB q' \<and> q' \<approx>SRBB p) \<and> p' \<approx>SRBB q'' \<and> q'' \<approx>SRBB p')"
        "(\<nexists>p'. p \<mapsto> \<tau> p') \<longrightarrow> (\<exists>q'. q \<Zsurj> q' \<and> (\<nexists>q''. q' \<mapsto> \<tau> q'') \<and> p \<approx>SRBB q' \<and> q' \<approx>SRBB p)"
        "\<forall>q' \<alpha>. q \<mapsto> \<alpha> q' \<longrightarrow>
             \<alpha> = \<tau> \<and> p \<approx>SRBB q' \<and> q' \<approx>SRBB p
          \<or> (\<exists>p' p''. p \<Zsurj> p' \<and> p' \<mapsto> \<alpha> p'' \<and> (p' \<approx>SRBB q \<and> q \<approx>SRBB p') \<and> p'' \<approx>SRBB q' \<and> q' \<approx>SRBB p'')"
        "(\<nexists>q'. q \<mapsto> \<tau> q') \<longrightarrow> (\<exists>p'. p \<Zsurj> p' \<and> (\<nexists>p''. p' \<mapsto> \<tau> p'') \<and> p' \<approx>SRBB q \<and> q \<approx>SRBB p')"
      show ?case
      proof
        from \<open>\<forall>q' \<alpha>. q \<mapsto> \<alpha> q' \<longrightarrow>
                \<alpha> = \<tau> \<and> p \<approx>SRBB q' \<and> q' \<approx>SRBB p
             \<or> (\<exists>p' p''. p \<Zsurj> p' \<and> p' \<mapsto> \<alpha> p'' \<and> (p' \<approx>SRBB q \<and> q \<approx>SRBB p') \<and> p'' \<approx>SRBB q' \<and> q' \<approx>SRBB p'')\<close>
        show "\<forall>q' \<alpha>. q \<mapsto> \<alpha> q' \<longrightarrow> \<alpha> = \<tau> \<and> q' \<approx>SRBB p \<or> (\<exists>p' p''. p \<Zsurj> p' \<and> p' \<mapsto> \<alpha> p'' \<and> q \<approx>SRBB p' \<and> q' \<approx>SRBB p'')"      
          by auto
      next
        from \<open>(\<nexists>q'. q \<mapsto> \<tau> q') \<longrightarrow> (\<exists>p'. p \<Zsurj> p' \<and> (\<nexists>p''. p' \<mapsto> \<tau> p'') \<and> p' \<approx>SRBB q \<and> q \<approx>SRBB p')\<close>
        show "(\<nexists>q'. q \<mapsto> \<tau> q') \<longrightarrow> (\<exists>p'. p \<Zsurj> p' \<and> (\<nexists>p''. p' \<mapsto> \<tau> p'') \<and> q \<approx>SRBB p')"
          by auto
      next
        from \<open>\<forall>p' \<alpha>. p \<mapsto> \<alpha> p' \<longrightarrow>
                \<alpha> = \<tau> \<and> p' \<approx>SRBB q \<and> q \<approx>SRBB p'
             \<or> (\<exists>q' q''. q \<Zsurj> q' \<and> q' \<mapsto> \<alpha> q'' \<and> (p \<approx>SRBB q' \<and> q' \<approx>SRBB p) \<and> p' \<approx>SRBB q'' \<and> q'' \<approx>SRBB p')\<close>
        show "\<forall>q' \<alpha>. p \<mapsto> \<alpha> q' \<longrightarrow> \<alpha> = \<tau> \<and> q \<approx>SRBB q' \<or> (\<exists>p' p''. q \<Zsurj> p' \<and> p' \<mapsto> \<alpha> p'' \<and> p' \<approx>SRBB p \<and> p'' \<approx>SRBB q')"
          by auto  
      next
        from \<open>(\<nexists>p'. p \<mapsto> \<tau> p') \<longrightarrow> (\<exists>q'. q \<Zsurj> q' \<and> (\<nexists>q''. q' \<mapsto> \<tau> q'') \<and> p \<approx>SRBB q' \<and> q' \<approx>SRBB p)\<close>
        show "(\<nexists>q'. p \<mapsto> \<tau> q') \<longrightarrow> (\<exists>p'. q \<Zsurj> p' \<and> (\<nexists>p''. p' \<mapsto> \<tau> p'') \<and> p' \<approx>SRBB p)"
          by auto
      qed
    qed
  qed
next
  show "transp (\<approx>SRBB)"
  proof (rule transpI)
    fix p q r
    assume "q \<approx>SRBB r"
       and "p \<approx>SRBB q"
    then show "p \<approx>SRBB r"
    proof (induct)
      case (1 p)
      then show ?case by auto
    next
      case (2 s t)
      then show ?case sorry
    qed
  qed
qed

end

lemma hml_srbb_in_infty_energy: "\<phi> \<in> \<O> (E \<infinity> \<infinity> \<infinity> \<infinity> \<infinity> \<infinity> \<infinity> \<infinity>)"
  by (simp add: \<O>_def leq_not_eneg)

end (* theory Stability_Respecting_Branching_Bisimilarity *)