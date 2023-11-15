theory HML_SRBB
imports Main Hennessy_Milner_Logic
begin

context lts_tau
begin

inductive is_hml_srbb :: "('a, 'i) hml_formula \<Rightarrow> bool" 
  and is_hml_chi :: "(('a, 'i) hml_formula, ('a, 'i) hml_psi) sum  \<Rightarrow> bool" where
srbb_true: "is_hml_srbb (HML_true)" |
srbb_eps: "is_hml_srbb (HML_eps \<phi>)" if "is_hml_chi (Inl \<phi>)"|
srbb_conj: "is_hml_srbb (HML_conj I F)" if 
"\<forall>i \<in> I. (\<exists>\<phi>. ((F i)) = (HML_neg (HML_eps \<phi>)) \<or> ((F i)) = HML_phi (HML_eps \<phi>) \<and> is_hml_chi (Inl \<phi>))" |

chi_poss: "is_hml_chi (Inl (\<langle>\<alpha>\<rangle>\<phi>))" if "is_hml_srbb \<phi>" |
chi_conj: "is_hml_chi (Inl (HML_conj I F))" if 
"(\<forall>i \<in> I. (\<exists>\<phi>. ((F i)) = (HML_neg (HML_eps \<phi>)) \<or> ((F i)) = HML_phi (HML_eps \<phi>) \<and> is_hml_chi (Inl \<phi>))) \<or> 
((\<exists>i \<in> I. \<exists>\<alpha> \<phi>. (F i) = (HML_soft_poss \<alpha> \<phi>) \<and> is_hml_chi (Inl \<phi>) 
    \<and> (\<forall>j \<in> I. \<exists>\<alpha> \<phi>. (F j) = HML_soft_poss \<alpha> \<phi> \<longrightarrow> i = j) 
    \<and> (\<forall>j \<in> I. i \<noteq> j \<longrightarrow> 
      (\<exists>\<phi>. ((F j)) = (HML_neg (HML_eps \<phi>)) \<or> ((F j)) = HML_phi (HML_eps \<phi>) \<and> is_hml_chi (Inl \<phi>)))) \<or>
(\<exists>i \<in> I. (F i) = (HML_neg (HML_tau HML_true)) 
    \<and> (\<forall>j \<in> I. i \<noteq> j \<longrightarrow> (\<exists>\<phi>. ((F j)) = (HML_neg (HML_eps \<phi>)) \<or> ((F j)) = HML_phi (HML_eps \<phi>) \<and> is_hml_chi (Inl \<phi>)))))"

end
end