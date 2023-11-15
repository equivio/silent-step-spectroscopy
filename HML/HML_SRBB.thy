theory HML_SRBB
imports Main HML
begin

context LTS_Tau
begin
inductive is_hml_srbb :: "('a, 'i) HML \<Rightarrow> bool" 
  and is_hml_chi :: "(('a, 'i) HML, ('a, 'i) HML_neg) sum  \<Rightarrow> bool" where
srbb_true: "is_hml_srbb (HML_true)" |
srbb_eps: "is_hml_srbb (HML_internal \<phi>)" if "is_hml_chi (Inl \<phi>)"|
srbb_conj: "is_hml_srbb (HML_conj I F)" if 
"\<forall>i \<in> I. (\<exists>\<phi>. ((F i)) = (HML_not (HML_internal \<phi>)) \<or> ((F i)) = HML_just (HML_internal \<phi>) \<and> is_hml_chi (Inl \<phi>))" |

chi_poss: "is_hml_chi (Inl (HML_poss \<alpha> \<phi>))" if "is_hml_srbb \<phi>" |
chi_conj: "is_hml_chi (Inl (HML_conj I F))" if 
"(\<forall>i \<in> I. (\<exists>\<phi>. ((F i)) = (HML_not (HML_internal \<phi>)) \<or> ((F i)) = HML_just (HML_internal \<phi>) \<and> is_hml_chi (Inl \<phi>))) \<or> 
((\<exists>i \<in> I. \<exists>\<alpha> \<phi>. (F i) = (HML_soft_poss \<alpha> \<phi>) \<and> is_hml_chi (Inl \<phi>)
    \<and> (\<forall>j \<in> I. \<exists>\<alpha> \<phi>. (F j) = HML_soft_poss \<alpha> \<phi> \<longrightarrow> i = j) 
    \<and> (\<forall>j \<in> I. i \<noteq> j \<longrightarrow> 
      (\<exists>\<phi>. ((F j)) = (HML_not (HML_internal \<phi>)) \<or> ((F j)) = HML_just (HML_internal \<phi>) \<and> is_hml_chi (Inl \<phi>)))) \<or>
(\<exists>i \<in> I. (F i) = (HML_not (HML_silent HML_true)) 
    \<and> (\<forall>j \<in> I. i \<noteq> j \<longrightarrow> (\<exists>\<phi>. ((F j)) = (HML_not (HML_internal \<phi>)) \<or> ((F j)) = HML_just (HML_internal \<phi>) \<and> is_hml_chi (Inl \<phi>)))))"

definition HML_SRBB :: \<open>('a, 'i) HML set\<close> where
\<open>HML_SRBB \<equiv> {\<phi>. is_hml_srbb \<phi>}\<close>

end

end