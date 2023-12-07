theory Energy
  imports EnergyGames "HOL-Library.Extended_Nat"
begin

datatype energy = E (one: "enat") (two: "enat") (three: "enat") (four: "enat")
                    (five: "enat") (six: "enat") (seven: "enat") (eight: "enat") | eneg

instantiation energy :: minus
begin
abbreviation "larger_or_eq e1 e2 \<equiv> ((one e1) \<ge> (one e2)) \<and> ((two e1) \<ge> (two e2))
                           \<and> ((three e1) \<ge> (three e2))\<and> ((four e1) \<ge> (four e2))
                           \<and> ((five e1) \<ge> (five e2))\<and> ((six e1) \<ge> (six e2))
                           \<and> ((seven e1) \<ge> (seven e2))\<and> ((eight e1) \<ge> (eight e2))"

definition minus_energy_def: "e1 - e2 \<equiv> if (larger_or_eq e1 e2) then 
                                          E ((one e1) - (one e2)) ((two e1) - (two e2)) 
                                            ((three e1) - (three e2)) ((four e1) - (four e2)) 
                                            ((five e1) - (five e2)) ((six e1) - (six e2))
                                            ((seven e1) - (seven e2)) ((eight e1) - (eight e2))
                                         else eneg"

instance ..

lemma energy_minus[simp]:
  assumes " larger_or_eq (E a1 b1 c1 d1 e1 f1 g1 h1) ( E a2 b2 c2 d2 e2 f2 g2 h2)"
  shows "E a1 b1 c1 d1 e1 f1 g1 h1 - E a2 b2 c2 d2 e2 f2 g2 h2 = E (a1 - a2) (b1 - b2) (c1 - c2) (d1 - d2) 
          (e1 - e2) (f1 - f2) (g1 -g2) (h1 - h2)" 
  using minus_energy_def assms by auto
end

definition "min1_6 e \<equiv> E (min (one e) (six e)) (two e) (three e) (four e) (five e) (six e) (seven e) (eight e)"
definition "min1_7 e \<equiv> E (min (one e) (seven e)) (two e) (three e) (four e) (five e) (six e) (seven e) (eight e)"

lemma min_1_6_simps[simp]:
  shows "one (min1_6 e) = min (one e) (six e)"
        "two (min1_6 e) = two e" 
        "three (min1_6 e) = three e"
        "four (min1_6 e) = four e"
        "five (min1_6 e) = five e"
        "six (min1_6 e) = six e"
        "seven (min1_6 e) = seven e"
        "eight (min1_6 e) = eight e"
  unfolding min1_6_def by (simp_all add: min1_6_def)

lemma min_1_7_simps:
  shows "one (min1_7 e) = min (one e) (seven e)"
        "two (min1_7 e) = two e" 
        "three (min1_7 e) = three e"
        "four (min1_7 e) = four e"
        "five (min1_7 e) = five e"
        "six (min1_7 e) = six e"
        "seven (min1_7 e) = seven e"
        "eight (min1_7 e) = eight e"
  unfolding min1_7_def by (simp_all add: min1_7_def)

end