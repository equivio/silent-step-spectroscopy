theory Silent_Step_Spectroscopy
  imports Spectroscopy_Game Expressiveness_Price HML_SRBB Weak_Traces
begin


theorem (in full_spec_game) spectroscopy_game_correctness:
  shows "(\<exists>\<phi> \<in> \<O> e. Inhabited_Tau_LTS.distinguishes_from step left right \<tau> \<phi> p Q)
       = (in_wina e (Attacker_Immediate p Q))"
  oops


end
