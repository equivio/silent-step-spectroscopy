theory Silent_Step_Spectroscopy
  imports Spectroscopy_Game Expressiveness_Price Weak_Traces
begin

theorem spectroscopy_game_correctness: "\<exists>\<phi> \<in> \<O> e. distinguishes_from \<phi> p Q = in_wina e (Attacker_Immediate p Q)"
  oops

end
