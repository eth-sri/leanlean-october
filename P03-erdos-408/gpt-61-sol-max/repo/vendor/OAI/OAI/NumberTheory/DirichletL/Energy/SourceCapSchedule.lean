module
public import Mathlib.Tactic

public import OAI.NumberTheory.DirichletL.Energy.WidthRanges
public import OAI.NumberTheory.DirichletL.Energy.FirstLiveAdmission

@[expose] public section

namespace OAI



namespace SevenEighths.CenteredMomentEnergySourceCapSchedule
open CenteredMomentEnergyWidthSchedule CenteredMomentEnergyWidthRanges
open CenteredMomentEnergyFirstLiveAdmission

section
variable (M B L ε A P : ℝ) (hM : 0≤M) (hB : 0≤B)

lemma count_pos  :0<count M ε:=by
  unfold count CenteredMomentFirstSecondLossParameters.depth
  omega
include hM hB in
lemma final_range_large    :
    20≤range M B L (count M ε):=by
  have hh:=range_mono M B L hM hB (show 1≤count M ε from count_pos M ε)
  grind [max, range, step, hh]
include hM hB in
lemma readyBudget_le_schedule    
    (hA:A≤2*range M B L (count M ε)+M+1)(hP:P≤B):
    readyBudget A P≤finalSourceCap M B L ε:=by
  grind [final_range_large, readyBudget, finalSourceCap, sourceCap]

end

end SevenEighths.CenteredMomentEnergySourceCapSchedule



end OAI
