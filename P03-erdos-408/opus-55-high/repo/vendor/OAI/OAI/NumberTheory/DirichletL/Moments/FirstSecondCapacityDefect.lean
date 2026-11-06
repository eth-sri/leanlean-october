module

public import OAI.NumberTheory.DirichletL.Moments.FirstSecondCapacityShift

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical

namespace SevenEighths.CenteredMomentFirstSecondCapacityLedger
local notation "O"=>ActualEisensteinCubic.O
variable {ι:Type*}[Fintype ι][DecidableEq ι]

lemma width_defect_cost (x B δ:ℝ)(hB:0≤B)(hδ:0≤δ)(hx:x≤δ):
    x+max (B-x) 0/6≤δ+B/6 := by
  grind

end SevenEighths.CenteredMomentFirstSecondCapacityLedger

end

end OAI
