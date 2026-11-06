module

public import OAI.NumberTheory.DirichletL.Moments.FirstNonexceptionalWeightSum
public import OAI.NumberTheory.DirichletL.Moments.FirstPhysicalSourceFixedFamily

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical

namespace SevenEighths.CenteredMomentFirstNonexceptionalFixedWeightSum
local notation "O"=>ActualEisensteinCubic.O
variable {ι:Type*}[Fintype ι][DecidableEq ι]
local instance : DecidableEq (ι⊕Fin 2):=Classical.decEq _

end SevenEighths.CenteredMomentFirstNonexceptionalFixedWeightSum

end

end OAI
