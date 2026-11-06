module

public import OAI.NumberTheory.DirichletL.Moments.SecondNonexceptionalCost
public import OAI.NumberTheory.DirichletL.Moments.SecondNonexceptionalAggregate
public import OAI.NumberTheory.DirichletL.Moments.OriginalCommonHarmonic

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical

namespace SevenEighths.CenteredMomentSecondNonexceptionalLiveSource
local notation "O" => HeckeFamily.O
variable {ι:Type*} [Fintype ι] [DecidableEq ι]
local instance : DecidableEq (ι⊕Fin 2):=Classical.decEq _

end SevenEighths.CenteredMomentSecondNonexceptionalLiveSource

end

end OAI
