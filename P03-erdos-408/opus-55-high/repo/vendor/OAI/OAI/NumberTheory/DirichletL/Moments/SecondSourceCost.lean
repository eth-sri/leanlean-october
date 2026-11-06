module

public import OAI.NumberTheory.DirichletL.Moments.SecondLiveEnergy
public import OAI.NumberTheory.DirichletL.Moments.RestrictedSourceNormalization

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical

namespace SevenEighths.CenteredMomentSecondSourceCost
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [Fintype ι]
local instance : DecidableEq (ι ⊕ Fin 2) := Classical.decEq _

end SevenEighths.CenteredMomentSecondSourceCost

end

end OAI
