module

public import OAI.NumberTheory.DirichletL.Moments.AmplificationActiveFamily
public import OAI.NumberTheory.DirichletL.Moments.AmplificationErrorEnergy
public import OAI.NumberTheory.DirichletL.Moments.AmplificationChildEnergy

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical

namespace SevenEighths.CenteredMomentAmplificationOriginalErrors
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [Fintype ι]
local instance : DecidableEq (ι ⊕ Fin 2) := Classical.decEq _

end SevenEighths.CenteredMomentAmplificationOriginalErrors

end

end OAI
