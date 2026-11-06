module

public import OAI.NumberTheory.DirichletL.Moments.FirstMaskedFamily
public import OAI.NumberTheory.DirichletL.Moments.AmplificationChildInput
public import OAI.NumberTheory.DirichletL.Moments.OriginalCommonHarmonic

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical

namespace SevenEighths.CenteredMomentFirstMaskedInput
local notation "O" => HeckeFamily.O
variable {ι : Type*} [Fintype ι]
local instance {κ : Type*} : DecidableEq κ := Classical.decEq _
local instance : DecidableEq (ι ⊕ Fin 2) := Classical.decEq _

end SevenEighths.CenteredMomentFirstMaskedInput

end

end OAI
