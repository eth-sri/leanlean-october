module

public import OAI.NumberTheory.DirichletL.Moments.NaturalFixedRaySourceFreeExceptional
public import OAI.NumberTheory.DirichletL.Moments.PrimeHeight

set_option linter.privateModule false

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical

namespace SevenEighths.CenteredMomentNaturalFixedRaySource
local notation "O" => HeckeFamily.O

variable {Δ : ℝ} {D : Parameters.HighData Δ}

end SevenEighths.CenteredMomentNaturalFixedRaySource

end

end OAI
