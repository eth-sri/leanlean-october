module

public import OAI.NumberTheory.DirichletL.Moments.NaturalFixedRaySourceCharacters

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical

namespace SevenEighths.CenteredMomentNaturalFixedRaySource
local notation "O" => HeckeFamily.O
variable (M : Ideal HeckeFamily.O) [NeZero M]
local instance : Finite (HeckeFamily.O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (HeckeFamily.O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

end SevenEighths.CenteredMomentNaturalFixedRaySource

end

end OAI
