module

public import OAI.NumberTheory.DirichletL.PrimeRows.NonfloorClass

@[expose] public section

namespace OAI

noncomputable section


namespace SevenEighths.ProbeHighRowFamily

local notation "O" => HeckeFamily.O
variable (M : Ideal O) [NeZero M]
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

end SevenEighths.ProbeHighRowFamily

end

end OAI
