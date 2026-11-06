module

public import OAI.NumberTheory.DirichletL.PrimeRows.NonfloorDyadic

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical
open Set
namespace SevenEighths.ProbeHighRowFamily
local notation "O" => HeckeFamily.O
variable (M : Ideal HeckeFamily.O) [NeZero M]
local instance : Finite (HeckeFamily.O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (HeckeFamily.O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

end SevenEighths.ProbeHighRowFamily

end

end OAI
