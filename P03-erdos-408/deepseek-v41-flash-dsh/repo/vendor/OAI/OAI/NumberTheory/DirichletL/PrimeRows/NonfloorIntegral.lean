module

public import OAI.NumberTheory.DirichletL.PrimeRows.NonfloorArithmetic

@[expose] public section

namespace OAI

noncomputable section


namespace SevenEighths.ProbeHighRowFamily

local notation "O" => HeckeFamily.O
variable (M : Ideal O) [NeZero M]
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

end SevenEighths.ProbeHighRowFamily

end

end OAI
