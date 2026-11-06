module

public import OAI.NumberTheory.DirichletL.Moments.NaturalFixedRaySourceSlots
public import OAI.NumberTheory.DirichletL.Moments.SlotNormalization

@[expose] public section

namespace OAI

noncomputable section


namespace SevenEighths.CenteredMomentNaturalFixedRaySource

local notation "O" => HeckeFamily.O
variable (M : Ideal O) [NeZero M]
variable (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

end SevenEighths.CenteredMomentNaturalFixedRaySource

end

end OAI
