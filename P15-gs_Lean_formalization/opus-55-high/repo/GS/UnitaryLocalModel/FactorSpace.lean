module

public import GS.UnitaryNonmanifold.BlockInvariant
public import GS.UnitaryManifold.BlockGroup

@[expose] public section


noncomputable section
open Matrix GS GS.NonmanifoldCompletion
namespace GS.UnitaryLocalModel

/-- The corresponding compact subtype, for results stated using CompactSpace. -/
abbrev SmallFactorSpace (q : ℕ) := {p : SmallBlockParameters ℂ q // p ∈ smallFactorSet ℂ q}

instance smallFactorSpace_compactSpace (q : ℕ) : CompactSpace (SmallFactorSpace q) :=
  isCompact_iff_compactSpace.mp (isCompact_smallFactorSet q)

section
variable (q : ℕ)
def smallFactorValue (p : SmallFactorSpace q) : CMat (q*2) :=
  smallFactorMap p.val

theorem range_smallFactorValue :
    Set.range (smallFactorValue q) = sFamily ℂ q := by
  rw [← image_smallFactorMap]
  aesop

end

end GS.UnitaryLocalModel
