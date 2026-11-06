module

public import OAI.NumberTheory.DirichletL.Moments.NaturalFixedRaySourceCharacters
public import OAI.NumberTheory.DirichletL.Moments.HeckeExceptionalEnergy

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical

namespace SevenEighths.CenteredMomentNaturalFixedRaySource
open HeckeFamily
local notation "O" => HeckeFamily.O

def internalQ (Q : Ideal HeckeFamily.O) (η₀ : Character) : Ideal HeckeFamily.O := Q⊓η₀.modulus

lemma internalQ_ne_zero (Q : Ideal HeckeFamily.O) (hQ : Q≠0) (η₀ : Character) : internalQ Q η₀≠0 :=
  Ideal.inf_ne_bot_of_ne_bot hQ η₀.modulus_ne_bot

lemma internalQ_ne_top (Q : Ideal HeckeFamily.O) (hQ : Q≠⊤) (η₀ : Character) : internalQ Q η₀≠⊤ := by
  intro h
  exact hQ (top_le_iff.mp (h ▸ (inf_le_left : internalQ Q η₀≤Q)))

variable (M : Ideal HeckeFamily.O) [NeZero M]
local instance : Finite (HeckeFamily.O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (HeckeFamily.O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

end SevenEighths.CenteredMomentNaturalFixedRaySource

end

end OAI
