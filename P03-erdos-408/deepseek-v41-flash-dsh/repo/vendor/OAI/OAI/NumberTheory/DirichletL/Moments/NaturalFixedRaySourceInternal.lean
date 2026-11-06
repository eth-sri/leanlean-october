module

public import OAI.NumberTheory.DirichletL.Moments.NaturalFixedRaySourceCharacters
public import OAI.NumberTheory.DirichletL.Moments.HeckeExceptionalEnergy

@[expose] public section

namespace OAI

noncomputable section


namespace SevenEighths.CenteredMomentNaturalFixedRaySource
open HeckeFamily CenteredExceptionalProfile CenteredExceptionalCount HeckeRowClosure CanonicalRowCompletion ConcretePrimeRowBridge CenteredMomentNaturalRowSource UniqueFactorizationMonoid
local notation "O" => HeckeFamily.O

def internalQ (Q : Ideal O) (η₀ : Character) : Ideal O := Q⊓η₀.modulus

lemma internalQ_ne_zero (Q : Ideal O) (hQ : Q≠0) (η₀ : Character) : internalQ Q η₀≠0 :=
  Ideal.inf_ne_bot_of_ne_bot hQ η₀.modulus_ne_bot

lemma internalQ_ne_top (Q : Ideal O) (hQ : Q≠⊤) (η₀ : Character) : internalQ Q η₀≠⊤ := by
  intro h
  exact hQ (top_le_iff.mp (h ▸ (inf_le_left : internalQ Q η₀≤Q)))

variable (M : Ideal O) [NeZero M]
variable (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

end SevenEighths.CenteredMomentNaturalFixedRaySource

end

end OAI
