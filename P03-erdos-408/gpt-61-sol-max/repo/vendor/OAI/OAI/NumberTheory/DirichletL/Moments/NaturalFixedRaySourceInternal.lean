module
public import Mathlib.Tactic

public import OAI.NumberTheory.DirichletL.Moments.NaturalFixedRaySourceCharacters
public import OAI.NumberTheory.DirichletL.Moments.HeckeExceptionalEnergy

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentNaturalFixedRaySource
open HeckeFamily CenteredExceptionalProfile CenteredExceptionalCount
open HeckeRowClosure CanonicalRowCompletion ConcretePrimeRowBridge
open CenteredMomentNaturalRowSource UniqueFactorizationMonoid
local notation "O" => HeckeFamily.O

def internalQ (Q : Ideal O) (η₀ : Character)  := Q⊓η₀.modulus

lemma internalQ_ne_zero  Q  (hQ : Q≠0)  η₀  : internalQ Q η₀≠0 :=
  Ideal.inf_ne_bot_of_ne_bot hQ η₀.modulus_ne_bot

lemma internalQ_ne_top  Q  (hQ : Q≠⊤)  η₀  : internalQ Q η₀≠⊤ := fun h => hQ (top_le_iff.mp (h ▸ inf_le_left))

variable (M : Ideal O) [NeZero M]

variable (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

end SevenEighths.CenteredMomentNaturalFixedRaySource

end

end OAI
