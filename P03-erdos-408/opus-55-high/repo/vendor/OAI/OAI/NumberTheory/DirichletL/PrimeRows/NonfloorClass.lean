module

public import OAI.NumberTheory.DirichletL.PrimeRows.NonfloorMoments
public import OAI.NumberTheory.DirichletL.PrimeRows.NonfloorExponent

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical
open Filter Set
namespace SevenEighths.ProbeHighRowFamily
open ProbeRaySlots
variable (M : Ideal HeckeFamily.O) [NeZero M]
local instance : Finite (HeckeFamily.O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (HeckeFamily.O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

omit [NeZero M] in
lemma nonfloorPoolOutside (S : Finset (Ideal HeckeFamily.O)) (N : ℕ) (c b : ℝ) (Y : Fin N→ℝ) :
    ∀j P,P∈pool (RayQuotient.identityClass M H) S c b (Y j) → P.val∉S :=
  by simp

end SevenEighths.ProbeHighRowFamily

end

end OAI
