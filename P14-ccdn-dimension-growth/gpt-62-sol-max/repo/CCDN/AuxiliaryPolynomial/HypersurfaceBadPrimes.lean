/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.AuxiliaryPolynomial.HypersurfaceBadReduction
public import CCDN.Plane.FiniteFieldConstants

/-! The good-reduction hypothesis used for local determinant estimates. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

/-- A polynomial with an irreducible image under a coefficient map is nonzero. -/
lemma ne_zero_of_irreducible_map {R S σ : Type*} [CommSemiring R] [CommSemiring S]
    {φ : R →+* S} {f : MvPolynomial σ R} (h : Irreducible (map φ f)) : f ≠ 0 := by
  aesop

/-- Good reduction at a prime `p`: the reduction of `f` modulo `p` is nonzero and
absolutely irreducible. -/
abbrev HasGoodReduction {σ : Type*} (f : MvPolynomial σ ℤ) (p : ℕ) [Fact p.Prime] : Prop :=
  map (Int.castRingHom (ZMod p)) f ≠ 0 ∧
    Irreducible (map (algebraMap (ZMod p) (AlgebraicClosure (ZMod p)))
      (map (Int.castRingHom (ZMod p)) f))

end
end CCDN
