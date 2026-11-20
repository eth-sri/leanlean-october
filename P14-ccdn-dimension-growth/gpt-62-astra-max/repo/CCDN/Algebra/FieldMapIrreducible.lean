/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Algebra.Equations
public import CCDN.ForMathlib.MvPolynomial
import Mathlib.Algebra.MvPolynomial.Nilpotent
import Mathlib.Algebra.Algebra.Rat

/-! Irreducibility descends along coefficient field extensions. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial


variable {F K σ : Type*} [Field F]

/-- A multivariate polynomial over a field whose image under a field homomorphism is irreducible
is itself irreducible. -/
lemma mvPolynomial_irreducible_of_field_map [Field K] (φ : F →+* K)
    (f : MvPolynomial σ F) (hf : Irreducible (MvPolynomial.map φ f)) : Irreducible f := by
  have hunit (q : MvPolynomial σ F) (hq : IsUnit (MvPolynomial.map φ q)) : IsUnit q := by
    obtain ⟨hc, hd⟩ := MvPolynomial.isUnit_iff_totalDegree_of_isReduced.mp hq
    apply MvPolynomial.isUnit_iff_totalDegree_of_isReduced.mpr
    refine ⟨isUnit_iff_ne_zero.mpr ?_, (MvPolynomial.totalDegree_map_of_injective φ.injective q) ▸ hd⟩
    intro hz
    apply hc.ne_zero
    rw [MvPolynomial.coeff_map, hz, map_zero]
  refine ⟨fun h => hf.not_isUnit (h.map _), ?_⟩
  intro g h he
  have hh := hf.isUnit_or_isUnit (by rw [he, map_mul])
  grind

/-- If the image of an integer polynomial in a field `F` of characteristic zero is irreducible,
then its image over `ℚ` is irreducible. -/
lemma rational_irreducible_of_charZero_map [CharZero F]
    (f : MvPolynomial σ ℤ) (hf : Irreducible (MvPolynomial.map (Int.castRingHom F) f)) :
    Irreducible (rationalEquation f) := by
  apply mvPolynomial_irreducible_of_field_map (algebraMap ℚ F)
  rw [map_map]
  have he : (algebraMap ℚ F).comp (Int.castRingHom ℚ) = Int.castRingHom F := by ext; simp
  rw [he]
  exact hf

end
end CCDN
