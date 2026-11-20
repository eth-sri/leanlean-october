/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import Mathlib.Algebra.MvPolynomial.Degrees
import CCDN.Algebra.PrimitiveNormalization
import CCDN.ForMathlib.MvPolynomial
import Mathlib.Algebra.Algebra.Rat
import Mathlib.Algebra.MvPolynomial.Nilpotent
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors

/-! Positive-degree irreducible integer equations remain irreducible over Q.
Primitive denominator-cleared divisors give an elementary Gauss argument. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

/-- An irreducible integer polynomial of positive total degree remains irreducible over `ℚ`. -/
theorem rational_map_irreducible_of_integer {n : ℕ}
    (f : MvPolynomial (Fin n) ℤ) (hir : Irreducible f) (hd : 0 < f.totalDegree) :
    Irreducible (map (Int.castRingHom ℚ) f) := by
  let φ := map (Int.castRingHom ℚ) (σ := Fin n)
  have hf0 := (map_ne_zero_iff φ (map_injective _ Int.cast_injective)).mpr hir.ne_zero
  refine ⟨fun hu => hd.ne' (by
    simpa [φ, totalDegree_map_of_injective (f := Int.castRingHom ℚ) Int.cast_injective] using
      (isUnit_iff_totalDegree_of_isReduced.mp hu).2), ?_⟩
  intro q r he
  change φ f = q * r at he
  have hq : q ≠ 0 := fun h => hf0 (by simp [he, h])
  obtain ⟨g, hg, ha⟩ := exists_primitive_integer_model q hq
  obtain ⟨u, hu⟩ := hg.rational_map_dvd_iff.mp (ha.dvd'.trans ⟨r, he⟩)
  rcases hir.isUnit_or_isUnit hu with h | h
  · exact Or.inl (ha.isUnit_iff.mpr (h.map φ))
  · right
    have hc : φ f ∣ q := by
      have hfu : Associated (φ g) (φ f) := by
        rw [hu, map_mul]
        exact associated_mul_unit_right _ _ (h.map φ)
      exact hfu.dvd'.trans ha.dvd'
    obtain ⟨v, hv⟩ := hc
    exact isUnit_iff_dvd_one.mpr ⟨v, mul_left_cancel₀ hq (by rw [← mul_assoc, ← he, ← hv, mul_one])⟩

/-- Mapping an integer polynomial to `ℚ` preserves its total degree. -/
lemma rational_map_totalDegree {σ : Type*} (f : MvPolynomial σ ℤ) :
    (MvPolynomial.map (Int.castRingHom ℚ) f).totalDegree = f.totalDegree :=
    totalDegree_map_of_injective Int.cast_injective _

/-- If the image of an integer polynomial in a field `F` of characteristic zero is irreducible,
then its image over `ℚ` is irreducible. -/
lemma rational_irreducible_of_charZero_map {F σ : Type*} [Field F] [CharZero F]
    (f : MvPolynomial σ ℤ) (hf : Irreducible (MvPolynomial.map (Int.castRingHom F) f)) :
    Irreducible (MvPolynomial.map (Int.castRingHom ℚ) f) := by
  apply mvPolynomial_irreducible_of_field_map (algebraMap ℚ F)
  rw [map_map]
  have he : (algebraMap ℚ F).comp (Int.castRingHom ℚ) = Int.castRingHom F := by ext; simp
  rw [he]
  exact hf

end
end CCDN
