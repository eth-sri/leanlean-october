/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Algebra.Coordinates

import Mathlib

public import CCDN.ClassGroup.NormPolynomial
public import CCDN.ClassGroup.TwoTorsion
public import CCDN.Height.Box
import CCDN.ClassGroup.BalancedGenerator

/-!
Concrete integer-translation fibers of the bounded square-norm set
inject into integral points on the two signed norm curves.

The first counting reduction for two-torsion ideal classes:
inject them into the finite set of bounded algebraic integers whose absolute
norm is a square. Both possible signs of the signed norm are retained.
-/

@[expose] public section
namespace CCDN
noncomputable section
open scoped NumberField
open NumberField NumberField.InfinitePlace

variable (K : Type*) [Field K] [NumberField K]

/-- The set of nonzero algebraic integers `β ∈ 𝓞 K` bounded by `B` at every infinite place whose
absolute norm `|N(β)|` is a perfect square. -/
def boundedSquareNormIntegers (B : ℝ) : Set (𝓞 K) :=
  {β | β ≠ 0 ∧ (∀ w : InfinitePlace K, w β ≤ B) ∧
    ∃ m : ℕ, (Algebra.norm ℤ β).natAbs = m ^ 2}

/-- There are finitely many bounded square-norm integers `boundedSquareNormIntegers K B`. -/
lemma boundedSquareNormIntegers_finite (B : ℝ) :
    (boundedSquareNormIntegers K B).Finite := by
  apply Set.Finite.of_injOn 
    (t := {x : K | IsIntegral ℤ x ∧ ∀ φ : K →+* ℂ, ‖φ x‖ ≤ B})
  · intro β hβ
    exact ⟨β.isIntegral_coe, fun φ ↦ hβ.2.1 (InfinitePlace.mk φ)⟩
  · simp_all
  · exact Embeddings.finite_of_norm_le K ℂ B

/-- The two-torsion subgroup of the class group of `K` has at most as many elements as there are
bounded square-norm integers at the balanced radius `9 * |discr K| ^ (1 / [K : ℚ])`; the
injection sends each class to a balanced generator of the square of a representative ideal. -/
theorem classGroupTwoTorsionCard_le_boundedSquareNormIntegers :
    classGroupTwoTorsionCard K ≤
      (boundedSquareNormIntegers K
        (9 * |(discr K : ℝ)| ^ (1 / (Module.finrank ℚ K : ℝ)))).ncard := by
  obtain ⟨β, hinj, hβ⟩ := exists_injective_balanced_two_torsion_generators K
  rw [classGroupTwoTorsionCard, ← Set.ncard_range_of_injective hinj]
  apply Set.ncard_le_ncard _ (boundedSquareNormIntegers_finite K _)
  rintro _ ⟨c, rfl⟩
  obtain ⟨h0, hw, m, hnorm⟩ := hβ c
  exact ⟨h0, fun w ↦ (hw w).le, m, hnorm⟩

omit [NumberField K] in
end
end CCDN

namespace CCDN
noncomputable section
open scoped NumberField
open NumberField NumberField.InfinitePlace

variable (K : Type*) [Field K] [NumberField K]

private lemma bounded_infinite_places_norm_le (α : 𝓞 K) {B : ℝ}
    (hα : ∀ w : InfinitePlace K, w (α : K) ≤ B) :
    ((Algebra.norm ℤ α).natAbs : ℝ) ≤ B ^ Module.finrank ℚ K := by
  classical
  have he : (∏ w : InfinitePlace K, w (α : K) ^ mult w) =
      ((Algebra.norm ℤ α).natAbs : ℝ) := by
    rw [prod_eq_abs_norm, ← Algebra.coe_norm_int]
    norm_cast
    exact (Nat.cast_natAbs (Algebra.norm ℤ α)).symm
  rw [← he, ← sum_mult_eq , ← Finset.prod_pow_eq_pow_sum]
  apply Finset.prod_le_prod₀
  · intro w _
    positivity
  · simp_all [pow_le_pow_left₀, apply_nonneg]

private lemma integer_translate_coordinate_le (α β : 𝓞 K) {B : ℝ}
    (hα : ∀ w : InfinitePlace K, w (α : K) ≤ B)
    (hβ : ∀ w : InfinitePlace K, w (β : K) ≤ B)
    {x : ℤ} (hx : α = algebraMap ℤ (𝓞 K) x - β) :
    |↑x| ≤ 2 * B := by
  classical
  let w : InfinitePlace K := Classical.arbitrary _
  have hxK : (x : K) = (α : K) + (β : K) := by
    simp_all
  calc
    |↑x| = w (x : K) := by
      rw [w.map_intCast, Int.norm_eq_abs]
    _ = w ((α : K) + (β : K)) := congrArg w hxK
    _ ≤ w (α : K) + w (β : K) := w.val.add_le _ _
    _ ≤ 2 * B := by linarith [hα w, hβ w]

variable (β : 𝓞 K)

/-- The bounded square-norm integers of the form `x - β` with `x ∈ ℤ`, that is, those in the
integer-translation class of `-β`. -/
def squareNormTranslateFiber  (B : ℝ)  :=
  {α | α ∈ boundedSquareNormIntegers K B ∧
    ∃ x : ℤ, α = algebraMap ℤ (𝓞 K) x - β}

/-- Each square-norm translate fiber `squareNormTranslateFiber K β B` is finite. -/
lemma squareNormTranslateFiber_finite  (B : ℝ) :
    (squareNormTranslateFiber K β B).Finite :=
  (boundedSquareNormIntegers_finite K B).subset (fun _ h ↦ h.1)

/-- The rational plane curve `y ^ 2 = ε * N(x - β)` cut out by the signed norm-curve polynomial of
`β` with sign `ε`. -/
def signedNormCurveLocus  (ε : ℤ)  :=
  zeroLocus (CCDN.rationalPolynomial (signedNormCurvePolynomial K β ε))

/-- If `β` is bounded by `B` at every infinite place, then the square-norm translate fiber of `β`
has at most as many elements as there are integral points of height at most
`max (2 * B) (√(B ^ n))` on the two signed norm curves `y ^ 2 = ±N(x - β)`, where `n = [K : ℚ]`. -/
theorem squareNormTranslateFiber_count_le  {B : ℝ}
    (hβ : ∀ w : InfinitePlace K, w (β : K) ≤ B) :
    (squareNormTranslateFiber K β B).ncard ≤
      count (signedNormCurveLocus K β 1) (max (2 * B) (Real.sqrt (B ^ Module.finrank ℚ K))) +
      count (signedNormCurveLocus K β (-1))
        (max (2 * B) (Real.sqrt (B ^ Module.finrank ℚ K))) := by
  classical
  let S := squareNormTranslateFiber K β B
  let H := max (2 * B) (Real.sqrt (B ^ Module.finrank ℚ K))
  let Z := signedNormCurveLocus K β 1 ∪ signedNormCurveLocus K β (-1)
  let P := integralPoints Z H
  choose x hx using fun α : S ↦ α.property.2
  choose m hm using fun α : S ↦ α.property.1.2.2
  have hpoint (α : S) : ![(m α : ℤ), x α] ∈ P := by
    apply mem_integralPoints.mpr
    constructor
    · intro i
      fin_cases i
      · have hsq : (m α : ℝ) ^ 2 ≤ B ^ Module.finrank ℚ K := by
          rw [← Nat.cast_pow, ← hm α]
          exact bounded_infinite_places_norm_le K α α.property.1.2.1
        have hh := Real.le_sqrt_of_sq_le hsq
        change |((m α : ℤ) : ℝ)| ≤ H
        simp only [Int.cast_natCast]
        rw [abs_of_nonneg (show 0 ≤ (m α : ℝ) by positivity)]
        exact hh.trans (le_max_right (2 * B) _)
      · exact (integer_translate_coordinate_le K α β α.property.1.2.1 hβ (hx α)).trans
          (le_max_left _ _)
    · have hnorm : (Algebra.norm ℤ
          (algebraMap ℤ (𝓞 K) (x α) - β)).natAbs = m α ^ 2 := by
        grind
      rcases square_norm_yields_signedNormCurve_point K β (x α) (m α) hnorm with h | h
      · left
        have hc := congrArg (Int.castRingHom ℚ) h
        rw [MvPolynomial.map_eval, map_zero] at hc
        exact hc
      · right
        have hc := congrArg (Int.castRingHom ℚ) h
        rw [MvPolynomial.map_eval, map_zero] at hc
        exact hc
  let ι : S → P := fun α ↦ ⟨![(m α : ℤ), x α], hpoint α⟩
  have hi : Function.Injective ι := by
    intro α γ he
    have h := congrArg (fun p : P ↦ p.val 1) he
    change x α = x γ at h
    apply Subtype.ext
    rw [hx α, hx γ, h]
  have hcard := by
    have h := Nat.card_le_card_of_injective ι hi
    simpa only [Nat.card_coe_set_eq, Nat.card_eq_fintype_card,
      Fintype.card_coe, count, P] using h
  exact hcard.trans (count_union_le _ _ _)

end
end CCDN
