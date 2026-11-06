/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

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
  {β | β ≠ 0 ∧ (∀ w : InfinitePlace K, w (β : K) ≤ B) ∧
    ∃ m : ℕ, (Algebra.norm ℤ β).natAbs = m ^ 2}

/-- There are finitely many bounded square-norm integers `boundedSquareNormIntegers K B`. -/
lemma boundedSquareNormIntegers_finite (B : ℝ) :
    (boundedSquareNormIntegers K B).Finite := by
  apply Set.Finite.of_injOn (f := fun β : 𝓞 K ↦ (β : K))
    (t := {x : K | IsIntegral ℤ x ∧ ∀ φ : K →+* ℂ, ‖φ x‖ ≤ B})
  · intro β hβ
    exact ⟨β.isIntegral_coe, fun φ ↦ hβ.2.1 (InfinitePlace.mk φ)⟩
  · exact RingOfIntegers.coe_injective.injOn
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
  obtain ⟨h0, hw, J, _, _, hnorm⟩ := hβ c
  exact ⟨h0, fun w ↦ (hw w).le, Ideal.absNorm (J : Ideal (𝓞 K)), hnorm⟩

/-- The bounded square-norm integers of the form `x - β` with `x ∈ ℤ`, that is, those in the
integer-translation class of `-β`. -/
def squareNormTranslateFiber (β : 𝓞 K) (B : ℝ) : Set (𝓞 K) :=
  {α | α ∈ boundedSquareNormIntegers K B ∧
    ∃ x : ℤ, α = algebraMap ℤ (𝓞 K) x - β}

/-- Each square-norm translate fiber `squareNormTranslateFiber K β B` is finite. -/
lemma squareNormTranslateFiber_finite (β : 𝓞 K) (B : ℝ) :
    (squareNormTranslateFiber K β B).Finite :=
  (boundedSquareNormIntegers_finite K B).subset fun _ h => h.1

/-- The rational plane curve `y ^ 2 = ε * N(x - β)` cut out by the signed norm-curve polynomial of
`β` with sign `ε`. -/
def signedNormCurveLocus (β : 𝓞 K) (ε : ℤ) : Set (RatPoint 2) :=
  zeroLocus (MvPolynomial.map (Int.castRingHom ℚ) (signedNormCurvePolynomial K β ε))

/-- If `β` is bounded by `B` at every infinite place, then the square-norm translate fiber of `β`
has at most as many elements as there are integral points of height at most
`max (2 * B) (√(B ^ n))` on the two signed norm curves `y ^ 2 = ±N(x - β)`, where `n = [K : ℚ]`. -/
theorem squareNormTranslateFiber_count_le (β : 𝓞 K) {B : ℝ}
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
  choose x hx using fun α : S => α.property.2
  choose m hm using fun α : S => α.property.1.2.2
  have hpoint (α : S) : ![(m α : ℤ), x α] ∈ P := by
    refine mem_integralPoints.mpr ⟨fun i => ?_, ?_⟩
    · fin_cases i
      · have hsq : (m α : ℝ) ^ 2 ≤ B ^ Module.finrank ℚ K := by
          rw [← Nat.cast_pow, ← hm α, show ((Algebra.norm ℤ (α : 𝓞 K)).natAbs : ℝ) =
              ∏ w : InfinitePlace K, w ((α : 𝓞 K) : K) ^ mult w by
            rw [prod_eq_abs_norm, ← Algebra.coe_norm_int]; exact mod_cast Nat.cast_natAbs _,
            ← sum_mult_eq (K := K), ← Finset.prod_pow_eq_pow_sum]
          exact Finset.prod_le_prod₀ (fun _ _ => by positivity)
            fun w _ => pow_le_pow_left₀ (apply_nonneg _ _) (α.property.1.2.1 w) _
        change |((m α : ℤ) : ℝ)| ≤ H
        simp only [Int.cast_natCast, abs_of_nonneg (Nat.cast_nonneg (α := ℝ) (m α))]
        exact (Real.le_sqrt_of_sq_le hsq).trans (le_max_right (2 * B) _)
      · let w : InfinitePlace K := Classical.arbitrary _
        have hxK : (x α : K) = ((α : 𝓞 K) : K) + (β : K) := by
          have h := congrArg (fun z : 𝓞 K => (z : K)) (hx α)
          simp only [map_sub, RingOfIntegers.coe_eq_algebraMap, ← IsScalarTower.algebraMap_apply] at h
          exact (eq_sub_iff_add_eq.mp h).symm
        change |(x α : ℝ)| ≤ H
        have hw_le : |(x α : ℝ)| ≤ 2 * B := by
          rw [← Int.norm_eq_abs, ← w.map_intCast, hxK]
          exact ((w.val.add_le ((α : 𝓞 K) : K) (β : K)).trans
            (add_le_add (α.property.1.2.1 w) (hβ w))).trans_eq (by ring)
        exact hw_le.trans (le_max_left _ _)
    · have hnorm : (Algebra.norm ℤ (algebraMap ℤ (𝓞 K) (x α) - β)).natAbs = m α ^ 2 := by
        rw [← hx α]; exact hm α
      rcases square_norm_yields_signedNormCurve_point K β (x α) (m α) hnorm with h | h <;>
      [left; right] <;> {
        have hc := congrArg (Int.castRingHom ℚ) h
        rw [MvPolynomial.map_eval, map_zero] at hc
        exact hc }
  let ι : S → P := fun α => ⟨![(m α : ℤ), x α], hpoint α⟩
  have hi : Function.Injective ι := fun α γ he =>
    Subtype.ext (by rw [hx α, hx γ, show x α = x γ from congrArg (fun p : P => p.val 1) he])
  have hcard : S.ncard ≤ count Z H := by
    simpa only [Nat.card_coe_set_eq, Nat.card_eq_fintype_card, Fintype.card_coe, count, P] using
      Nat.card_le_card_of_injective ι hi
  exact hcard.trans (count_union_le _ _ _)

end
end CCDN
