/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Statements
import CCDN.Analysis.SmallDegreeSurfaceNumerics
import CCDN.Curve.AffineCurveCount
import CCDN.Surface.NonlinearCount

/-! Nonlinear initial curves whose degrees are at most logarithmic in the
box radius. The full affine curve theorem and the strict surface exponent
gap give a linear bound in every surface degree at least five. -/

@[expose] public section
namespace CCDN
noncomputable section

/-- For each `k`, there is a constant `C` such that, for `d ≥ 5` and a finite family of
integral affine curves of degree at least two, each of degree at most `D (log B + 1)` and of
total degree at most `A B^(1/√d) (log B + 1)^k`, the union of the curves has at most
`C A D² (D + 1) B` integral points of height at most `B`. -/
theorem logarithmic_degree_curve_union_bound (k : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (S : Finset (Ideal (CoordinatePolynomial 3)))
        (δ : Ideal (CoordinatePolynomial 3) → ℕ) (d : ℕ), 5 ≤ d →
      ∀ A D B : ℝ, 0 ≤ A → 0 ≤ D → 1 ≤ B →
      (∀ P ∈ S, P.IsPrime ∧ 2 ≤ δ P ∧ HasAffineCurveDegree P (δ P)) →
      (∀ P ∈ S, (δ P : ℝ) ≤ D * (Real.log B + 1)) →
      (∑ P ∈ S, (δ P : ℝ)) ≤
        A * B ^ (1 / Real.sqrt (d : ℝ)) * (Real.log B + 1) ^ k →
      (count (⋃ P ∈ S, idealZeroLocus P) B : ℝ) ≤ C * A * D ^ 2 * (D + 1) * B := by
  obtain ⟨K, hK, hcount⟩ := affine_curve_count 3 (by omega)
  let C₀ := ((k + 3).factorial / (1 / 20 : ℝ) ^ (k + 3) * Real.exp (1 / 20))
  have hC₀ : 0 < C₀ := by dsimp only [C₀]; positivity
  refine ⟨K * C₀, mul_pos hK hC₀, fun S δ d hd A D B hA hD hB hcurve hcap hbudget => ?_⟩
  have hB0 : 0 < B := zero_lt_one.trans_le hB
  have hlog := Real.log_nonneg hB
  have hsingle (P) (hP : P ∈ S) :
      curveBound (δ P) B ≤ (δ P : ℝ) * D ^ 2 * (D + 1) * B ^ (1 / 2 : ℝ) * (Real.log B + 1) ^ 3 := by
    have hδR : (2 : ℝ) ≤ δ P := mod_cast (hcurve P hP).2.1
    have hpow : B ^ (1 / (δ P : ℝ)) ≤ B ^ (1 / 2 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hB (one_div_le_one_div_of_le (by norm_num) hδR)
    have hsq := pow_le_pow_left₀ (by positivity) (hcap P hP) 2
    have hlogδ : Real.log B + δ P ≤ (D + 1) * (Real.log B + 1) := by linarith [hcap P hP]
    have hcube : (δ P : ℝ) ^ 3 ≤ (δ P : ℝ) * (D * (Real.log B + 1)) ^ 2 := by
      nlinarith [mul_le_mul_of_nonneg_left hsq (Nat.cast_nonneg (α := ℝ) (δ P))]
    unfold curveBound
    exact (mul_le_mul (mul_le_mul hcube hpow (by positivity) (by positivity)) hlogδ
      (by positivity) (by positivity)).trans_eq (by ring)
  have hsum : ∑ P ∈ S, curveBound (δ P) B ≤ C₀ * A * D ^ 2 * (D + 1) * B := by
    calc
      _ ≤ (∑ P ∈ S, (δ P : ℝ)) * D ^ 2 * (D + 1) * B ^ (1 / 2 : ℝ) * (Real.log B + 1) ^ 3 :=
        (Finset.sum_le_sum hsingle).trans_eq (by simp only [Finset.sum_mul])
      _ ≤ (A * B ^ (1 / Real.sqrt (d : ℝ)) * (Real.log B + 1) ^ k) *
          D ^ 2 * (D + 1) * B ^ (1 / 2 : ℝ) * (Real.log B + 1) ^ 3 := by gcongr
      _ = (A * D ^ 2 * (D + 1)) *
          (B ^ (1 / Real.sqrt (d : ℝ) + 1 / 2) * (Real.log B + 1) ^ (k + 3)) := by
        rw [Real.rpow_add hB0, pow_add]; ring
      _ ≤ _ := (mul_le_mul_of_nonneg_left (surface_nonlinear_polylog_weight hd (k + 3) hB)
        (by positivity)).trans_eq (by dsimp only [C₀]; ring)
  have hunion : (count (⋃ P ∈ S, idealZeroLocus P) B : ℝ) ≤ ∑ P ∈ S, (count (idealZeroLocus P) B : ℝ) :=
    mod_cast count_biUnion_finset_le S idealZeroLocus B
  refine hunion.trans (((Finset.sum_le_sum fun P hP => ?_).trans_eq
    (Finset.mul_sum _ _ _).symm).trans
    ((mul_le_mul_of_nonneg_left hsum hK.le).trans_eq (by ring)))
  obtain ⟨hp, hδ, hdeg⟩ := hcurve P hP
  exact hcount P hp (δ P) (by omega) hdeg B hB

end
end CCDN
