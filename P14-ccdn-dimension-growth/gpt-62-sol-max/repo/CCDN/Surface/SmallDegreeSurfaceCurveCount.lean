/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Statements
public import CCDN.Analysis.SmallDegreeSurfaceNumerics

/-! Nonlinear initial curves whose degrees are at most logarithmic in the
box radius. The full affine curve theorem and the strict surface exponent
gap give a linear bound in every surface degree at least five. -/

@[expose] public section
namespace CCDN
noncomputable section

private theorem curveBound_logarithmic_degree {δ : ℕ} (hδ : 2 ≤ δ)
    {B D : ℝ} (hB : 1 ≤ B)
    (hδD : (δ : ℝ) ≤ D * (Real.log B + 1)) :
    curveBound δ B ≤ (δ : ℝ) * D ^ 2 * (D + 1) *
      B ^ (1 / 2 : ℝ) * (Real.log B + 1) ^ 3 := by
  have hlog := Real.log_nonneg hB
  have hδR : (2 : ℝ) ≤ δ := by exact_mod_cast hδ
  have hpow : B ^ (1 / (δ : ℝ)) ≤ B ^ (1 / 2 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hB (one_div_le_one_div_of_le (by norm_num) hδR)
  have hlogδ : Real.log B + δ ≤ (D + 1) * (Real.log B + 1) := by linarith
  calc
    curveBound δ B = (δ : ℝ) * (δ : ℝ) ^ 2 * B ^ (1 / (δ : ℝ)) * (Real.log B + δ) := by
      unfold curveBound
      ring
    _ ≤ (δ : ℝ) * (D * (Real.log B + 1)) ^ 2 * B ^ (1 / 2 : ℝ) *
        ((D + 1) * (Real.log B + 1)) := by gcongr
    _ = _ := by ring

/-- Sum the affine curve bound over components with logarithmically bounded degree. -/
theorem sum_curveBound_logarithmic_degrees {ι : Type*}
    (S : Finset ι) (δ : ι → ℕ) {d : ℕ} (hd : 5 ≤ d)
    {A D B : ℝ} (hA : 0 ≤ A) (hD : 0 ≤ D) (hB : 1 ≤ B)
    (hδ : ∀ i ∈ S, 2 ≤ δ i)
    (hcap : ∀ i ∈ S, (δ i : ℝ) ≤ D * (Real.log B + 1))
    (hbudget : (∑ i ∈ S, (δ i : ℝ)) ≤
      A * B ^ (1 / Real.sqrt (d : ℝ)) * (Real.log B + 1)) :
    ∑ i ∈ S, curveBound (δ i) B ≤
      logarithmicBoxConstant 4 (1 / 20) * A * D ^ 2 * (D + 1) * B := by
  have hB0 : 0 < B := zero_lt_one.trans_le hB
  have hlog := Real.log_nonneg hB
  let T := D ^ 2 * (D + 1) * B ^ (1 / 2 : ℝ) * (Real.log B + 1) ^ 3
  calc
    _ ≤ ∑ i ∈ S, (δ i : ℝ) * T := Finset.sum_le_sum (fun i hi => by
      refine (curveBound_logarithmic_degree (hδ i hi) hB (hcap i hi)).trans_eq ?_
      dsimp [T]
      ring)
    _ ≤ (A * B ^ (1 / Real.sqrt (d : ℝ)) * (Real.log B + 1)) * T := by
      rw [← Finset.sum_mul]
      gcongr
    _ = (A * D ^ 2 * (D + 1)) *
        (B ^ (1 / Real.sqrt (d : ℝ) + 1 / 2) * (Real.log B + 1) ^ 4) := by
      dsimp [T]
      rw [Real.rpow_add hB0]
      ring
    _ ≤ (A * D ^ 2 * (D + 1)) * (logarithmicBoxConstant 4 (1 / 20) * B) := by
      exact mul_le_mul_of_nonneg_left
        (box_polylog_weight 4 (by norm_num : (0 : ℝ) < 1 / 20) hB
          (by linarith [surface_inverse_sqrt_le_nine_twentieths hd])) (by positivity)
    _ = _ := by ring

end
end CCDN
