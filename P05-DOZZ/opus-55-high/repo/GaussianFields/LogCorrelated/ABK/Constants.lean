/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import Mathlib.MeasureTheory.Integral.Gamma
public import GaussianFields.LogCorrelated.ABK

/-!
# GaussianFields.LogCorrelated/ABK/Constants

Port of the corresponding GaussianFields source module.
-/

public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal InnerProductSpace NNReal ProbabilityTheory Topology

namespace GaussianFields

/-- ABK-local positivity helper for the project Euclidean norm. -/
theorem abkEuclideanNorm_pos_of_ne_zero {d : Nat} {x : Vec d} (hx : x ≠ 0) :
    0 < euclideanNorm x := by
  refine lt_of_le_of_ne (euclideanNorm_nonneg x) ?_
  intro hzero
  apply hx
  ext i
  have hcoord_abs : |x i| ≤ 0 := by
    simpa [hzero] using abs_apply_le_euclideanNorm x i
  exact abs_eq_zero.mp (le_antisymm hcoord_abs (abs_nonneg (x i)))

/-- A canonical radial representative: first coordinate `s`, all other coordinates zero. -/
@[expose]
def abkRadialPoint (d : Nat) (s : ℝ) : Vec d :=
  fun i => if (i : Nat) = 0 then s else 0

/-- The Euclidean open ball of radius `r` centered at the origin. -/
@[expose]
def abkBall (d : Nat) (r : ℝ) : Set (Vec d) :=
  {x | euclideanNorm x < r}

/-- The Euclidean unit ball used in the ABK constants. -/
@[expose]
def abkUnitBall (d : Nat) : Set (Vec d) :=
  abkBall d 1

/-- The Lebesgue volume `|B_1|` of the project Euclidean unit ball. -/
@[expose]
noncomputable def abkUnitBallVolume (d : Nat) : ℝ :=
  ((volume : Measure (Vec d)) (abkUnitBall d)).toReal

/-- The unscaled self-convolution `(ζ * ζ)(x)`. -/
@[expose]
noncomputable def abkCutoffSelfConvolution {d : Nat} (ζ : ABKCutoff d)
    (x : Vec d) : ℝ :=
  ∫ y : Vec d, ζ y * ζ (x - y)

/-- The ABK constant `M_0 = ∫ |ζ|^2`.  Since `ζ` is nonnegative, this is `∫ ζ^2`. -/
@[expose]
noncomputable def abkM0 {d : Nat} (ζ : ABKCutoff d) : ℝ :=
  ∫ x : Vec d, (ζ x) ^ (2 : Nat)

/-- The reciprocal constant `M_α^{-1}` in the ABK power decomposition. -/
@[expose]
noncomputable def abkMAlphaInv {d : Nat} (ζ : ABKCutoff d) (α : ℝ) : ℝ :=
  ∫ r in Set.Ioi (0 : ℝ),
    r ^ (-(1 + α)) * abkCutoffSelfConvolution ζ (abkRadialPoint d r⁻¹)


/-- The radicand in the canonical ABK normalization. -/
@[expose]
noncomputable def abkNormalizationRadicand {d : Nat} (ζ : ABKCutoff d) : ℝ :=
  (d : ℝ) * abkUnitBallVolume d / (abkM0 ζ * (2 * Real.pi) ^ d)

/-- The canonical ABK normalization
`(d |B_1| / (M_0 (2π)^d))^{1/2}`. -/
@[expose]
noncomputable def abkNormalization {d : Nat} (ζ : ABKCutoff d) : ℝ :=
  Real.sqrt (abkNormalizationRadicand ζ)

/-- The covariance prefactor `d |B_1| / (2π)^d`. -/
@[expose]
noncomputable def abkLGFCovarianceConstant (d : Nat) : ℝ :=
  (d : ℝ) * abkUnitBallVolume d / (2 * Real.pi) ^ d
section
variable {d : Nat} (ζ : ABKCutoff d)




/-- The canonical normalization squared is its radicand whenever the radicand is nonnegative. -/
theorem abkNormalization_sq (h : 0 ≤ abkNormalizationRadicand ζ) :
    abkNormalization ζ ^ (2 : Nat) = abkNormalizationRadicand ζ := by
  simpa [abkNormalization, pow_two] using Real.sq_sqrt h

/-- At the origin, the cutoff self-convolution is `M_0`. -/
theorem abkCutoffSelfConvolution_zero :
    abkCutoffSelfConvolution ζ 0 = abkM0 ζ := by
  refine integral_congr_ae ?_
  filter_upwards with y
  have hneg := ζ.radial _ _ (euclideanNorm_neg y)
  simp
  grind

/-- The cutoff square mass `M_0` is strictly positive. -/
theorem abkM0_pos : 0 < abkM0 ζ := by
  unfold abkM0
  let f : Vec d → ℝ := fun x => (ζ x) ^ 2
  have hf_int : Integrable f (volume : Measure (Vec d)) := by
    simpa [f] using ζ.memLp_two.integrable_sq
  have hf_nonneg : 0 ≤ f := by
    intro x
    positivity
  have hzero_norm : euclideanNorm (0 : Vec d) ≤ (1 / 2) := by
    simp [euclideanNorm, euclideanNormSq, euclideanDot]
  have hf_zero : f 0 ≠ 0 := by
    dsimp [f]
    rw [ζ.eq_one_of_norm_le_half 0 hzero_norm]
    norm_num
  exact integral_pos_of_integrable_nonneg_nonzero (ζ.continuous.pow 2) hf_int hf_nonneg hf_zero

/-- The cutoff square mass `M_0` is nonzero. -/
theorem abkM0_ne_zero : abkM0 ζ ≠ 0 :=
  (abkM0_pos ζ).ne'

/-- Multiplying the canonical normalization radicand by `M_0` leaves the ABK covariance
prefactor. -/
theorem abkNormalizationRadicand_mul_abkM0 :
    abkNormalizationRadicand ζ * abkM0 ζ = abkLGFCovarianceConstant d := by
  have hM0 := abkM0_ne_zero ζ
  have htwopi : (2 * Real.pi) ^ d ≠ 0 :=
    by simp
  unfold abkNormalizationRadicand abkLGFCovarianceConstant
  field_simp

end

end GaussianFields

end
