/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import GaussianFields.LogCorrelated.ABK.ScaleSpace

/-!
# GaussianFields ABK test functions and convolution

Port of the corresponding GaussianFields source module.
-/

public section

open MeasureTheory ProbabilityTheory
open scoped Convolution ENNReal InnerProductSpace NNReal ProbabilityTheory Topology

namespace GaussianFields

/-! ## ABK kernels -/

/-- The scaled cutoff `ζ_r(x) = ζ(x / r)`, written using scalar multiplication. -/
@[expose]
noncomputable def abkScaledCutoff {d : Nat} (ζ : ABKCutoff d) (r : ℝ)
    (x : Vec d) : ℝ :=
  ζ (r⁻¹ • x)
section
variable {d : Nat}
section
variable (ζ : ABKCutoff d)

/-- The scaled ABK cutoff is continuous. -/
theorem continuous_abkScaledCutoff (r : ℝ) :
    Continuous (abkScaledCutoff ζ r) := by
  exact ζ.continuous.comp (continuous_const_smul (r⁻¹))

/-- At nonzero scale, the scaled ABK cutoff has compact support. -/
theorem hasCompactSupport_abkScaledCutoff {r : ℝ}
    (hr : r ≠ 0) :
    HasCompactSupport (abkScaledCutoff ζ r) := by
  exact ζ.hasCompactSupport.comp_smul (inv_ne_zero hr)

end
section
variable (ψ : MeanZeroTestFunction d)

/-- Compact support of `ψ` gives integrability of the first radial moment `|x| |ψ x|`. -/
theorem integrable_euclideanNorm_mul_abs_meanZeroTestFunction :
    Integrable (fun x : Vec d => euclideanNorm x * |ψ x|)
      (volume : Measure (Vec d)) := by
  have hcont : Continuous (fun x => euclideanNorm x * |ψ x|) :=
    (continuous_euclideanNorm).mul ψ.continuous.abs
  have hcomp : HasCompactSupport (fun x => euclideanNorm x * |ψ x|) :=
    ψ.hasCompactSupport.abs.mul_left
  exact hcont.integrable_of_hasCompactSupport hcomp

/-- A compactly supported mean-zero test function is supported in some local Euclidean ball. -/
theorem exists_support_subset_euclideanClosedBall_meanZeroTestFunction :
    ∃ R, 0 ≤ R ∧ Function.support ψ ⊆ {x : Vec d | euclideanNorm x ≤ R} := by
  rcases ψ.hasCompactSupport.exists_pos_le_norm with ⟨R, hR_pos, hvanish⟩
  refine ⟨(d : ℝ) * R, mul_nonneg (Nat.cast_nonneg d) hR_pos.le, ?_⟩
  intro x hx
  have hnorm_le : ‖x‖ ≤ R := by
    by_contra hnot
    bound
  calc
    euclideanNorm x ≤ d * ‖x‖ := euclideanNorm_le_card_mul_norm x
    _ ≤ d * R := mul_le_mul_of_nonneg_left hnorm_le (Nat.cast_nonneg d)

/-- Compactly supported continuous test functions are uniformly bounded. -/
theorem exists_abs_meanZeroTestFunction_le :
    ∃ M, 0 ≤ M ∧ ∀ x : Vec d, |ψ x| ≤ M := by
  rcases ψ.continuous.bounded_above_of_compact_support ψ.hasCompactSupport with ⟨C, hC⟩
  refine ⟨max C 0, le_max_right C 0, ?_⟩
  simp_all

end
section
variable (ζ : ABKCutoff d)

/-- Scaling the ABK cutoff divides its Lipschitz constant by `|r|`. -/
theorem abkScaledCutoff_lipschitz_bound :
    ∃ L, 0 ≤ L ∧
      ∀ r x y,
        |abkScaledCutoff ζ r x - abkScaledCutoff ζ r y| ≤
          L * |r|⁻¹ * euclideanNorm (x - y) := by
  rcases ζ.lipschitz with ⟨L, hL_nonneg, hL⟩
  refine ⟨L, hL_nonneg, ?_⟩
  intro r x y
  have hsub : r⁻¹ • x - r⁻¹ • y = r⁻¹ • (x - y) := by
    ext i
    simp
    ring
  calc
    |abkScaledCutoff ζ r x - abkScaledCutoff ζ r y|
        = |ζ _ - ζ _| := rfl
    _ ≤ L * euclideanNorm _ := hL ..
    _ = L * |r|⁻¹ * euclideanNorm _ := by
      rw [hsub, euclideanNorm_smul, abs_inv]
      ring

/-- If the scaled cutoff is nonzero at positive scale `r`, then the original point lies in the
Euclidean ball of radius `r`. -/
theorem euclideanNorm_le_of_abkScaledCutoff_ne_zero {r : ℝ} (hr : 0 < r) {x : Vec d} (hx : abkScaledCutoff ζ r x ≠ 0) :
    euclideanNorm x ≤ r := by
  have hunit := ζ.support_subset_unitBall hx
  have hscaled : euclideanNorm (r⁻¹ • x) = r⁻¹ * euclideanNorm x := by
    rw [euclideanNorm_smul, abs_of_pos (inv_pos.mpr hr)]
  have hunit' : r⁻¹ * euclideanNorm x ≤ 1 := by
    simp_all
  calc
    euclideanNorm x = r * (r⁻¹ * euclideanNorm x) := by
      field_simp
    _ ≤ r * 1 := mul_le_mul_of_nonneg_left hunit' hr.le
    _ = r := by ring

end

end

/-- The ABK spatial convolution `(ζ_r * ψ)(y)`. -/
@[expose]
noncomputable def abkSpatialConvolution {d : Nat} (ζ : ABKCutoff d)
    (ψ : MeanZeroTestFunction d) (r : ℝ) (y : Vec d) : ℝ :=
  ∫ x : Vec d, abkScaledCutoff ζ r (y - x) * ψ x
section
variable {d : Nat}
section
variable (ζ : ABKCutoff d) (ψ : MeanZeroTestFunction d)

/-- The ABK convolution integrand is jointly strongly measurable in scale, space, and the
integration variable. -/
theorem stronglyMeasurable_abkSpatialConvolution_integrand_prod :
    StronglyMeasurable
      (fun q : (ℝ × Vec d) × Vec d =>
        abkScaledCutoff ζ q.1.1 (q.1.2 - q.2) * ψ q.2) := by
  exact (ζ.continuous.measurable.comp (by fun_prop)).stronglyMeasurable.mul
    (ψ.continuous.measurable.comp (by fun_prop)).stronglyMeasurable

/-- The ABK spatial convolution is jointly strongly measurable in scale and space. -/
theorem stronglyMeasurable_abkSpatialConvolution_prod :
    StronglyMeasurable
      (fun p : ℝ × Vec d => abkSpatialConvolution ζ ψ p.1 p.2) := by
  simpa [abkSpatialConvolution] using
    (stronglyMeasurable_abkSpatialConvolution_integrand_prod ζ ψ).integral_prod_right'

/-- The hand-written ABK spatial convolution is Mathlib convolution with the same kernel. -/
theorem abkSpatialConvolution_eq_convolution (r : ℝ) (y : Vec d) :
    abkSpatialConvolution ζ ψ r y =
      ((ψ : Vec d → ℝ) ⋆[ContinuousLinearMap.mul ℝ ℝ, (volume : Measure (Vec d))]
        abkScaledCutoff ζ r) y := by
  rw [abkSpatialConvolution, convolution_def]
  refine integral_congr_ae ?_
  filter_upwards with x
  simp [ContinuousLinearMap.mul_apply', mul_comm]

/-- At nonzero scale, the ABK spatial convolution is continuous in the spatial variable. -/
theorem continuous_abkSpatialConvolution {r : ℝ} (hr : r ≠ 0) :
    Continuous (fun y : Vec d => abkSpatialConvolution ζ ψ r y) := by
  have hconv :=
    (hasCompactSupport_abkScaledCutoff ζ hr).continuous_convolution_right
      (ContinuousLinearMap.mul ℝ ℝ) ψ.integrable.locallyIntegrable
      (continuous_abkScaledCutoff ζ r)
  refine hconv.congr ?_
  intro y
  exact (abkSpatialConvolution_eq_convolution ζ ψ r y).symm
section
variable (r : ℝ) (y : Vec d)

/-- The integrand defining `(ζ_r * ψ)(y)` is integrable. -/
theorem integrable_abkSpatialConvolution_integrand :
    Integrable (fun x : Vec d => abkScaledCutoff ζ r (y - x) * ψ x)
      (volume : Measure (Vec d)) := by
  refine Integrable.mono' ψ.integrable.norm ?_ ?_
  · have hcont :
        Continuous (fun x => abkScaledCutoff ζ r (y - x) * ψ x) := by
      have hinner : Continuous fun x => r⁻¹ • (y - x) := by
        fun_prop
      exact (ζ.continuous.comp hinner).mul ψ.continuous
    exact hcont.aestronglyMeasurable
  · filter_upwards with x
    have hz_nonneg : 0 ≤ ζ (r⁻¹ • (y - x)) := ζ.nonneg _
    have hz_le_one : ζ (r⁻¹ • (y - x)) ≤ 1 := ζ.le_one _
    calc
      ‖abkScaledCutoff ζ r _ * ψ x‖
          = |ζ _ * ψ x| := by
            rfl
      _ = |ζ _| * |ψ x| := abs_mul ..
      _ = ζ _ * |ψ x| := by
            simp_all
      _ ≤ 1 * |ψ x| := mul_le_mul_of_nonneg_right hz_le_one (abs_nonneg (ψ x))
      _ = |ψ x| := by ring
      _ = ‖ψ x‖ := by rfl

/-- Mean-zero cancellation form of the ABK convolution.  This is the identity used for the
large-scale estimate. -/
theorem abkSpatialConvolution_eq_integral_sub_scaledCutoff :
    abkSpatialConvolution ζ ψ r y =
      ∫ x : Vec d,
        (abkScaledCutoff ζ r (y - x) - abkScaledCutoff ζ r y) * ψ x := by
  let A : Vec d → ℝ := fun x => abkScaledCutoff ζ r (y - x) * ψ x
  let B : Vec d → ℝ := fun x => abkScaledCutoff ζ r y * ψ x
  have hA :=
    integrable_abkSpatialConvolution_integrand ζ ψ r y
  have hB :=
    ψ.integrable.const_mul (abkScaledCutoff ζ r y)
  have hrewrite :
      (fun x =>
        (abkScaledCutoff ζ r (y - x) - abkScaledCutoff ζ r y) * ψ x) =
        fun x => A x - B x := by
    grind
  calc
    abkSpatialConvolution ζ ψ r y = ∫ x : Vec d, A x := rfl
    _ = ∫ x : Vec d, A x - B x := by
          rw [integral_sub hA hB, integral_const_mul, ψ.integral_eq_zero, mul_zero, sub_zero]
    _ = ∫ x : Vec d,
        (abkScaledCutoff ζ r _ - abkScaledCutoff ζ r y) * ψ x := by
          simp_all

/-- The cancellation-form integrand is integrable. -/
theorem integrable_abkSpatialConvolution_cancellation_integrand :
    Integrable
      (fun x : Vec d =>
        (abkScaledCutoff ζ r (y - x) - abkScaledCutoff ζ r y) * ψ x)
      (volume : Measure (Vec d)) := by
  let A : Vec d → ℝ := fun x => abkScaledCutoff ζ r (y - x) * ψ x
  let B : Vec d → ℝ := fun x => abkScaledCutoff ζ r y * ψ x
  have hA :=
    integrable_abkSpatialConvolution_integrand ζ ψ r y
  have hB :=
    ψ.integrable.const_mul (abkScaledCutoff ζ r y)
  have hrewrite :
      (fun x =>
        (abkScaledCutoff ζ r (y - x) - abkScaledCutoff ζ r y) * ψ x) =
        fun x => A x - B x := by
    grind
  rw [hrewrite]
  fun_prop

end

/-- Mean-zero cancellation and Lipschitz regularity give a uniform large-scale pointwise bound. -/
theorem abs_abkSpatialConvolution_le_scaled_moment :
    ∃ L, 0 ≤ L ∧ ∀ r y,
      |abkSpatialConvolution ζ ψ r y| ≤
        L * |r|⁻¹ *
          ∫ x : Vec d, euclideanNorm x * |ψ x| := by
  rcases abkScaledCutoff_lipschitz_bound ζ with ⟨L, hL_nonneg, hL⟩
  refine ⟨L, hL_nonneg, ?_⟩
  intro r y
  let F : Vec d → ℝ :=
    fun x => (abkScaledCutoff ζ r (y - x) - abkScaledCutoff ζ r y) * ψ x
  have hF_int :=
    integrable_abkSpatialConvolution_cancellation_integrand ζ ψ r y
  have hmoment_int :=
    integrable_euclideanNorm_mul_abs_meanZeroTestFunction ψ
  have hconst_nonneg :=
    mul_nonneg hL_nonneg (inv_nonneg.mpr (abs_nonneg r))
  have hpoint :
      ∀ x : Vec d,
        ‖F x‖ ≤ L * |r|⁻¹ * (euclideanNorm x * |ψ x|) := by
    intro x
    have hdiff : (y - x) - y = -x := by
      simp
    have hnorm : euclideanNorm ((y - x) - y) = euclideanNorm x := by
      rw [hdiff, euclideanNorm_neg]
    calc
      ‖F x‖
          = |(abkScaledCutoff ζ r _ - abkScaledCutoff ζ r y) * ψ x| := by
            rfl
      _ = |abkScaledCutoff ζ r (y - x) - abkScaledCutoff ζ r y| * |ψ x| := by
            simp
      _ ≤ (L * |r|⁻¹ * euclideanNorm _) * |ψ x| := by bound
      _ = L * |r|⁻¹ * (euclideanNorm x * |ψ x|) := by
            grind
  have hintegral_bound :
      ∫ x : Vec d, ‖F x‖ ∂volume ≤
        ∫ x : Vec d, L * |r|⁻¹ * (euclideanNorm x * |ψ x|)
          ∂volume := integral_mono hF_int.norm (hmoment_int.const_mul (L * |r|⁻¹)) hpoint
  calc
    |abkSpatialConvolution ζ ψ r y|
        = ‖abkSpatialConvolution ζ ψ r y‖ := by rfl
    _ = ‖∫ x : Vec d, F x ∂volume‖ := by
          rw [abkSpatialConvolution_eq_integral_sub_scaledCutoff ζ ψ r y]
    _ ≤ ∫ x : Vec d, ‖F x‖ ∂volume :=
          norm_integral_le_integral_norm F
    _ ≤ ∫ x : Vec d, L * |r|⁻¹ * (euclideanNorm x * |ψ x|)
          ∂volume := hintegral_bound
    _ = L * |r|⁻¹ *
          ∫ x : Vec d, euclideanNorm x * |ψ x| := by
          rw [integral_const_mul]
section
variable {R r : ℝ}
section
variable (hψ_support : Function.support ψ ⊆ {x : Vec d | euclideanNorm x ≤ R}) (hr : 0 < r)
include hψ_support hr

/-- If `ψ` is supported in a Euclidean ball of radius `R`, then at positive scale the ABK
convolution vanishes outside a controlled ball.  The harmless factor `d` comes from comparing the
local Euclidean norm with Mathlib's product sup norm. -/
theorem abkSpatialConvolution_eq_zero_of_euclideanNorm_gt {y : Vec d}
    (hy : (d : ℝ) * (R + r) < euclideanNorm y) :
    abkSpatialConvolution ζ ψ r y = 0 := by
  refine integral_eq_zero_of_ae ?_
  filter_upwards with x
  by_cases hψx : ψ x = 0
  · simp_all
  · have hcut_zero : abkScaledCutoff ζ r (y - x) = 0 := by
      by_contra hcut
      have hcut_norm :=
        euclideanNorm_le_of_abkScaledCutoff_ne_zero ζ hr hcut
      have hy_decomp : x + (y - x) = y := by
        simp
      have hy_le : euclideanNorm y ≤ d * (R + r) := by
        calc
          euclideanNorm y = euclideanNorm _ := by simp
          _ ≤ d * ‖x + (y - x)‖ :=
                euclideanNorm_le_card_mul_norm _
          _ ≤ d * (‖x‖ + ‖y - x‖) := mul_le_mul_of_nonneg_left (norm_add_le x (y - x))
                  (Nat.cast_nonneg d)
          _ ≤ d * (R + r) := by
                refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg d)
                exact add_le_add ((norm_le_euclideanNorm x).trans (hψ_support hψx))
                  ((norm_le_euclideanNorm _).trans hcut_norm)
      exact (not_lt_of_ge hy_le) hy
    simp_all

/-- Support form of `abkSpatialConvolution_eq_zero_of_euclideanNorm_gt`. -/
theorem support_abkSpatialConvolution_subset_euclideanClosedBall :
    Function.support (fun y : Vec d => abkSpatialConvolution ζ ψ r y) ⊆
      {y : Vec d | euclideanNorm y ≤ (d : ℝ) * (R + r)} := by
  intro y hy
  by_contra hnot
  exact hy (abkSpatialConvolution_eq_zero_of_euclideanNorm_gt ζ ψ hψ_support hr
    (lt_of_not_ge hnot))

end

end

end

/-- The local Euclidean ball is contained in the product closed ball, giving a concrete volume
upper bound. -/
theorem volume_euclideanClosedBall_le {A : ℝ} (hA_nonneg : 0 ≤ A) :
    volume {y : Vec d | euclideanNorm y ≤ A} ≤
      ENNReal.ofReal ((2 * A) ^ d) := by
  have hsubset :
      {y : Vec d | euclideanNorm y ≤ A} ⊆ Metric.closedBall 0 A := by
    intro y hy
    have hynorm := (norm_le_euclideanNorm y).trans hy
    simp_all
  calc
    volume {y : Vec d | euclideanNorm y ≤ A}
        ≤ volume _ := measure_mono hsubset
    _ = ENNReal.ofReal _ := by
          simp_all
section
variable (A : ℝ)

/-- Local Euclidean closed balls are measurable. -/
theorem measurableSet_euclideanClosedBall :
    MeasurableSet {y : Vec d | euclideanNorm y ≤ A} :=
  (isClosed_le continuous_euclideanNorm continuous_const).measurableSet

/-- Local Euclidean closed balls are compact. -/
theorem isCompact_euclideanClosedBall :
    IsCompact {y : Vec d | euclideanNorm y ≤ A} := by
  have hclosed : IsClosed {y : Vec d | euclideanNorm y ≤ A} :=
    isClosed_le continuous_euclideanNorm continuous_const
  have hsubset :
      {y : Vec d | euclideanNorm y ≤ A} ⊆ Metric.closedBall 0 A := by
    intro y hy
    have hynorm := (norm_le_euclideanNorm y).trans hy
    simp_all
  exact (isCompact_closedBall 0 A).of_isClosed_subset hclosed hsubset

end
section
variable (ζ : ABKCutoff d) (ψ : MeanZeroTestFunction d) {r : ℝ}
section
variable (hr : 0 < r)
include hr

/-- At positive scale, the ABK spatial convolution has compact support. -/
theorem hasCompactSupport_abkSpatialConvolution :
    HasCompactSupport (fun y : Vec d => abkSpatialConvolution ζ ψ r y) := by
  rcases exists_support_subset_euclideanClosedBall_meanZeroTestFunction ψ with
    ⟨R, _hR_nonneg, hψ_support⟩
  let A := d * (R + r)
  refine HasCompactSupport.of_support_subset_isCompact
    (isCompact_euclideanClosedBall A) ?_
  simpa [A] using
    support_abkSpatialConvolution_subset_euclideanClosedBall ζ ψ hψ_support hr

/-- At positive scale, the square of the ABK spatial convolution is integrable. -/
theorem integrable_sq_abkSpatialConvolution :
    Integrable (fun y : Vec d => (abkSpatialConvolution ζ ψ r y) ^ (2 : Nat))
      (volume : Measure (Vec d)) := by
  have hcont :=
    continuous_abkSpatialConvolution ζ ψ hr.ne'
  have hcont_sq :
      Continuous (fun y => (abkSpatialConvolution ζ ψ r y) ^ (2 : Nat)) :=
    hcont.pow 2
  have hcs : HasCompactSupport (abkSpatialConvolution ζ ψ r) :=
    hasCompactSupport_abkSpatialConvolution ζ ψ hr
  have hcs_sq :
      HasCompactSupport
        (fun y =>
          abkSpatialConvolution ζ ψ r y * abkSpatialConvolution ζ ψ r y) :=
    hcs.mul_left
  exact hcont_sq.integrable_of_hasCompactSupport (by
    simpa [pow_two] using hcs_sq)

end

end

end

end GaussianFields

end
