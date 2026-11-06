/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import GaussianFields.LogCorrelated.ABK.Convolution

/-!
# GaussianFields ABK convolution bounds

Port of the corresponding GaussianFields source module.
-/

public section

open MeasureTheory ProbabilityTheory
open scoped Convolution ENNReal InnerProductSpace NNReal ProbabilityTheory Topology

namespace GaussianFields
section
variable {d : Nat}
section
variable {f : Vec d → ℝ}

/-- A uniformly bounded square-integrable function supported in a finite Euclidean ball has its
`L²` mass bounded by `M^2` times the volume of that ball. -/
theorem integral_norm_sq_le_measure_mul_of_abs_le_of_support_subset {M A : ℝ}
    (hf_int : Integrable (fun y : Vec d => (f y) ^ (2 : Nat))
      (volume : Measure (Vec d)))
    (hM_nonneg : 0 ≤ M) (hA_nonneg : 0 ≤ A)
    (hpoint : ∀ y : Vec d, |f y| ≤ M)
    (hsupport : Function.support f ⊆ {y : Vec d | euclideanNorm y ≤ A}) :
    ∫ y : Vec d, ‖(f y) ^ (2 : Nat)‖ ∂(volume : Measure (Vec d)) ≤
      ((volume : Measure (Vec d)) {y : Vec d | euclideanNorm y ≤ A}).toReal * M ^ (2 : Nat) := by
  let S := {y : Vec d | euclideanNorm y ≤ A}
  have hS_meas : MeasurableSet S := measurableSet_euclideanClosedBall A
  have hS_finite : (volume : Measure (Vec d)) S ≠ ∞ := by
    have hvol_le : (volume : Measure (Vec d)) S ≤ ENNReal.ofReal ((2 * A) ^ d) :=
      volume_euclideanClosedBall_le hA_nonneg
    exact (hvol_le.trans_lt ENNReal.ofReal_lt_top).ne
  have hconst_int :
      Integrable (S.indicator fun _ => M ^ (2 : Nat))
        volume := (integrableOn_const hS_finite).integrable_indicator
      hS_meas
  have hpointwise :
      (fun y => ‖(f y) ^ 2‖) ≤ᶠ[ae volume]
        S.indicator (fun _ => M ^ 2) := by
    filter_upwards with y
    by_cases hyS : y ∈ S
    · have hsq_nonneg := sq_nonneg (f y)
      have hsq_le : (f y) ^ 2 ≤ M ^ 2 := sq_le_sq.2 (by grind)
      simp_all
    · have hfy_zero : f y = 0 := by
        by_contra hne
        tauto
      simp_all
  calc
    ∫ y : Vec d, ‖(f y) ^ 2‖ ∂volume
        ≤ ∫ y : Vec d, S.indicator (fun _ => M ^ 2) y
            ∂volume :=
          integral_mono_ae hf_int.norm hconst_int hpointwise
    _ = (volume S).toReal * M ^ 2 := by
          rwa [integral_indicator_const, MeasureTheory.measureReal_def, smul_eq_mul]

/-- A uniformly bounded integrable function supported in a measurable finite set has integral
bounded by `M` times the set volume. -/
theorem abs_integral_le_measure_mul_of_abs_le_of_support_subset {M : ℝ} {S : Set (Vec d)}
    (hf_int : Integrable f (volume : Measure (Vec d)))
    (hS_meas : MeasurableSet S)
    (hS_finite : (volume : Measure (Vec d)) S ≠ ∞)
    (hpoint : ∀ y : Vec d, |f y| ≤ M)
    (hsupport : Function.support f ⊆ S) :
    |∫ y : Vec d, f y ∂(volume : Measure (Vec d))| ≤
      ((volume : Measure (Vec d)) S).toReal * M := by
  have hconst_int :
      Integrable (S.indicator fun _ => M)
        volume := (integrableOn_const hS_finite).integrable_indicator hS_meas
  have hpointwise :
      (fun y => ‖f y‖) ≤ᶠ[ae volume]
        S.indicator (fun _ => M) := by
    filter_upwards with y
    by_cases hyS : y ∈ S
    · simp_all
    · have hfy_zero : f y = 0 := by
        by_contra hne
        simp_all
      simp_all
  calc
    |∫ y : Vec d, f y ∂volume|
        = ‖∫ y : Vec d, f y ∂volume‖ := by
          rfl
    _ ≤ ∫ y : Vec d, ‖f y‖ ∂volume :=
          norm_integral_le_integral_norm f
    _ ≤ ∫ y : Vec d, S.indicator (fun _ => M) y
          ∂volume :=
          integral_mono_ae hf_int.norm hconst_int hpointwise
    _ = (volume S).toReal * M := by
          aesop

end
section
variable (ζ : ABKCutoff d) (ψ : MeanZeroTestFunction d)

/-- Small-scale pointwise bound: compact support and boundedness of `ψ`, together with the cutoff
support, give `|ζ_r * ψ| = O(r^d)`. -/
theorem abs_abkSpatialConvolution_le_small :
    ∃ C, 0 ≤ C ∧ ∀ r y, 0 < r →
      |abkSpatialConvolution ζ ψ r y| ≤ C * r ^ d := by
  rcases exists_abs_meanZeroTestFunction_le ψ with ⟨B, hB_nonneg, hB⟩
  refine ⟨B * 2 ^ d, mul_nonneg hB_nonneg (pow_nonneg zero_le_two d), ?_⟩
  intro r y hr
  let S := Metric.closedBall y r
  have hS_meas : MeasurableSet S := measurableSet_closedBall
  have hS_finite : (volume : Measure (Vec d)) S ≠ ∞ := by
    rw [Real.volume_pi_closedBall y hr.le, Fintype.card_fin]
    exact ENNReal.ofReal_ne_top
  let F : Vec d → ℝ := fun x => abkScaledCutoff ζ r (y - x) * ψ x
  have hpoint : ∀ x : Vec d, |F x| ≤ B := by
    intro x
    have hz_nonneg : 0 ≤ abkScaledCutoff ζ r (y - x) := ζ.nonneg _
    have hz_le_one : abkScaledCutoff ζ r (y - x) ≤ 1 := ζ.le_one _
    calc
      |F x| = |abkScaledCutoff ζ r _ * ψ x| := rfl
      _ = |abkScaledCutoff ζ r _| * |ψ x| := abs_mul ..
      _ = abkScaledCutoff ζ r _ * |ψ x| := by simp_all
      _ ≤ 1 * B := mul_le_mul hz_le_one (hB x) (abs_nonneg (ψ x)) zero_le_one
      _ = B := by ring
  have hsupport : Function.support F ⊆ S := by
    intro x hx
    have hcut_ne : abkScaledCutoff ζ r (y - x) ≠ 0 := by
      aesop
    have hnorm : euclideanNorm (y - x) ≤ r :=
      euclideanNorm_le_of_abkScaledCutoff_ne_zero ζ hr hcut_ne
    exact by
      calc
        dist x y = ‖x - y‖ := dist_eq_norm x y
        _ ≤ euclideanNorm _ := norm_le_euclideanNorm _
        _ = euclideanNorm _ := euclideanNorm_sub_comm x y
        _ ≤ r := hnorm
  have hbound :=
    abs_integral_le_measure_mul_of_abs_le_of_support_subset
     
      (integrable_abkSpatialConvolution_integrand ζ ψ r y)
      hS_meas hS_finite hpoint hsupport
  have hvol_real : ((volume : Measure (Vec d)) S).toReal = (2 * r) ^ d := by
    rw [Real.volume_pi_closedBall y hr.le, Fintype.card_fin]
    rw [ENNReal.toReal_ofReal]
    exact pow_nonneg (mul_nonneg zero_le_two hr.le) d
  calc
    |abkSpatialConvolution ζ ψ r y| = |∫ x : Vec d, F x ∂(volume : Measure (Vec d))| := rfl
    _ ≤ ((volume : Measure (Vec d)) S).toReal * B := hbound
    _ = (2 * r) ^ d * B := by simp_all
    _ = (B * 2 ^ d) * r ^ d := by
          ring

/-- Small-scale spatial square estimate: `‖ζ_r * ψ‖₂² = O(r^{2d})`.  After multiplying by the
ABK prefactor `r^{-(d+1)}`, this becomes the small-scale `O(r^{d-1})` integrand. -/
theorem integral_norm_sq_abkSpatialConvolution_le_small :
    ∃ C, 0 ≤ C ∧ ∀ r : ℝ, 0 < r → r ≤ 1 →
      Integrable (fun y : Vec d => (abkSpatialConvolution ζ ψ r y) ^ (2 : Nat))
        (volume : Measure (Vec d)) →
      (∫ y : Vec d, ‖(abkSpatialConvolution ζ ψ r y) ^ (2 : Nat)‖
        ∂(volume : Measure (Vec d))) ≤ C * r ^ (2 * d) := by
  rcases exists_support_subset_euclideanClosedBall_meanZeroTestFunction ψ with
    ⟨R, hR_nonneg, hψ_support⟩
  rcases abs_abkSpatialConvolution_le_small ζ ψ with ⟨M, hM_nonneg, hpoint⟩
  let A := d * (R + 1)
  let V := (2 * A) ^ d
  refine ⟨V * M ^ 2, mul_nonneg ?_ (sq_nonneg M), ?_⟩
  · positivity
  intro r hr_pos hr_le_one hsection_int
  have hA_nonneg :=
    mul_nonneg (Nat.cast_nonneg d) (add_nonneg hR_nonneg zero_le_one)
  have hsupport :
      Function.support (abkSpatialConvolution ζ ψ r) ⊆
        {y : Vec d | euclideanNorm y ≤ A} := by
    have hsupport_r :=
      support_abkSpatialConvolution_subset_euclideanClosedBall ζ ψ hψ_support hr_pos
    intro y hy
    have hrad_le : d * (R + r) ≤ A := by
      have hRr : R + r ≤ R + 1 := by linarith
      exact mul_le_mul_of_nonneg_left hRr (Nat.cast_nonneg d)
    exact (hsupport_r hy).trans hrad_le
  have hbasic :=
    integral_norm_sq_le_measure_mul_of_abs_le_of_support_subset
     
     
      hsection_int
      (mul_nonneg hM_nonneg (pow_nonneg hr_pos.le d))
      hA_nonneg
      (fun y => hpoint r y hr_pos)
      hsupport
  have hvol_real_le :
      (volume {y : Vec d | euclideanNorm y ≤ A}).toReal ≤ V := by
    have hvol_le :
        volume {y : Vec d | euclideanNorm y ≤ A} ≤
          ENNReal.ofReal V := by
      simpa [V] using volume_euclideanClosedBall_le hA_nonneg
    have hV_nonneg : 0 ≤ V := pow_nonneg (mul_nonneg zero_le_two hA_nonneg) d
    simpa [ENNReal.toReal_ofReal hV_nonneg] using
      ENNReal.toReal_mono ENNReal.ofReal_ne_top hvol_le
  have hmass_le :
      (volume {y : Vec d | euclideanNorm y ≤ A}).toReal *
          (M * r ^ d) ^ 2 ≤
        V * (M * r ^ d) ^ 2 := mul_le_mul_of_nonneg_right hvol_real_le (sq_nonneg (M * r ^ d))
  calc
    (∫ y : Vec d, ‖(abkSpatialConvolution ζ ψ r y) ^ 2‖
        ∂volume)
        ≤ (volume {y : Vec d | euclideanNorm y ≤ A}).toReal *
            (M * r ^ d) ^ 2 := hbasic
    _ ≤ V * (M * r ^ d) ^ 2 := hmass_le
    _ = (V * M ^ 2) * r ^ (2 * d) := by
          calc
            V * (M * r ^ d) ^ 2 = V * M ^ 2 * (r ^ d) ^ 2 := by
              ring
            _ = (V * M ^ 2) * r ^ (2 * d) := by
              rw [← pow_mul, Nat.mul_comm d 2]

end

/-- For large positive scales, the support ball from the ABK convolution has volume `O(r^d)`. -/
theorem volume_abkSupportBall_le_large {R r : ℝ}
    (hR_nonneg : 0 ≤ R) (hr : 1 ≤ r) :
    volume {y : Vec d | euclideanNorm y ≤ (d : ℝ) * (R + r)} ≤
      ENNReal.ofReal (((2 * (d : ℝ) * (R + 1)) ^ d) * r ^ d) := by
  have hd_nonneg : 0 ≤ (d : ℝ) := Nat.cast_nonneg d
  have hA_nonneg :=
    mul_nonneg hd_nonneg (add_nonneg hR_nonneg (le_trans zero_le_one hr))
  have hRr : R + r ≤ (R + 1) * r := by
    nlinarith
  have hbase_le :
      2 * (d * (R + r)) ≤ (2 * d * (R + 1)) * r := by
    nlinarith
  have hbase_nonneg :=
    mul_nonneg zero_le_two hA_nonneg
  have hpow_le :=
    pow_le_pow_left₀ hbase_nonneg hbase_le d
  calc
    volume {y : Vec d | euclideanNorm y ≤ d * (R + r)}
        ≤ ENNReal.ofReal _ :=
          volume_euclideanClosedBall_le hA_nonneg
    _ ≤ ENNReal.ofReal _ :=
          ENNReal.ofReal_le_ofReal hpow_le
    _ = ENNReal.ofReal _ := by
          rw [mul_pow]

/-- The large-scale ABK spatial square estimate following from mean-zero cancellation.  The bound
has the form `O(r^d |r|^{-2})`; after the kernel prefactor `r^{-(d+1)}` this is the ABK `O(r^-3)`
scale integrand. -/
theorem integral_norm_sq_abkSpatialConvolution_le_large (ζ : ABKCutoff d) (ψ : MeanZeroTestFunction d) :
    ∃ C, 0 ≤ C ∧ ∀ r : ℝ, 1 ≤ r →
      Integrable (fun y : Vec d => (abkSpatialConvolution ζ ψ r y) ^ (2 : Nat))
        (volume : Measure (Vec d)) →
      (∫ y : Vec d, ‖(abkSpatialConvolution ζ ψ r y) ^ (2 : Nat)‖
        ∂(volume : Measure (Vec d))) ≤ C * r ^ d * |r|⁻¹ ^ (2 : Nat) := by
  rcases exists_support_subset_euclideanClosedBall_meanZeroTestFunction ψ with
    ⟨R, hR_nonneg, hψ_support⟩
  rcases abs_abkSpatialConvolution_le_scaled_moment ζ ψ with ⟨L, hL_nonneg, hpoint⟩
  let J := ∫ x : Vec d, euclideanNorm x * |ψ x|
  have hJ_nonneg : 0 ≤ J := integral_nonneg fun x => mul_nonneg (euclideanNorm_nonneg x) (abs_nonneg (ψ x))
  let Cvol := (2 * d * (R + 1)) ^ d
  let C := Cvol * (L * J) ^ 2
  have hCvol_nonneg : 0 ≤ Cvol := pow_nonneg
      (mul_nonneg (mul_nonneg zero_le_two (Nat.cast_nonneg d))
        (add_nonneg hR_nonneg zero_le_one)) d
  have hC_nonneg : 0 ≤ C := mul_nonneg hCvol_nonneg (sq_nonneg (L * J))
  refine ⟨C, hC_nonneg, ?_⟩
  intro r hr hsection_int
  have hr_nonneg := le_trans zero_le_one hr
  let A := d * (R + r)
  have hA_nonneg :=
    mul_nonneg (Nat.cast_nonneg d) (add_nonneg hR_nonneg hr_nonneg)
  have hsupport :
      Function.support (fun y : Vec d => abkSpatialConvolution ζ ψ r y) ⊆
        {y : Vec d | euclideanNorm y ≤ A} := by
    simpa [A] using support_abkSpatialConvolution_subset_euclideanClosedBall ζ ψ
      hψ_support (lt_of_lt_of_le zero_lt_one hr)
  have hM_nonneg :=
    mul_nonneg (mul_nonneg hL_nonneg (inv_nonneg.mpr (abs_nonneg r))) hJ_nonneg
  have hbasic :=
    integral_norm_sq_le_measure_mul_of_abs_le_of_support_subset
      (f := fun y : Vec d => abkSpatialConvolution ζ ψ r y)
      (M := L * |r|⁻¹ * J) (A := A)
      hsection_int hM_nonneg hA_nonneg (hpoint r) hsupport
  have hvol_le :
      volume {y : Vec d | euclideanNorm y ≤ A} ≤
        ENNReal.ofReal (Cvol * r ^ d) := by
    simpa [A, Cvol] using volume_abkSupportBall_le_large (d := d) (R := R) (r := r)
      hR_nonneg hr
  have hvol_real_le :
      ((volume : Measure (Vec d)) {y : Vec d | euclideanNorm y ≤ A}).toReal ≤
        Cvol * r ^ d := by
    have hfinite : ENNReal.ofReal (Cvol * r ^ d) ≠ ∞ := ENNReal.ofReal_ne_top
    have hnonneg :=
      mul_nonneg hCvol_nonneg (pow_nonneg hr_nonneg d)
    simpa [ENNReal.toReal_ofReal hnonneg] using ENNReal.toReal_mono hfinite hvol_le
  have hmass_le :
      (volume {y : Vec d | euclideanNorm y ≤ A}).toReal *
          (L * |r|⁻¹ * J) ^ 2 ≤
        (Cvol * r ^ d) * (L * |r|⁻¹ * J) ^ 2 := mul_le_mul_of_nonneg_right hvol_real_le (sq_nonneg (L * |r|⁻¹ * J))
  calc
    (∫ y : Vec d, ‖(abkSpatialConvolution ζ ψ r y) ^ 2‖
        ∂volume)
        ≤ (volume {y : Vec d | euclideanNorm y ≤ A}).toReal *
            (L * |r|⁻¹ * J) ^ 2 := hbasic
    _ ≤ (Cvol * r ^ d) * (L * |r|⁻¹ * J) ^ 2 := hmass_le
    _ = C * r ^ d * |r|⁻¹ ^ 2 := by
          simp [C, Cvol, abs_of_nonneg hr_nonneg]
          ring_nf
section
variable {r : ℝ}
section
variable (hr : 0 < r)
include hr

/-- The large-scale ABK power count:
`r^{-(d+1)} r^d r^{-2} = r^{-3}`. -/
theorem abk_largeScale_power_identity :
    (r ^ (-(((d : ℝ) + 1) / 2))) ^ (2 : Nat) * r ^ d * (|r|⁻¹) ^ (2 : Nat) =
      r ^ (-3 : ℝ) := by
  let a := -(((d : ℝ) + 1) / 2)
  have hpref : (r ^ a) ^ (2 : Nat) = r ^ (-((d : ℝ) + 1)) := by
    calc
      (r ^ a) ^ 2
          = r ^ (a * ((2 : Nat) : ℝ)) :=
            (Real.rpow_mul_natCast hr.le a 2).symm
      _ = r ^ (-((d : ℝ) + 1)) := by
            aesop
  have hinv : (|r|⁻¹) ^ (2 : Nat) = r ^ (-2 : ℝ) := by
    simp
  have hnat : r ^ d = r ^ (d : ℝ) := by
    simp
  change _ ^ 2 * r ^ d * (|r|⁻¹) ^ (2 : Nat) = r ^ (-3)
  rw [hpref, hinv, hnat, ← Real.rpow_add hr, ← Real.rpow_add hr]
  norm_num

/-- The small-scale ABK power count:
`r^{-(d+1)} r^{2d} = r^{d-1}`. -/
theorem abk_smallScale_power_identity :
    (r ^ (-(((d : ℝ) + 1) / 2))) ^ (2 : Nat) * r ^ (2 * d) =
      r ^ ((d : ℝ) - 1) := by
  have hr_nonneg : 0 ≤ r := hr.le
  let a := -(((d : ℝ) + 1) / 2)
  have hpref : (r ^ a) ^ (2 : Nat) = r ^ (-((d : ℝ) + 1)) := by
    calc
      (r ^ a) ^ (2 : Nat)
          = r ^ (a * ((2 : Nat) : ℝ)) :=
            (Real.rpow_mul_natCast hr_nonneg a 2).symm
      _ = r ^ (-((d : ℝ) + 1)) := by
            aesop
  have hnat : r ^ (2 * d) = r ^ (((2 * d : Nat) : ℝ)) := by
    norm_cast
  rw [hpref, hnat]
  rw [← Real.rpow_add hr]
  grind

end

end

end

end GaussianFields

end
