/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
public import GaussianFields.LogCorrelated.ABK.Constants

/-!
# GaussianFields.LogCorrelated/ABK/Dilation

Port of the corresponding GaussianFields source module.
-/

public section

open MeasureTheory
open scoped ENNReal Topology

namespace GaussianFields


/-- Change variables by `x ↦ r⁻¹ x` in `Vec d`. -/
theorem integral_comp_inv_smul_vec {d : Nat} (f : Vec d → ℝ) {r : ℝ} (hr : 0 ≤ r) :
    (∫ x : Vec d, f (r⁻¹ • x) ∂(volume : Measure (Vec d))) =
      r ^ d * ∫ x : Vec d, f x ∂(volume : Measure (Vec d)) := by
  have hraw :=
    MeasureTheory.Measure.integral_comp_inv_smul_of_nonneg
      (μ := volume) f hr
  simp_all

/-- The scaled self-convolution `(ζ_r * ζ_r)(x)`. -/
@[expose]
noncomputable def abkScaledCutoffSelfConvolution {d : Nat} (ζ : ABKCutoff d)
    (r : ℝ) (x : Vec d) : ℝ :=
  ∫ y : Vec d, abkScaledCutoff ζ r y * abkScaledCutoff ζ r (x - y)
section
variable {d : Nat} (ζ : ABKCutoff d)

/-- The scaled cutoff self-convolution obeys the exact ABK dilation law
`(ζ_r * ζ_r)(x) = r^d (ζ * ζ)(x/r)` for positive `r`. -/
theorem abkScaledCutoffSelfConvolution_eq_pow_mul {r : ℝ} (hr : 0 < r) (x : Vec d) :
    abkScaledCutoffSelfConvolution ζ r x =
      r ^ d * abkCutoffSelfConvolution ζ (r⁻¹ • x) := by
  let F : Vec d → ℝ := fun u => ζ u * ζ (r⁻¹ • x - u)
  have hscale := integral_comp_inv_smul_vec (d := d) F hr.le
  unfold abkScaledCutoffSelfConvolution abkCutoffSelfConvolution abkScaledCutoff
  rw [← hscale]
  refine integral_congr_ae ?_
  filter_upwards with y
  have hsub : r⁻¹ • (x - y) = r⁻¹ • x - r⁻¹ • y := by
    ext i
    simp
    ring
  tauto
section
variable (r : ℝ)

/-- The scaled cutoff is even, inherited from radiality of the ABK cutoff. -/
theorem abkScaledCutoff_neg (x : Vec d) :
    abkScaledCutoff ζ r (-x) = abkScaledCutoff ζ r x := by
  have hsmul : r⁻¹ • (-x) = -(r⁻¹ • x) := by
    simp
  exact ζ.radial _ _ (by rw [hsmul, euclideanNorm_neg])

/-- The overlap of two translated scaled cutoffs is the scaled cutoff self-convolution at the
separation vector. -/
theorem integral_abkScaledCutoff_mul_abkScaledCutoff_sub_eq_selfConvolution (x z : Vec d) :
    (∫ y : Vec d,
        abkScaledCutoff ζ r (x - y) * abkScaledCutoff ζ r (z - y)
        ∂(volume : Measure (Vec d))) =
      abkScaledCutoffSelfConvolution ζ r (x - z) := by
  let F : Vec d → ℝ := fun u =>
    abkScaledCutoff ζ r u * abkScaledCutoff ζ r (z - x + u)
  have hneg :
      (∫ y : Vec d, F (-y) ∂volume) =
        ∫ y : Vec d, F y ∂volume := (Measure.measurePreserving_neg volume).integral_comp
        (Homeomorph.neg (Vec d)).measurableEmbedding F
  have htrans :
      (∫ y : Vec d, F (x - y) ∂volume) =
        ∫ y : Vec d, F (-y) ∂volume := by
    have h :=
      (MeasureTheory.measurePreserving_add_right volume (-x)).integral_comp'
        (f := MeasurableEquiv.addRight (-x)) (fun y : Vec d => F (-y))
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using h
  calc
    (∫ y : Vec d,
        abkScaledCutoff ζ r _ * abkScaledCutoff ζ r _
        ∂volume)
        = ∫ y : Vec d, F _ ∂volume := by
            aesop
    _ = ∫ y : Vec d, F y ∂volume := by
          linarith
    _ = abkScaledCutoffSelfConvolution ζ r _ := by
          unfold abkScaledCutoffSelfConvolution
          refine integral_congr_ae ?_
          filter_upwards with y
          dsimp [F]
          have harg : z - x + y = -(x - z - y) := by
            ring
          rw [harg, abkScaledCutoff_neg]

end

end

end GaussianFields

end
