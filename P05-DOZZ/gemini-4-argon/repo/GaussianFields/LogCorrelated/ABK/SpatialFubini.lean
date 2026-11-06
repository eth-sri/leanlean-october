/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import GaussianFields.LogCorrelated.ABK.Dilation

/-!
# GaussianFields.LogCorrelated/ABK/SpatialFubini

Port of the corresponding GaussianFields source module.
-/

public section

open MeasureTheory
open scoped ENNReal Topology

namespace GaussianFields


/-- Pairing a fixed-scale ABK spatial convolution against a compactly supported continuous
function allows the convolution integral to be swapped by Fubini. -/
theorem integral_abkSpatialConvolution_mul_eq_integral_integral {d}
    ζ ψ r
    {F} (hF_cont : Continuous F) (hF_cs : HasCompactSupport F) :
    (∫ y : Vec d, abkSpatialConvolution ζ ψ r y * F y
        ∂(volume : Measure (Vec d))) =
      ∫ x : Vec d,
        ψ x *
          (∫ y : Vec d, abkScaledCutoff ζ r (y - x) * F y
            ∂(volume : Measure (Vec d)))
        ∂(volume : Measure (Vec d)) := by
  have hasCompactSupport_abkSpatialConvolution_pair_integrand : HasCompactSupport (Function.uncurry (fun y x => (abkScaledCutoff ζ r (y - x) * ψ x) * F y)) := by
    refine HasCompactSupport.of_support_subset_isCompact
      (hF_cs.isCompact.prod ψ.hasCompactSupport.isCompact) ?_
    intro p hp
    exact ⟨subset_tsupport F (by intro hzero; exact hp (by simp [Function.uncurry, hzero])), subset_tsupport ψ (by intro hzero; exact hp (by simp [Function.uncurry, hzero]))⟩
  let G : Vec d → Vec d → ℝ := fun y x =>
    (abkScaledCutoff ζ r (y - x) * ψ x) * F y
  calc
    (∫ y : Vec d, abkSpatialConvolution ζ ψ r y * F y
        ∂(volume : Measure (Vec d)))
        = ∫ y : Vec d, ∫ x : Vec d, G y x ∂(volume : Measure (Vec d))
            ∂(volume : Measure (Vec d)) := by
          refine integral_congr_ae ?_
          filter_upwards with y
          unfold abkSpatialConvolution
          rw [integral_mul_const]
    _ = ∫ x : Vec d, ∫ y : Vec d, G y x ∂(volume : Measure (Vec d))
          ∂(volume : Measure (Vec d)) := by
          exact MeasureTheory.integral_integral_swap_of_hasCompactSupport (by change Continuous (fun p : Vec d × Vec d => (abkScaledCutoff ζ r (p.1 - p.2) * ψ p.2) * F p.1); exact ((ζ.continuous.comp ((continuous_const_smul (r⁻¹)).comp (continuous_fst.sub continuous_snd : Continuous (fun p : Vec d × Vec d => p.1 - p.2)))).mul (ψ.continuous.comp continuous_snd)).mul (hF_cont.comp continuous_fst)) (by simpa [G] using hasCompactSupport_abkSpatialConvolution_pair_integrand)
    _ = ∫ x : Vec d,
        ψ x *
          (∫ y : Vec d, abkScaledCutoff ζ r (y - x) * F y
            ∂(volume : Measure (Vec d)))
        ∂(volume : Measure (Vec d)) := by
          refine integral_congr_ae ?_
          filter_upwards with x
          rw [← integral_const_mul]
          refine integral_congr_ae ?_
          filter_upwards with y
          dsimp [G]
          ring


/-- Fixed-scale spatial covariance identity: the `L²` inner product of two ABK spatial
convolutions is the double integral against the scaled cutoff self-convolution. -/
theorem integral_abkSpatialConvolution_mul_abkSpatialConvolution_eq_selfConvolution_integral
    {d} ζ ψ φ {r}
    (hr : 0 < r) :
    (∫ y : Vec d,
        abkSpatialConvolution ζ ψ r y * abkSpatialConvolution ζ φ r y
        ∂(volume : Measure (Vec d))) =
      ∫ x : Vec d,
        ψ x *
          (∫ z : Vec d,
            φ z * abkScaledCutoffSelfConvolution ζ r (x - z)
            ∂(volume : Measure (Vec d)))
        ∂(volume : Measure (Vec d)) := by
  have integral_abkScaledCutoff_mul_abkSpatialConvolution_eq_selfConvolution_integral {d} ζ φ {r} (hr : r ≠ 0) x : (∫ y : Vec d, abkScaledCutoff ζ r (y - x) * abkSpatialConvolution ζ φ r y ∂(volume : Measure (Vec d))) = ∫ z : Vec d, φ z * abkScaledCutoffSelfConvolution ζ r (x - z) ∂(volume : Measure (Vec d)) := by
    let F : Vec d → ℝ := fun y => abkScaledCutoff ζ r (y - x)
    calc
      (∫ y : Vec d,
          abkScaledCutoff ζ r (y - x) * abkSpatialConvolution ζ φ r y
          ∂(volume : Measure (Vec d)))
          = ∫ y : Vec d, abkSpatialConvolution ζ φ r y * F y
              ∂(volume : Measure (Vec d)) := by
            refine integral_congr_ae ?_
            filter_upwards with y
            dsimp [F]
            ring
      _ = ∫ z : Vec d,
            φ z *
              (∫ y : Vec d, abkScaledCutoff ζ r (y - z) * F y
                ∂(volume : Measure (Vec d)))
            ∂(volume : Measure (Vec d)) := (integral_abkSpatialConvolution_mul_eq_integral_integral (ζ := ζ) (ψ := φ) (r := r) (by dsimp [F]; exact (continuous_abkScaledCutoff ζ r).comp (continuous_id.sub continuous_const)) (show HasCompactSupport F by simpa [F, Function.comp_def] using (hasCompactSupport_abkScaledCutoff ζ hr).comp_homeomorph (Homeomorph.subRight x)))
      _ = ∫ z : Vec d,
          φ z * abkScaledCutoffSelfConvolution ζ r (x - z)
          ∂(volume : Measure (Vec d)) := by
            refine integral_congr_ae ?_
            filter_upwards with z
            congr 1
            dsimp [F]
            calc
              (∫ y : Vec d,
                  abkScaledCutoff ζ r (y - z) * abkScaledCutoff ζ r (y - x)
                  ∂(volume : Measure (Vec d)))
                  = ∫ y : Vec d,
                      abkScaledCutoff ζ r (x - y) * abkScaledCutoff ζ r (z - y)
                      ∂(volume : Measure (Vec d)) := by
                    refine integral_congr_ae ?_
                    filter_upwards with y
                    have hyz : y - z = -(z - y) := by
                      ext i
                      simp only [Pi.sub_apply, Pi.neg_apply]
                      ring
                    have hyx : y - x = -(x - y) := by
                      ext i
                      simp only [Pi.sub_apply, Pi.neg_apply]
                      ring
                    rw [hyz, hyx, abkScaledCutoff_neg, abkScaledCutoff_neg]
                    ring
              _ = abkScaledCutoffSelfConvolution ζ r (x - z) := by
                    exact integral_abkScaledCutoff_mul_abkScaledCutoff_sub_eq_selfConvolution
                      ζ r x z
  calc
    (∫ y : Vec d,
        abkSpatialConvolution ζ ψ r y * abkSpatialConvolution ζ φ r y
        ∂(volume : Measure (Vec d)))
        = ∫ x : Vec d,
            ψ x *
              (∫ y : Vec d,
                abkScaledCutoff ζ r (y - x) *
                  abkSpatialConvolution ζ φ r y
                ∂(volume : Measure (Vec d)))
            ∂(volume : Measure (Vec d)) := (integral_abkSpatialConvolution_mul_eq_integral_integral (ζ := ζ) (ψ := ψ) (r := r) (continuous_abkSpatialConvolution ζ φ hr.ne') (hasCompactSupport_abkSpatialConvolution ζ φ hr))
    _ = ∫ x : Vec d,
        ψ x *
          (∫ z : Vec d,
            φ z * abkScaledCutoffSelfConvolution ζ r (x - z)
            ∂(volume : Measure (Vec d)))
        ∂(volume : Measure (Vec d)) := by
          refine integral_congr_ae ?_
          filter_upwards with x
          rw [integral_abkScaledCutoff_mul_abkSpatialConvolution_eq_selfConvolution_integral
            ζ φ hr.ne' x]

end GaussianFields

end
