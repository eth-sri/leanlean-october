/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import GaussianFields.LogCorrelated.ABK.Volume
public import Mathlib.Analysis.InnerProductSpace.Projection.Reflection
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# GaussianFields.LogCorrelated/ABK/Radial

Port of the corresponding GaussianFields source module.
-/

public section

open MeasureTheory
open scoped Convolution ENNReal Topology

namespace GaussianFields


/-- Triangle inequality for the project Euclidean norm, transferred from Mathlib's
`EuclideanSpace` norm. -/
theorem euclideanNorm_add_le {d : Nat} (x y : Vec d) :
    euclideanNorm (x + y) ≤ euclideanNorm x + euclideanNorm y := by
  rw [← norm_toLp_two_eq_euclideanNorm (x + y), ← norm_toLp_two_eq_euclideanNorm x,
    ← norm_toLp_two_eq_euclideanNorm y]
  exact norm_add_le (WithLp.toLp 2 x : EuclideanSpace ℝ (Fin d)) (WithLp.toLp 2 y)

variable {d : Nat} (ζ : ABKCutoff d)



include d ζ in
/-- The cutoff self-convolution is continuous. -/
theorem continuous_abkCutoffSelfConvolution  :
    Continuous (abkCutoffSelfConvolution ζ) := by
  have hζ_int : Integrable ζ (volume : Measure (Vec d)) :=
    ζ.continuous.integrable_of_hasCompactSupport ζ.hasCompactSupport
  have hconv  :=
    ζ.hasCompactSupport.continuous_convolution_right
      (ContinuousLinearMap.mul ℝ ℝ) hζ_int.locallyIntegrable ζ.continuous
  continuity

include d ζ in
/-- The unscaled cutoff self-convolution vanishes outside the Euclidean ball of radius `2`. -/
theorem abkCutoffSelfConvolution_eq_zero_of_two_lt_norm  {x : Vec d} (hx : 2 < euclideanNorm x) :
    abkCutoffSelfConvolution ζ x = 0 := by
  unfold abkCutoffSelfConvolution
  refine integral_eq_zero_of_ae ?_
  filter_upwards with y
  by_cases hy : ζ y = 0
  · simp [hy]
  by_cases hxy : ζ (x - y) = 0
  · simp [hxy]
  have hy_norm  := ζ.support_subset_unitBall hy
  have hxy_norm  := ζ.support_subset_unitBall hxy
  have hdecomp : y + (x - y) = x := by
    simp_all
  have hx_le : euclideanNorm x ≤ 2 := by
    calc
      euclideanNorm x = euclideanNorm (y + (x - y)) := by rw [hdecomp]
      _ ≤ euclideanNorm y + euclideanNorm (x - y) := euclideanNorm_add_le y (x - y)
      _ ≤ 1 + 1 := add_le_add hy_norm hxy_norm
      _ = 2 := by norm_num
  exfalso
  exact (not_lt_of_ge hx_le) hx

/-- The canonical radial representative has Euclidean norm `|s|` in positive dimension. -/
theorem euclideanNorm_abkRadialPoint {d : Nat} (hd : 0 < d) (s : ℝ) :
    euclideanNorm (abkRadialPoint d s) = |s| := by
  rw [euclideanNorm, euclideanNormSq_eq_sum]
  have hsum :
      (∑ i : Fin d, abkRadialPoint d s i * abkRadialPoint d s i) = s * s := by
    let i0 : Fin d := ⟨0, hd⟩
    calc
      (∑ i : Fin d, abkRadialPoint d s i * abkRadialPoint d s i)
          = abkRadialPoint d s i0 * abkRadialPoint d s i0 := by
            refine Finset.sum_eq_single i0 ?_ ?_
            · intro i _hi hne
              have hi : (i : Nat) ≠ 0 := by
                bound
              simp [abkRadialPoint, hi]
            · intro hi
              simp at hi
      _ = s * s := by
            simp [abkRadialPoint, i0]
  rw [hsum]
  simpa [pow_two] using Real.sqrt_sq_eq_abs s

/-- Nonnegative radii are represented with the prescribed Euclidean norm. -/
theorem euclideanNorm_abkRadialPoint_of_nonneg {d : Nat} (hd : 0 < d)
    {s : ℝ} (hs : 0 ≤ s) :
    euclideanNorm (abkRadialPoint d s) = s := by
  rw [euclideanNorm_abkRadialPoint hd s, abs_of_nonneg hs]

/-- Radial representative form of the support cutoff for `ζ * ζ`. -/
theorem abkCutoffSelfConvolution_radial_eq_zero_of_two_lt {d : Nat} (hd : 0 < d)
    (ζ : ABKCutoff d) {t : ℝ} (ht : 2 < t) :
    abkCutoffSelfConvolution ζ (abkRadialPoint d t) = 0 := abkCutoffSelfConvolution_eq_zero_of_two_lt_norm ζ
    (by simpa [euclideanNorm_abkRadialPoint_of_nonneg hd (le_of_lt (by linarith : 0 < t))]
      using ht)

include d ζ in
/-- The cutoff self-convolution is radial when the cutoff is radial. -/
theorem abkCutoffSelfConvolution_radial  {x y : Vec d}
    (h : euclideanNorm x = euclideanNorm y) :
    abkCutoffSelfConvolution ζ x = abkCutoffSelfConvolution ζ y := by
  let xE : EuclideanSpace ℝ (Fin d) := WithLp.toLp 2 x
  let yE : EuclideanSpace ℝ (Fin d) := WithLp.toLp 2 y
  have hnorm : ‖xE‖ = ‖yE‖ := by
    simpa [xE, yE, norm_toLp_two_eq_euclideanNorm] using h
  let R : EuclideanSpace ℝ (Fin d) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin d) :=
    Submodule.reflection (ℝ ∙ (xE - yE))ᗮ
  have hRxy  := Submodule.reflection_sub hnorm
  let e : Vec d ≃ᵐ Vec d :=
    ((MeasurableEquiv.toLp 2 (Vec d)).trans R.toMeasurableEquiv).trans
      (MeasurableEquiv.toLp 2 (Vec d)).symm
  have he_mp : MeasurePreserving e := (PiLp.volume_preserving_ofLp (Fin d)).comp
      ((LinearIsometryEquiv.measurePreserving R).comp (PiLp.volume_preserving_toLp (Fin d)))
  have he_norm : ∀ v : Vec d, euclideanNorm (e v) = euclideanNorm v := by
    intro v
    rw [← norm_toLp_two_eq_euclideanNorm (e v), ← norm_toLp_two_eq_euclideanNorm v]
    continuity
  have he_sub : ∀ v : Vec d, e (x - v) = y - e v := by
    continuity
  symm
  calc
    abkCutoffSelfConvolution ζ y
        = ∫ v : Vec d,
            ζ (e v) * ζ (y - e v) ∂(volume : Measure (Vec d)) := by
          unfold abkCutoffSelfConvolution
          rw [← he_mp.integral_comp' (f := e)
            (g := fun u : Vec d => ζ u * ζ (y - u))]
    _ = ∫ v : Vec d, ζ v * ζ (x - v) ∂(volume : Measure (Vec d)) := by
          refine integral_congr_ae ?_
          filter_upwards with v
          have hζ₁  := ζ.radial _ _ (he_norm v)
          have hζ₂ : ζ (y - e v) = ζ (x - v) := by
            rw [← he_sub v]
            exact ζ.radial _ _ (he_norm (x - v))
          rw [hζ₁, hζ₂]
    _ = abkCutoffSelfConvolution ζ x := rfl

end GaussianFields

end
