/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.Brownian.BrownianHeatDensity
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import Mathlib.MeasureTheory.Measure.Lebesgue.Integral

/-!
# Gaussian heat-kernel normalization identities

These identities reduce half-line Gaussian integrals to the full Gaussian mass by reflection.
They are the scalar integration layer for normalizing the explicit conditioned transition kernels.
-/

@[expose] public section

open MeasureTheory Set

namespace DOZZ.Proofs
section
variable {t : ℝ}
section
variable (ht : 0 < t)
include ht

/-- The Brownian heat density is integrable for every positive time. -/
theorem integrable_brownianHeatDensity :
    Integrable (brownianHeatDensity t) (volume : Measure ℝ) := by
  have hsqrt : 0 < Real.sqrt (2 * Real.pi * t) := by positivity
  have hcoef : 0 < 1 / (2 * t) := by positivity
  refine ((integrable_exp_neg_mul_sq hcoef).mul_const ((Real.sqrt (2 * Real.pi * t))⁻¹)).congr ?_
  filter_upwards [] with x
  change Real.exp _ * (Real.sqrt _)⁻¹ =
    (if 0 < t then Real.exp _ / Real.sqrt _
      else 0)
  grind

/-- The heat density has total mass one. -/
theorem integral_brownianHeatDensity :
    ∫ x : ℝ, brownianHeatDensity t x = 1 := by
  have hsqrt : 0 < Real.sqrt (2 * Real.pi * t) := by positivity
  have hfun : (fun x : ℝ => brownianHeatDensity t x) =
      (fun x => Real.exp (-(1 / (2 * t)) * x ^ 2) * (Real.sqrt (2 * Real.pi * t))⁻¹) := by
    funext x
    change (if 0 < t then Real.exp _ / Real.sqrt _
        else 0) = _
    grind
  rw [hfun, integral_mul_const, integral_gaussian]
  field_simp

end

end

private theorem volume_map_add_right (a : ℝ) :
    (volume : Measure ℝ).map (fun x : ℝ => x + a) = volume :=
  Measure.IsAddRightInvariant.map_add_right_eq_self a
section
variable {t a : ℝ}
section
variable (ht : 0 < t)
include ht

/-- Translating a heat density does not change its full-line integral. -/
theorem integral_brownianHeatDensity_translate :
    ∫ x : ℝ, brownianHeatDensity t (x + a) = 1 := by
  let e := (Homeomorph.addRight a).toMeasurableEquiv
  have he :=
    (Homeomorph.addRight a).isClosedEmbedding.measurableEmbedding
  calc
    ∫ x : ℝ, brownianHeatDensity t _ =
        ∫ y : ℝ, brownianHeatDensity t y ∂(volume.map e) := by
          symm
          exact he.integral_map (brownianHeatDensity t)
    _ = ∫ y : ℝ, brownianHeatDensity t y := by
          rw [show volume.map e = volume from volume_map_add_right a]
    _ = 1 := integral_brownianHeatDensity ht

/-- A reflected pair of translates of a normalized even density has total half-line mass one. -/
theorem integral_brownianHeatDensity_halfline_pair :
    (∫ y in Set.Ioi 0, brownianHeatDensity t (y - a) ∂(volume : Measure ℝ)) +
      ∫ y in Set.Ioi 0, brownianHeatDensity t (y + a) ∂(volume : Measure ℝ) = 1 := by
  have hshiftInt : Integrable (fun y => brownianHeatDensity t (y - a))
      volume := by
    have he :=
      (Homeomorph.addRight (-a)).isClosedEmbedding.measurableEmbedding
    have hmap :=
      volume_map_add_right (-a)
    have hmapInt : Integrable (brownianHeatDensity t)
        (volume.map (fun y => y + -a)) := by
      rw [hmap]
      exact integrable_brownianHeatDensity ht
    exact he.integrable_map_iff.mp hmapInt
  have hreflect :
      (∫ y in Set.Ioi 0, brownianHeatDensity t (y + a) ∂volume) =
        ∫ y in Set.Iic 0, brownianHeatDensity t (y - a) ∂volume := by
    calc
      (∫ y in Set.Ioi 0, brownianHeatDensity t (y + a) ∂volume) =
          ∫ y in Set.Ioi 0, brownianHeatDensity t (-(y + a)) ∂volume := by
            apply setIntegral_congr_fun measurableSet_Ioi
            intro y hy
            simp [brownianHeatDensity, ht]
            ring
      _ = ∫ y in Set.Iic 0, brownianHeatDensity t (y - a) ∂volume := by
            simpa [sub_eq_add_neg, add_comm] using
              (integral_comp_neg_Ioi (f := fun y : ℝ => brownianHeatDensity t (y - a)) 0)
  have hsplit := integral_add_compl (μ := volume)
   
    (s := Set.Iic 0) measurableSet_Iic hshiftInt
  calc
    (∫ y in Set.Ioi 0, brownianHeatDensity t (y - a) ∂volume) +
        ∫ y in Set.Ioi 0, brownianHeatDensity t (y + a) ∂volume =
        (∫ y in Set.Ioi 0, brownianHeatDensity t (y - a) ∂volume) +
          ∫ y in Set.Iic 0, brownianHeatDensity t (y - a) ∂volume := by
            linarith
    _ = (∫ y in Set.Iic 0, brownianHeatDensity t (y - a) ∂volume) +
          ∫ y in Set.Ioi 0, brownianHeatDensity t (y - a) ∂volume := add_comm ..
    _ = ∫ y : ℝ, brownianHeatDensity t (y - a) := by
          simp_all
    _ = 1 := by
          simpa [sub_eq_add_neg] using
            integral_brownianHeatDensity_translate ht

end

end

end DOZZ.Proofs

end
