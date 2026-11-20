/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Brownian.ConditionedKernelAlgebra
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import Mathlib.MeasureTheory.Measure.Lebesgue.Integral
public import Mathlib.MeasureTheory.Group.Integral

/-!
# Gaussian heat-kernel normalization identities

These identities reduce half-line Gaussian integrals to the full Gaussian mass by reflection.
They are the scalar integration layer for normalizing the explicit conditioned transition kernels.
-/

@[expose] public section

open MeasureTheory Set

namespace DOZZ.Proofs

section
variable {t : ℝ} (ht : 0 < t)
include ht

/-- The Brownian heat density is integrable for every positive time. -/
theorem integrable_brownianHeatDensity :
    Integrable (brownianHeatDensity t) (volume : Measure ℝ) := by
  have hsqrt : 0 < Real.sqrt (2 * Real.pi * t) := by positivity
  have hcoef : 0 < 1 / (2 * t) := by positivity
  have hbase : Integrable (fun x : ℝ => Real.exp (-(1 / (2 * t)) * x ^ 2))
      (volume : Measure ℝ) := integrable_exp_neg_mul_sq hcoef
  have hmul := hbase.mul_const ((Real.sqrt (2 * Real.pi * t))⁻¹)
  refine hmul.congr ?_
  filter_upwards [] with x
  change Real.exp (-(1 / (2 * t)) * x ^ 2) * (Real.sqrt (2 * Real.pi * t))⁻¹ =
    (if 0 < t then Real.exp (-(x ^ 2) / (2 * t)) / Real.sqrt (2 * Real.pi * t)
      else 0)
  rw [ite_eq_left ht, div_eq_mul_inv]
  congr 1
  field_simp [ht.ne', hsqrt.ne']

/-- The heat density has total mass one. -/
theorem integral_brownianHeatDensity :
    ∫ x : ℝ, brownianHeatDensity t x = 1 := by
  have hsqrt : 0 < Real.sqrt (2 * Real.pi * t) := by positivity
  have hfun : (fun x : ℝ => brownianHeatDensity t x) =
      (fun x => Real.exp (-(1 / (2 * t)) * x ^ 2) * (Real.sqrt (2 * Real.pi * t))⁻¹) := by
    funext x
    change (if 0 < t then Real.exp (-(x ^ 2) / (2 * t)) / Real.sqrt (2 * Real.pi * t)
        else 0) = _
    rw [ite_eq_left ht, div_eq_mul_inv]
    congr 1
    field_simp [ht.ne', hsqrt.ne']
  rw [hfun, integral_mul_const, integral_gaussian]
  have hroot : Real.sqrt (Real.pi / (1 / (2 * t))) = Real.sqrt (2 * Real.pi * t) := by
    congr 1
    field_simp [ht.ne']
  rw [hroot]
  field_simp [hsqrt.ne']

theorem integrable_brownianHeatDensity_translate (a : ℝ) :
    Integrable (fun y : ℝ => brownianHeatDensity t (y + a)) (volume : Measure ℝ) :=
  (integrable_brownianHeatDensity ht).comp_add_right a

/-- A translated heat density is integrable on the full real line. -/
theorem integrable_brownianHeatDensity_sub_const (a : ℝ) :
    Integrable (fun y : ℝ => brownianHeatDensity t (y - a)) (volume : Measure ℝ) :=
  (integrable_brownianHeatDensity ht).comp_sub_right a

end

section
variable {t a : ℝ} (ht : 0 < t)
include ht

/-- Translating a heat density does not change its full-line integral. -/
theorem integral_brownianHeatDensity_translate :
    ∫ x : ℝ, brownianHeatDensity t (x + a) = 1 := by
  rw [integral_add_right_eq_self, integral_brownianHeatDensity ht]

/-- A reflected pair of translates of a normalized even density has total half-line mass one. -/
theorem integral_brownianHeatDensity_halfline_pair :
    (∫ y in Ioi 0, brownianHeatDensity t (y - a)) +
      (∫ y in Ioi 0, brownianHeatDensity t (y + a)) = 1 := by
  have hrefl (y : ℝ) : brownianHeatDensity t (-y - a) = brownianHeatDensity t (y + a) := by
    rw [show -y - a = -(y + a) by ring, brownianHeatDensity_even]
  have h : (∫ y in Ioi 0, brownianHeatDensity t (y + a)) =
      ∫ y in Iic 0, brownianHeatDensity t (y - a) := by
    simpa only [hrefl, neg_zero] using
      (integral_comp_neg_Ioi 0 (fun y : ℝ => brownianHeatDensity t (y - a)))
  rw [h, add_comm, ← compl_Iic, integral_add_compl measurableSet_Iic
    (integrable_brownianHeatDensity_sub_const ht a)]
  simpa only [sub_eq_add_neg] using integral_brownianHeatDensity_translate (a := -a) ht

end

/-- A reflected pair of translated heat densities. -/
noncomputable def brownianHeatPair (t a y : ℝ) : ℝ :=
  brownianHeatDensity t (y - a) + brownianHeatDensity t (y + a)

section
variable {t : ℝ} (ht : 0 < t) (a : ℝ)
include ht

theorem integrable_brownianHeatPair :
    Integrable (brownianHeatPair t a) :=
  (integrable_brownianHeatDensity_sub_const ht a).add (integrable_brownianHeatDensity_translate ht a)

theorem integral_brownianHeatPair :
    ∫ y in Ioi 0, brownianHeatPair t a y = 1 := by
  simp only [brownianHeatPair]
  rw [integral_add (integrable_brownianHeatDensity_sub_const ht a).integrableOn
    (integrable_brownianHeatDensity_translate ht a).integrableOn]
  exact integral_brownianHeatDensity_halfline_pair ht

end

end DOZZ.Proofs

end
