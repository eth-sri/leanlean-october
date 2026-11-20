/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.GMC.GaussianCovariance

/-! The definition `DOZZ.gaussianVariance`. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace Set
open scoped Distributions ENNReal NNReal

namespace DOZZ

/-- The variance of a centered square-integrable real random variable. See [KRV, Theorem 12.1]. -/
noncomputable def gaussianVariance {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (Z : Ω → ℝ) : ℝ :=
  gaussianCovariance P Z Z

section
variable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)

theorem gaussianCovariance_const_mul_right
    (Y Z : Ω → ℝ) (c : ℝ) :
    gaussianCovariance P Y (fun ω => c * Z ω) = c * gaussianCovariance P Y Z := by
  simp only [gaussianCovariance, ← integral_const_mul]
  congr 1
  ext ω
  ring

theorem gaussianVariance_const_mul
    (Z : Ω → ℝ) (c : ℝ) :
    gaussianVariance P (fun ω => c * Z ω) = c ^ 2 * gaussianVariance P Z := by
  simp only [gaussianVariance, gaussianCovariance, ← integral_const_mul]
  congr 1
  ext ω
  ring

end

end DOZZ
