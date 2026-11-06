/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GFF.TorusH2Coefficients
public import DOZZ.GFF.TorusPeriodizationCLM

/-!
# DOZZ.GFF.TorusH2CoefficientCLM

The weighted Fourier coefficient map is a continuous linear map on the test-function space. The
weight is realized by applying the torus Laplacian before taking Fourier coefficients, so no
unbounded multiplier is applied to an arbitrary `L²` sequence.
-/

@[expose] public section

open MeasureTheory
open Set Metric
open scoped ENNReal InnerProductSpace Topology lp

namespace DOZZ

/-- The second derivative in one unit-box coordinate, written as a continuous linear operator on
test functions. -/
noncomputable def unitBoxSecondDerivativeCLM (L : ℝ) (v : ℂ) :
    TestFn →L[ℝ] TestFn := by
  let D : TestFn →L[ℝ] TestFn := TestFunction.lineDerivCLM ℝ v
  exact L ^ 2 • (D.comp D)

theorem lineDerivCLM_eq_directionalDerivativeTest f v :
    TestFunction.lineDerivCLM ℝ v f = directionalDerivativeTest f v := by
  ext z
  rw [TestFunction.lineDerivCLM_apply_of_le (by simp : (⊤ : ENat) + 1 ≤ ⊤), directionalDerivativeTest_apply]
  exact ((f.contDiff.differentiable (by simp)).differentiableAt).lineDeriv_eq_fderiv

theorem unitBoxSecondDerivativeCLM_apply L v f :
    unitBoxSecondDerivativeCLM L v f =
      unitBoxDirectionalDerivativeTest L
        (unitBoxDirectionalDerivativeTest L f v) v := by
  let D : TestFn →L[ℝ] TestFn := TestFunction.lineDerivCLM ℝ v
  have hunit g : unitBoxDirectionalDerivativeTest L g v = L • D g := by
    rw [unitBoxDirectionalDerivativeTest, ← lineDerivCLM_eq_directionalDerivativeTest]
  change L ^ 2 • (D (D f)) = _
  calc
    L ^ 2 • (D (D f)) = L • (L • D (D f)) := by
      rw [smul_smul, pow_two]
    _ = L • D (L • D f) := by rw [map_smul]
    _ = L • D (unitBoxDirectionalDerivativeTest L f v) := by rw [hunit]
    _ = unitBoxDirectionalDerivativeTest L (unitBoxDirectionalDerivativeTest L f v) v :=
      (hunit _).symm

/-- The unweighted Fourier coefficient isometrically represented in complex `ℓ²`. -/
noncomputable def torusRawFourierCoeffCLM (L : ℝ) :
  TestFn →L[ℝ] lp (fun _ : Fin 2 → ℤ => ℂ) (2 : ℝ≥0∞) :=
  (ContinuousLinearMap.restrictScalars ℝ
      (((UnitAddTorus.mFourierBasis (d := Fin 2)).repr.toLinearIsometry).toContinuousLinearMap)).comp
    (torusPeriodizationLpCLM L)

@[simp]
theorem torusRawFourierCoeffCLM_apply L f k :
    torusRawFourierCoeffCLM L f k =
      UnitAddTorus.mFourierCoeff (torusPeriodizationLp L f) k := by
  change ((UnitAddTorus.mFourierBasis (d := Fin 2)).repr
    (torusPeriodizationLpCLM L f)) k = _
  rw [torusPeriodizationLpCLM_apply, UnitAddTorus.mFourierBasis_repr]

/-- The weighted complex coefficient `((1 + |k|²) c_k)_k` of a test on the concrete unit torus.
It is continuous in the test-function topology because the weight is represented by the Laplacian.
-/
noncomputable def torusH2WeightedFourierCoeffCLM (L : ℝ) :
    TestFn →L[ℝ] lp (fun _ : Fin 2 → ℤ => ℂ) (2 : ℝ≥0∞) := by
  let raw := torusRawFourierCoeffCLM L
  let c : ℝ := (4 * Real.pi ^ 2)⁻¹
  exact raw - c • (raw.comp (unitBoxSecondDerivativeCLM L 1)) -
    c • (raw.comp (unitBoxSecondDerivativeCLM L Complex.I))

theorem torusH2WeightedFourierCoeffCLM_apply (L R : ℝ) (hL : 0 < L)
    (hRbox : R + 2 < L / 2) (f : TestFn)
    (hf : Function.support f ⊆ ball (0 : ℂ) R) (k : Fin 2 → ℤ) :
    torusH2WeightedFourierCoeffCLM L f k = torusSobolevWeight k •
      UnitAddTorus.mFourierCoeff (torusPeriodizationLp L f) k := by
  let c₀ := UnitAddTorus.mFourierCoeff (torusPeriodizationLp L f) k
  have hD0 : (torusRawFourierCoeffCLM L
      (unitBoxSecondDerivativeCLM L 1 f)) k =
      ((2 * Real.pi * Complex.I * (k 0 : ℝ)) ^ 2) * c₀ := by
    rw [unitBoxSecondDerivativeCLM_apply, torusRawFourierCoeffCLM_apply]
    have hfreq := torusPeriodizationCoeff_unitBoxDirectionalDerivative_twice
      L R hL hRbox f hf 1 k
    rw [(show (innerSL ℝ) (unitTorusFourierFrequency k) (1 : ℂ) = (k 0 : ℝ) by rw [unitTorusFourierFrequency_innerSL]; simp)] at hfreq
    simpa [c₀] using hfreq
  have hD1 : (torusRawFourierCoeffCLM L
      (unitBoxSecondDerivativeCLM L Complex.I f)) k =
      ((2 * Real.pi * Complex.I * (k 1 : ℝ)) ^ 2) * c₀ := by
    rw [unitBoxSecondDerivativeCLM_apply, torusRawFourierCoeffCLM_apply]
    have hfreq := torusPeriodizationCoeff_unitBoxDirectionalDerivative_twice
      L R hL hRbox f hf Complex.I k
    rw [(show (innerSL ℝ) (unitTorusFourierFrequency k) Complex.I = (k 1 : ℝ) by rw [unitTorusFourierFrequency_innerSL]; simp)] at hfreq
    simpa [c₀] using hfreq
  let c := (4 * Real.pi ^ 2)⁻¹
  have hscalar (j : Fin 2) :
      ((c : ℂ) * ((2 * Real.pi * Complex.I * (k j : ℝ)) ^ 2)) =
        -((k j : ℝ) ^ 2 : ℂ) := by
    have hfreq : ((2 * Real.pi * Complex.I * (k j : ℝ)) ^ 2) =
        -((4 * Real.pi ^ 2 * (k j : ℝ) ^ 2 : ℝ) : ℂ) := by
      simp only [mul_pow, Complex.I_sq]
      push_cast
      ring
    rw [hfreq]
    dsimp [c]
    push_cast
    field_simp [(show (4 * Real.pi ^ 2 : ℝ) ≠ 0 by positivity)]
  have hscalar_mul (j : Fin 2) :
      c • (((2 * Real.pi * Complex.I * (k j : ℝ)) ^ 2) * c₀) =
        -((k j : ℝ) ^ 2) • c₀ := by
    rw [Complex.real_smul, ← mul_assoc, hscalar]
    simp [Complex.real_smul]
  change (torusRawFourierCoeffCLM L f -
      (4 * Real.pi ^ 2)⁻¹ •
        torusRawFourierCoeffCLM L (unitBoxSecondDerivativeCLM L 1 f) -
      (4 * Real.pi ^ 2)⁻¹ •
        torusRawFourierCoeffCLM L (unitBoxSecondDerivativeCLM L Complex.I f)) k = _
  simp only [lp.coeFn_sub, lp.coeFn_smul]
  change (torusRawFourierCoeffCLM L f) k -
      (4 * Real.pi ^ 2)⁻¹ •
        (torusRawFourierCoeffCLM L (unitBoxSecondDerivativeCLM L 1 f)) k -
      (4 * Real.pi ^ 2)⁻¹ •
        (torusRawFourierCoeffCLM L (unitBoxSecondDerivativeCLM L Complex.I f)) k = _
  rw [(torusRawFourierCoeffCLM_apply L f k : (torusRawFourierCoeffCLM L f) k = c₀), hD0, hD1, hscalar_mul 0, hscalar_mul 1]
  simp [c₀, torusSobolevWeight, sub_eq_add_neg, add_smul]

end DOZZ

end
