/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic

/-! Converting finite nonnegative moments to signed real expectations. -/
public section
open MeasureTheory
open scoped ENNReal
namespace DOZZ.Proofs

/-- A finite extended-real moment supplies both real integrability and its expectation. -/
theorem real_moment_of_finite {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {f : Ω → ℝ≥0∞} (hm : AEMeasurable f P) (hf : (∫⁻ ω, f ω ∂P) ≠ ⊤) :
    Integrable (fun ω => (f ω).toReal) P ∧
      (∫ ω, (f ω).toReal ∂P) = (∫⁻ ω, f ω ∂P).toReal :=
  ⟨integrable_toReal_of_lintegral_ne_top hm hf, integral_toReal hm (ae_lt_top' hm hf)⟩

/-- The same conversion for an arbitrary real power weight. -/
theorem weighted_real_moment_of_finite {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {A : Ω → ℝ≥0∞} {b : Ω → ℝ} {s q : ℝ}
    (hAm : AEMeasurable A P) (hbm : AEMeasurable b P) (hb : ∀ ω, 0 ≤ b ω)
    (hf : (∫⁻ ω, ENNReal.ofReal ((b ω)^s)*A ω ^q ∂P) ≠ ⊤) :
    Integrable (fun ω => (b ω)^s*(A ω).toReal ^q) P ∧
      (∫ ω, (b ω)^s*(A ω).toReal ^q ∂P) =
        (∫⁻ ω, ENNReal.ofReal ((b ω)^s)*A ω ^q ∂P).toReal := by
  simpa only [Pi.mul_apply, ENNReal.toReal_mul, ENNReal.toReal_rpow,
    ENNReal.toReal_ofReal (Real.rpow_nonneg (hb _) _)] using
    real_moment_of_finite ((hbm.pow_const s).ennreal_ofReal.mul (hAm.pow_const q)) hf

end DOZZ.Proofs
