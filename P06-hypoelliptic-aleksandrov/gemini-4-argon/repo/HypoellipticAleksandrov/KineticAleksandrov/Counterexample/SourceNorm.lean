module

public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.ShellSource
public import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator
import Mathlib.Tactic.Linarith

/-! # The radius-uniform subcritical source norm -/

@[expose] public section

namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample

open MeasureTheory Set

/- The norm of a measurable nonnegative source supported on a finite-volume shell. -/
theorem eLpNorm_le_shell_bound {d } (f : XV d → ℝ) (S : Set (XV d))
    (p B : ℝ) (hp : 0 < p) (hB : 0 ≤ B) (hf : AEStronglyMeasurable f volume)
    (hS : MeasurableSet S) (hbound : ∀ q, 0 ≤ f q ∧ f q ≤ B)
    (hsupp : ∀ q, q ∉ S → f q = 0) :
    eLpNorm f (ENNReal.ofReal p) volume ≤ ENNReal.ofReal B * volume S ^ (1 / p) := by
  have hm : ∀ᵐ q ∂volume, ‖f q‖ ≤ ‖S.indicator (fun _ => B) q‖ := by
    filter_upwards [] with q
    by_cases hq : q ∈ S
    · rw [indicator_of_mem hq, Real.norm_eq_abs, abs_of_nonneg (hbound q).1,
        Real.norm_eq_abs, abs_of_nonneg hB]
      exact (hbound q).2
    · rw [hsupp q hq, indicator_of_notMem hq]
  apply (eLpNorm_mono_ae hf hm).trans_eq
  rw [eLpNorm_indicator_const hS.nullMeasurableSet (ENNReal.ofReal_ne_zero_iff.mpr hp)
    ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal hp.le]
  rw [← ofReal_norm, Real.norm_eq_abs, abs_of_nonneg hB]

/- The shell norm powers combine to the precise source exponent. -/
end HypoellipticAleksandrov.KineticAleksandrov.Counterexample
