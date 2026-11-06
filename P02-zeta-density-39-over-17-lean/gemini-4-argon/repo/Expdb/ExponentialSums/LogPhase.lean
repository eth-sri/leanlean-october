module

public import Expdb.ExponentialSums.PhaseFunctions
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Order.Interval.Finset.Nat

import Mathlib.Analysis.Fourier.FourierTransformDeriv
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# The logarithmic phase

Reusable facts about the logarithmic model phase, including its derivatives, separation on
dyadic intervals, and the explicit main term of its oscillatory integral.
-/

@[expose] public section

open Filter Topology
open scoped ContDiff Expdb FourierTransform

noncomputable section

namespace Expdb

/-- The fixed logarithmic phase `u ↦ log u`, regarded as a variable family. -/
def logPhase : VariableFunction (VariableObject.fixed ℝ) ℝ :=
  fun _ ↦ Real.log

/-- The derivatives of `log` on the phase interval agree with the reference derivatives for
model exponent one. -/
theorem iteratedDerivWithin_log_eq_rpow_neg_one
    (p : ℕ) (u : phaseInterval) :
    iteratedDerivWithin (p + 1) Real.log phaseInterval u =
      iteratedDerivWithin p (modelPhase 1) phaseInterval u := by
  have hu_pos : 0 < (u : ℝ) := lt_of_lt_of_le zero_lt_one u.property.1
  rw [show modelPhase 1 = fun v : ℝ ↦ v ^ (-(1 : ℝ)) from rfl]
  have hunique : UniqueDiffOn ℝ phaseInterval :=
    uniqueDiffOn_Icc (by norm_num [phaseInterval])
  rw [iteratedDerivWithin_eq_iteratedDeriv hunique
      (Real.contDiffAt_log.2 hu_pos.ne') u.property,
    iteratedDerivWithin_eq_iteratedDeriv hunique
      (Real.contDiffAt_rpow_const_of_ne hu_pos.ne') u.property,
    iteratedDeriv_succ', Real.deriv_log']
  congr 1
  funext v
  exact (Real.rpow_neg_one v).symm

/-- The fixed logarithmic phase `u ↦ log u` is a model phase function, with model exponent
`σ = 1`. -/
theorem isModelPhaseFunction_log : IsModelPhaseFunction logPhase := by
  refine ⟨?_, 1, zero_lt_one, ?_⟩
  · intro i
    change ContDiffOn ℝ ∞ Real.log phaseInterval
    exact Real.contDiffOn_log.mono fun u hu ↦ by
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      exact ne_of_gt (lt_of_lt_of_le zero_lt_one hu.1)
  · intro p u
    rw [VariableObject.IsInfinitesimal]
    simp only [modelPhaseError_apply, modelPhaseErrorAt, logPhase,
      iteratedDerivWithin_log_eq_rpow_neg_one, sub_self, norm_zero]
    exact tendsto_const_nhds


