/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Correlations.Tails.WilliamsSplitValue
public import DOZZ.Statements.Brownian.TwoSidedReflectionCutMass

/-! Exact maximum splitting of the inward Brownian polar exponential integral. -/

@[expose] public section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace DOZZ.Proofs

/-- Retain a stopped negative half and the complete positive half above the marked lifetime. -/
noncomputable def stoppedReflectionMass (γ : ℝ) (τ : ℝ≥0)
    (B : BrownianPath × BrownianPath) (Z : Measure ℝ) : ℝ≥0∞ :=
  ∫⁻ s, (if -(τ : ℝ) ≤ s then ENNReal.ofReal
    (Real.exp (γ * twoSidedConditionedValue (fun _ : Unit => B) () s)) else 0) ∂Z

/-- Stopping the negative half at its last exit leaves the retained reflection mass unchanged.
This connects the lifetime-marked Williams law to the literal last-cut mass
`DOZZ.twoSidedReflectionCutMass`. -/
theorem stopped_reflection_mass_lastExit
    (γ c : ℝ) (qplus qminus : BrownianPath) (Z : Measure ℝ) :
    stoppedReflectionMass γ (negativeLastExitTime qminus c)
      (qplus, stopBrownianPath qminus (negativeLastExitTime qminus c)) Z =
        twoSidedReflectionCutMass γ c (fun _ : Unit => (qplus,qminus))
          (fun _ : Unit => Z) () := by
  apply lintegral_congr
  intro s
  by_cases hcut : -(negativeLastExitTime qminus c) ≤ s
  · rw [ite_eq_left hcut, ite_eq_left hcut]
    congr 2
    by_cases hs : 0 ≤ s
    · rw [twoSidedConditionedValue, dite_eq_left hs,
        twoSidedConditionedValue, dite_eq_left hs]
    · have hnn := neg_nonneg.mpr (le_of_not_ge hs)
      have hle : NNReal.mk (-s) hnn ≤ negativeLastExitTime qminus c := by
        rw [← NNReal.coe_le_coe, NNReal.coe_mk]
        linarith
      rw [twoSidedConditionedValue, dite_eq_right hs,
        twoSidedConditionedValue, dite_eq_right hs]
      change γ * qminus (min (NNReal.mk (-s) hnn) (negativeLastExitTime qminus c)) =
        γ * qminus (NNReal.mk (-s) hnn)
      simp_all
  grind

/-- The polar integral is the exponential maximum times the mass of the maximum-centered
split, truncated by its actual pre-maximum lifetime. Only the deterministic zero atom of the
lateral measure is removed; there is no stopping or restart at a last exit in this identity. -/
theorem williams_polar_split (γ ν : ℝ) (p : BrownianPath)
    (Z : Measure ℝ) (hZ0 : Z {0} = 0) :
    (∫⁻ t, (if 0 < t then ENNReal.ofReal
      (Real.exp (γ * (p (Real.toNNReal t) - ν * t))) else 0) ∂Z) =
      ENNReal.ofReal (Real.exp (γ * driftedBrownianMaximum ν p)) *
        stoppedReflectionMass γ (driftedBrownianMaximumTime ν p)
          (williamsSplitPaths ν p)
          (Z.map (fun s => s - (driftedBrownianMaximumTime ν p : ℝ))) := by
  let σ := driftedBrownianMaximumTime ν p
  let B := williamsSplitPaths ν p
  let m := driftedBrownianMaximum ν p
  have hf : Measurable (fun s => if -(σ : ℝ) ≤ s then ENNReal.ofReal
      (Real.exp (γ * twoSidedConditionedValue (fun _ => B) () s)) else 0) :=
    Measurable.ite measurableSet_Ici
      ((measurable_twoSidedConditionedValue (fun _ => B) ()).const_mul γ).exp.ennreal_ofReal
      measurable_const
  change _ = ENNReal.ofReal _ * ∫⁻ s,
    (if -(σ : ℝ) ≤ s then ENNReal.ofReal
      (Real.exp (γ * twoSidedConditionedValue (fun _ => B) () s)) else 0)
        ∂Z.map (fun s => s - (σ : ℝ))
  have hshift : Measurable (fun s => s - (σ : ℝ)) := by fun_prop
  rw [lintegral_map hf hshift,
    ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply lintegral_congr_ae
  have hne : ∀ᵐ t ∂Z, t ≠ 0 := by
    rw [ae_iff]
    simp_all
  filter_upwards [hne] with t ht0
  by_cases ht : 0 < t
  · have hcut : -(σ : ℝ) ≤ t - (σ : ℝ) := by linarith only [ht]
    simp only [ite_eq_left ht, ite_eq_left hcut]
    have hvalue := williams_split_value ν p (Real.toNNReal t)
    rw [Real.coe_toNNReal t ht.le] at hvalue
    change twoSidedConditionedValue (fun _ : Unit => B) () (t - (σ : ℝ)) =
      p (Real.toNNReal t) - ν * t - m at hvalue
    rw [hvalue, ← ENNReal.ofReal_mul (Real.exp_nonneg _), ← Real.exp_add]
    grind
  grind


end DOZZ.Proofs
