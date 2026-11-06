/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Correlations.Tails.ParetoTailError

/-! Higher moments control the excluded and perturbation events in the one-insertion tail
estimate. -/

@[expose] public section
open MeasureTheory

namespace DOZZ.Proofs

theorem power_tail_le_moment
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsFiniteMeasure P]
    (A : Ω → ℝ) (hA0 : ∀ ω, 0 ≤ A ω) (r b : ℝ) (hr : 0 < r) (hb : 0 < b)
    (hAi : Integrable (fun ω => A ω^r) P) :
    (P {ω | b < A ω}).toReal ≤ b^(-r) * ∫ ω, A ω^r ∂P := by
  have hbpow := Real.rpow_pos_of_pos hb r
  have hle : (P {ω | b < A ω}).toReal ≤ (∫ ω, A ω^r ∂P)/(b^r) := by
    apply (le_div_iff₀ hbpow).mpr
    rw [mul_comm]
    exact (mul_le_mul_of_nonneg_left (measureReal_mono (by intro ω hω; exact Real.rpow_le_rpow hb.le hω.le hr.le) (measure_ne_top _ _)) hbpow.le).trans (mul_meas_ge_le_integral_of_nonneg (ae_of_all P fun ω => Real.rpow_nonneg (hA0 ω) r) hAi (b^r))
  exact hle.trans_eq (by rw [Real.rpow_neg hb.le]; ring)


end DOZZ.Proofs
