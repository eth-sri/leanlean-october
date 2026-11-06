/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Correlations.Tails.OffCenterCircleLaw
public import DOZZ.Correlations.Tails.GaussianPinCopy
public import DOZZ.Correlations.Tails.PinPotential

/-! The independent pin copy for the actual translated circle field.
The correction vanishes to first order at the insertion center. -/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace DOZZ.Proofs


/-- The unshifted local circle variance retains the exact exterior normalization. -/
theorem offCenter_circle_self_covariance
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) X
    Xc (hX : IsEquatorGFF P X) (hc : IsCircleAverage P X Xc)
    z (hz : 2 ≤ ‖z‖) (p : localCircle) :
    covariance (fun ω => Xc ω (z + p.val.1) p.val.2)
      (fun ω => Xc ω (z + p.val.1) p.val.2) P =
        p.val.2 + 2 * Real.log ‖z + p.val.1‖ := by
  rw [circleAverage_covariance P X Xc hX hc]
  simp only [sub_self, nnnorm_zero, circleLogPotential_zero, max_self, Real.log_exp,
    neg_neg, (circle_pin_exterior (z + p.val.1) p.val.2 (localCircle_exterior z hz p))]
  ring

/-- Pointwise regression coefficient of the residual local field on the equator pin. -/
noncomputable def localPinCoefficient (z x : ℂ) : ℝ :=
  (Real.log ‖z + x‖ - Real.log ‖z‖) / (2 * Real.log ‖z‖)

/-- Uniform first-order bound on the regression coefficient. -/
theorem local_pin_coefficient_bound z x
    (hz : 2 ≤ ‖z‖) (hx : ‖x‖ ≤ 1) :
    |localPinCoefficient z x| ≤ ‖x‖ / (2 * Real.log ‖z‖) := by
  unfold localPinCoefficient
  rw [abs_div, abs_of_pos (offCenter_pin_variance_pos z hz)]
  exact div_le_div_of_nonneg_right (offCenter_pin_potential_bound z x hz hx)
    (offCenter_pin_variance_pos z hz).le

/-- Original translated circles and their pin have the same whole law after replacing
that pin by a copy and retaining the explicit small spatial correction. -/
theorem offCenter_circle_pin_copy_law
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) X
    Xc (hX : IsEquatorGFF P X) (hc : IsCircleAverage P X Xc)
    (hm : Measurable (fun q : Ω × (ℂ × ℝ) => Xc q.1 q.2.1 q.2.2))
    z (hz : 2 ≤ ‖z‖) :
    P.map (fun ω (j : Option localCircle) => j.elim (Xc ω z 0)
      (fun p => Xc ω (z + p.val.1) p.val.2)) =
    (P.prod P).map (fun q (j : Option localCircle) => j.elim (Xc q.2 z 0)
      (fun p => Xc q.2 z 0 + (Xc q.1 (z + p.val.1) p.val.2 - Xc q.1 z 0) +
        localPinCoefficient z p.val.1 * (Xc q.2 z 0 - Xc q.1 z 0))) := by
  have offCenter_circle_pin_covariance (p : localCircle) : covariance (fun ω => Xc ω (z + p.val.1) p.val.2) (fun ω => Xc ω z 0) P = Real.log ‖z + p.val.1‖ + Real.log ‖z‖ := by
    have hzpin := circle_pin_exterior z 0
      (by simpa only [neg_zero, Real.exp_zero, one_add_one_eq_two] using hz)
    rw [circleAverage_covariance P X Xc hX hc]
    simp only [add_sub_cancel_left, neg_zero, Real.exp_zero] at hzpin ⊢
    rw [(show circleLogPotential ‖p.val.1‖₊ ⟨Real.exp (-p.val.2), Real.exp_pos _⟩ ⟨1, by norm_num⟩ = 0 by simpa only [Real.log_one] using circleLogPotential_of_add_le (d := ‖p.val.1‖₊) ⟨Real.exp (-p.val.2), Real.exp_pos _⟩ ⟨1, by norm_num⟩ p.property), (circle_pin_exterior (z + p.val.1) p.val.2 (localCircle_exterior z hz p)), hzpin]
    ring
  let k : Option localCircle → ℂ × ℝ := fun j =>
    j.elim (z, 0) (fun p => (z + p.val.1, p.val.2))
  let Z : Option localCircle → Ω → ℝ := fun j ω => Xc ω (k j).1 (k j).2
  rw [← (show (fun ω j => Z j ω) = (fun ω (j : Option localCircle) => j.elim (Xc ω z 0) (fun p => Xc ω (z + p.val.1) p.val.2)) by funext ω j; cases j <;> rfl), (gaussian_pin_copy_law P Z ((circleAverage_isGaussianProcess P X Xc hX hc).1.comp_right k) (by apply measurable_pi_iff.mpr; intro j; exact hm.comp (measurable_id.prodMk measurable_const)) (2 * Real.log ‖z‖) (offCenter_pin_variance_pos z hz).ne' (offCenter_origin_variance X Xc hX hc z hz))]
  congr 1
  funext q j
  cases j with
  | none => rfl
  | some p =>
    change Xc q.1 (z + p.val.1) p.val.2 +
      covariance (fun ω => Xc ω (z + p.val.1) p.val.2) (fun ω => Xc ω z 0) P /
        (2 * Real.log ‖z‖) * (Xc q.2 z 0 - Xc q.1 z 0) = _
    rw [offCenter_circle_pin_covariance p]
    simp only [Option.elim_some]
    unfold localPinCoefficient
    field_simp [(offCenter_pin_variance_pos z hz).ne',
      (Real.log_pos (by linarith : 1 < ‖z‖)).ne']
    ring


end DOZZ.Proofs
