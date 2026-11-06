/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.FourPoint.Dual.Multipliers
import Mathlib.Tactic

/-! # Gamma recurrence in the first dual coefficient extraction

The first ratio is simplified independently of the second. All divisions are justified on the
strict parameter intervals.
-/

public section

namespace DOZZ.Proofs

/-- The first connection ratio is precisely the literal l-function multiplier. -/
theorem dual_connection_first_multiplier A B c δ
    (hc : 0 < c) (hc₁ : c < 1) (hδ : 0 < δ) (hδ₁ : δ < 1) :
    (-δ / (c - 1)) * (Real.Gamma (2 - c) / Real.Gamma c) *
      (Real.Gamma δ / Real.Gamma (-δ)) * lR A * lR B =
        lR A * lR B / (lR c * lR (-δ)) := by
  have hG1c := (Real.Gamma_pos_of_pos (sub_pos.mpr hc₁)).ne'
  have hGδ := (Real.Gamma_pos_of_pos hδ).ne'
  have hGnegδ : Real.Gamma (-δ) ≠ 0 := Real.Gamma_ne_zero
    (real_ne_neg_nat_of_frac (k := -1) (by push_cast; linarith only [hδ₁])
      (by push_cast; linarith only [hδ]))
  have hrecδ : Real.Gamma (1 - -δ) = δ * Real.Gamma δ := by
    rw [show 1 - -δ = δ + 1 by ring]
    exact Real.Gamma_add_one hδ.ne'
  have hcne : c - 1 ≠ 0 := by linarith only [hc₁]
  unfold lR
  rw [(show Real.Gamma (2 - c) = (1 - c) * Real.Gamma (1 - c) by rw [show 2 - c = (1 - c) + 1 by ring]; exact Real.Gamma_add_one (sub_pos.mpr hc₁).ne'), hrecδ]
  field_simp [((Real.Gamma_pos_of_pos hc).ne'), hG1c, hGδ, hGnegδ, hδ.ne', hcne]
  ring


/-- Reciprocal l-ratios agree even with the totalized convention. -/
theorem dual_lR_one_sub_eq_inv t : lR (1 - t) = (lR t)⁻¹ := by
  unfold lR
  rw [show 1 - (1 - t) = t by ring, inv_div]

/-- The second multiplier uses C₁=1−δ, giving its two denominator arguments. -/
theorem dual_connection_second_multiplier A B c δ
    (hc : 0 < c) (hc₁ : c < 1) (hδ : 0 < δ) (hδ₁ : δ < 1) :
    ((c - 1) / δ) * (Real.Gamma (2 - c) / Real.Gamma c) *
      (Real.Gamma (-δ) / Real.Gamma δ) * lR (c - A) * lR (c - B) =
        lR (-δ) * lR (2 - c) / (lR (1 - c + B) * lR (1 - c + A)) := by
  have dual_connection_second_multiplier_base : ((c - 1) / δ) * (Real.Gamma (2 - c) / Real.Gamma c) * (Real.Gamma (-δ) / Real.Gamma δ) = lR (-δ) * lR (2 - c) := by
    have hGδ := (Real.Gamma_pos_of_pos hδ).ne'
    have hGcm : Real.Gamma (c - 1) ≠ 0 := Real.Gamma_ne_zero
      (real_ne_neg_nat_of_frac (k := -1) (by push_cast; linarith only [hc])
        (by push_cast; linarith only [hc₁]))
    have hrecC : Real.Gamma c = (c - 1) * Real.Gamma (c - 1) := by
      have hr := Real.Gamma_add_one (by linarith only [hc₁] : c - 1 ≠ 0)
      simpa only [sub_add_cancel] using hr
    have hGnegδ : Real.Gamma (-δ) ≠ 0 := Real.Gamma_ne_zero
      (real_ne_neg_nat_of_frac (k := -1) (by push_cast; linarith only [hδ₁])
        (by push_cast; linarith only [hδ]))
    unfold lR
    rw [(show Real.Gamma (1 - -δ) = δ * Real.Gamma δ by rw [show 1 - -δ = δ + 1 by ring]; exact Real.Gamma_add_one hδ.ne'), show 1 - (2 - c) = c - 1 by ring]
    rw [hrecC]
    have hcm : c - 1 ≠ 0 := by linarith only [hc₁]
    field_simp [((Real.Gamma_pos_of_pos hc).ne'), hGδ, hGcm, hδ.ne', hcm, hGnegδ]
  rw [dual_connection_second_multiplier_base]
  rw [show 1 - c + B = 1 - (c - B) by ring,
    show 1 - c + A = 1 - (c - A) by ring,
    dual_lR_one_sub_eq_inv, dual_lR_one_sub_eq_inv]
  simp only [div_eq_mul_inv, mul_inv, inv_inv]
  ring

end DOZZ.Proofs
