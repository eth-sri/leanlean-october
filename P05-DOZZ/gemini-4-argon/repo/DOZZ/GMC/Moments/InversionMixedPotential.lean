/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GMC.Moments.InversionAdmissible
public import DOZZ.GMC.CirclePotential

/-! Exact mixed circle potentials for the inverted local field. -/

@[expose] public section

open MeasureTheory
open Set Metric Real
namespace DOZZ.Proofs

open CirclePotential


/-- Averaging the source field over an ordinary source circle, then evaluating at an inverted
point, gives a clipped target logarithm with scale `exp (-s) * ‖x‖ * ‖y‖`. The remainder is
exactly the pinning potential averaged on the source circle. -/
theorem inversion_innerPot_eq {x y} (hx : x ≠ 0) (hy : y ≠ 0) s :
    innerPot y⁻¹ s x⁻¹ =
      -Real.log (max ‖x - y‖ (Real.exp (-s) * (‖x‖ * ‖y‖))) +
        Real.log (normPlus x) + Real.log (normPlus y) +
          (regAvg y⁻¹ s - Real.log (normPlus y⁻¹)) := by
  have hxN := norm_pos_iff.mpr hx
  have hyN := norm_pos_iff.mpr hy
  have hc := mul_pos hxN hyN
  have hmax : max (‖x - y‖ / (‖x‖ * ‖y‖)) (Real.exp (-s)) =
      max ‖x - y‖ (Real.exp (-s) * (‖x‖ * ‖y‖)) / (‖x‖ * ‖y‖) := by
    rw [← max_div_div_right hc.le]
    congr 1
    field_simp
  unfold innerPot
  rw [complexInv_distance_of_ne_zero hx hy, hmax,
    Real.log_div (lt_of_lt_of_le (mul_pos (Real.exp_pos _) hc) (le_max_right _ _) : 0 < max ‖x - y‖ (Real.exp (-s) * (‖x‖ * ‖y‖))).ne' hc.ne', Real.log_mul hxN.ne' hyN.ne',
    normPlus_inv_identity hx, normPlus_inv_identity hy,
    Real.log_div (lt_of_lt_of_le one_pos (le_max_left _ _) : 0 < normPlus x).ne' hxN.ne', Real.log_div (lt_of_lt_of_le one_pos (le_max_left _ _) : 0 < normPlus y).ne' hyN.ne']
  ring





/-- A uniform pointwise error on a circle bounds the difference of its two averages. -/
theorem abs_circleAverage_sub_circleAverage_le {f g : ℂ → ℝ} {x} {ε C}
    (hf : CircleIntegrable f x ε) (hg : CircleIntegrable g x ε)
    (hbound : ∀ u ∈ sphere x |ε|, |f u - g u| ≤ C) :
    |circleAverage f x ε - circleAverage g x ε| ≤ C := by
  rw [← circleAverage_fun_sub hf hg, abs_le]
  constructor
  · have h := circleAverage_mono (circleIntegrable_const (-C) x ε) (hf.sub hg)
      (fun u hu => (abs_le.mp (hbound u hu)).1)
    rw [circleAverage_const] at h
    exact h
  · exact circleAverage_mono_on_of_le_circle (hf.sub hg)
      (fun u hu => (abs_le.mp (hbound u hu)).2)

/-- The separated mixed covariance estimate after averaging in the target variable. This is
the ordinary-target-circle versus pulled-source-circle estimate used in compatibility. -/
theorem inversion_circleAverage_mixed_offDiagonal_le {x y} {ε}
    (hy : y ≠ 0) (hε : 0 < ε) (hεx : ε < ‖x‖) s
    (hsep : Real.exp (-s) * ((‖x‖ + ε) * ‖y‖) ≤ ‖x - y‖ - ε) :
    |circleAverage (fun u => innerPot y⁻¹ s u⁻¹) x ε -
      circleAverage (fun u => gffKernel u y) x ε| ≤ Real.exp (-s) := by
  have inversion_innerPot_sub_gffKernel_le {x} {y} (hx : x ≠ 0) (hy : y ≠ 0) s (hsep : Real.exp (-s) * (‖x‖ * ‖y‖) ≤ ‖x - y‖) : |innerPot y⁻¹ s x⁻¹ - gffKernel x y| ≤ Real.exp (-s) := by
    simpa only [max_eq_left hsep, gffKernel] using ((show |innerPot y⁻¹ s x⁻¹ - (-Real.log (max ‖x - y‖ (Real.exp (-s) * (‖x‖ * ‖y‖))) + Real.log (normPlus x) + Real.log (normPlus y))| ≤ Real.exp (-s) by rw [inversion_innerPot_eq hx hy s]; simpa only [add_sub_cancel_left, regAvg] using abs_circleAverage_log_normPlus_sub_le y⁻¹ (Real.exp_pos (-s))))
  have hU : sphere x |ε| ⊆ ({0} : Set ℂ)ᶜ := by
    intro u hu
    change u ≠ 0
    intro hu0
    have : ‖x‖ = ε := by simpa [hu0] using (show ‖u - x‖ = ε by simpa only [mem_sphere_iff_norm, abs_of_pos hε] using hu)
    linarith
  apply abs_circleAverage_sub_circleAverage_le (((continuous_innerPot y⁻¹ s).comp_continuousOn (continuousOn_inv₀.mono hU)).circleIntegrable') (by exact ((circleIntegrable_log_norm_sub_const ε).neg.add continuous_log_normPlus.continuousOn.circleIntegrable').add (circleIntegrable_const (Real.log (normPlus y)) x ε))
  intro u hu
  have hux : ‖u - x‖ = ε := by
    simpa only [mem_sphere_iff_norm, abs_of_pos hε] using hu
  have hudist : ‖x - y‖ - ε ≤ ‖u - y‖ := by
    have h := norm_sub_le_norm_sub_add_norm_sub x u y
    rw [norm_sub_rev x u, hux] at h
    linarith
  apply inversion_innerPot_sub_gffKernel_le (hU hu) hy s
  calc
    Real.exp (-s) * (‖u‖ * ‖y‖) ≤
        Real.exp (-s) * ((‖x‖ + ε) * ‖y‖) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (by simpa only [add_sub_cancel, hux] using (norm_add_le x (u - x))) (norm_nonneg _))
        (Real.exp_pos _).le
    _ ≤ ‖u - y‖ := hsep.trans hudist

/-- Mixed ordinary-target/pulled-source circle potentials satisfy the same logarithmic bound,
including coincident centers. Bounds on the logarithmic norms encode a compact punctured chart.
-/
theorem inversion_circleAverage_mixed_log_bound
    {x y} {R B r s} (hR : 0 ≤ R) (hxR : ‖x‖ ≤ R) (hyR : ‖y‖ ≤ R)
    (hr : 0 ≤ r) (hs : 0 ≤ s) (hy : y ≠ 0) (hylog : |Real.log ‖y‖| ≤ B)
    (hcircle : ∀ u ∈ sphere x (Real.exp (-r)),
      u ≠ 0 ∧ |Real.log ‖u‖| ≤ B) :
    |circleAverage (fun u => innerPot y⁻¹ s u⁻¹) x (Real.exp (-r)) -
      Real.log (1 / max ‖x - y‖ (max (Real.exp (-r)) (Real.exp (-s))))| ≤
      (2 * B + 2) + (Real.log 3 + 2 * Real.log (1 + R)) := by
  have inversion_innerPot_sub_innerPot_le {x} {y} (hx : x ≠ 0) (hy : y ≠ 0) s : |innerPot y⁻¹ s x⁻¹ - innerPot y s x| ≤ |Real.log (‖x‖ * ‖y‖)| + 2 * Real.exp (-s) := by
    have inversion_logmax_mul_scale_bound {q} {t} {c} (hq : 0 ≤ q) (ht : 0 < t) (hc : 0 < c) : |Real.log (max q (t * c)) - Real.log (max q t)| ≤ |Real.log c| := by
      by_cases hq0 : q = 0
      · rw [hq0, max_eq_right (mul_pos ht hc).le, max_eq_right ht.le,
          Real.log_mul ht.ne' hc.ne']
        simp
      · have hqpos : 0 < q := lt_of_le_of_ne hq (Ne.symm hq0)
        simpa only [div_inv_eq_mul, max_comm, Real.log_inv, abs_neg] using (inversion_logmax_div_scale_bound ht.le hqpos (inv_pos.mpr hc))
    rw [inversion_innerPot_eq hx hy s]
    unfold innerPot
    rw [(show -Real.log (max ‖x - y‖ (Real.exp (-s) * (‖x‖ * ‖y‖))) + Real.log (normPlus x) + Real.log (normPlus y) + (regAvg y⁻¹ s - Real.log (normPlus y⁻¹)) - (-Real.log (max ‖x - y‖ (Real.exp (-s))) + Real.log (normPlus x) + regAvg y s) = -(Real.log (max ‖x - y‖ (Real.exp (-s) * (‖x‖ * ‖y‖))) - Real.log (max ‖x - y‖ (Real.exp (-s)))) + (regAvg y⁻¹ s - Real.log (normPlus y⁻¹)) - (regAvg y s - Real.log (normPlus y)) by ring)]
    calc
      _ ≤ |-(Real.log (max ‖x - y‖ (Real.exp (-s) * (‖x‖ * ‖y‖))) -
          Real.log (max ‖x - y‖ (Real.exp (-s)))) +
          (regAvg y⁻¹ s - Real.log (normPlus y⁻¹))| +
          |regAvg y s - Real.log (normPlus y)| := by
        simpa only [Real.norm_eq_abs] using norm_sub_le
          (-(Real.log (max ‖x - y‖ (Real.exp (-s) * (‖x‖ * ‖y‖))) -
            Real.log (max ‖x - y‖ (Real.exp (-s)))) +
            (regAvg y⁻¹ s - Real.log (normPlus y⁻¹)))
          (regAvg y s - Real.log (normPlus y))
      _ ≤ |Real.log (max ‖x - y‖ (Real.exp (-s) * (‖x‖ * ‖y‖))) -
          Real.log (max ‖x - y‖ (Real.exp (-s)))| +
          |regAvg y⁻¹ s - Real.log (normPlus y⁻¹)| +
          |regAvg y s - Real.log (normPlus y)| := by
        apply add_le_add _ le_rfl
        simpa only [abs_neg] using abs_add_le
          (-(Real.log (max ‖x - y‖ (Real.exp (-s) * (‖x‖ * ‖y‖))) -
            Real.log (max ‖x - y‖ (Real.exp (-s)))))
          (regAvg y⁻¹ s - Real.log (normPlus y⁻¹))
      _ ≤ |Real.log (‖x‖ * ‖y‖)| + Real.exp (-s) + Real.exp (-s) :=
        add_le_add (add_le_add (inversion_logmax_mul_scale_bound (norm_nonneg (x - y)) (Real.exp_pos (-s)) (mul_pos (norm_pos_iff.mpr hx) (norm_pos_iff.mpr hy))) (abs_circleAverage_log_normPlus_sub_le y⁻¹ (Real.exp_pos (-s)))) (abs_circleAverage_log_normPlus_sub_le y (Real.exp_pos (-s)))
      _ = _ := by ring
  have hcomp : |circleAverage (fun u => innerPot y⁻¹ s u⁻¹) x (Real.exp (-r)) -
      circleAverage (innerPot y s) x (Real.exp (-r))| ≤ 2 * B + 2 := by
    apply abs_circleAverage_sub_circleAverage_le (((continuous_innerPot y⁻¹ s).comp_continuousOn (continuousOn_inv₀.mono (by intro u hu; exact (hcircle u (by simpa only [abs_of_pos (Real.exp_pos _)] using hu)).1))).circleIntegrable')
      (continuous_innerPot y s).continuousOn.circleIntegrable'
    intro u hu
    obtain ⟨hu0, hulog⟩ := hcircle u (by
      simpa only [abs_of_pos (Real.exp_pos _)] using hu)
    have : |Real.log (‖u‖ * ‖y‖)| ≤ 2 * B := by
      rw [Real.log_mul (norm_ne_zero_iff.mpr hu0) (norm_ne_zero_iff.mpr hy)]
      exact (abs_add_le _ _).trans (by linarith)
    have hexp : Real.exp (-s) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    exact (inversion_innerPot_sub_innerPot_le hu0 hy s).trans (by linarith)
  have hstandard := abs_circleKernel_sub_log_le R hR x y hxR hyR r s hr hs
  rw [circleKernel_eq] at hstandard
  exact (abs_sub_le (circleAverage (fun u => innerPot y⁻¹ s u⁻¹) x (Real.exp (-r))) (circleAverage (innerPot y s) x (Real.exp (-r))) (Real.log (1 / max ‖x - y‖ (max (Real.exp (-r)) (Real.exp (-s)))))).trans (add_le_add hcomp hstandard)

end DOZZ.Proofs
