/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.FourPoint.Dual.IncrementIntegrability
public import Mathlib.Analysis.Convex.Deriv
import Mathlib.Tactic
/-! Relative control of the signed inverse increment under the kernel squeeze factors. -/
@[expose] public section
open Set
namespace DOZZ.Proofs




/-- The literal inner-kernel squeeze gives a relative error in the signed increment,
controlled by the unscaled inverse-power loss. -/
theorem dual_negative_increment_kernel_squeeze (p A t u θlo θhi : ℝ)
    (hp : 0 < p) (hA : 0 < A) (ht : 0 ≤ t) (hlo : 0 ≤ θlo) (hhi : 0 ≤ θhi)
    (hu : θlo*t ≤ u) (hv : u ≤ θhi*t) :
    |((A+u)^(-p)-A^(-p))-((A+t)^(-p)-A^(-p))| ≤
      max |θlo-1| |θhi-1| * (A^(-p)-(A+t)^(-p)) := by
  have dual_negative_increment_relative_scale (θ : ℝ) (hp : 0 < p) (hA : 0 < A) (ht : 0 ≤ t) (hθ : 0 ≤ θ) : |((A+θ*t)^(-p)-A^(-p))-((A+t)^(-p)-A^(-p))| ≤ |θ-1| *(A^(-p)-(A+t)^(-p)) := by
    have dual_inverse_increment_scale_lower t θ (hp : 0 < p) (hA : 0 < A) (ht : 0 ≤ t) (hθ : 0 ≤ θ) (hθ1 : θ ≤ 1) : θ*(A^(-p)-(A+t)^(-p)) ≤ A^(-p)-(A+θ*t)^(-p) := by
      have dual_inverse_increment_concave : ConcaveOn ℝ (Ici 0) (fun t : ℝ => A^(-p)-(A+t)^(-p)) := by
        let g := fun t : ℝ => A^(-p)-(A+t)^(-p)
        have hd t (ht : t ∈ Ici 0) : HasDerivAt g (p*(A+t)^(-p-1)) t := by
          have ht0 : 0 ≤ t := ht
          convert (((Real.hasDerivAt_rpow_const (x := A+t) (p := -p) (Or.inl (by linarith only [hA, ht0]))).comp t ((hasDerivAt_id t).const_add A)).const_sub (A^(-p))) using 1 <;> simp only [g, Function.comp_def, mul_one, neg_mul, neg_neg]
        have hm : AntitoneOn (deriv g) (interior (Ici 0)) := by
          intro x hx y hy hxy
          have hx0 : 0 ≤ x := interior_subset hx
          rw [(hd x hx0).deriv, (hd y (interior_subset hy)).deriv]
          apply mul_le_mul_of_nonneg_left _ hp.le
          exact Real.rpow_le_rpow_of_nonpos (by linarith only [hA, hx0])
            (add_le_add le_rfl hxy) (by linarith only [hp])
        exact hm.concaveOn_of_deriv (convex_Ici 0)
          (fun t ht => (hd t ht).continuousAt.continuousWithinAt)
          (fun t ht => (hd t (interior_subset ht)).differentiableAt.differentiableWithinAt)
      simpa only [smul_eq_mul, mul_zero, zero_add, add_zero, sub_self] using ((dual_inverse_increment_concave).2 (show (0 : ℝ) ∈ Ici 0 from le_rfl) (show t ∈ Ici 0 from ht) (sub_nonneg.mpr hθ1) hθ (by ring : (1-θ)+θ = 1))
    by_cases hθ1 : θ ≤ 1
    · have hlow := dual_inverse_increment_scale_lower t θ hp hA ht hθ hθ1
      rw [abs_of_nonneg (by linarith only [(Real.rpow_le_rpow_of_nonpos (by positivity) (add_le_add le_rfl (mul_le_of_le_one_left ht hθ1)) (neg_nonpos.mpr hp.le) : (A+t)^(-p) ≤ (A+θ*t)^(-p))]), abs_of_nonpos (by linarith only [hθ1])]
      nlinarith only [hlow]
    · have hθpos : 0 < θ := lt_of_lt_of_le zero_lt_one (le_of_not_ge hθ1)
      have hlow := dual_inverse_increment_scale_lower (θ*t) (1/θ) hp hA
        (mul_nonneg hθ ht) (by positivity) ((div_le_one hθpos).mpr (le_of_not_ge hθ1))
      rw [(show (1/θ)*(θ*t) = t by field_simp)] at hlow
      have hscaled := mul_le_mul_of_nonneg_left hlow hθpos.le
      rw [(show θ*(1/θ*(A^(-p)-(A+θ*t)^(-p))) = A^(-p)-(A+θ*t)^(-p) by field_simp)] at hscaled
      rw [abs_of_nonpos (by linarith only [(Real.rpow_le_rpow_of_nonpos (by linarith only [hA, ht]) (add_le_add le_rfl (le_mul_of_one_le_left ht (le_of_not_ge hθ1))) (neg_nonpos.mpr hp.le) : (A+θ*t)^(-p) ≤ (A+t)^(-p))]), abs_of_nonneg (by linarith only [hθpos, hθ1])]
      nlinarith only [hscaled]
  have hLoss : 0 ≤ A^(-p)-(A+t)^(-p) := sub_nonneg.mpr
    (Real.rpow_le_rpow_of_nonpos hA (by linarith only [ht]) (neg_nonpos.mpr hp.le))
  obtain ⟨hHil, _⟩ := abs_le.mp ((dual_negative_increment_relative_scale θhi hp hA ht hhi).trans (mul_le_mul_of_nonneg_right (le_max_right |θlo-1| |θhi-1|) hLoss))
  obtain ⟨_, hLou⟩ := abs_le.mp ((dual_negative_increment_relative_scale θlo hp hA ht hlo).trans (mul_le_mul_of_nonneg_right (le_max_left |θlo-1| |θhi-1|) hLoss))
  exact abs_le.mpr ⟨by linarith only [(by simpa only [one_mul] using dual_negative_increment_antitone p A 1 u (θhi*t) hp.le hA zero_le_one ((mul_nonneg hlo ht).trans hu) hv), hHil], by linarith only [(by simpa only [one_mul] using dual_negative_increment_antitone p A 1 (θlo*t) u hp.le hA zero_le_one (mul_nonneg hlo ht) hu), hLou]⟩

end DOZZ.Proofs
