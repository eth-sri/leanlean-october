/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.FourPoint.Reflected.MaximumBufferError
import Mathlib.Tactic
/-! Signed inverse-power bounds for the last-cut Williams mass. -/
@[expose] public section
namespace DOZZ.Proofs

/-- The Williams increment lies between the full-mass increment and the fixed-cut
increment, with an explicit first-order correction for a bounded maximum. -/
theorem reflected_williams_increment_squeeze (p A b γ H m J K j : ℝ)
    (hp : 0 < p) (hA : 0 < A) (hb : 0 ≤ b) (hγ : 0 ≤ γ)
    (hj : 0 ≤ j) (hjJ : j ≤ J) (hK : 0 ≤ K) (hKJ : K ≤ J)
    (hcut : H < m → K ≤ j) :
    (A+b*Real.exp (γ*m)*J)^(-p)-A^(-p) ≤
      (A+b*Real.exp (γ*m)*j)^(-p)-A^(-p) ∧
    (A+b*Real.exp (γ*m)*j)^(-p)-A^(-p) ≤
      (A+b*Real.exp (γ*m)*K)^(-p)-A^(-p)+
        p*A^(-p-1)*b*Real.exp (γ*H)*J := by
  have hbe : 0 ≤ b*Real.exp (γ*m) := by positivity
  have := hj.trans hjJ
  constructor
  · exact sub_le_sub_right (Real.rpow_le_rpow_of_nonpos (add_pos_of_pos_of_nonneg hA (mul_nonneg hbe hj))
      (add_le_add_right (mul_le_mul_of_nonneg_left hjJ hbe) A) (neg_nonpos.mpr hp.le)) _
  · by_cases hm : m ≤ H
    · have hjneg : (A+b*Real.exp (γ*m)*j)^(-p)-A^(-p) ≤ 0 :=
        sub_nonpos.mpr (Real.rpow_le_rpow_of_nonpos hA
          (le_add_of_nonneg_right (mul_nonneg hbe hj)) (neg_nonpos.mpr hp.le))
      exact hjneg.trans (by linarith only [(reflected_bounded_maximum_increment_bound p A b γ H m J K hp hA hb hγ hm hK hKJ),(neg_le_abs ((A+b*Real.exp (γ*m)*K)^(-p)-A^(-p)))])
    · have hKj := hcut (lt_of_not_ge hm)
      exact (sub_le_sub_right (Real.rpow_le_rpow_of_nonpos (add_pos_of_pos_of_nonneg hA (mul_nonneg hbe hK)) (add_le_add_right (mul_le_mul_of_nonneg_left hKj hbe) A) (neg_nonpos.mpr hp.le)) (A^(-p))).trans (le_add_of_nonneg_right (by positivity))

end DOZZ.Proofs
