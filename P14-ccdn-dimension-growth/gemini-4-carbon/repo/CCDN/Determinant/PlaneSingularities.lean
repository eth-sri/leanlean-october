/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import Mathlib.Algebra.MvPolynomial.PDeriv
import CCDN.Algebra.CharZeroOrGT
import CCDN.ForMathlib.MvPolynomialDerivative
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors

/-! The singular-point correction in the finite-field curve estimate. The
remaining estimate for all nonsingular rational points is not asserted here. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

/-- A partial derivative lowers the total degree by at least one. -/
theorem pderiv_totalDegree_le {K σ : Type*} [Field K]
    (f : MvPolynomial σ K) (i : σ) : (pderiv i f).totalDegree ≤ f.totalDegree - 1 := by
  classical
  apply Finset.sup_le
  intro m hm
  have hcoeff : f.coeff (m + Finsupp.single i 1) ≠ 0 := by
    have h := mem_support_iff.mp hm
    rw [coeff_pderiv] at h
    exact left_ne_zero_of_mul h
  have hd := le_totalDegree (mem_support_iff.mpr hcoeff)
  have he : (m + Finsupp.single i 1).sum (fun _ e => e) = m.sum (fun _ e => e) + 1 := by
    rw [Finsupp.sum_add_index (by simp) (by intros; rfl)]
    simp
  rw [he] at hd
  omega

/-- A nonzero polynomial does not divide any of its nonzero partial derivatives, since these
have smaller total degree. -/
theorem not_dvd_pderiv_of_pderiv_ne_zero {K σ : Type*} [Field K]
    {f : MvPolynomial σ K} (hf : f ≠ 0) {i : σ} (hi : pderiv i f ≠ 0) : ¬ f ∣ pderiv i f := by
  rintro ⟨q, he⟩
  have hq : q ≠ 0 := by rintro rfl; exact hi (by rw [he, mul_zero])
  have hpos : 0 < f.totalDegree := by
    refine Nat.pos_of_ne_zero fun h0 => hi ?_
    rw [totalDegree_eq_zero_iff_eq_C.mp h0, pderiv_C]
  have htotal := totalDegree_mul_of_isDomain hf hq
  rw [← he] at htotal
  have := pderiv_totalDegree_le f i
  omega

end
end CCDN
