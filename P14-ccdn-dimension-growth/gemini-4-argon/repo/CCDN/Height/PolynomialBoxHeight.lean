/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Height.IntegerCoefficientHeight
public import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith

/-! Coefficient-height bounds for evaluating a polynomial on a bounded box.
The constants depend only on total degree and the number of variables. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

/-- An evaluation estimate with no coefficient-dependent constants. -/
theorem polynomial_eval₂_box_bound {σ : Type*} [Fintype σ]
    (f : MvPolynomial σ ℤ) (H A : ℝ) (hH : 0 ≤ H) (hA : 1 ≤ A)
    (hf : CoefficientHeightLE f H)
    (v : σ → ℝ) (hv : ∀ i, |v i| ≤ A) :
    |eval₂ (Int.castRingHom ℝ) v f| ≤
      ((f.totalDegree : ℝ) + 1) ^ Fintype.card σ * H * A ^ f.totalDegree := by
  classical
  rw [eval₂_eq']
  calc
    |∑ e ∈ f.support, (Int.castRingHom ℝ) (f.coeff e) * ∏ i, v i ^ e i| ≤
        ∑ e ∈ f.support, |(Int.castRingHom ℝ) (f.coeff e) * ∏ i, v i ^ e i| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _e ∈ f.support, H * A ^ f.totalDegree := by
      refine Finset.sum_le_sum fun e he => ?_
      have hd : ∑ i, e i ≤ f.totalDegree := by
        simpa only [Finsupp.sum_fintype e (fun _ k => k) (fun _ => rfl)] using le_totalDegree he
      have hp : |∏ i, v i ^ e i| ≤ A ^ f.totalDegree := by
        rw [Finset.abs_prod]
        exact (Finset.prod_le_prod₀ (fun _ _ => abs_nonneg _) fun i _ =>
          (abs_pow _ _).le.trans (pow_le_pow_left₀ (abs_nonneg _) (hv i) _)).trans
          ((Finset.prod_pow_eq_pow_sum _ _ _).trans_le (pow_le_pow_right₀ hA hd))
      rw [abs_mul]
      exact mul_le_mul (hf e) hp (abs_nonneg _) hH
    _ = (f.support.card : ℝ) * H * A ^ f.totalDegree := by simp; ring
    _ ≤ ((f.totalDegree : ℝ) + 1) ^ Fintype.card σ * H * A ^ f.totalDegree := by
      let ψ : {e // e ∈ f.support} → σ → Fin (f.totalDegree + 1) :=
        fun e i => ⟨e.val i, Nat.lt_succ_of_le
          (((degreeOf_le_iff.mp le_rfl) e.val e.property).trans (degreeOf_le_totalDegree f i))⟩
      have hi : Function.Injective ψ := fun e e' h =>
        Subtype.ext (Finsupp.ext fun i => congrArg (fun w => (w i).val) h)
      have hc : (f.support.card : ℝ) ≤ ((f.totalDegree : ℝ) + 1) ^ Fintype.card σ :=
        mod_cast (by simpa using Fintype.card_le_of_injective ψ hi :
          f.support.card ≤ (f.totalDegree + 1) ^ Fintype.card σ)
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hc hH)
        (pow_nonneg (by linarith) _)

end
end CCDN
