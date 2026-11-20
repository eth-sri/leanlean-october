/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Determinant.PlaneMultiplicity
public import Mathlib.Algebra.MvPolynomial.PDeriv

/-! Multiplicity greater than one forces a singular point. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

private lemma origin_power_pderiv_zero {K σ : Type*} [Field K]
    {f : MvPolynomial σ K} {μ : ℕ} (hμ : 2 ≤ μ)
    (hf : f ∈ idealOfVars σ K ^ μ) (j : σ) :
    eval (0 : σ → K) (pderiv j f) = 0 := by
  classical
  rw [mem_pow_idealOfVars_iff'] at hf
  have hc := hf (Finsupp.single j 1)
    (by simp; omega)
  simpa only [eval_zero, constantCoeff_eq, coeff_pderiv, zero_add,
    Finsupp.coe_zero, Pi.zero_apply, Nat.cast_zero, zero_add, mul_one] using hc

section

variable {K σ : Type*} [Field K]
  (f : MvPolynomial σ K) (a : σ → K) {μ : ℕ}
include K σ f a μ

/-- Only singular points can have local order at least two. -/
theorem singular_of_origin_order_ge_two (hμ : 2 ≤ μ)
    (hf : originShift a f ∈ idealOfVars σ K ^ μ) :
    ∀ j, eval a (pderiv j f) = 0 := by
  intro j
  rw [← eval_zero_originShift, ← pderiv_originShift]
  exact origin_power_pderiv_zero hμ hf j

/-- In particular, every positive order at a smooth point is one. -/
theorem origin_order_eq_one_of_smooth (hμ : 0 < μ)
    (hf : originShift a f ∈ idealOfVars σ K ^ μ)
    (hs : ∃ j, eval a (pderiv j f) ≠ 0) : μ = 1 := by
  by_contra h
  obtain ⟨j, hj⟩ := hs
  exact hj (singular_of_origin_order_ge_two f a (by omega) hf j)

end

end
end CCDN
