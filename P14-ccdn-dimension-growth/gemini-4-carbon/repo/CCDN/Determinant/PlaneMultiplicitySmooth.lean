/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Algebra.OriginShift
public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.Data.ZMod.Basic
public import Mathlib.RingTheory.MvPolynomial.Ideal
import CCDN.Determinant.PlaneSingularities

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
  simpa only [eval_zero, constantCoeff_eq, coeff_pderiv, zero_add,
    Finsupp.coe_zero, Pi.zero_apply, Nat.cast_zero, mul_one]
    using hf (Finsupp.single j 1) (by simp; omega)

theorem singular_of_origin_order_ge_two {K σ : Type*} [Field K]
    (f : MvPolynomial σ K) (a : σ → K) {μ : ℕ} (hμ : 2 ≤ μ)
    (hf : originShift a f ∈ idealOfVars σ K ^ μ) (j : σ) :
    eval a (pderiv j f) = 0 := by
  rw [← eval_zero_originShift, ← pderiv_originShift]
  exact origin_power_pderiv_zero hμ hf j

theorem origin_order_eq_one_of_smooth {K σ : Type*} [Field K]
    (f : MvPolynomial σ K) (a : σ → K) {μ : ℕ} (hμ : 0 < μ)
    (hf : originShift a f ∈ idealOfVars σ K ^ μ)
    (hs : ∃ j, eval a (pderiv j f) ≠ 0) : μ = 1 := by
  by_contra h
  obtain ⟨j, hj⟩ := hs
  exact hj (singular_of_origin_order_ge_two f a (by omega) hf j)

end
end CCDN
