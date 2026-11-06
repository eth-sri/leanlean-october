/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

import Mathlib.Data.ZMod.Basic
import Mathlib.RingTheory.MvPolynomial.Ideal

/-! Coefficientwise integer lifts preserve homogeneous weights and origin-ideal
powers. -/

namespace CCDN
noncomputable section
open MvPolynomial

section
variable {σ : Type*} {p : ℕ}

/-- The integer polynomial lifting a polynomial over `ZMod p` coefficientwise, using the
representatives `ZMod.val` in `[0, p)`. -/
def modularPolynomialLift (f : MvPolynomial σ (ZMod p)) :
    MvPolynomial σ ℤ := ∑ e ∈ f.support, monomial e (f.coeff e).val

lemma coeff_modularPolynomialLift
    (f : MvPolynomial σ (ZMod p)) (e : σ →₀ ℕ) :
    (modularPolynomialLift f).coeff e = (f.coeff e).val := by
  classical
  simp only [modularPolynomialLift, coeff_sum, coeff_monomial]
  rw [Finset.sum_ite_eq']
  split_ifs with he
  · rfl
  · simp_all

/-- Reducing the coefficientwise lift of `f` modulo `p` recovers `f`. -/
lemma map_modularPolynomialLift [NeZero p]
    (f : MvPolynomial σ (ZMod p)) :
    map (Int.castRingHom (ZMod p)) (modularPolynomialLift f) = f := by
  ext e
  simp only [coeff_map, coeff_modularPolynomialLift, Int.coe_castRingHom,
    Int.cast_natCast, ZMod.natCast_zmod_val]

end

variable {σ : Type*} {p k : ℕ} (f : MvPolynomial σ (ZMod p))

/-- The coefficientwise lift of a homogeneous polynomial of degree `k` over `ZMod p` is
homogeneous of degree `k`. -/
lemma modularPolynomialLift_homogeneous
    (hf : f.IsHomogeneous k) :
    (modularPolynomialLift f).IsHomogeneous k := by
  intro e he
  exact hf (by
    intro h
    exact he (by simp only [coeff_modularPolynomialLift, h, ZMod.val_zero, Nat.cast_zero]))

/-- If `f` lies in the `k`-th power of the ideal of the origin over `ZMod p`, then so does its
coefficientwise lift over `ℤ`. -/
lemma modularPolynomialLift_mem_origin_power
    (hf : f ∈ idealOfVars σ (ZMod p) ^ k) :
    modularPolynomialLift f ∈ idealOfVars σ ℤ ^ k := by
  rw [mem_pow_idealOfVars_iff'] at hf ⊢
  intro e he
  rw [coeff_modularPolynomialLift, hf e he, ZMod.val_zero, Nat.cast_zero]

