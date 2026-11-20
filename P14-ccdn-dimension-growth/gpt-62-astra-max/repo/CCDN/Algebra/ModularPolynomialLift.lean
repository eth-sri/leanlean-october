/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Algebra.Equations
public import Mathlib.Data.ZMod.Basic
public import Mathlib.RingTheory.MvPolynomial.Ideal

/-! Coefficientwise integer lifts preserve homogeneous weights and origin-ideal
powers. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

variable {σ : Type*} {p k : ℕ} (f : MvPolynomial σ (ZMod p))

/-- The integer polynomial lifting a polynomial over `ZMod p` coefficientwise, using the
representatives `ZMod.val` in `[0, p)`. -/
def modularPolynomialLift :
    MvPolynomial σ ℤ := ∑ e ∈ f.support, monomial e (f.coeff e).val

private lemma coeff_modularPolynomialLift (e : σ →₀ ℕ) :
    (modularPolynomialLift f).coeff e = (f.coeff e).val := by
  classical
  simp only [modularPolynomialLift, coeff_sum, coeff_monomial]
  simp_all

/-- Reducing the coefficientwise lift of `f` modulo `p` recovers `f`. -/
lemma map_modularPolynomialLift [NeZero p]
    (f : MvPolynomial σ (ZMod p)) :
    residueEquation p (modularPolynomialLift f) = f := by
  ext e
  simp only [coeff_map, coeff_modularPolynomialLift, Int.coe_castRingHom,
    Int.cast_natCast, ZMod.natCast_zmod_val]

/-- The coefficientwise lift of a homogeneous polynomial of degree `k` over `ZMod p` is
homogeneous of degree `k`. -/
lemma modularPolynomialLift_homogeneous (hf : f.IsHomogeneous k) :
    (modularPolynomialLift f).IsHomogeneous k := by
  intro e he
  have hfe : f.coeff e ≠ 0 := by
    grind [coeff_modularPolynomialLift, ZMod.val_zero, Nat.cast_zero]
  exact hf hfe

/-- If `f` lies in the `k`-th power of the ideal of the origin over `ZMod p`, then so does its
coefficientwise lift over `ℤ`. -/
lemma modularPolynomialLift_mem_origin_power (hf : f ∈ idealOfVars σ (ZMod p) ^ k) :
    modularPolynomialLift f ∈ idealOfVars σ ℤ ^ k := by
  rw [mem_pow_idealOfVars_iff'] at hf ⊢
  grind [coeff_modularPolynomialLift, ZMod.val_zero, Nat.cast_zero]

end
end CCDN
