/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

import Mathlib

public import Mathlib.Data.ZMod.Basic
public import Mathlib.RingTheory.MvPolynomial.Ideal

/-! Coefficientwise integer lifts preserve homogeneous weights and origin-ideal
powers. -/

@[expose] public section
namespace CCDN
open MvPolynomial

variable {σ : Type*}

variable {p : ℕ}

/-- The integer polynomial lifting a polynomial over `ZMod p` coefficientwise, using the
representatives `ZMod.val` in `[0, p)`. -/
noncomputable def modularPolynomialLift   (f : MvPolynomial σ (ZMod p)) :
    MvPolynomial σ ℤ := ∑ e ∈ f.support, monomial e (f.coeff e).val

private lemma coeff_modularPolynomialLift  
    (f : MvPolynomial σ (ZMod p)) (e : σ →₀ ℕ) :
    (modularPolynomialLift f).coeff e = (f.coeff e).val := by
  classical
  simp_all [ coeff_monomial, Finset.sum_ite_eq', modularPolynomialLift]

/-- Reducing the coefficientwise lift of `f` modulo `p` recovers `f`. -/
lemma map_modularPolynomialLift   [NeZero p]
    (f : MvPolynomial σ (ZMod p)) :
    map (Int.castRingHom (ZMod p)) (modularPolynomialLift f) = f := by
  ext e
  simp_all [coeff_map, coeff_modularPolynomialLift]

/-- The coefficientwise lift of a homogeneous polynomial of degree `k` over `ZMod p` is
homogeneous of degree `k`. -/
lemma modularPolynomialLift_homogeneous  {p k : ℕ}
    (f : MvPolynomial σ (ZMod p)) (hf : f.IsHomogeneous k) :
    (modularPolynomialLift f).IsHomogeneous k := by
  intro e he
  have hfe : f.coeff e ≠ 0 := by
    simp_all [coeff_modularPolynomialLift]
  exact hf hfe

/-- If `f` lies in the `k`-th power of the ideal of the origin over `ZMod p`, then so does its
coefficientwise lift over `ℤ`. -/
lemma modularPolynomialLift_mem_origin_power  {p k : ℕ}
    (f : MvPolynomial σ (ZMod p)) (hf : f ∈ idealOfVars σ (ZMod p) ^ k) :
    modularPolynomialLift f ∈ idealOfVars σ ℤ ^ k := by
  simp_all [mem_pow_idealOfVars_iff', coeff_modularPolynomialLift, ZMod.val_zero]

end CCDN
