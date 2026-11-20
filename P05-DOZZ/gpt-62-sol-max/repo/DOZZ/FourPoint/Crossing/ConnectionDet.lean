/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Hypergeom.ConnectionDet
import Mathlib.Tactic
public import DOZZ.Hypergeom.ClassificationDiagonalConnection

/-! # The real connection determinant used in coefficient extraction -/

public section
namespace DOZZ.Proofs

/-- The complex connection determinant `gauss_connection_det` specializes to real Gamma entries. -/
theorem crossing_connection_det_real (a b c : ℝ)
    (hc : ∀ n : ℤ, c ≠ (n : ℝ))
    (hδ : ∀ n : ℤ, c - a - b ≠ (n : ℝ)) :
    (gaussConnectionReal₁₁ a b c) *
      (gaussConnectionReal₂₂ a b c) -
      (gaussConnectionReal₁₂ a b c) *
      (gaussConnectionReal₂₁ a b c) =
    (c - 1) / (c - a - b) := by
  apply Complex.ofReal_injective
  simpa only [gaussConnectionReal₁₁, gaussConnectionReal₁₂, gaussConnectionReal₂₁,
    gaussConnectionReal₂₂, ← Complex.Gamma_ofReal, Complex.ofReal_mul, Complex.ofReal_sub,
    Complex.ofReal_add, Complex.ofReal_inv, Complex.ofReal_div, Complex.ofReal_one,
    Complex.ofReal_ofNat] using
    gauss_connection_det (a : ℂ) (b : ℂ) (c : ℂ) (by exact_mod_cast hc) (by exact_mod_cast hδ)

/-- No integer lies in the open unit interval. -/
theorem unit_interval_ne_int {x : ℝ} (h0 : 0 < x) (h1 : x < 1) (n : ℤ) : x ≠ (n : ℝ) := by
  rintro rfl
  have h0' : 0 < n := by exact_mod_cast h0
  have h1' : n < 1 := by exact_mod_cast h1
  omega

end DOZZ.Proofs
