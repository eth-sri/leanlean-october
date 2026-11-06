/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Hypergeom.ConnectionDet
import Mathlib.Tactic
public import DOZZ.Hypergeom.RealConnectionCoefficients

/-! # The real connection determinant used in coefficient extraction -/

public section
namespace DOZZ.Proofs

/-- The complex connection determinant `gauss_connection_det` specializes to real Gamma entries. -/
theorem crossing_connection_det_real (a b c : ℝ)
    (hc : ∀ n : ℤ, c ≠ (n : ℝ))
    (hδ : ∀ n : ℤ, c - a - b ≠ (n : ℝ)) :
    (realGaussConnection₀₀ a b c) *
      (realGaussConnection₁₁ a b c) -
      (realGaussConnection₀₁ a b c) *
      (realGaussConnection₁₀ a b c) =
    (c - 1) / (c - a - b) := by
  have hcC : ∀ n : ℤ, (c : ℂ) ≠ (n : ℂ) := by
    intro n hn
    apply hc n
    exact_mod_cast hn
  have hδC : ∀ n : ℤ, (c : ℂ) - (a : ℂ) - (b : ℂ) ≠ (n : ℂ) := by
    intro n hn
    apply hδ n
    exact_mod_cast hn
  have hd := gauss_connection_det (a : ℂ) (b : ℂ) (c : ℂ) hcC hδC
  have hca : (c : ℂ) - (a : ℂ) = ((c - a : ℝ) : ℂ) := by push_cast; rfl
  have hcb : (c : ℂ) - (b : ℂ) = ((c - b : ℝ) : ℂ) := by push_cast; rfl
  have hδcast : (c : ℂ) - (a : ℂ) - (b : ℂ) = ((c - a - b : ℝ) : ℂ) := by push_cast; rfl
  have hsum : (a : ℂ) + (b : ℂ) - (c : ℂ) = ((a + b - c : ℝ) : ℂ) := by push_cast; rfl
  have hc2 : (2 : ℂ) - (c : ℂ) = ((2 - c : ℝ) : ℂ) := by push_cast; rfl
  have ha1 : (1 : ℂ) - (a : ℂ) = ((1 - a : ℝ) : ℂ) := by push_cast; rfl
  have hb1 : (1 : ℂ) - (b : ℂ) = ((1 - b : ℝ) : ℂ) := by push_cast; rfl
  have hac : (a : ℂ) - (c : ℂ) + 1 = ((a - c + 1 : ℝ) : ℂ) := by push_cast; rfl
  have hbc : (b : ℂ) - (c : ℂ) + 1 = ((b - c + 1 : ℝ) : ℂ) := by push_cast; rfl
  have hcm : (c : ℂ) - 1 = ((c - 1 : ℝ) : ℂ) := by push_cast; rfl
  rw [hδcast, hca, hcb, hsum, hc2, ha1, hb1, hac, hbc, hcm] at hd
  simp only [Complex.Gamma_ofReal, ← Complex.ofReal_mul, ← Complex.ofReal_inv,
    ← Complex.ofReal_sub, ← Complex.ofReal_div] at hd
  exact Complex.ofReal_injective hd

end DOZZ.Proofs
