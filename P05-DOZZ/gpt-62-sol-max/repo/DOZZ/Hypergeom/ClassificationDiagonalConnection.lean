/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Hypergeom.ConnectionDiagonalAlgebra
public import DOZZ.Hypergeom.GaussConnectionMinus
public import DOZZ.Hypergeom.GaussConnectionPlus
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta

/-! Undivided coefficient transfer for the real Gauss connection matrix. -/

@[expose] public section

namespace DOZZ.Proofs

/-- The entries of the Gauss connection matrix on real parameters. -/
noncomputable def gaussConnectionReal₁₁ (a b c : ℝ) : ℝ :=
  Real.Gamma c * Real.Gamma (c - a - b) * (Real.Gamma (c - a))⁻¹ * (Real.Gamma (c - b))⁻¹

noncomputable def gaussConnectionReal₁₂ (a b c : ℝ) : ℝ :=
  Real.Gamma c * Real.Gamma (a + b - c) * (Real.Gamma a)⁻¹ * (Real.Gamma b)⁻¹

noncomputable def gaussConnectionReal₂₁ (a b c : ℝ) : ℝ :=
  Real.Gamma (2 - c) * Real.Gamma (c - a - b) * (Real.Gamma (1 - a))⁻¹ * (Real.Gamma (1 - b))⁻¹

noncomputable def gaussConnectionReal₂₂ (a b c : ℝ) : ℝ :=
  Real.Gamma (2 - c) * Real.Gamma (a + b - c) *
    (Real.Gamma (a - c + 1))⁻¹ * (Real.Gamma (b - c + 1))⁻¹

section
variable (a b c : ℝ)
local notation "u" => gaussConnectionReal₁₁ a b c
local notation "v" => gaussConnectionReal₁₂ a b c
local notation "w" => gaussConnectionReal₂₁ a b c
local notation "x" => gaussConnectionReal₂₂ a b c

theorem gaussConnectionReal_cross (α δ : ℝ) : α * u * v + δ * w * x =
    Real.Gamma (c - a - b) * Real.Gamma (a + b - c) *
      (gaussK₁ a b c * α + gaussK₂ a b c * δ) := by
  unfold gaussConnectionReal₁₁ gaussConnectionReal₁₂ gaussConnectionReal₂₁ gaussConnectionReal₂₂ gaussK₁ gaussK₂
  ring

/-- Both connection formulas use the same real matrix. -/
theorem gauss_connection_real {H : ℂ → ℂ → ℂ → ℂ → ℂ}
    (hH : IsGaussHypergeometricFamily H)
    (hc : ∀ n : ℤ, c ≠ (n : ℝ)) (hδ : ∀ n : ℤ, c - a - b ≠ (n : ℝ))
    (z : ℂ) (hz : z ∈ gaussCutPlane) :
    gaussFMinus H a b c z = (u : ℂ) * gaussGMinus H a b c z + (v : ℂ) * gaussGPlus H a b c z ∧
    gaussFPlus H a b c z = (w : ℂ) * gaussGMinus H a b c z + (x : ℂ) * gaussGPlus H a b c z := by
  have hcC : ∀ n : ℤ, (c : ℂ) ≠ (n : ℂ) := by exact_mod_cast hc
  have hδC : ∀ n : ℤ, (c : ℂ) - (a : ℂ) - (b : ℂ) ≠ (n : ℂ) := by exact_mod_cast hδ
  constructor
  · simpa only [gaussConnectionReal₁₁, gaussConnectionReal₁₂, ← Complex.Gamma_ofReal,
      Complex.ofReal_mul, Complex.ofReal_sub, Complex.ofReal_add, Complex.ofReal_inv] using
      gauss_connection_minus hH a b c hcC hδC z hz
  · simpa only [gaussConnectionReal₂₁, gaussConnectionReal₂₂, ← Complex.Gamma_ofReal,
      Complex.ofReal_mul, Complex.ofReal_sub, Complex.ofReal_add, Complex.ofReal_inv,
      Complex.ofReal_ofNat, Complex.ofReal_one] using gauss_connection_plus hH a b c hcC hδC z hz

end

/-- The diagonal norm-square connection identity uses only the undivided coefficient constraint, and
therefore also covers the `K₂ = 0` case. -/
theorem gauss_diagonal_one_basis_of_constraint
    {H : ℂ → ℂ → ℂ → ℂ → ℂ}
    (hH : IsGaussHypergeometricFamily H) (a b c α δ : ℝ)
    (hc : ∀ n : ℤ, c ≠ (n : ℝ))
    (hδint : ∀ n : ℤ, c - a - b ≠ (n : ℝ))
    (hconstraint : gaussK₁ a b c * α + gaussK₂ a b c * δ = 0) :
    ∀ z ∈ gaussCutPlane,
      α * ‖gaussFMinus H a b c z‖ ^ 2 + δ * ‖gaussFPlus H a b c z‖ ^ 2 =
        (α * (gaussConnectionReal₁₁ a b c) ^ 2 +
          δ * (gaussConnectionReal₂₁ a b c) ^ 2) *
            ‖gaussGMinus H a b c z‖ ^ 2 +
        (α * (gaussConnectionReal₁₂ a b c) ^ 2 +
          δ * (gaussConnectionReal₂₂ a b c) ^ 2) *
            ‖gaussGPlus H a b c z‖ ^ 2 := by
  intro z hz
  obtain ⟨hm, hp⟩ := gauss_connection_real a b c hH hc hδint z hz
  have hcross := gaussConnectionReal_cross a b c α δ
  rw [hconstraint, mul_zero] at hcross
  rw [hm, hp]
  simpa only [Complex.normSq_eq_norm_sq] using real_diagonal_normSq_connection_change
    α δ _ _ _ _ _ _ hcross

end DOZZ.Proofs
