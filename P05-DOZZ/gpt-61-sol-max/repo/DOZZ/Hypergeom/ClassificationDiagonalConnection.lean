/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Hypergeom.ConnectionDiagonalAlgebra
public import DOZZ.Hypergeom.ODE.ConnectionGammaCoefficients
public import DOZZ.Hypergeom.GaussConnectionMinus
public import DOZZ.Hypergeom.GaussConnectionPlus
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
public import DOZZ.Hypergeom.RealConnectionCoefficients

/-! Undivided coefficient transfer for the real Gauss connection matrix. -/

public section

namespace DOZZ.Proofs

/-- The weighted connection cross coefficient vanishes directly from the undivided `K₁,K₂` relation.
This remains valid when either diagonal coefficient or `K₂` vanishes. -/
theorem gaussGammaConnection_weighted_cross_eq_zero_of_constraint
    (a b c α δ : ℝ) (hconstraint : gaussK₁ a b c * α + gaussK₂ a b c * δ = 0) :
    (α : ℂ) * gaussConnectionMinusGammaCoefficient₁ (a, b, c) *
        gaussConnectionMinusGammaCoefficient₂ (a, b, c) +
      (δ : ℂ) * gaussConnectionPlusGammaCoefficient₁ (a, b, c) *
        gaussConnectionPlusGammaCoefficient₂ (a, b, c) = 0 := by
  let u  := realGaussConnection₀₀ a b c
  let v  := realGaussConnection₀₁ a b c
  let w  := realGaussConnection₁₀ a b c
  let x  := realGaussConnection₁₁ a b c
  have hU : gaussConnectionMinusGammaCoefficient₁ (a, b, c) = (u : ℂ) := (realGaussConnection₀₀_cast a b c).symm
  have hV : gaussConnectionMinusGammaCoefficient₂ (a, b, c) = (v : ℂ) := (realGaussConnection₀₁_cast a b c).symm
  have hW : gaussConnectionPlusGammaCoefficient₁ (a, b, c) = (w : ℂ) := (realGaussConnection₁₀_cast a b c).symm
  have hX : gaussConnectionPlusGammaCoefficient₂ (a, b, c) = (x : ℂ) := (realGaussConnection₁₁_cast a b c).symm
  have hUV : u * v =
      Real.Gamma (c - a - b) * Real.Gamma (a + b - c) * gaussK₁ a b c := by
    dsimp [u, v, gaussK₁]
    ring
  have hWX : w * x =
      Real.Gamma (c - a - b) * Real.Gamma (a + b - c) * gaussK₂ a b c := by
    dsimp [w, x, gaussK₂]
    ring
  have hcross : α * u * v + δ * w * x = 0 := by
    grind
  rw [hU, hV, hW, hX]
  exact_mod_cast hcross

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
        (α * (realGaussConnection₀₀ a b c) ^ 2 +
          δ * (realGaussConnection₁₀ a b c) ^ 2) *
            ‖gaussGMinus H a b c z‖ ^ 2 +
        (α * (realGaussConnection₀₁ a b c) ^ 2 +
          δ * (realGaussConnection₁₁ a b c) ^ 2) *
            ‖gaussGPlus H a b c z‖ ^ 2 := by
  let u  := realGaussConnection₀₀ a b c
  let v  := realGaussConnection₀₁ a b c
  let w  := realGaussConnection₁₀ a b c
  let x  := realGaussConnection₁₁ a b c
  have hU : gaussConnectionMinusGammaCoefficient₁ (a, b, c) = (u : ℂ) := (realGaussConnection₀₀_cast a b c).symm
  have hV : gaussConnectionMinusGammaCoefficient₂ (a, b, c) = (v : ℂ) := (realGaussConnection₀₁_cast a b c).symm
  have hW : gaussConnectionPlusGammaCoefficient₁ (a, b, c) = (w : ℂ) := (realGaussConnection₁₀_cast a b c).symm
  have hX : gaussConnectionPlusGammaCoefficient₂ (a, b, c) = (x : ℂ) := (realGaussConnection₁₁_cast a b c).symm
  have hUGamma := (realGaussConnection₀₀_cast a b c).symm
  have hVGamma := (realGaussConnection₀₁_cast a b c).symm
  have hWGamma := (realGaussConnection₁₀_cast a b c).symm
  have hXGamma := (realGaussConnection₁₁_cast a b c).symm
  have hcC : ∀ n : ℤ, (c : ℂ) ≠ (n : ℂ) := by
    assumption_mod_cast
  have hδC : ∀ n : ℤ, (c : ℂ) - (a : ℂ) - (b : ℂ) ≠ (n : ℂ) := by
    assumption_mod_cast
  have hminus := gauss_connection_minus hH (a : ℂ) (b : ℂ) (c : ℂ) hcC hδC
  have hplus := gauss_connection_plus hH (a : ℂ) (b : ℂ) (c : ℂ) hcC hδC
  have hcross := gaussGammaConnection_weighted_cross_eq_zero_of_constraint
    a b c α δ hconstraint
  rw [hU, hV, hW, hX] at hcross
  have hcrossR : α * u * v + δ * w * x = 0 := by
    assumption_mod_cast
  intro z hz
  have hminus' : gaussFMinus H (a : ℂ) (b : ℂ) (c : ℂ) z =
      (u : ℂ) * gaussGMinus H (a : ℂ) (b : ℂ) (c : ℂ) z +
        (v : ℂ) * gaussGPlus H (a : ℂ) (b : ℂ) (c : ℂ) z := by
    simpa only [hUGamma, hVGamma, u, v] using hminus z hz
  have hplus' : gaussFPlus H (a : ℂ) (b : ℂ) (c : ℂ) z =
      (w : ℂ) * gaussGMinus H (a : ℂ) (b : ℂ) (c : ℂ) z +
        (x : ℂ) * gaussGPlus H (a : ℂ) (b : ℂ) (c : ℂ) z := by
    simpa only [hWGamma, hXGamma, w, x] using hplus z hz
  have hnorm := real_diagonal_normSq_connection_change α δ u v w x
    (gaussGMinus H (a : ℂ) (b : ℂ) (c : ℂ) z)
    (gaussGPlus H (a : ℂ) (b : ℂ) (c : ℂ) z) hcrossR
  calc
    _ = α * Complex.normSq (gaussFMinus H (a : ℂ) (b : ℂ) (c : ℂ) z) +
        δ * Complex.normSq (gaussFPlus H (a : ℂ) (b : ℂ) (c : ℂ) z) := by
      simp only [← Complex.normSq_eq_norm_sq]
    _ = α * Complex.normSq ((u : ℂ) * gaussGMinus H (a : ℂ) (b : ℂ) (c : ℂ) z +
          (v : ℂ) * gaussGPlus H (a : ℂ) (b : ℂ) (c : ℂ) z) +
        δ * Complex.normSq ((w : ℂ) * gaussGMinus H (a : ℂ) (b : ℂ) (c : ℂ) z +
          (x : ℂ) * gaussGPlus H (a : ℂ) (b : ℂ) (c : ℂ) z) := by
      rw [hminus', hplus']
    _ = (α * u ^ 2 + δ * w ^ 2) *
          Complex.normSq (gaussGMinus H (a : ℂ) (b : ℂ) (c : ℂ) z) +
        (α * v ^ 2 + δ * x ^ 2) *
          Complex.normSq (gaussGPlus H (a : ℂ) (b : ℂ) (c : ℂ) z) := hnorm
    _ = _ := by
      simp only [← Complex.normSq_eq_norm_sq]
      simp [u, v, w, x]

end DOZZ.Proofs
