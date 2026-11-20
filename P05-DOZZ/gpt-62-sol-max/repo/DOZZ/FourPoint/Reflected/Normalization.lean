/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.FourPoint.FourPointT
public import DOZZ.Statements.FourPoint.GammaHalfMoment
public import DOZZ.Statements.Brownian.ReflectionR
public import DOZZ.FourPoint.Reflected.Window
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Tactic

/-! # Exact normalizations for reflected half-charge fusion

These identities retain the literal moment, including its totalized ENNReal convention.
-/

public section

open MeasureTheory

namespace DOZZ.Proofs

/-- The half-charge four-point zero-mode exponent. -/
theorem fourPointSExp_gammaHalf (γ α₁ α₂ α₃ : ℝ) :
    fourPointSExp γ (-γ / 2) α₁ α₂ α₃ =
      (α₁ + α₂ + α₃ - γ / 2 - 2 * Q γ) / γ := by
  unfold fourPointSExp
  congr 1
  ring

/-- The reduced four-point function is the literal half-charge moment times its prefactor. -/
theorem fourPointT_eq_gammaHalfMoment {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (M : Ω → Measure ℂ) (γ μ α₁ α₂ α₃ : ℝ) (z : ℂ) :
    fourPointT P M γ μ (-γ / 2) α₁ α₂ α₃ z =
      (2 * μ ^ (-(α₁ + α₂ + α₃ - γ / 2 - 2 * Q γ) / γ) / γ *
        Real.Gamma ((α₁ + α₂ + α₃ - γ / 2 - 2 * Q γ) / γ)) *
      gammaHalfMoment P M γ α₁ α₂ α₃
        ((α₁ + α₂ + α₃ - γ / 2 - 2 * Q γ) / γ) z := by
  unfold fourPointT gammaHalfMoment
  rw [fourPointSExp_gammaHalf]
  simp only [neg_div]

/-- The exact prefactor cancels the inner reflected coefficient, without a finiteness premise. -/
theorem reflected_prefactor_cancel (γ μ p R C : ℝ) (hγ : 0 < γ)
    (hμ : 0 < μ) (hp : 0 < p) :
    (2 * μ ^ (-p) / γ * Real.Gamma p) *
      (1 / 2 * μ ^ p * γ * (Real.Gamma p)⁻¹ * R * C) = R * C := by
  have hpow : μ ^ (-p) * μ ^ p = 1 := by
    rw [← Real.rpow_add hμ, neg_add_cancel, Real.rpow_zero]
  have hΓ : Real.Gamma p ≠ 0 := (Real.Gamma_pos_of_pos hp).ne'
  calc
    _ = (μ ^ (-p) * μ ^ p) * (γ / γ) *
        (Real.Gamma p * (Real.Gamma p)⁻¹) * R * C := by ring
    _ = R * C := by rw [hpow, div_self hγ.ne', mul_inv_cancel₀ hΓ]; ring

section
variable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (M : Ω → Measure ℂ)
  (B : Ω → BrownianPath × BrownianPath) (Z : Ω → Measure ℝ)
include Ω P M B Z

/-- Cancellation of the zero-mode and cosmological factors is independent of the shift. -/
theorem fusion_inner_coefficient_eq (γ μ χ α₁ α₂ α₃ : ℝ) (hγ : γ ≠ 0) (hμ : 0 < μ) :
    let p := (α₁ + α₂ + α₃ - χ - 2 * Q γ) / γ
    let a := reflectionExponent γ α₁
    (a * Real.Gamma (-a) * Real.Gamma (p + a) / Real.Gamma p) *
      reflectionBarR P γ α₁ B Z *
      (∫⁻ ω, rho γ (M ω) (2 * Q γ - α₁ - χ) α₂ α₃ ^ (-(p + a)) ∂P).toReal =
    1 / 2 * μ ^ p * γ * (Real.Gamma p)⁻¹ * reflectionR P γ μ α₁ B Z *
      structureConstant P M γ μ (2 * Q γ - α₁ - χ) α₂ α₃ := by
  dsimp only
  set p := (α₁ + α₂ + α₃ - χ - 2 * Q γ) / γ
  set a := reflectionExponent γ α₁
  have horder : sExp γ (2 * Q γ - α₁ - χ) α₂ α₃ = p + a := by
    simp only [sExp, p, a, reflectionExponent]
    ring
  rw [structureConstant, horder, reflectionR, ← show a = reflectionExponent γ α₁ from rfl]
  have hpow : μ ^ p * μ ^ a * μ ^ (-(p + a)) = 1 := by
    rw [← Real.rpow_add hμ, ← Real.rpow_add hμ, add_neg_cancel, Real.rpow_zero]
  let c := (∫⁻ ω, rho γ (M ω) (2 * Q γ - α₁ - χ) α₂ α₃ ^ (-(p + a)) ∂P).toReal
  calc
    _ = (a * Real.Gamma (-a) * Real.Gamma (p + a) / Real.Gamma p * reflectionBarR P γ α₁ B Z * c) *
        ((μ ^ p * μ ^ a * μ ^ (-(p + a))) * (γ * γ⁻¹)) := by
      rw [hpow, mul_inv_cancel₀ hγ, one_mul, mul_one]
    _ = _ := by dsimp only [c]; ring

/-- The independent-maximum coefficient is exactly the inner-limit coefficient. -/
theorem reflected_inner_coefficient_eq (γ μ α₁ α₂ α₃ : ℝ) (hγ : 0 < γ) (hμ : 0 < μ)
    (hs : 2 * Q γ + γ / 2 < α₁ + α₂ + α₃) :
    let p := (α₁ + α₂ + α₃ - γ / 2 - 2 * Q γ) / γ
    let a := reflectionExponent γ α₁
    (a * Real.Gamma (-a) * Real.Gamma (p + a) / Real.Gamma p) *
      reflectionBarR P γ α₁ B Z *
      (∫⁻ ω, rho γ (M ω) (2 * Q γ - α₁ - γ / 2) α₂ α₃ ^ (-(p + a)) ∂P).toReal =
    1 / 2 * μ ^ p * γ * (Real.Gamma p)⁻¹ * reflectionR P γ μ α₁ B Z *
      structureConstant P M γ μ (2 * Q γ - α₁ - γ / 2) α₂ α₃ :=
  fusion_inner_coefficient_eq P M B Z γ μ (γ / 2) α₁ α₂ α₃ hγ.ne' hμ

end

end DOZZ.Proofs
