/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.Defs.Q
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# The reflected γ/2 shift at a real charge: algebra and parameter windows

The reflected shift at a real `α₁` near `Q` combines three identities: the coefficient identity
`R(α₁) C(2Q - α₁ - γ/2) = ρ C(α₁ - γ/2)` from the two diagonal representations
(`DOZZ.degenerateFourPoint_diagonal_classification`, `DOZZ.gammaHalf_reflected_formula`), the first
reflection shift `R(α₁) D = -μπ R(α₁ + γ/2)` (`DOZZ.reflectionR_first_shift_meromorphic`), and
`ρ D = 𝒜` (the Gamma identity). Eliminating `R(α₁)` and `ρ` gives
`R(α₁ + γ/2) C(2Q - α₁ - γ/2) = -𝒜 C(α₁ - γ/2)/(πμ)`.
-/

@[expose] public section

namespace DOZZ.Proofs

/-- **The reflected shift, as pure algebra.** -/
theorem reflected_shift_algebra {Rz Rz2 C₁ C₂ ρ D A μπ : ℂ} (hμπ : μπ ≠ 0) (hD : D ≠ 0)
    (hshift : Rz = -μπ * Rz2 / D) (hcoef : Rz * C₁ = ρ * C₂) (hρ : ρ * D = A) :
    Rz2 * C₁ = -(1 / μπ) * A * C₂ := by
  grind

/-- The window for the reflected γ/2 formula (`DOZZ.gammaHalf_reflected_formula`) near `Q`: with
`ξ = 1/2`, every `α₁` with `Q - γ/16 < α₁ < Q` satisfies the near-`Q` slack condition. -/
theorem reflected_near_window {γ α₁ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (h1 : Q γ - γ / 16 < α₁)
    (h2 : α₁ < Q γ) :
    ∃ ξ : ℝ, 0 < ξ ∧ ξ < 1 ∧ γ * (Q γ - α₁) < ξ ∧
      γ * (Q γ - α₁) < (1 - ξ) * (γ * (Q γ - α₁) + (α₁ + γ / 2 - Q γ) ^ 2 / 2) := by
  refine ⟨1 / 2, by norm_num, by norm_num, ?_, ?_⟩
  · nlinarith
  nlinarith

end DOZZ.Proofs

end
