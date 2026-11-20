/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Hypergeom.ODE.ConnectionMidpointCramer
import Mathlib.Analysis.SpecialFunctions.Gamma.Deriv
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta

/-! Parameter regularity of the four Gamma coefficients in the connection formulas. -/

@[expose] public section

open scoped Topology

namespace DOZZ.Proofs

/-- The first Gamma coefficient in the zero-to-one connection formula. -/
noncomputable def gaussConnectionMinusGammaCoefficient₁ (p : ℂ × ℂ × ℂ) : ℂ :=
  Complex.Gamma p.2.2 * Complex.Gamma (p.2.2 - p.1 - p.2.1) *
    (Complex.Gamma (p.2.2 - p.1))⁻¹ * (Complex.Gamma (p.2.2 - p.2.1))⁻¹

/-- The second Gamma coefficient in the zero-to-one connection formula. -/
noncomputable def gaussConnectionMinusGammaCoefficient₂ (p : ℂ × ℂ × ℂ) : ℂ :=
  Complex.Gamma p.2.2 * Complex.Gamma (p.1 + p.2.1 - p.2.2) *
    (Complex.Gamma p.1)⁻¹ * (Complex.Gamma p.2.1)⁻¹

/-- The first Gamma coefficient in the powered zero-to-one connection formula. -/
noncomputable def gaussConnectionPlusGammaCoefficient₁ (p : ℂ × ℂ × ℂ) : ℂ :=
  Complex.Gamma (2 - p.2.2) * Complex.Gamma (p.2.2 - p.1 - p.2.1) *
    (Complex.Gamma (1 - p.1))⁻¹ * (Complex.Gamma (1 - p.2.1))⁻¹

/-- The second Gamma coefficient in the powered zero-to-one connection formula. -/
noncomputable def gaussConnectionPlusGammaCoefficient₂ (p : ℂ × ℂ × ℂ) : ℂ :=
  Complex.Gamma (2 - p.2.2) * Complex.Gamma (p.1 + p.2.1 - p.2.2) *
    (Complex.Gamma (p.1 - p.2.2 + 1))⁻¹ *
      (Complex.Gamma (p.2.1 - p.2.2 + 1))⁻¹

section
variable {p : ℂ × ℂ × ℂ} (hp : p ∈ gaussConnectionParameterDomain)
include hp

private theorem connection_c_polefree :
    ∀ n : ℕ, p.2.2 ≠ -(n : ℂ) := by
  intro n he
  exact hp.1 (-(n : ℤ)) (by simpa using he)

private theorem connection_delta_polefree :
    ∀ n : ℕ, p.2.2 - p.1 - p.2.1 ≠ -(n : ℂ) := by
  intro n he
  exact hp.2 (-(n : ℤ)) (by simpa using he)

private theorem connection_neg_delta_polefree :
    ∀ n : ℕ, p.1 + p.2.1 - p.2.2 ≠ -(n : ℂ) := by
  intro n he
  apply hp.2 n
  have he' := congrArg (fun z : ℂ => -z) he
  linear_combination he'

private theorem connection_two_sub_c_polefree :
    ∀ n : ℕ, 2 - p.2.2 ≠ -(n : ℂ) := by
  intro n he
  apply hp.1 ((n : ℤ) + 2)
  push_cast at he ⊢
  linear_combination -he

end

section
variable {p : ℂ × ℂ × ℂ} (f : ℂ × ℂ × ℂ → ℂ) (hf : DifferentiableAt ℂ f p)
include hf

private theorem gamma_comp_differentiableAt
    (hfree : ∀ n : ℕ, f p ≠ -(n : ℂ)) :
    DifferentiableAt ℂ (fun q => Complex.Gamma (f q)) p := by
  fun_prop

private theorem invGamma_comp_differentiableAt :
    DifferentiableAt ℂ (fun q => (Complex.Gamma (f q))⁻¹) p := by
  have hGammaInv : Differentiable ℂ (fun z : ℂ => (Complex.Gamma z)⁻¹) :=
    Complex.differentiable_one_div_Gamma
  have hAt := hGammaInv (f p)
  apply hAt.comp <;> assumption

end

section
variable {p : ℂ × ℂ × ℂ} (hp : p ∈ gaussConnectionParameterDomain)
include hp

omit hp in
private theorem differentiableAt_gammaRatio
    {a b c d : ℂ × ℂ × ℂ → ℂ}
    (ha : DifferentiableAt ℂ a p) (hb : DifferentiableAt ℂ b p)
    (hc : DifferentiableAt ℂ c p) (hd : DifferentiableAt ℂ d p)
    (ha0 : ∀ n : ℕ, a p ≠ -(n : ℂ)) (hb0 : ∀ n : ℕ, b p ≠ -(n : ℂ)) :
    DifferentiableAt ℂ (fun q => Complex.Gamma (a q) * Complex.Gamma (b q) *
      (Complex.Gamma (c q))⁻¹ * (Complex.Gamma (d q))⁻¹) p :=
  (((gamma_comp_differentiableAt a ha ha0).mul (gamma_comp_differentiableAt b hb hb0)).mul
    (invGamma_comp_differentiableAt c hc)).mul (invGamma_comp_differentiableAt d hd)

/-- The first unpowered Gamma coefficient is differentiable throughout the connection domain. -/
theorem gaussConnectionMinusGammaCoefficient₁_differentiableAt :
    DifferentiableAt ℂ gaussConnectionMinusGammaCoefficient₁ p := by
  unfold gaussConnectionMinusGammaCoefficient₁
  exact differentiableAt_gammaRatio (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop)
    (connection_c_polefree hp) (connection_delta_polefree hp)

/-- The second unpowered Gamma coefficient is differentiable throughout the connection domain. -/
theorem gaussConnectionMinusGammaCoefficient₂_differentiableAt :
    DifferentiableAt ℂ gaussConnectionMinusGammaCoefficient₂ p := by
  unfold gaussConnectionMinusGammaCoefficient₂
  exact differentiableAt_gammaRatio (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop)
    (connection_c_polefree hp) (connection_neg_delta_polefree hp)

/-- The first powered Gamma coefficient is differentiable throughout the connection domain. -/
theorem gaussConnectionPlusGammaCoefficient₁_differentiableAt :
    DifferentiableAt ℂ gaussConnectionPlusGammaCoefficient₁ p := by
  unfold gaussConnectionPlusGammaCoefficient₁
  exact differentiableAt_gammaRatio (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop)
    (connection_two_sub_c_polefree hp) (connection_delta_polefree hp)

/-- The second powered Gamma coefficient is differentiable throughout the connection domain. -/
theorem gaussConnectionPlusGammaCoefficient₂_differentiableAt :
    DifferentiableAt ℂ gaussConnectionPlusGammaCoefficient₂ p := by
  unfold gaussConnectionPlusGammaCoefficient₂
  exact differentiableAt_gammaRatio (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop)
    (connection_two_sub_c_polefree hp) (connection_neg_delta_polefree hp)

end

end DOZZ.Proofs
