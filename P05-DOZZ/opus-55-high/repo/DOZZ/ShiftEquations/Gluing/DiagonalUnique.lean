/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.Hypergeom.GaussFMinus
public import DOZZ.Statements.Hypergeom.GaussFPlus
public import DOZZ.Statements.Hypergeom.GaussCutPlane
public import DOZZ.Statements.Hypergeom.IsGaussHypergeometricFamily
import DOZZ.Hypergeom.ClassificationHermitianMixedJet
import DOZZ.Hypergeom.BasisWronskians
import DOZZ.Hypergeom.BasisRegularity
import DOZZ.Hypergeom.ODE.CutPlaneTopology
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.SpecialFunctions.Pow.Complex

/-!
# Uniqueness of diagonal Gauss representations

A real function on the principal cut plane has at most one representation
`A |F₋|² + D |F₊|²` in the Gauss basis at zero, provided the denominator parameter `c` avoids the
integers. The proof views the representation as a constant Hermitian tensor in the two holomorphic
functions `F₋` and `F₊`, and applies the coefficient-recovery theorem for such tensors at the
midpoint `1/2`, where the explicit Wronskian of the zero basis does not vanish.

## Main results

* `DOZZ.Proofs.diagonal_gauss_coefficients_unique`: the diagonal coefficients `A` and `D` are
  determined by the function they represent.
-/

@[expose] public section

open Filter Topology Set

namespace DOZZ.Proofs

/-- The product of a complex number and its conjugate is the cast of its squared norm. -/
private theorem diagUnique_mul_star_eq_norm_sq (z : ℂ) :
    z * star z = ((‖z‖ ^ 2 : ℝ) : ℂ) := by
  rw [Complex.star_def, Complex.mul_conj', Complex.ofReal_pow]

/-- A Hermitian tensor with real diagonal coefficients and zero off-diagonal coefficients is the
cast of the real combination of the squared norms of the two holomorphic factors. -/
private theorem diagUnique_tensor_eq_ofReal (f g : ℂ → ℂ) (A D : ℝ) (z : ℂ) :
    hermitianQuadraticTensor f g (A : ℂ) 0 0 (D : ℂ) z =
      ((A * ‖f z‖ ^ 2 + D * ‖g z‖ ^ 2 : ℝ) : ℂ) := by
  simp only [hermitianQuadraticTensor, zero_mul, add_zero]
  calc
    A * f z * star (f z) + D * g z * star (g z)
        = A * (f z * star (f z)) + D * (g z * star (g z)) := by ring
    _ = _ := by
      rw [diagUnique_mul_star_eq_norm_sq, diagUnique_mul_star_eq_norm_sq]
      push_cast
      ring
section
variable {H : ℂ → ℂ → ℂ → ℂ → ℂ}
section
variable (hH : IsGaussHypergeometricFamily H)
include hH

/-- The Wronskian of the zero basis does not vanish at the midpoint `1/2` of the cut plane when the
denominator parameter avoids the integers. -/
theorem diagUnique_wronskian_ne_zero (a b c : ℂ) (hc : ∀ n : ℤ, c ≠ (n : ℂ)) :
    gaussFMinus H a b c (1 / 2 : ℂ) * deriv (gaussFPlus H a b c) (1 / 2 : ℂ) -
      deriv (gaussFMinus H a b c) (1 / 2 : ℂ) * gaussFPlus H a b c (1 / 2 : ℂ) ≠ 0 := by
  have hmid : (1 / 2) ∈ gaussCutPlane := by norm_num [gaussCutPlane]
  rw [gaussFPlus_wronskian_identity hH a b c hc _ hmid]
  have h1c : 1 - c ≠ 0 := by
    intro he
    apply hc 1
    grind
  have hmid0 : (1 / 2 : ℂ) ≠ 0 := by norm_num
  have hmid1 : (1 : ℂ) - 1 / 2 ≠ 0 := by norm_num
  simp_all

/-- **Uniqueness of diagonal Gauss representations.** If a real function on the cut plane has two
representations `A |F₋|² + D |F₊|²` in the Gauss basis at zero with `c ∉ ℤ`, the coefficients
agree. -/
theorem diagonal_gauss_coefficients_unique {a b c : ℝ} (hc : ∀ n : ℤ, (c : ℂ) ≠ (n : ℂ))
    {T : ℂ → ℝ} {A₁ D₁ A₂ D₂ : ℝ}
    (h₁ : ∀ z ∈ gaussCutPlane, T z =
      A₁ * ‖gaussFMinus H a b c z‖ ^ 2 + D₁ * ‖gaussFPlus H a b c z‖ ^ 2)
    (h₂ : ∀ z ∈ gaussCutPlane, T z =
      A₂ * ‖gaussFMinus H a b c z‖ ^ 2 + D₂ * ‖gaussFPlus H a b c z‖ ^ 2) :
    A₁ = A₂ ∧ D₁ = D₂ := by
  have hF :=
    (gaussFMinus_differentiableOn_cutPlane hH a b c hc).analyticOnNhd
      gaussCutPlane_isOpen
  have hG :=
    (gaussFPlus_differentiableOn_cutPlane hH a b c hc).analyticOnNhd
      gaussCutPlane_isOpen
  have hmid : (1 / 2) ∈ gaussCutPlane := by norm_num [gaussCutPlane]
  have hEq : ∀ z ∈ gaussCutPlane,
      hermitianQuadraticTensor (gaussFMinus H a b c)
        (gaussFPlus H a b c) A₁ 0 0 D₁ z =
      hermitianQuadraticTensor (gaussFMinus H a b c)
        (gaussFPlus H a b c) A₂ 0 0 D₂ z := by
    intro z hz
    rw [diagUnique_tensor_eq_ofReal, diagUnique_tensor_eq_ofReal, ← h₁ z hz, ← h₂ z hz]
  have hcoeff := hermitianTensor_coefficients_eq_of_eqOn gaussCutPlane_isOpen hF hG
    A₁ 0 0 D₁ A₂ 0 0 D₂ hmid
    (diagUnique_wronskian_ne_zero hH a b c hc) hEq
  simp_all

end

end

end DOZZ.Proofs

end
