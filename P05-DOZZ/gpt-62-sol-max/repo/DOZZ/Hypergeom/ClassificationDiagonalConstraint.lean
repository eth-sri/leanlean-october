/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Hypergeom.ClassificationCutCrossingJets
public import DOZZ.Hypergeom.ClassificationHermitianMixedJet
public import DOZZ.Hypergeom.ClassificationReflection
public import DOZZ.Hypergeom.BasisRegularity
public import DOZZ.Hypergeom.ClassificationDiagonalConnection
public import DOZZ.Hypergeom.ODE.CutPlaneTopology
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta

/-! The one-basis reflection and connection formulas force the diagonal coefficient relation. -/

@[expose] public section

open scoped Topology

namespace DOZZ.Proofs

/-- The product of a complex number and its conjugate is its complex norm square. -/
theorem complex_mul_star_eq_normSq (z : ℂ) :
    z * star z = (Complex.normSq z : ℂ) := by
  simpa only [Complex.star_def, Complex.normSq_eq_norm_sq, Complex.ofReal_pow] using Complex.mul_conj' z

/-- Reflection identifies the shifted zero basis with the one basis. -/
private theorem gaussFPlus_reflection_eq_gaussGPlus
    (H : ℂ → ℂ → ℂ → ℂ → ℂ) (a b c z : ℂ) :
    gaussFPlus H a b (1 + a + b - c) (1 - z) = gaussGPlus H a b c z := by
  have he : 1 - (1 + a + b - c) = c - a - b := by ring
  have hA : a - (1 + a + b - c) + 1 = c - b := by ring
  have hB : b - (1 + a + b - c) + 1 = c - a := by ring
  have hC : 2 - (1 + a + b - c) = 1 + c - a - b := by ring
  simp only [gaussFPlus, gaussGPlus, he, hA, hB, hC]

/-- A reflected real solution has a diagonal Hermitian representation in the one basis, and
comparison with its zero-basis representation forces the undivided coefficient constraint. -/
theorem realGaussSolution_canonical_diagonal_constraint
    {H : ℂ → ℂ → ℂ → ℂ → ℂ} (hH : IsGaussHypergeometricFamily H)
    (a b c : ℝ) (hc : ∀ n : ℤ, c ≠ (n : ℝ))
    (hδ : ∀ n : ℤ, c - a - b ≠ (n : ℝ))
    (T : ℂ → ℝ) (hT : IsRealGaussSolution a b c T) :
    ∃ α δ : ℝ,
      (∀ z ∈ gaussCutPlane,
        T z = α * ‖gaussFMinus H a b c z‖ ^ 2 +
          δ * ‖gaussFPlus H a b c z‖ ^ 2) ∧
      gaussK₁ a b c * α + gaussK₂ a b c * δ = 0 := by
  obtain ⟨α, δ, β, hrep, hβ⟩ :=
    realGaussSolution_canonical_hermitian_offDiagonal_zero hH a b c hc T hT
  let c₁ : ℝ := 1 + a + b - c
  have hc₁ : ∀ n : ℤ, c₁ ≠ (n : ℝ) := by
    intro n hn
    apply hδ (1 - n)
    dsimp [c₁] at hn
    push_cast at hn ⊢
    linarith
  let T₁ : ℂ → ℝ := fun z => T (1 - z)
  have hT₁ : IsRealGaussSolution a b c₁ T₁ := by
    simpa [T₁, c₁] using realGaussSolution_reflection a b c T hT
  obtain ⟨α₁, δ₁, β₁, hrep₁, hβ₁⟩ :=
    realGaussSolution_canonical_hermitian_offDiagonal_zero hH a b c₁ hc₁ T₁ hT₁
  let u := gaussConnectionReal₁₁ a b c
  let v := gaussConnectionReal₁₂ a b c
  let w := gaussConnectionReal₂₁ a b c
  let x := gaussConnectionReal₂₂ a b c
  let A := α * u ^ 2 + δ * w ^ 2
  let B := α * u * v + δ * w * x
  let D := α * v ^ 2 + δ * x ^ 2
  let F₁ := gaussFMinus H a b c
  let F₂ := gaussFPlus H a b c
  let G₁ := gaussGMinus H a b c
  let G₂ := gaussGPlus H a b c
  have hδC : ∀ n : ℤ, (c : ℂ) - (a : ℂ) - (b : ℂ) ≠ (n : ℂ) := by exact_mod_cast hδ
  have hlocal := gauss_local_basis_one hH (a : ℂ) (b : ℂ) (c : ℂ) hδC
  have hmid : (1 / 2 : ℂ) ∈ gaussCutPlane := by norm_num [gaussCutPlane]
  have hWmid : G₁ (1 / 2) * deriv G₂ (1 / 2) - deriv G₁ (1 / 2) * G₂ (1 / 2) ≠ 0 := by
    dsimp only [G₁, G₂]
    rw [(hlocal.2.2.1 _ hmid).2.2]
    exact mul_ne_zero (mul_ne_zero (neg_ne_zero.mpr (by simpa using hδC 0))
      (Complex.cpow_ne_zero_iff.mpr (Or.inl (by norm_num))))
      (Complex.cpow_ne_zero_iff.mpr (Or.inl (by norm_num)))
  have hEq : ∀ z ∈ gaussCutPlane,
      hermitianQuadraticTensor G₁ G₂ A B B D z = hermitianQuadraticTensor G₁ G₂ α₁ 0 0 δ₁ z := by
    intro z hz
    obtain ⟨hm, hp⟩ := gauss_connection_real a b c hH hc hδ z hz
    have hOrig : (T z : ℂ) = hermitianQuadraticTensor F₁ F₂ α 0 0 δ z := by
      simpa [F₁, F₂, hβ, hermitianQuadraticTensor, star_mul, mul_comm, mul_left_comm, mul_assoc]
        using hrep z hz
    have hc₁cast : (c₁ : ℂ) = 1 + (a : ℂ) + (b : ℂ) - (c : ℂ) := by push_cast [c₁]; rfl
    have hRef : (T z : ℂ) = hermitianQuadraticTensor G₁ G₂ α₁ 0 0 δ₁ z := by
      simpa [hβ₁, T₁, hc₁cast, sub_sub_cancel, G₁, G₂, gaussGMinus, gaussFMinus,
        gaussFPlus_reflection_eq_gaussGPlus, hermitianQuadraticTensor, star_mul,
        mul_comm, mul_left_comm, mul_assoc] using hrep₁ (1 - z) (one_sub_gaussCutPlane_subset_gaussCutPlane hz)
    rw [← hRef, hOrig]
    simp only [hermitianQuadraticTensor, F₁, F₂, G₁, G₂, hm, hp]
    simp [A, B, D, u, v, w, x, star_add, star_mul, mul_add, add_mul]
    ring
  have hcoeff := hermitianTensor_coefficients_eq_of_eqOn gaussCutPlane_isOpen
    (hlocal.1.analyticOnNhd gaussCutPlane_isOpen) (hlocal.2.1.analyticOnNhd gaussCutPlane_isOpen)
    A B B D α₁ 0 0 δ₁ hmid hWmid hEq
  have hB : B = 0 := Complex.ofReal_injective (by simpa using hcoeff.2.1)
  have hGammaDelta : Real.Gamma (c - a - b) ≠ 0 := by
    apply Real.Gamma_ne_zero
    intro n hn
    apply hδ (-(n : ℤ))
    push_cast at hn ⊢
    linarith
  have hGammaNegDelta : Real.Gamma (a + b - c) ≠ 0 := by
    apply Real.Gamma_ne_zero
    intro n hn
    apply hδ n
    push_cast at hn ⊢
    linarith
  refine ⟨α, δ, ?_, (mul_eq_zero.mp ?_).resolve_left (mul_ne_zero hGammaDelta hGammaNegDelta)⟩
  · intro z hz
    have hmul (s : ℝ) (f : ℂ) : f * star ((s : ℂ) * f) = (s * ‖f‖ ^ 2 : ℝ) := by
      rw [star_mul, Complex.star_def, Complex.conj_ofReal, ← mul_assoc,
        Complex.mul_conj', ← Complex.ofReal_pow, ← Complex.ofReal_mul, mul_comm]
    exact Complex.ofReal_injective (by simpa only [hβ, zero_mul, star_zero, add_zero, zero_add,
      hmul, ← Complex.ofReal_add] using hrep z hz)
  · rw [← gaussConnectionReal_cross]
    exact hB

end DOZZ.Proofs
