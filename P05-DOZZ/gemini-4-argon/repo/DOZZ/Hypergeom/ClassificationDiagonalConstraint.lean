/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Hypergeom.ClassificationCutCrossingJets
public import DOZZ.Hypergeom.ClassificationHermitianMixedJet
public import DOZZ.Hypergeom.ClassificationReflection
public import DOZZ.Hypergeom.BasisRegularity
public import DOZZ.Hypergeom.GaussConnectionMinus
public import DOZZ.Hypergeom.GaussConnectionPlus
public import DOZZ.Hypergeom.ODE.CutPlaneTopology
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta

/-! The one-basis reflection and connection formulas force the diagonal coefficient relation. -/

@[expose] public section

open scoped Topology

namespace DOZZ.Proofs

/-- The product of a complex number and its conjugate is its complex norm square. -/
theorem complex_mul_star_eq_normSq (z : ℂ) :
    z * star z = (Complex.normSq z : ℂ) := by
  calc
    z * star z = (‖z‖ ^ 2 : ℝ) := by
      simpa [Complex.star_def] using Complex.mul_conj' z
    _ = (Complex.normSq z : ℂ) := by rw [Complex.normSq_eq_norm_sq]


/-- A reflected real solution has a diagonal Hermitian representation in the one basis, and
comparison with its zero-basis representation forces the undivided coefficient constraint. -/
theorem realGaussSolution_canonical_diagonal_constraint
    {H} (hH : IsGaussHypergeometricFamily H)
    a b c (hc : ∀ n : ℤ, c ≠ (n : ℝ))
    (hδ : ∀ n : ℤ, c - a - b ≠ (n : ℝ))
    T (hT : IsRealGaussSolution a b c T) :
    ∃ α δ : ℝ,
      (∀ z ∈ gaussCutPlane,
        T z = α * ‖gaussFMinus H a b c z‖ ^ 2 +
          δ * ‖gaussFPlus H a b c z‖ ^ 2) ∧
      gaussK₁ a b c * α + gaussK₂ a b c * δ = 0 := by
  have gaussFPlus_reflection_eq_gaussGPlus a b c z : gaussFPlus H a b (1 + a + b - c) (1 - z) = gaussGPlus H a b c z := by
    have he : 1 - (1 + a + b - c) = c - a - b := by ring
    have hA : a - (1 + a + b - c) + 1 = c - b := by ring
    have hB : b - (1 + a + b - c) + 1 = c - a := by ring
    have hC : 2 - (1 + a + b - c) = 1 + c - a - b := by ring
    simp only [gaussFPlus, gaussGPlus, he, hA, hB, hC]
  obtain ⟨α, δ, β, hrep, hβ⟩ :=
    realGaussSolution_canonical_hermitian_offDiagonal_zero hH a b c hc T hT
  let c₁ := 1 + a + b - c
  have hc₁ : ∀ n : ℤ, c₁ ≠ (n : ℝ) := by
    intro n hn
    apply hδ (1 - n)
    dsimp [c₁] at hn
    push_cast at hn ⊢
    linarith
  let T₁ : ℂ → ℝ := fun z => T (1 - z)
  obtain ⟨α₁, δ₁, β₁, hrep₁, hβ₁⟩ :=
    realGaussSolution_canonical_hermitian_offDiagonal_zero hH a b c₁ hc₁ T₁ (by simpa [T₁, c₁] using realGaussSolution_reflection a b c T hT)
  let u := Real.Gamma c * Real.Gamma (c - a - b) *
    (Real.Gamma (c - a))⁻¹ * (Real.Gamma (c - b))⁻¹
  let v := Real.Gamma c * Real.Gamma (a + b - c) *
    (Real.Gamma a)⁻¹ * (Real.Gamma b)⁻¹
  let w := Real.Gamma (2 - c) * Real.Gamma (c - a - b) *
    (Real.Gamma (1 - a))⁻¹ * (Real.Gamma (1 - b))⁻¹
  let x := Real.Gamma (2 - c) * Real.Gamma (a + b - c) *
    (Real.Gamma (a - c + 1))⁻¹ * (Real.Gamma (b - c + 1))⁻¹
  let A := α * u ^ 2 + δ * w ^ 2
  let B := α * u * v + δ * w * x
  let D := α * v ^ 2 + δ * x ^ 2
  have hδcast : ((c - a - b : ℝ) : ℂ) = (c : ℂ) - (a : ℂ) - (b : ℂ) := by
    push_cast
    ring
  have hnegδcast : ((a + b - c : ℝ) : ℂ) = (a : ℂ) + (b : ℂ) - (c : ℂ) := by
    push_cast
    ring
  have h2cCast : ((2 - c : ℝ) : ℂ) = (2 : ℂ) - (c : ℂ) := by push_cast; ring
  have hcC : ∀ n : ℤ, (c : ℂ) ≠ (n : ℂ) := by
    intro n hn
    apply hc n
    exact_mod_cast hn
  have hδC : ∀ n : ℤ, (c : ℂ) - (a : ℂ) - (b : ℂ) ≠ (n : ℂ) := by
    intro n hn
    apply hδ n
    have hn' : ((c - a - b : ℝ) : ℂ) = (n : ℂ) := by
      calc
        ((c - a - b : ℝ) : ℂ) = (c : ℂ) - (a : ℂ) - (b : ℂ) := hδcast
        _ = (n : ℂ) := hn
    exact_mod_cast hn'
  have hlocal := gauss_local_basis_one hH (a : ℂ) (b : ℂ) (c : ℂ) hδC
  have hmid : (1 / 2 : ℂ) ∈ gaussCutPlane := by
    norm_num [gaussCutPlane]
  have hδ0 : (c : ℂ) - (a : ℂ) - (b : ℂ) ≠ 0 := by
    intro hz
    apply hδ 0
    exact_mod_cast (show ((c - a - b : ℝ) : ℂ) = 0 by rw [hδcast]; exact hz)
  have hEq : ∀ z ∈ gaussCutPlane,
      hermitianQuadraticTensor (gaussGMinus H (a : ℂ) (b : ℂ) (c : ℂ))
        (gaussGPlus H (a : ℂ) (b : ℂ) (c : ℂ)) (A : ℂ) (B : ℂ) (B : ℂ) (D : ℂ) z =
      hermitianQuadraticTensor (gaussGMinus H (a : ℂ) (b : ℂ) (c : ℂ))
        (gaussGPlus H (a : ℂ) (b : ℂ) (c : ℂ)) (α₁ : ℂ) 0 0 (δ₁ : ℂ) z := by
    intro z hz
    have hminus := (gauss_connection_minus hH (a : ℂ) (b : ℂ) (c : ℂ) hcC hδC) z hz
    have hplus := (gauss_connection_plus hH (a : ℂ) (b : ℂ) (c : ℂ) hcC hδC) z hz
    have hOrig := hrep z hz
    rw [hβ] at hOrig
    have hRef := hrep₁ (1 - z) (one_sub_gaussCutPlane_subset_gaussCutPlane hz)
    rw [hβ₁] at hRef
    have hRefTensor : (T z : ℂ) = hermitianQuadraticTensor
        (gaussGMinus H (a : ℂ) (b : ℂ) (c : ℂ))
        (gaussGPlus H (a : ℂ) (b : ℂ) (c : ℂ)) (α₁ : ℂ) 0 0 (δ₁ : ℂ) z := by
      calc
        (T z : ℂ) = (T (1 - (1 - z)) : ℂ) := by congr 1; ring_nf
        _ = (T₁ (1 - z) : ℂ) := rfl
        _ = hermitianQuadraticTensor
            (gaussFMinus H (a : ℂ) (b : ℂ) (c₁ : ℂ))
            (gaussFPlus H (a : ℂ) (b : ℂ) (c₁ : ℂ))
            (α₁ : ℂ) 0 0 (δ₁ : ℂ) (1 - z) := by
          simpa [hermitianQuadraticTensor, star_mul, mul_comm, mul_left_comm, mul_assoc] using hRef
        _ = hermitianQuadraticTensor
            (gaussGMinus H (a : ℂ) (b : ℂ) (c : ℂ))
            (gaussGPlus H (a : ℂ) (b : ℂ) (c : ℂ))
            (α₁ : ℂ) 0 0 (δ₁ : ℂ) z := by
          have hc₁cast : (c₁ : ℂ) = 1 + (a : ℂ) + (b : ℂ) - (c : ℂ) := by
            dsimp [c₁]
            push_cast
            ring
          simp only [hermitianQuadraticTensor]
          rw [(show gaussFMinus H (a : ℂ) (b : ℂ) (c₁ : ℂ) (1 - z) = gaussGMinus H (a : ℂ) (b : ℂ) (c : ℂ) z by rw [hc₁cast]; rfl), (show gaussFPlus H (a : ℂ) (b : ℂ) (c₁ : ℂ) (1 - z) = gaussGPlus H (a : ℂ) (b : ℂ) (c : ℂ) z by rw [hc₁cast]; exact gaussFPlus_reflection_eq_gaussGPlus (a : ℂ) (b : ℂ) (c : ℂ) z)]
    have hchange : hermitianQuadraticTensor
        (gaussFMinus H (a : ℂ) (b : ℂ) (c : ℂ))
        (gaussFPlus H (a : ℂ) (b : ℂ) (c : ℂ)) (α : ℂ) 0 0 (δ : ℂ) z =
      hermitianQuadraticTensor (gaussGMinus H (a : ℂ) (b : ℂ) (c : ℂ))
        (gaussGPlus H (a : ℂ) (b : ℂ) (c : ℂ)) (A : ℂ) (B : ℂ) (B : ℂ) (D : ℂ) z := by
      simp only [hermitianQuadraticTensor]
      rw [(show gaussFMinus H (a : ℂ) (b : ℂ) (c : ℂ) z = (u : ℂ) * gaussGMinus H (a : ℂ) (b : ℂ) (c : ℂ) z + (v : ℂ) * gaussGPlus H (a : ℂ) (b : ℂ) (c : ℂ) z by rw [(show Complex.Gamma (c : ℂ) * Complex.Gamma ((c : ℂ) - (a : ℂ) - (b : ℂ)) * (Complex.Gamma ((c : ℂ) - (a : ℂ)))⁻¹ * (Complex.Gamma ((c : ℂ) - (b : ℂ)))⁻¹ = (u : ℂ) by rw [← hδcast, ← (show ((c - a : ℝ) : ℂ) = (c : ℂ) - (a : ℂ) by push_cast; ring), ← (show ((c - b : ℝ) : ℂ) = (c : ℂ) - (b : ℂ) by push_cast; ring)]; simp only [u, Complex.Gamma_ofReal, Complex.ofReal_inv, Complex.ofReal_mul]), (show Complex.Gamma (c : ℂ) * Complex.Gamma ((a : ℂ) + (b : ℂ) - (c : ℂ)) * (Complex.Gamma (a : ℂ))⁻¹ * (Complex.Gamma (b : ℂ))⁻¹ = (v : ℂ) by rw [← hnegδcast]; simp only [v, Complex.Gamma_ofReal, Complex.ofReal_inv, Complex.ofReal_mul])] at hminus; exact hminus), (show gaussFPlus H (a : ℂ) (b : ℂ) (c : ℂ) z = (w : ℂ) * gaussGMinus H (a : ℂ) (b : ℂ) (c : ℂ) z + (x : ℂ) * gaussGPlus H (a : ℂ) (b : ℂ) (c : ℂ) z by rw [(show Complex.Gamma (2 - (c : ℂ)) * Complex.Gamma ((c : ℂ) - (a : ℂ) - (b : ℂ)) * (Complex.Gamma (1 - (a : ℂ)))⁻¹ * (Complex.Gamma (1 - (b : ℂ)))⁻¹ = (w : ℂ) by rw [← h2cCast, ← hδcast, ← (show ((1 - a : ℝ) : ℂ) = (1 : ℂ) - (a : ℂ) by push_cast; ring), ← (show ((1 - b : ℝ) : ℂ) = (1 : ℂ) - (b : ℂ) by push_cast; ring)]; simp only [w, Complex.Gamma_ofReal, Complex.ofReal_inv, Complex.ofReal_mul]), (show Complex.Gamma (2 - (c : ℂ)) * Complex.Gamma ((a : ℂ) + (b : ℂ) - (c : ℂ)) * (Complex.Gamma ((a : ℂ) - (c : ℂ) + 1))⁻¹ * (Complex.Gamma ((b : ℂ) - (c : ℂ) + 1))⁻¹ = (x : ℂ) by rw [← h2cCast, ← hnegδcast, ← (show ((a - c + 1 : ℝ) : ℂ) = (a : ℂ) - (c : ℂ) + 1 by push_cast; ring), ← (show ((b - c + 1 : ℝ) : ℂ) = (b : ℂ) - (c : ℂ) + 1 by push_cast; ring)]; simp only [x, Complex.Gamma_ofReal, Complex.ofReal_inv, Complex.ofReal_mul])] at hplus; exact hplus)]
      simp [A, B, D, star_add, star_mul, mul_add, add_mul]
      ring_nf
    calc
      _ = hermitianQuadraticTensor
          (gaussFMinus H (a : ℂ) (b : ℂ) (c : ℂ))
          (gaussFPlus H (a : ℂ) (b : ℂ) (c : ℂ)) (α : ℂ) 0 0 (δ : ℂ) z := hchange.symm
      _ = (T z : ℂ) := (show (T z : ℂ) = hermitianQuadraticTensor (gaussFMinus H (a : ℂ) (b : ℂ) (c : ℂ)) (gaussFPlus H (a : ℂ) (b : ℂ) (c : ℂ)) (α : ℂ) 0 0 (δ : ℂ) z by simpa [hermitianQuadraticTensor, star_mul, mul_comm, mul_left_comm, mul_assoc] using hOrig).symm
      _ = hermitianQuadraticTensor
          (gaussGMinus H (a : ℂ) (b : ℂ) (c : ℂ))
          (gaussGPlus H (a : ℂ) (b : ℂ) (c : ℂ)) (α₁ : ℂ) 0 0 (δ₁ : ℂ) z := hRefTensor
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
  refine ⟨α, δ, ?_, (by apply (mul_eq_zero.mp ?_).resolve_left (mul_ne_zero hGammaDelta hGammaNegDelta); rw [← (show B = Real.Gamma (c - a - b) * Real.Gamma (a + b - c) * (gaussK₁ a b c * α + gaussK₂ a b c * δ) by dsimp [B, u, v, w, x, gaussK₁, gaussK₂]; ring), (Complex.ofReal_injective (hermitianTensor_coefficients_eq_of_eqOn gaussCutPlane_isOpen (hlocal.1.analyticOnNhd gaussCutPlane_isOpen) (hlocal.2.1.analyticOnNhd gaussCutPlane_isOpen) A B B D α₁ 0 0 δ₁ hmid (by rw [((hlocal.2.2.1 (1 / 2 : ℂ) hmid).2.2)]; exact mul_ne_zero (mul_ne_zero (neg_ne_zero.mpr hδ0) (Complex.cpow_ne_zero_iff.mpr (Or.inl (by norm_num)))) (Complex.cpow_ne_zero_iff.mpr (Or.inl (by norm_num)))) hEq).2.1)])⟩
  intro z hz
  apply Complex.ofReal_injective
  calc
    (T z : ℂ) = gaussFMinus H (a : ℂ) (b : ℂ) (c : ℂ) z *
        star ((α : ℂ) * gaussFMinus H (a : ℂ) (b : ℂ) (c : ℂ) z) +
      gaussFPlus H (a : ℂ) (b : ℂ) (c : ℂ) z *
        star ((δ : ℂ) * gaussFPlus H (a : ℂ) (b : ℂ) (c : ℂ) z) := by
      simpa [hβ] using (hrep z hz)
    _ = (α : ℂ) * (gaussFMinus H (a : ℂ) (b : ℂ) (c : ℂ) z *
          star (gaussFMinus H (a : ℂ) (b : ℂ) (c : ℂ) z)) +
        (δ : ℂ) * (gaussFPlus H (a : ℂ) (b : ℂ) (c : ℂ) z *
          star (gaussFPlus H (a : ℂ) (b : ℂ) (c : ℂ) z)) := by
      simp only [star_mul, Complex.star_def, Complex.conj_ofReal]
      ring
    _ = (α : ℂ) * Complex.normSq (gaussFMinus H (a : ℂ) (b : ℂ) (c : ℂ) z) +
        (δ : ℂ) * Complex.normSq (gaussFPlus H (a : ℂ) (b : ℂ) (c : ℂ) z) := by
      rw [complex_mul_star_eq_normSq, complex_mul_star_eq_normSq]
    _ = (α : ℂ) * (‖gaussFMinus H (a : ℂ) (b : ℂ) (c : ℂ) z‖ ^ 2 : ℝ) +
        (δ : ℂ) * (‖gaussFPlus H (a : ℂ) (b : ℂ) (c : ℂ) z‖ ^ 2 : ℝ) := by
      simp only [Complex.normSq_eq_norm_sq]
    _ = ((α * ‖gaussFMinus H a b c z‖ ^ 2 +
        δ * ‖gaussFPlus H a b c z‖ ^ 2 : ℝ) : ℂ) := by push_cast; ring

end DOZZ.Proofs
