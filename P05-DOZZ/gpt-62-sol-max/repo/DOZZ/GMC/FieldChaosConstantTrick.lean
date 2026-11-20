/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GMC.FieldGaussianCommonScalar
public import DOZZ.GMC.FieldChaosConvexPower
public import DOZZ.GMC.FieldChaosConcavePower

/-! The common Gaussian scalar constant trick for continuum power moments. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped Distributions ENNReal NNReal

namespace DOZZ.Proofs

/-- Add independent noise of variance `C` to the second field and account for its
scalar Wick moment. The resulting comparison applies in both power regimes. -/
private theorem kahane_power_compare_with_scalar
    {ΩX ΩY S : Type*} [MeasurableSpace ΩX] [MeasurableSpace ΩY] [MeasurableSpace S]
    (PX : Measure ΩX) (PY : Measure ΩY) (Φ : ΩX → S → ℝ) (Ψ : ΩY → S → ℝ)
    (hΦ : IsCenteredGaussianField PX Φ) (hΨ : IsCenteredGaussianField PY Ψ)
    (ν : Measure S) [IsFiniteMeasure ν] (h : S → ℝ≥0) (hh : Measurable h)
    (hhb : ∃ c : ℝ≥0, ∀ x, h x ≤ c) (γ C p : ℝ) (hC : 0 ≤ C)
    (hcov : ∀ᵐ q ∂ν.prod ν,
      (∫ ω, Φ ω q.1 * Φ ω q.2 ∂PX) - (∫ ω, Ψ ω q.1 * Ψ ω q.2 ∂PY) ≤ C)
    (hdiag : ∀ᵐ x ∂ν,
      (∫ ω, Φ ω x ^ 2 ∂PX) - (∫ ω, Ψ ω x ^ 2 ∂PY) ≤ C) :
    let K := ENNReal.ofReal (Real.exp (γ ^ 2 * C / 2 * (p ^ 2 - p)))
    let I := ∫⁻ ω, fieldChaosMass PX Φ ν h γ ω ^ p ∂PX
    let J := ∫⁻ ω, fieldChaosMass PY Ψ ν h γ ω ^ p ∂PY
    ((p ≤ 0 ∨ 1 ≤ p) → I ≤ K * J) ∧ ((0 < p ∧ p < 1) → K * J ≤ I) := by
  let c := Real.sqrt C
  let Q := PY.prod (gaussianReal 0 1)
  let Ψc (ω : ΩY × ℝ) (x : S) := Ψ ω.1 x + c * ω.2
  have hc : c ^ 2 = C := Real.sq_sqrt hC
  have hΨc := independent_common_scalar_add_isCenteredGaussianField PY Ψ hΨ c
  have hcov' (x y : S) :
      (∫ ω, Ψc ω x * Ψc ω y ∂Q) = (∫ ω, Ψ ω x * Ψ ω y ∂PY) + C := by
    simpa only [DOZZ.gaussianCovariance, Ψc, Q, hc] using
      gaussianCovariance_field_independent_common_scalar_add PY Ψ hΨ c x y
  have hcXY : ∀ᵐ xy ∂ν.prod ν,
      (∫ ω, Φ ω xy.1 * Φ ω xy.2 ∂PX) ≤ ∫ ω, Ψc ω xy.1 * Ψc ω xy.2 ∂Q :=
    hcov.mono fun xy hxy => by rw [hcov']; linarith
  have hdXY : ∀ᵐ x ∂ν, (∫ ω, Φ ω x ^ 2 ∂PX) ≤ ∫ ω, Ψc ω x ^ 2 ∂Q :=
    hdiag.mono fun x hx => by simp only [pow_two] at hx ⊢; rw [hcov']; linarith
  simpa only [← hc, ← fieldChaosMoment_independent_common_scalar_factor PY Ψ hΨ ν h hh hhb γ c p] using ⟨fun hp => kahane_field_power_convex PX Q Φ Ψc hΦ hΨc ν h hh hhb γ p hp hcXY hdXY,
      fun hp => kahane_field_power_concave PX Q Φ Ψc hΦ hΨc ν h hh hhb γ p hp hcXY hdXY⟩

private theorem cancel_exp_factor (A : ℝ) {a b : ℝ≥0∞}
    (h : ENNReal.ofReal (Real.exp A) * a ≤ b) : a ≤ ENNReal.ofReal (Real.exp (-A)) * b := by
  have hmul : ENNReal.ofReal (Real.exp (-A)) * ENNReal.ofReal (Real.exp A) = 1 := by
    rw [← ENNReal.ofReal_mul (Real.exp_nonneg _), ← Real.exp_add, neg_add_cancel, Real.exp_zero,
      ENNReal.ofReal_one]
  simpa only [← mul_assoc, hmul, one_mul] using
    mul_le_mul_of_nonneg_left h (by positivity : 0 ≤ ENNReal.ofReal (Real.exp (-A)))

section
variable {ΩX ΩY S : Type*} [MeasurableSpace ΩX] [MeasurableSpace ΩY] [MeasurableSpace S]
  (PX : Measure ΩX) (PY : Measure ΩY) (Φ : ΩX → S → ℝ) (Ψ : ΩY → S → ℝ)
  (hΦ : IsCenteredGaussianField PX Φ) (hΨ : IsCenteredGaussianField PY Ψ) (ν : Measure S)
  [IsFiniteMeasure ν] (h : S → ℝ≥0) (hh : Measurable h) (hhb : ∃ c : ℝ≥0, ∀ x, h x ≤ c) (γ C p : ℝ)
  (hC : 0 ≤ C)
include ΩX ΩY S hΦ hΨ hh hhb hC

/-- Continuum constant trick for convex powers, including negative powers. -/
theorem kahane_field_constant_trick
    (hp : p ≤ 0 ∨ 1 ≤ p)
    (hcov : ∀ᵐ q ∂ν.prod ν,
      |(∫ ω, Φ ω q.1 * Φ ω q.2 ∂PX) -
        (∫ ω, Ψ ω q.1 * Ψ ω q.2 ∂PY)| ≤ C)
    (hdiag : ∀ᵐ x ∂ν,
      |(∫ ω, Φ ω x ^ 2 ∂PX) - (∫ ω, Ψ ω x ^ 2 ∂PY)| ≤ C) :
    ENNReal.ofReal (Real.exp (-(γ ^ 2 * C / 2 * (p ^ 2 - p)))) *
        (∫⁻ ω, fieldChaosMass PY Ψ ν h γ ω ^ p ∂PY) ≤
          ∫⁻ ω, fieldChaosMass PX Φ ν h γ ω ^ p ∂PX ∧
      (∫⁻ ω, fieldChaosMass PX Φ ν h γ ω ^ p ∂PX) ≤
        ENNReal.ofReal (Real.exp (γ ^ 2 * C / 2 * (p ^ 2 - p))) *
          (∫⁻ ω, fieldChaosMass PY Ψ ν h γ ω ^ p ∂PY) := by
  have hXY := kahane_power_compare_with_scalar PX PY Φ Ψ hΦ hΨ ν h hh hhb γ C p hC
    (hcov.mono fun _ h => (abs_le.mp h).2) (hdiag.mono fun _ h => (abs_le.mp h).2)
  have hYX := kahane_power_compare_with_scalar PY PX Ψ Φ hΨ hΦ ν h hh hhb γ C p hC
    (hcov.mono fun _ h => by linarith [(abs_le.mp h).1])
    (hdiag.mono fun _ h => by linarith [(abs_le.mp h).1])
  refine ⟨?_, hXY.1 hp⟩
  let A := γ ^ 2 * C / 2 * (p ^ 2 - p)
  calc
    _ ≤ ENNReal.ofReal (Real.exp (-A)) *
        (ENNReal.ofReal (Real.exp A) * ∫⁻ ω, fieldChaosMass PX Φ ν h γ ω ^ p ∂PX) :=
      mul_le_mul_of_nonneg_left (hYX.1 hp) (by positivity)
    _ = _ := by
      rw [← mul_assoc, ← ENNReal.ofReal_mul (Real.exp_nonneg _), ← Real.exp_add,
        neg_add_cancel, Real.exp_zero, ENNReal.ofReal_one, one_mul]

/-- Continuum constant trick for concave powers `0 < p < 1`. -/
theorem kahane_field_constant_trick_concave
    (hp : 0 < p ∧ p < 1)
    (hcov : ∀ᵐ q ∂ν.prod ν,
      |(∫ ω, Φ ω q.1 * Φ ω q.2 ∂PX) -
        (∫ ω, Ψ ω q.1 * Ψ ω q.2 ∂PY)| ≤ C)
    (hdiag : ∀ᵐ x ∂ν,
      |(∫ ω, Φ ω x ^ 2 ∂PX) - (∫ ω, Ψ ω x ^ 2 ∂PY)| ≤ C) :
    ENNReal.ofReal (Real.exp (-(γ ^ 2 * C / 2 * (p - p ^ 2)))) *
        (∫⁻ ω, fieldChaosMass PY Ψ ν h γ ω ^ p ∂PY) ≤
          ∫⁻ ω, fieldChaosMass PX Φ ν h γ ω ^ p ∂PX ∧
      (∫⁻ ω, fieldChaosMass PX Φ ν h γ ω ^ p ∂PX) ≤
        ENNReal.ofReal (Real.exp (γ ^ 2 * C / 2 * (p - p ^ 2))) *
          (∫⁻ ω, fieldChaosMass PY Ψ ν h γ ω ^ p ∂PY) := by
  have hXY := kahane_power_compare_with_scalar PX PY Φ Ψ hΦ hΨ ν h hh hhb γ C p hC
    (hcov.mono fun _ h => (abs_le.mp h).2) (hdiag.mono fun _ h => (abs_le.mp h).2)
  have hYX := kahane_power_compare_with_scalar PY PX Ψ Φ hΨ hΦ ν h hh hhb γ C p hC
    (hcov.mono fun _ h => by linarith [(abs_le.mp h).1])
    (hdiag.mono fun _ h => by linarith [(abs_le.mp h).1])
  have hsign : -(γ ^ 2 * C / 2 * (p - p ^ 2)) = γ ^ 2 * C / 2 * (p ^ 2 - p) := by ring
  rw [hsign]
  refine ⟨hXY.2 hp, ?_⟩
  simpa only [← hsign, neg_neg] using cancel_exp_factor _ (hYX.2 hp)

end

end DOZZ.Proofs
