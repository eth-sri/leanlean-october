/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Probability.Distributions.Gaussian.Real

/-! # Splitting Gaussian averages of antitone functions

For an antitone function `f` with values in `[0, 1]`, a Gaussian average of `f (y + γ w)` is at
most the Gaussian lower-tail probability `P {γ w < -u}` plus `f (y - u)`: off the tail event the
shift `γ w` is at least `-u`, and antitonicity compares `f (y + γ w)` with `f (y - u)`. Applying
this twice, together with the elementary bound `(s + t)^2 ≤ (1 + 1/ε) s^2 + (1 + ε) t^2`, controls
two nested Gaussian averages of `f`. -/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace DOZZ.Proofs

/-! ### Elementary and integrability lemmas -/


/-- A measurable function with values in `[0, 1]` is integrable for a finite measure. -/
theorem gaussianSplit_integrable_of_bounds {μ : Measure ℝ} [IsFiniteMeasure μ] {g : ℝ → ℝ}
    (hg : Measurable g) (h0 : ∀ y, 0 ≤ g y) (h1 : ∀ y, g y ≤ 1) : Integrable g μ :=
  Integrable.of_bound hg.aestronglyMeasurable 1
    (ae_of_all _ fun y => by rw [Real.norm_of_nonneg (h0 y)]; exact h1 y)

/-- The Gaussian lower-tail event `{w | γ w < -u}` is measurable. -/
theorem gaussianSplit_measurableSet_tail γ u : MeasurableSet {w : ℝ | γ * w < -u} :=
  measurableSet_lt (by fun_prop) (by fun_prop)

/-! ### The inner average -/

/-- The integrand of the inner Gaussian average is integrable. -/
theorem gaussianSplit_integrable_shift (f : ℝ → ℝ) (hf : Antitone f) (hf0 : ∀ y, 0 ≤ f y)
    (hf1 : ∀ y, f y ≤ 1) (γ : ℝ) (v : ℝ≥0) (y : ℝ) :
    Integrable (fun w => f (y + γ * w)) (gaussianReal 0 v) :=
  gaussianSplit_integrable_of_bounds (hf.measurable.comp (by fun_prop)) (fun _ => hf0 _)
    (fun _ => hf1 _)


/-- The inner Gaussian average is nonnegative. -/
theorem gaussianSplit_inner_nonneg (f : ℝ → ℝ) (hf0 : ∀ y, 0 ≤ f y) γ (v : ℝ≥0)
    y : 0 ≤ ∫ w, f (y + γ * w) ∂gaussianReal 0 v :=
  integral_nonneg fun _ => hf0 _

/-- The inner Gaussian average is at most one. -/
theorem gaussianSplit_inner_le_one (f : ℝ → ℝ) (hf : Antitone f) (hf0 : ∀ y, 0 ≤ f y)
    (hf1 : ∀ y, f y ≤ 1) (γ : ℝ) (v : ℝ≥0) (y : ℝ) :
    ∫ w, f (y + γ * w) ∂gaussianReal 0 v ≤ 1 := by
  calc ∫ w, f (y + γ * w) ∂gaussianReal 0 v ≤ ∫ _w, (1 : ℝ) ∂gaussianReal 0 v :=
        integral_mono (gaussianSplit_integrable_shift f hf hf0 hf1 γ v y) (integrable_const _)
          fun _ => hf1 _
    _ = 1 := by simp

/-- The inner Gaussian average is antitone in the base point. -/
theorem gaussianSplit_inner_antitone (f : ℝ → ℝ) (hf : Antitone f) (hf0 : ∀ y, 0 ≤ f y)
    (hf1 : ∀ y, f y ≤ 1) (γ : ℝ) (v : ℝ≥0) :
    Antitone fun y => ∫ w, f (y + γ * w) ∂gaussianReal 0 v := by
  intro y₁ y₂ h
  exact integral_mono (gaussianSplit_integrable_shift f hf hf0 hf1 γ v y₂)
    (gaussianSplit_integrable_shift f hf hf0 hf1 γ v y₁) fun w => hf (by linarith)


/-! ### The outer average -/



/-- Two nested Gaussian averages of an antitone function bounded by one: away from Gaussian
lower-tail events of size `u` in each average, the shifts are at least `-u`. -/
theorem gaussianSplit_two_branch
    (f : ℝ → ℝ) (hf : Antitone f) (hf0 : ∀ y, 0 ≤ f y) (hf1 : ∀ y, f y ≤ 1)
    (γ : ℝ) (v₁ v₂ : ℝ≥0) (x a u ε : ℝ) (hε : 0 < ε) :
    (∫ ξ, (∫ w, f (x + a + γ * ξ + γ * w) ∂gaussianReal 0 v₂) ^ 2 ∂gaussianReal 0 v₁) ≤
      (gaussianReal 0 v₁ {ξ | γ * ξ < -u}).toReal +
        (1 + ε) * f (x + a - 2 * u) ^ 2 +
        (1 + 1 / ε) * ((gaussianReal 0 v₂ {w | γ * w < -u}).toReal) ^ 2 := by
  have gaussianSplit_outer_pointwise (ξ : ℝ) : (∫ w, f (x + a + γ * ξ + γ * w) ∂gaussianReal 0 v₂) ^ 2 ≤ {ξ : ℝ | γ * ξ < -u}.indicator 1 ξ + ((1 + ε) * f (x + a - 2 * u) ^ 2 + (1 + 1 / ε) * ((gaussianReal 0 v₂ {w | γ * w < -u}).toReal) ^ 2) := by
    have gaussianSplit_sq_pointwise ψ (hψa : Antitone ψ) (hψ0 : ∀ y, 0 ≤ ψ y) (hψ1 : ∀ y, ψ y ≤ 1) (γ : ℝ) c (u : ℝ) (ε : ℝ) (P : ℝ) (F : ℝ) (hε : 0 < ε) (hψ : ψ (c - u) ≤ P + F) (ξ : ℝ) : ψ (c + γ * ξ) ^ 2 ≤ {ξ : ℝ | γ * ξ < -u}.indicator 1 ξ + ((1 + ε) * F ^ 2 + (1 + 1 / ε) * P ^ 2) := by
      have gaussianSplit_sq_add_le (s : ℝ) (t : ℝ) (ε : ℝ) (hε : 0 < ε) : (s + t) ^ 2 ≤ (1 + 1 / ε) * s ^ 2 + (1 + ε) * t ^ 2 := by
        have : 0 ≤ (s - ε * t) ^ 2 / ε := by positivity
        have : (1 + 1 / ε) * s ^ 2 + (1 + ε) * t ^ 2 - (s + t) ^ 2 = (s - ε * t) ^ 2 / ε := by
          field_simp
          ring
        linarith
      have : 0 ≤ (1 + ε) * F ^ 2 + (1 + 1 / ε) * P ^ 2 := by positivity
      by_cases hξ : γ * ξ < -u
      · have hmem : ξ ∈ {ξ : ℝ | γ * ξ < -u} := hξ
        rw [Set.indicator_of_mem hmem]
        have : ψ (c + γ * ξ) ^ 2 ≤ 1 := pow_le_one₀ (hψ0 _) (hψ1 _)
        simp only [Pi.one_apply]
        linarith
      · have hnot : ξ ∉ {ξ : ℝ | γ * ξ < -u} := hξ
        rw [Set.indicator_of_notMem hnot, zero_add]
        calc ψ (c + γ * ξ) ^ 2 ≤ (P + F) ^ 2 :=
              pow_le_pow_left₀ (hψ0 _) ((hψa (by linarith [not_lt.1 hξ])).trans hψ) 2
          _ ≤ (1 + 1 / ε) * P ^ 2 + (1 + ε) * F ^ 2 := gaussianSplit_sq_add_le P F ε hε
          _ = (1 + ε) * F ^ 2 + (1 + 1 / ε) * P ^ 2 := by ring
    have gaussianSplit_inner_le (v : ℝ≥0) (u : ℝ) (y : ℝ) : ∫ w, f (y + γ * w) ∂gaussianReal 0 v ≤ (gaussianReal 0 v {w | γ * w < -u}).toReal + f (y - u) := by
      have gaussianSplit_pointwise (w : ℝ) : f (y + γ * w) ≤ {w : ℝ | γ * w < -u}.indicator 1 w + f (y - u) := by
        by_cases hw : γ * w < -u
        · have hmem : w ∈ {w : ℝ | γ * w < -u} := hw
          rw [Set.indicator_of_mem hmem]
          have := hf1 (y + γ * w)
          have := hf0 (y - u)
          simp only [Pi.one_apply]
          linarith
        · have hnot : w ∉ {w : ℝ | γ * w < -u} := hw
          rw [Set.indicator_of_notMem hnot]
          simpa using hf (by linarith [not_lt.1 hw])
      have hB := gaussianSplit_measurableSet_tail γ u
      have hind : Integrable ({w : ℝ | γ * w < -u}.indicator (1 : ℝ → ℝ)) (gaussianReal 0 v) :=
        (integrable_const (1 : ℝ)).indicator hB
      calc ∫ w, f (y + γ * w) ∂gaussianReal 0 v
          ≤ ∫ w, ({w : ℝ | γ * w < -u}.indicator 1 w + f (y - u)) ∂gaussianReal 0 v :=
            integral_mono (gaussianSplit_integrable_shift f hf hf0 hf1 γ v y)
              (hind.add (integrable_const _)) fun w => gaussianSplit_pointwise w
        _ = (gaussianReal 0 v {w | γ * w < -u}).toReal + f (y - u) := by
            rw [integral_add hind (integrable_const _), integral_indicator_one hB, integral_const]
            simp [Measure.real]
    have hψ : ∫ w, f (x + a - u + γ * w) ∂gaussianReal 0 v₂ ≤
        (gaussianReal 0 v₂ {w | γ * w < -u}).toReal + f (x + a - 2 * u) := by
      have h := gaussianSplit_inner_le v₂ u (x + a - u)
      rwa [(show x + a - u - u = x + a - 2 * u by ring)] at h
    exact gaussianSplit_sq_pointwise (fun y => ∫ w, f (y + γ * w) ∂gaussianReal 0 v₂)
      (gaussianSplit_inner_antitone f hf hf0 hf1 γ v₂)
      (gaussianSplit_inner_nonneg f hf0 γ v₂) (gaussianSplit_inner_le_one f hf hf0 hf1 γ v₂)
      γ (x + a) u ε _ _ hε hψ ξ
  have hB := gaussianSplit_measurableSet_tail γ u
  have hind : Integrable ({ξ : ℝ | γ * ξ < -u}.indicator (1 : ℝ → ℝ)) (gaussianReal 0 v₁) :=
    (integrable_const (1 : ℝ)).indicator hB
  calc ∫ ξ, (∫ w, f (x + a + γ * ξ + γ * w) ∂gaussianReal 0 v₂) ^ 2 ∂gaussianReal 0 v₁
      ≤ ∫ ξ, ({ξ : ℝ | γ * ξ < -u}.indicator 1 ξ +
          ((1 + ε) * f (x + a - 2 * u) ^ 2 +
            (1 + 1 / ε) * ((gaussianReal 0 v₂ {w | γ * w < -u}).toReal) ^ 2)) ∂gaussianReal 0 v₁ :=
        integral_mono (gaussianSplit_integrable_of_bounds (((gaussianSplit_inner_antitone f hf hf0 hf1 γ v₂).measurable.comp (by fun_prop : Measurable fun ξ : ℝ => x + a + γ * ξ)).pow_const 2) (fun _ => sq_nonneg _) fun ξ => pow_le_one₀ (gaussianSplit_inner_nonneg f hf0 γ v₂ (x + a + γ * ξ)) (gaussianSplit_inner_le_one f hf hf0 hf1 γ v₂ (x + a + γ * ξ))) (hind.add (integrable_const _))
          fun ξ => gaussianSplit_outer_pointwise ξ
    _ = (gaussianReal 0 v₁ {ξ | γ * ξ < -u}).toReal +
          ((1 + ε) * f (x + a - 2 * u) ^ 2 +
            (1 + 1 / ε) * ((gaussianReal 0 v₂ {w | γ * w < -u}).toReal) ^ 2) := by
        rw [integral_add hind (integrable_const _), integral_indicator_one hB, integral_const]
        simp [Measure.real]
    _ = (gaussianReal 0 v₁ {ξ | γ * ξ < -u}).toReal +
          (1 + ε) * f (x + a - 2 * u) ^ 2 +
          (1 + 1 / ε) * ((gaussianReal 0 v₂ {w | γ * w < -u}).toReal) ^ 2 := by ring

end DOZZ.Proofs
