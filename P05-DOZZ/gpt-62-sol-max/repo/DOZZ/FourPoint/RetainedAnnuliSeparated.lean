/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.FourPoint.RetainedAnnuliComparison
public import DOZZ.GMC.SharpMoments.GluedFieldGaussian

/-! Independent reference pieces for spatially separated retained masses. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal Distributions

namespace DOZZ.Proofs

section
variable {Ω S : Type*} [MeasurableSpace Ω] [MeasurableSpace S] (P : Measure Ω) (Φ : Ω → S → ℝ)
  (hΦ : IsCenteredGaussianField P Φ) (A : Set S)
include Ω S hΦ

/-- A retained weight supported in the first piece uses precisely the first independent copy. -/
theorem piece_field_mass_first (ν : Measure S) (h : S → ℝ≥0) (hs : ∀ x, x ∉ A → h x = 0)
    (γ : ℝ) (w : Ω × Ω) :
    fieldChaosMass (P.prod P) (independent_piece_field Φ A) ν h γ w =
      fieldChaosMass P Φ ν h γ w.1 := by
  unfold fieldChaosMass
  apply lintegral_congr
  intro x
  rw [independent_piece_field_variance P Φ hΦ A x]
  by_cases hx : x ∈ A
  · simp only [independent_piece_field, Set.indicator_of_mem hx,
      Set.indicator_of_notMem (show x ∉ Aᶜ from fun h => h hx), add_zero]
  · simp only [hs x hx, ENNReal.coe_zero, zero_mul]

/-- A retained weight supported in the second piece uses precisely the second independent copy. -/
theorem piece_field_mass_second (ν : Measure S) (h : S → ℝ≥0) (hs : ∀ x, x ∈ A → h x = 0)
    (γ : ℝ) (w : Ω × Ω) :
    fieldChaosMass (P.prod P) (independent_piece_field Φ A) ν h γ w =
      fieldChaosMass P Φ ν h γ w.2 := by
  unfold fieldChaosMass
  apply lintegral_congr
  intro x
  rw [independent_piece_field_variance P Φ hΦ A x]
  by_cases hx : x ∈ A
  · simp only [hs x hx, ENNReal.coe_zero, zero_mul]
  · simp only [independent_piece_field, Set.indicator_of_notMem hx,
      Set.indicator_of_mem (show x ∈ Aᶜ from hx), zero_add]

/-- A bounded cross-piece covariance gives an upper product bound by independent masses.
The within-piece laws and the common scalar factor appear explicitly. -/
theorem two_retained_blocks_inverse_compare (hA : MeasurableSet A) (ν : Measure S) [IsFiniteMeasure ν]
    (h₀ h₁ : S → ℝ≥0) (hm₀ : Measurable h₀) (hm₁ : Measurable h₁)
    (hb₀ : ∃ c : ℝ≥0, ∀ x, h₀ x ≤ c) (hb₁ : ∃ c : ℝ≥0, ∀ x, h₁ x ≤ c)
    (hs₀ : ∀ x, x ∉ A → h₀ x = 0) (hs₁ : ∀ x, x ∈ A → h₁ x = 0)
    (γ C a b : ℝ) (hC : 0 ≤ C) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hcross : ∀ᵐ xy ∂ν.prod ν,
      (xy.1 ∈ A ↔ xy.2 ∉ A) → (∫ ω, Φ ω xy.1 * Φ ω xy.2 ∂P) ≤ C) :
    (∫⁻ ω, (fieldChaosMass P Φ ν h₀ γ ω) ^ (-a) *
      (fieldChaosMass P Φ ν h₁ γ ω) ^ (-b) ∂P) ≤
      ENNReal.ofReal (Real.exp (γ ^ 2 * C / 2 * ((a + b) ^ 2 + a + b))) *
        (∫⁻ ω, (fieldChaosMass P Φ ν h₀ γ ω) ^ (-a) ∂P) *
          (∫⁻ ω, (fieldChaosMass P Φ ν h₁ γ ω) ^ (-b) ∂P) := by
  classical
  have  := (hΦ.2 0 (fun i : Fin 0 => Fin.elim0 i)).1
  let Ψ := independent_piece_field Φ A
  have hΨ := independent_piece_field_gaussian P Φ hΦ A hA
  have hcov : ∀ᵐ xy ∂ν.prod ν,
      (∫ ω, Φ ω xy.1 * Φ ω xy.2 ∂P) ≤
        (∫ w, Ψ w xy.1 * Ψ w xy.2 ∂P.prod P) + C := by
    filter_upwards [hcross] with xy hxy
    change gaussianCovariance P _ _ ≤ gaussianCovariance (P.prod P) _ _ + C
    rw [independent_piece_field_covariance P Φ hΦ A xy.1 xy.2]
    by_cases h : xy.1 ∈ A ↔ xy.2 ∈ A
    · simp [h, hC]
    · simpa [h, gaussianCovariance] using hxy (by tauto)
  have hdiag : ∀ᵐ x ∂ν, (∫ ω, Φ ω x ^ 2 ∂P) ≤ (∫ w, Ψ w x ^ 2 ∂P.prod P) + C := by
    filter_upwards [] with x
    rw [independent_piece_field_variance P Φ hΦ A x]
    exact le_add_of_nonneg_right hC
  have hk := retained_fields_multi_negative_compare P (P.prod P) Φ Ψ hΦ hΨ ν
    ![h₀, h₁] (by intro k; fin_cases k <;> assumption)
    (by intro k; fin_cases k <;> assumption) γ C hC ![a, b]
    (by intro k; fin_cases k <;> assumption) hcov hdiag
  simp only [Fin.prod_univ_two, Fin.sum_univ_two, Matrix.cons_val_zero,
    Matrix.cons_val_one] at hk
  have hm0 : AEMeasurable (fun ω => (fieldChaosMass P Φ ν h₀ γ ω) ^ (-a)) P :=
    (centeredGaussianField_fieldChaosMass_measurable P Φ hΦ ν h₀ hm₀ γ).aemeasurable.pow_const _
  have hm1 : AEMeasurable (fun ω => (fieldChaosMass P Φ ν h₁ γ ω) ^ (-b)) P :=
    (centeredGaussianField_fieldChaosMass_measurable P Φ hΦ ν h₁ hm₁ γ).aemeasurable.pow_const _
  have hrhs : (∫⁻ w : Ω × Ω, (fieldChaosMass (P.prod P) Ψ ν h₀ γ w) ^ (-a) *
      (fieldChaosMass (P.prod P) Ψ ν h₁ γ w) ^ (-b) ∂P.prod P) =
        (∫⁻ ω, (fieldChaosMass P Φ ν h₀ γ ω) ^ (-a) ∂P) *
          (∫⁻ ω, (fieldChaosMass P Φ ν h₁ γ ω) ^ (-b) ∂P) := by
    dsimp only [Ψ]
    simp_rw [piece_field_mass_first P Φ hΦ A ν h₀ hs₀,
      piece_field_mass_second P Φ hΦ A ν h₁ hs₁]
    exact lintegral_prod_mul hm0 hm1
  rw [hrhs] at hk
  simpa only [mul_assoc, add_assoc] using hk

end

end DOZZ.Proofs
