/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.FourPoint.RootedPairMoments
public import DOZZ.FourPoint.Fusion.RootedLowerBound
public import DOZZ.FourPoint.RootedPairIdentity
public import DOZZ.FourPoint.TaylorWeightedJensen
public import DOZZ.GMC.Annulus.PositiveRoot

/-! The annular Jensen observable under the one-root identity `equatorGFF_rooted_GMC_identity`. -/

@[expose] public section
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal
namespace DOZZ.Proofs

section
variable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
  (γ : ℝ) (hγ : 0 < γ)
include hX hγ

/-- The weighted one-root identity, with a measurable functional of the supplied measure. -/
theorem rooted_weight_identity (hγ2 : γ < 2) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (f : ℂ → ℝ≥0∞) (hf : Measurable f) (hft : ∀ x, f x ≠ ⊤)
    (G : Measure ℂ → ℝ≥0∞) (hG : Measurable G) :
    (∫⁻ ω, (∫⁻ x, f x ∂M ω) * G (M ω) ∂P) =
      ∫⁻ x, f x * (∫⁻ ω, G (gmcRootedMeasure γ x (M ω)) ∂P) ∂gmcReferenceMeasure := by
  have h := equatorGFF_rooted_GMC_identity P X hX γ hγ hγ2 M hM
    (fun x _ μ => f x * G μ)
    ((hf.comp measurable_fst).mul (hG.comp (measurable_snd.comp measurable_snd)))
  calc
    _ = ∫⁻ ω, ∫⁻ x, f x * G (M ω) ∂M ω ∂P := by
      apply lintegral_congr
      intro ω
      exact (lintegral_mul_const _ hf).symm
    _ = _ := h
    _ = _ := by
      apply lintegral_congr
      intro x
      exact lintegral_const_mul' _ _ (hft x)

/-- A uniform rooted estimate on a region bounds its weighted mass expectation. -/
theorem rooted_set_weight_le (hγ₂ : γ < 2) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    {B : Set ℂ} (hB : MeasurableSet B) {K : ℂ → ℝ} (hK : Measurable K)
    {G : Measure ℂ → ℝ≥0∞} (hG : Measurable G) {C : ℝ≥0∞}
    (hroot : ∀ x ∈ B, (∫⁻ ω, G (gmcRootedMeasure γ x (M ω)) ∂P) ≤ C) :
    (∫⁻ ω, (∫⁻ x in B, ENNReal.ofReal (K x) ∂M ω) * G (M ω) ∂P) ≤
      C * ∫⁻ x in B, ENNReal.ofReal (K x) ∂gmcReferenceMeasure := by
  let f := B.indicator (fun x => ENNReal.ofReal (K x))
  have hf : Measurable f := (ENNReal.measurable_ofReal.comp hK).indicator hB
  have ht (x : ℂ) : f x ≠ ⊤ := by by_cases hx : x ∈ B <;> simp [f, hx]
  simp only [← lintegral_indicator hB]
  rw [rooted_weight_identity P X hX γ hγ hγ₂ M hM f hf ht G hG, mul_comm C, ← lintegral_mul_const C hf]
  exact lintegral_mono fun x => by
    by_cases hx : x ∈ B
    · exact mul_le_mul' le_rfl (hroot x hx)
    · simp [f, hx]

/-- Every measurable half-unit region obeys the one-root annular upper bound. -/
theorem twoRooted_annular_spatial_bound (hγ2 : γ < 2) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (α₁ α₂ α₃ p : ℝ) (hp : 0 ≤ p) :
    ∃ C : ℝ, 0 < C ∧ ∀ z : ℂ, ‖z‖ ≤ 1 / 4 →
      ∀ B : Set ℂ, MeasurableSet B → (∀ x ∈ B, ‖x‖ ≤ 1 / 2) →
        gammaHalfTwoRootedMajorantOn P M γ α₁ α₂ α₃ p z B ≤
          ENNReal.ofReal C * ∫⁻ x in B,
            ENNReal.ofReal (gammaHalfKernel γ α₁ α₂ α₃ z x / ‖x - z‖ ^ 2) := by
  obtain ⟨C, hC, hbound⟩ := rooted_coulomb_inverse_uniform P X hX γ hγ hγ2 M hM
    ![-γ / 2, α₁, α₂] α₃ (p + 1) (by linarith only [hp])
  refine ⟨C, hC, ?_⟩
  intro z hz B hB hunit
  let K (x : ℂ) := gammaHalfKernel γ α₁ α₂ α₃ z x / ‖x - z‖ ^ 2
  have hK : Measurable K := (gammaHalfKernel_measurable γ α₁ α₂ α₃ z).div
    (((measurable_id.sub_const z).norm).pow_const 2)
  let G : Measure ℂ → ℝ≥0∞ := fun μ => (coulombMass γ μ ![-γ / 2, α₁, α₂] ![z, 0, 1] α₃) ^ (-p - 1)
  have hG : Measurable G := (coulombMass_measure_measurable γ
    ![-γ / 2, α₁, α₂] ![z, 0, 1] α₃).pow_const _
  have hzunit := three_roots_in_unit_disk (show ‖z‖ ≤ 1 by linarith)
  rw [← gmcReferenceMeasure_restrict_unit_chart B hB (fun x hx => (hunit x hx).trans (by norm_num))]
  refine (gammaHalf_region_jensen_reduction P X hX γ hγ hγ2 M hM α₁ α₂ α₃ p hp z B).trans
    (rooted_set_weight_le P X hX γ hγ hγ2 M hM hB hK hG ?_)
  intro x _
  simpa only [G, show -p - 1 = -(p + 1) by ring] using hbound x ![z, 0, 1] hzunit

end

end DOZZ.Proofs
