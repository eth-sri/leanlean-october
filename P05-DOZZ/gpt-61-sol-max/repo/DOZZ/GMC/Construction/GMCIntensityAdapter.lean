/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-/
module

public import DOZZ.GMC.Assembly.UniformL1
public import DOZZ.GMC.Assembly.CircleGMCExists
public import DOZZ.GMC.Construction.GMCIntensityL1
public import DOZZ.GMC.Construction.GMCUniqueAe

/-! Exact first-moment intensity from the uniform compact-test L¹ construction. -/

public section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped Distributions ENNReal NNReal

namespace DOZZ.Proofs

private theorem integral_indicator_one_toReal
    (A : Set ℂ) (hA : MeasurableSet A) (μ : Measure ℂ) :
    ∫ x, A.indicator (fun _ : ℂ => (1 : ℝ)) x ∂μ = (μ A).toReal := by
  continuity

variable {Ω : Type*} [_inst1 : MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X) (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)

include Ω _inst1 P X hX γ hγ hγ2 M hM in
/-- Uniform `L¹` convergence for the singleton charge and the indicator of a bounded Borel set
implies the bounded-mass hypothesis in the general intensity bridge. -/
theorem equatorGFF_GMC_bounded_mass_l1_of_uniform_L1

    (Xc : Ω → ℂ → ℝ → ℝ) (hXc : IsCircleAverage P X Xc)
    (A : Set ℂ) (hA : MeasurableSet A) (R : ℝ)
    (hAR : A ⊆ Metric.closedBall (0 : ℂ) R) :
    Tendsto (fun r => ∫⁻ ω, ENNReal.ofReal
      |(regularizedGMC P Xc γ r ω A).toReal - (M ω A).toReal| ∂P)
      atTop (𝓝 0) := by
  classical
  let I : Set ℝ := {γ}
  let K : Set ℂ := Metric.closedBall (0 : ℂ) R
  have hExists : ∀ η ∈ Set.Ioo (0 : ℝ) 2, ∃ N : Ω → Measure ℂ,
      IsGMCOf P X η N := by
    intro η hη
    obtain ⟨_, N, _, hN⟩ :=
      equatorGFF_circle_average_GMC_exists P X hX η hη.1 hη.2
    exact ⟨N, hN⟩
  let Mfam : ℝ → Ω → Measure ℂ := fun η =>
    if hη : η ∈ Set.Ioo (0 : ℝ) 2 then Classical.choose (hExists η hη) else 0
  have hI : IsCompact I := by simp [I]
  have hI2 : I ⊆ Set.Ioo (0 : ℝ) 2 := by
    continuity
  have hK : IsCompact K := isCompact_closedBall _ _
  have hMfam : ∀ η ∈ Set.Ioo (0 : ℝ) 2, IsGMCOf P X η (Mfam η) := by
    grind

  have hγinterval : γ ∈ Set.Ioo (0 : ℝ) 2 := ⟨hγ, hγ2⟩
  have hUnique  :=
    equatorGFF_GMC_unique_ae P X hX γ M (Mfam γ) hM (hMfam γ hγinterval)
  let fA : ℂ → ℝ := A.indicator (fun _ => (1 : ℝ))
  have hfA : Measurable fA := measurable_const.indicator hA
  have hfBound : ∀ x, |fA x| ≤ 1 := by
    intro x
    by_cases hx : x ∈ A <;> simp [fA, hx]
  have hfSupport : ∀ x ∉ K, fA x = 0 := by
    intro x hxK
    by_cases hxA : x ∈ A
    · exact (hxK (hAR hxA)).elim
    · simp [fA, hxA]
  have hRegIntegral (r : ℝ) : ∀ᵐ ω ∂P,
      ∫ x, fA x ∂regularizedGMC P Xc γ r ω =
        (regularizedGMC P Xc γ r ω A).toReal := by
    filter_upwards [regularizedGMC_finite_ae P X hX Xc hXc γ r] with ω hω
    exact integral_indicator_one_toReal A hA _
  have hMIntegral : ∀ ω,
      ∫ x, fA x ∂M ω = (M ω A).toReal := by
    intro ω
    exact integral_indicator_one_toReal A hA (M ω)
  let S : ℝ → ℝ≥0∞ := fun r => ⨆ η ∈ I, ⨆ (f : ℂ → ℝ) (_ : Measurable f)
      (_ : ∀ x, |f x| ≤ 1) (_ : ∀ x ∉ K, f x = 0),
      ∫⁻ ω, ENNReal.ofReal
        |∫ x, f x ∂regularizedGMC P Xc η r ω - ∫ x, f x ∂Mfam η ω| ∂P
  have hS : Tendsto S atTop (𝓝 0) := equatorGFF_GMC_uniform_L1 P X hX Xc hXc Mfam hMfam
      I hI hI2 K hK 1
  have hbound (r : ℝ) :
      ∫⁻ ω, ENNReal.ofReal
        |(regularizedGMC P Xc γ r ω A).toReal - (M ω A).toReal| ∂P ≤ S r := by
    have hEq :
        ∫⁻ ω, ENNReal.ofReal
          |(regularizedGMC P Xc γ r ω A).toReal - (M ω A).toReal| ∂P =
        ∫⁻ ω, ENNReal.ofReal
          |∫ x, fA x ∂regularizedGMC P Xc γ r ω - ∫ x, fA x ∂Mfam γ ω| ∂P := by
      apply lintegral_congr_ae
      filter_upwards [hRegIntegral r, hUnique] with ω hω hωM
      grind
    rw [hEq]
    change _ ≤ ⨆ η ∈ I, ⨆ (f : ℂ → ℝ) (_ : Measurable f)
      (_ : ∀ x, |f x| ≤ 1) (_ : ∀ x ∉ K, f x = 0),
      ∫⁻ ω, ENNReal.ofReal
        |∫ x, f x ∂regularizedGMC P Xc η r ω - ∫ x, f x ∂Mfam η ω| ∂P
    refine le_iSup_of_le γ ?_
    refine le_iSup_of_le (show γ ∈ I by simp [I]) ?_
    refine le_iSup_of_le fA ?_
    simp_all
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hS
    (fun r => zero_le) hbound

include Ω _inst1 P X hX γ hγ hγ2 M hM in
/-- Exact expected GMC mass on every measurable set. -/
theorem equatorGFF_GMC_intensity
     (A : Set ℂ) (hA : MeasurableSet A) :
    ∫⁻ ω, M ω A ∂P = gmcReferenceMeasure A := by
  obtain ⟨Xc, hXc, _⟩ := hM.2
  refine equatorGFF_GMC_intensity_of_bounded_mass_l1 P X hX γ hγ hγ2 M hM Xc hXc
    (fun B hB R hBR => ?_) A hA
  exact equatorGFF_GMC_bounded_mass_l1_of_uniform_L1 P X hX γ hγ hγ2 M hM
    Xc hXc B hB R hBR

include Ω _inst1 P X hX γ hγ hγ2 M hM in
/-- The exact intensity forces the limiting chaos to be nonzero almost surely. -/
theorem equatorGFF_GMC_nontrivial
     :
    ¬ ∀ᵐ ω ∂P, M ω = 0 := by
  apply equatorGFF_GMC_nontrivial_of_intensity P M
  intro A hA
  exact equatorGFF_GMC_intensity P X hX γ hγ hγ2 M hM A hA

end DOZZ.Proofs
