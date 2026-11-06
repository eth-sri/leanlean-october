/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.SharedHyp

public import DOZZ.ShiftEquations.Shift.FirstShift
public import DOZZ.Correlations.Analytic.StructureConstantHolomorphic
public import DOZZ.Correlations.Residue.Assembly
public import DOZZ.Correlations.SumTail.Assembly

/-!
# The `R̄` representation and the first shift, with the holomorphic extension discharged

`unitVolumeStructureConstant_holomorphic_near_extended_domain` is proved, so the reductions for
`DOZZ.reflectionBarR_holomorphic_representation` and `DOZZ.reflectionR_first_shift_meromorphic` need
only the γ/2 crossing (`gammaHalf_crossing`), the residue bridge, and (for the first shift) the tail
estimate `twoInsertion_tail_sum_uniform`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology Set

namespace DOZZ.Proofs

/-- **The `R̄` representation from the γ/2 crossing and the residue bridge.** -/
theorem reflectionBarR_holomorphic_representation_of_crossing_bridge
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr)
    (M : Ω → Measure ℂ) (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2)
    (hX : IsEquatorGFF P X) (hM : IsGMCOf P X γ M)
    (hCross : CrossingHyp P M γ)
    (hBridge : ∀ α2 α3 : ℝ, 0 < α2 ∧ α2 ≤ α3 ∧ γ / 2 < α3 ∧ α3 < Q γ →
      ∃ B : ℝ → Ω → BrownianPath × BrownianPath, ∃ Z : Ω → Measure ℝ,
        IsSourceLateralProjection P X γ M Z ∧ IsReflectionData P γ α3 (B α3) Z ∧
        Tendsto (fun ε : ℝ => ε * unitVolumeStructureConstant P M γ
            (α3 - α2 + ε) α2 α3) (𝓝[>] 0)
          (𝓝 (bridgeMultiplicity α2 α3 * reflectionExponent γ α3 *
            reflectionBarR P γ α3 (B α3) Z)))
    (I : Set ℝ) (hI : ∀ α ∈ I, γ / 2 < α ∧ α < Q γ) :
    ∃ B : ℝ → Ω → BrownianPath ×
        BrownianPath,
      ∃ Z : Ω → Measure ℝ,
        IsSourceLateralProjection P X γ M Z ∧
          (∀ α ∈ I,
            IsReflectionData P γ α (B α) Z) ∧
            ∃ V : Set ℂ, IsOpen V ∧
              (∀ α ∈ I, (α : ℂ) ∈ V) ∧
              ∃ f : ℂ → ℂ, DifferentiableOn ℂ f V ∧
                (∀ α ∈ I,
                  f (α : ℂ) =
                    (unitVolumeStructureConstant P M γ α γ α : ℂ)) ∧
                DifferentiableOn ℂ
                  (fun z => rbarCoefficient γ z * f z) V ∧
                (∀ α ∈ I,
                  rbarCoefficient γ (α : ℂ) * f (α : ℂ) =
                    (reflectionBarR P γ α (B α) Z : ℂ)) :=
  reflectionBarR_holomorphic_representation_of_deps P X M γ hγ hγ2 hX hM hCross hBridge
    (unitVolumeStructureConstant_holomorphic_near_extended_domain P X M γ hγ hγ2 hX hM) I hI

/-- **The first shift of `R` from the γ/2 crossing, the residue bridge and the two-insertion tail
estimate.** -/
theorem reflectionR_first_shift_meromorphic_of_crossing_bridge_tail
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr)
    (M : Ω → Measure ℂ) (γ μ : ℝ)
    (hγ : 0 < γ) (hγ2 : γ < 2) (hμ : 0 < μ)
    (hX : IsEquatorGFF P X) (hM : IsGMCOf P X γ M)
    (hCross : CrossingHyp P M γ)
    (hBridge : ∀ α2 α3 : ℝ, 0 < α2 ∧ α2 ≤ α3 ∧ γ / 2 < α3 ∧ α3 < Q γ →
      ∃ B : ℝ → Ω → BrownianPath × BrownianPath, ∃ Z : Ω → Measure ℝ,
        IsSourceLateralProjection P X γ M Z ∧ IsReflectionData P γ α3 (B α3) Z ∧
        Tendsto (fun ε : ℝ => ε * unitVolumeStructureConstant P M γ
            (α3 - α2 + ε) α2 α3) (𝓝[>] 0)
          (𝓝 (bridgeMultiplicity α2 α3 * reflectionExponent γ α3 *
            reflectionBarR P γ α3 (B α3) Z)))
    (hTail : TailHyp P X M γ) :
    ∃ B : ℝ → Ω → BrownianPath ×
        BrownianPath,
      ∃ Z : Ω → Measure ℝ,
        IsSourceLateralProjection P X γ M Z ∧
          (∀ α : ℝ, γ / 2 < α → α < Q γ →
            IsReflectionData P γ α (B α) Z) ∧
            ∃ h : ℝ, 0 < h ∧ ∃ R : ℂ → ℂ,
              MeromorphicOn R {z | |z.im| < h} ∧
              (∀ α : ℝ, γ / 2 < α → α < Q γ →
                R (α : ℂ) =
                  (reflectionR P γ μ α (B α) Z : ℂ)) ∧
              ∀ᶠ z in codiscrete ℂ,
                R (z - γ / 2) =
                  -(μ * Real.pi : ℂ) * R z /
                    (lFun (-((γ : ℂ) ^ 2) / 4) *
                      lFun ((γ : ℂ) * z / 2 - (γ : ℂ) ^ 2 / 4) *
                      lFun (2 + (γ : ℂ) ^ 2 / 2 - (γ : ℂ) * z / 2)) :=
  reflectionR_first_shift_meromorphic_of_deps P X M γ μ hγ hγ2 hμ hX hM hCross hBridge hTail
    (unitVolumeStructureConstant_holomorphic_near_extended_domain P X M γ hγ hγ2 hX hM)

/-- **The `R̄` representation from the γ/2 crossing alone** (the residue bridge is the theorem
`unitVolumeStructureConstant_threeToTwo_residue_bridge`). -/
theorem reflectionBarR_holomorphic_representation_of_crossing
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr)
    (M : Ω → Measure ℂ) (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2)
    (hX : IsEquatorGFF P X) (hM : IsGMCOf P X γ M)
    (hCross : CrossingHyp P M γ)
    (I : Set ℝ) (hI : ∀ α ∈ I, γ / 2 < α ∧ α < Q γ) :
    ∃ B : ℝ → Ω → BrownianPath ×
        BrownianPath,
      ∃ Z : Ω → Measure ℝ,
        IsSourceLateralProjection P X γ M Z ∧
          (∀ α ∈ I,
            IsReflectionData P γ α (B α) Z) ∧
            ∃ V : Set ℂ, IsOpen V ∧
              (∀ α ∈ I, (α : ℂ) ∈ V) ∧
              ∃ f : ℂ → ℂ, DifferentiableOn ℂ f V ∧
                (∀ α ∈ I,
                  f (α : ℂ) =
                    (unitVolumeStructureConstant P M γ α γ α : ℂ)) ∧
                DifferentiableOn ℂ
                  (fun z => rbarCoefficient γ z * f z) V ∧
                (∀ α ∈ I,
                  rbarCoefficient γ (α : ℂ) * f (α : ℂ) =
                    (reflectionBarR P γ α (B α) Z : ℂ)) :=
  reflectionBarR_holomorphic_representation_of_crossing_bridge P X M γ hγ hγ2 hX hM hCross
    (fun α2 α3 hα =>
      unitVolumeStructureConstant_threeToTwo_residue_bridge P X M γ α2 α3 hγ hγ2 hα hX hM) I hI

/-- **The first shift of `R` from the γ/2 crossing alone** (the residue bridge and the tail estimate
are the theorems `unitVolumeStructureConstant_threeToTwo_residue_bridge` and
`twoInsertion_tail_sum_uniform`). -/
theorem reflectionR_first_shift_meromorphic_of_crossing
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr)
    (M : Ω → Measure ℂ) (γ μ : ℝ)
    (hγ : 0 < γ) (hγ2 : γ < 2) (hμ : 0 < μ)
    (hX : IsEquatorGFF P X) (hM : IsGMCOf P X γ M)
    (hCross : CrossingHyp P M γ) :
    ∃ B : ℝ → Ω → BrownianPath ×
        BrownianPath,
      ∃ Z : Ω → Measure ℝ,
        IsSourceLateralProjection P X γ M Z ∧
          (∀ α : ℝ, γ / 2 < α → α < Q γ →
            IsReflectionData P γ α (B α) Z) ∧
            ∃ h : ℝ, 0 < h ∧ ∃ R : ℂ → ℂ,
              MeromorphicOn R {z | |z.im| < h} ∧
              (∀ α : ℝ, γ / 2 < α → α < Q γ →
                R (α : ℂ) =
                  (reflectionR P γ μ α (B α) Z : ℂ)) ∧
              ∀ᶠ z in codiscrete ℂ,
                R (z - γ / 2) =
                  -(μ * Real.pi : ℂ) * R z /
                    (lFun (-((γ : ℂ) ^ 2) / 4) *
                      lFun ((γ : ℂ) * z / 2 - (γ : ℂ) ^ 2 / 4) *
                      lFun (2 + (γ : ℂ) ^ 2 / 2 - (γ : ℂ) * z / 2)) :=
  reflectionR_first_shift_meromorphic_of_crossing_bridge_tail P X M γ μ hγ hγ2 hμ hX hM hCross
    (fun α2 α3 hα =>
      unitVolumeStructureConstant_threeToTwo_residue_bridge P X M γ α2 α3 hγ hγ2 hα hX hM)
    (fun K2 K3 hK2 hK3 hpos2 hpos3 hsep A2 A3 hA2 hA3 hα2 hα3 F2s F3s radius supBound
        derivBound lowerBound hF2 hF3 =>
      twoInsertion_tail_sum_uniform P X M γ hγ hγ2 hX hM K2 K3 hK2 hK3 hpos2 hpos3 hsep A2 A3
        hA2 hA3 hα2 hα3 F2s F3s radius supBound derivBound lowerBound hF2 hF3)

end DOZZ.Proofs

end
