/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.ShiftEquations.Shift.FirstShift
public import DOZZ.Correlations.Analytic.StructureConstantHolomorphic
public import DOZZ.Correlations.Residue.Assembly
public import DOZZ.Correlations.SumTail.Assembly
public import DOZZ.ShiftEquations.Contracts
public import DOZZ.Correlations.TailContracts

/-!
# The `R̄` representation and the first shift, with the holomorphic extension discharged

`unitVolumeStructureConstant_holomorphic_near_extended_domain` is proved, so the reductions for
`DOZZ.reflectionBarR_holomorphic_representation` and `DOZZ.reflectionR_first_shift_meromorphic` need
only the γ/2 crossing (`gammaHalf_crossing`), the residue bridge, and (for the first shift) the tail
estimate `twoInsertion_tail_sum_uniform`.
-/

public section

open MeasureTheory ProbabilityTheory Filter Topology Set

namespace DOZZ.Proofs

variable {Ω : Type*} [_inst1 : MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr) (M : Ω → Measure ℂ)

include Ω _inst1 P X M in
/-- **The `R̄` representation from the γ/2 crossing and the residue bridge.** -/
theorem reflectionBarR_holomorphic_representation_of_crossing_bridge
     (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2)
    (hX : IsEquatorGFF P X) (hM : IsGMCOf P X γ M)
    (hCross : Contract.unitCrossing P M γ)
    (hBridge : Contract.residueBridge P X M γ)
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

include Ω _inst1 P X M in
/-- **The first shift of `R` from the γ/2 crossing, the residue bridge and the two-insertion tail
estimate.** -/
theorem reflectionR_first_shift_meromorphic_of_crossing_bridge_tail
     (γ μ : ℝ)
    (hγ : 0 < γ) (hγ2 : γ < 2) (hμ : 0 < μ)
    (hX : IsEquatorGFF P X) (hM : IsGMCOf P X γ M)
    (hCross : Contract.unitCrossing P M γ)
    (hBridge : Contract.residueBridge P X M γ)
    (hTail : Contract.uniformTwoInsertionTail P X M γ) :
    Contract.firstShift P X M γ μ :=
  reflectionR_first_shift_meromorphic_of_deps P X M γ μ hγ hγ2 hμ hX hM hCross hBridge hTail
    (unitVolumeStructureConstant_holomorphic_near_extended_domain P X M γ hγ hγ2 hX hM)

include Ω _inst1 P X M in
/-- **The `R̄` representation from the γ/2 crossing alone** (the residue bridge is the theorem
`unitVolumeStructureConstant_threeToTwo_residue_bridge`). -/
theorem reflectionBarR_holomorphic_representation_of_crossing
     (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2)
    (hX : IsEquatorGFF P X) (hM : IsGMCOf P X γ M)
    (hCross : Contract.unitCrossing P M γ)
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

include Ω _inst1 P X M in
/-- **The first shift of `R` from the γ/2 crossing alone** (the residue bridge and the tail estimate
are the theorems `unitVolumeStructureConstant_threeToTwo_residue_bridge` and
`twoInsertion_tail_sum_uniform`). -/
theorem reflectionR_first_shift_meromorphic_of_crossing
     (γ μ : ℝ)
    (hγ : 0 < γ) (hγ2 : γ < 2) (hμ : 0 < μ)
    (hX : IsEquatorGFF P X) (hM : IsGMCOf P X γ M)
    (hCross : Contract.unitCrossing P M γ) :
    Contract.firstShift P X M γ μ :=
  reflectionR_first_shift_meromorphic_of_crossing_bridge_tail P X M γ μ hγ hγ2 hμ hX hM hCross
    (fun α2 α3 hα =>
      unitVolumeStructureConstant_threeToTwo_residue_bridge P X M γ α2 α3 hγ hγ2 hα hX hM)
    (fun K2 K3 hK2 hK3 hpos2 hpos3 hsep A2 A3 hA2 hA3 hα2 hα3 F2s F3s radius supBound
        derivBound lowerBound hF2 hF3 =>
      twoInsertion_tail_sum_uniform P X M γ hγ hγ2 hX hM K2 K3 hK2 hK3 hpos2 hpos3 hsep A2 A3
        hA2 hA3 hα2 hα3 F2s F3s radius supBound derivBound lowerBound hF2 hF3)

end DOZZ.Proofs

end
