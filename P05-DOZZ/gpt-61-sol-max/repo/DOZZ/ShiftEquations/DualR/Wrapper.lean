/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.ShiftEquations.DualR.Assembly
public import DOZZ.ShiftEquations.Shift.Wrappers
public import DOZZ.ShiftEquations.Gluing.ReflectedWrapper
public import DOZZ.ShiftEquations.Inversion.Reduction
public import DOZZ.ShiftEquations.FirstStrip.Closed
public import DOZZ.ShiftEquations.Contracts
public import DOZZ.ShiftEquations.ContinuationContracts

/-!
# The dual shift of `R` from the γ/2 crossing, the gluing, the inversion and the second dual seed

The inputs `DOZZ.reflectionR_first_shift_meromorphic` and
`DOZZ.reflectionBarR_holomorphic_representation` of
`reflectionR_dual_shift_unknown_constant_of_deps` follow from the unit-volume conjunct of the γ/2
crossing `DOZZ.gammaHalf_crossing` alone (`reflectionR_first_shift_meromorphic_of_crossing`,
`reflectionBarR_holomorphic_representation_of_crossing`).
-/

public section

open MeasureTheory Filter Topology Set

namespace DOZZ.Proofs

variable {Ω : Type*} [_inst1 : MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr) (M : Ω → Measure ℂ) (γ μ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (hγirr : Irrational (γ ^ 2)) (hμ : 0 < μ) (hX : IsEquatorGFF P X) (hM : IsGMCOf P X γ M) (hCross : Contract.unitCrossing P M γ)

include Ω _inst1 P X M γ μ hγ hγ2 hγirr hμ hX hM hCross in
/-- **The dual shift of `R` from the γ/2 crossing, the gluing, the inversion and the second dual
seed.** `hCross` is the unit-volume conjunct of `DOZZ.gammaHalf_crossing`; `hShiftGluing`, `hInversion`, `hSeed`
are the conclusions of `DOZZ.structureConstant_reflected_shift_and_gluing`,
`DOZZ.reflectionR_inversion_meromorphic` and `DOZZ.dual_crossing_seed_two`, at the given field,
chaos, coupling and cosmological constant. -/
theorem reflectionR_dual_shift_unknown_constant_of_crossing
    
    (hShiftGluing : Contract.shiftGluing P X M γ μ)
    (hInversion : ∃ B : ℝ → Ω → BrownianPath × BrownianPath,
      ∃ Z : Ω → Measure ℝ,
        IsSourceLateralProjection P X γ M Z ∧
          (∀ α : ℝ, γ / 2 < α → α < Q γ →
            IsReflectionData P γ α (B α) Z) ∧
            ∃ h : ℝ, 0 < h ∧ ∃ R : ℂ → ℂ,
              MeromorphicOn R {z | |z.im| < h} ∧
              (∀ α : ℝ, γ / 2 < α → α < Q γ →
                R (α : ℂ) =
                  (reflectionR P γ μ α (B α) Z : ℂ)) ∧
              ∀ᶠ z in codiscrete ℂ, R z * R (2 * Q γ - z) = 1)
    (hSeed : Contract.dualSecondSeed P X M γ μ) :
    Contract.dualReflectionContinuation P X M γ μ :=
  reflectionR_dual_shift_unknown_constant_of_deps P X M γ μ hγ hγ2 hγirr hμ hX hM
    (reflectionR_first_shift_meromorphic_of_crossing P X M γ μ hγ hγ2 hμ hX hM hCross)
    (fun I _ hI => reflectionBarR_holomorphic_representation_of_crossing P X M γ hγ hγ2 hX hM
      hCross I hI)
    hShiftGluing hInversion hSeed

include Ω _inst1 P X M γ μ hγ hγ2 hγirr hμ hX hM hCross in
/-- **The dual shift of `R` from the γ/2 crossing, the first structure shift and the second dual
seed.** The statements `DOZZ.reflectionR_first_shift_meromorphic` and
`DOZZ.reflectionBarR_holomorphic_representation` follow from the crossing `DOZZ.gammaHalf_crossing`;
`DOZZ.structureConstant_reflected_shift_and_gluing` follows from
`DOZZ.reflectionR_first_shift_meromorphic` and `DOZZ.structureConstant_first_shift_strip`
(`structureConstant_reflected_shift_and_gluing_of_shifts`, with
`DOZZ.degenerateFourPoint_diagonal_classification` and `DOZZ.gammaHalf_reflected_formula` applied
directly), and `DOZZ.reflectionR_inversion_meromorphic` follows from
`DOZZ.structureConstant_reflected_shift_and_gluing` (`reflectionR_inversion_meromorphic_of_reflected_shift_and_gluing`).
`hFirstStrip` is the conclusion of `DOZZ.structureConstant_first_shift_strip` at the given field, chaos,
coupling and cosmological constant. -/
theorem reflectionR_dual_shift_unknown_constant_of_crossing_firstShift
    
    (hFirstStrip : ∀ η : ℝ, (0 < η ∧ Q γ - 2 * η > γ) → ∀ α₂ α₃ : ℝ,
      (Q γ - η < α₂ ∧ α₂ < Q γ) → (Q γ - η < α₃ ∧ α₃ < Q γ) →
      Contract.singleChargeContinuation P M γ μ η α₂ α₃)
    (hSeed : Contract.dualSecondSeed P X M γ μ) :
    Contract.dualReflectionContinuation P X M γ μ := by
  have hFirstShift := reflectionR_first_shift_meromorphic_of_crossing P X M γ μ hγ hγ2 hμ hX hM hCross
  have hShiftGluing := fun η hη α₂ α₃ hα₂ hα₃ =>
    structureConstant_reflected_shift_and_gluing_of_shifts P X M γ μ η hγ hγ2 hμ hη hX hM α₂ α₃
      hα₂ hα₃ hFirstShift (hFirstStrip η hη α₂ α₃ hα₂ hα₃)
  exact reflectionR_dual_shift_unknown_constant_of_crossing P X M γ μ hγ hγ2 hγirr hμ hX hM hCross
    hShiftGluing (reflectionR_inversion_meromorphic_of_reflected_shift_and_gluing P X M γ μ hγ hγ2 hμ hX hM hShiftGluing) hSeed

include Ω _inst1 P X M γ μ hγ hγ2 hγirr hμ hX hM hCross in
/-- **The dual shift of `R` from the γ/2 crossing and the second dual seed**, with
`DOZZ.structureConstant_first_shift_strip` proved from the unreflected formula
(`structureConstant_first_shift_strip_unconditional`). -/
theorem reflectionR_dual_shift_unknown_constant_of_crossing_seed
    
    (hSeed : Contract.dualSecondSeed P X M γ μ) :
    Contract.dualReflectionContinuation P X M γ μ :=
  reflectionR_dual_shift_unknown_constant_of_crossing_firstShift P X M γ μ hγ hγ2 hγirr hμ hX hM
    hCross (fun η hη α₂ α₃ hα₂ hα₃ =>
      structureConstant_first_shift_strip_unconditional P X M γ μ η hγ hγ2 hμ hη hX hM α₂ α₃ hα₂ hα₃)
    hSeed

end DOZZ.Proofs

end
