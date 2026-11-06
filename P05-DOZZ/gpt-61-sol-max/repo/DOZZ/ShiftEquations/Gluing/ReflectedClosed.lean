/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.ShiftEquations.Gluing.ReflectedWrapper
public import DOZZ.ShiftEquations.FirstStrip.Closed
public import DOZZ.ShiftEquations.Shift.Wrappers
public import DOZZ.ShiftEquations.Contracts
public import DOZZ.ShiftEquations.ContinuationContracts

/-!
# The reflected shift and gluing from the first reflection shift alone, and from the γ/2 crossing

With `DOZZ.structureConstant_first_shift_strip` proved from the unreflected formula
(`structureConstant_first_shift_strip_unconditional`),
`DOZZ.structureConstant_reflected_shift_and_gluing` needs only
`DOZZ.reflectionR_first_shift_meromorphic`, and that needs only the unit-volume conjunct of the γ/2
crossing `DOZZ.gammaHalf_crossing`.
-/

public section

open MeasureTheory Filter Topology Set

namespace DOZZ.Proofs

variable {Ω : Type*} [_inst1 : MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr) (M : Ω → Measure ℂ) (γ μ η : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (hμ : 0 < μ) (hη : 0 < η ∧ Q γ - 2 * η > γ) (hX : IsEquatorGFF P X) (hM : IsGMCOf P X γ M) (α₂ α₃ : ℝ) (hα₂ : Q γ - η < α₂ ∧ α₂ < Q γ) (hα₃ : Q γ - η < α₃ ∧ α₃ < Q γ)

include Ω _inst1 P X M γ μ η hγ hγ2 hμ hη hX hM α₂ α₃ hα₂ hα₃ in
/-- **The reflected shift and gluing from the first reflection shift.** -/
theorem structureConstant_reflected_shift_and_gluing_of_firstShiftReflection
    
    (hFirstShift : Contract.firstShift P X M γ μ) :
    Contract.fixedChargeShiftGluing P X M γ μ η α₂ α₃ :=
  structureConstant_reflected_shift_and_gluing_of_shifts P X M γ μ η hγ hγ2 hμ hη hX hM α₂ α₃
    hα₂ hα₃ hFirstShift
    (structureConstant_first_shift_strip_unconditional P X M γ μ η hγ hγ2 hμ hη hX hM α₂ α₃ hα₂ hα₃)

include Ω _inst1 P X M γ μ η hγ hγ2 hμ hη hX hM α₂ α₃ hα₂ hα₃ in
/-- **The reflected shift and gluing from the γ/2 crossing.** `hCross` is the unit-volume conjunct
of `gammaHalf_crossing`. -/
theorem structureConstant_reflected_shift_and_gluing_of_crossing
    
    (hCross : Contract.unitCrossing P M γ) :
    Contract.fixedChargeShiftGluing P X M γ μ η α₂ α₃ :=
  structureConstant_reflected_shift_and_gluing_of_firstShiftReflection P X M γ μ η hγ hγ2 hμ hη hX
    hM α₂ α₃ hα₂ hα₃
    (reflectionR_first_shift_meromorphic_of_crossing P X M γ μ hγ hγ2 hμ hX hM hCross)

end DOZZ.Proofs

end
