/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import DOZZ.Statements.Correlations.BridgeMultiplicity
import Mathlib.Analysis.SpecialFunctions.Gamma.Deriv

/-! Pole-free multiplication turning the unit-volume residue into the full three-to-two
residue. -/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal
namespace DOZZ.Proofs

/-- The full moment formula is exactly Gamma times the unit-volume moment, including the
normalization. This algebra does not divide by Gamma at a totalized pole. -/
theorem residue_structureConstant_eq_unitVolume
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (M : Ω → Measure ℂ)
    (γ μ a b c : ℝ) :
    structureConstant P M γ μ a b c =
      μ ^ (-sExp γ a b c) * Real.Gamma (sExp γ a b c) *
        unitVolumeStructureConstant P M γ a b c := by
  unfold structureConstant unitVolumeStructureConstant
  ring

end DOZZ.Proofs
