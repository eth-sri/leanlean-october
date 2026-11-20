/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.FourPoint.Dual.OuterInverseGuard
public import DOZZ.Statements.GMC.EquatorGFFRootedGMCIdentity
import DOZZ.GMC.SharpMoments.SeibergWeight
import Mathlib.Tactic
public import DOZZ.FourPoint.Fusion.RetainedZero

/-! # The zero kernel with an independent retained radius -/

@[expose] public section
open MeasureTheory Set
open scoped ENNReal
namespace DOZZ.Proofs

/-- The retained zero mass specialized to the dual insertion. -/
noncomputable def dualRetainedZeroMass (γ α₁ α₂ α₃ r : ℝ) (μ : Measure ℂ) : ℝ≥0∞ :=
  retainedZeroMass γ (-2 / γ) α₁ α₂ α₃ r μ

end DOZZ.Proofs
