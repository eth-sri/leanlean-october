/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.FourPoint.GammaHalfRootKernelBar

/-! The definition `DOZZ.gammaHalfTwoRootedP1`. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace Set
open scoped ENNReal NNReal Topology

namespace DOZZ

/-- The spatial expectation in the pure (`false`) or mixed (`true`) two-rooted term. -/
noncomputable def gammaHalfTwoRootedSpatial {Ω : Type*} [MeasurableSpace Ω]
    (mixed : Bool) (P : Measure Ω) (M : Ω → Measure ℂ) (γ α₁ α₂ α₃ p : ℝ) (z : ℂ) : ℂ :=
  ∫ ω, let J : ℂ := ((coulombMass γ (M ω) ![-γ / 2, α₁, α₂] ![z, 0, 1] α₃ ^ (-p - 2)).toReal : ℂ)
       let Z := gammaHalfRootKernelZ M γ α₁ α₂ α₃ ω z
       if mixed then J * Z * gammaHalfRootKernelBar M γ α₁ α₂ α₃ ω z else J * Z ^ 2 ∂P

/-- The two-rooted z-z contribution p1. -/
noncomputable def gammaHalfTwoRootedP1 {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (M : Ω → Measure ℂ) (γ α₁ α₂ α₃ p : ℝ) (z : ℂ) : ℂ :=
  ((p * (p + 1) * (γ ^ 2 / 4) ^ 2 : ℝ) : ℂ) * z ^ 2 *
    (∫ t in Set.Icc (0 : ℝ) 1, (1 - t : ℝ) *
      gammaHalfTwoRootedSpatial false P M γ α₁ α₂ α₃ p (t * z) ∂volume)

end DOZZ
