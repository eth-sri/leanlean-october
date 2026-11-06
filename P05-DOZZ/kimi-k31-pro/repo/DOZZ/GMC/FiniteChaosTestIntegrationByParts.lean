/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import DOZZ.GMC.FiniteChaosInterpolationCalculus
import DOZZ.GMC.FiniteGaussianIntegrationByPartsGrowth

/-! Gaussian integration by parts for a Wick weight times the derivative of a scalar chaos test. -/


open MeasureTheory ProbabilityTheory
open scoped Distributions Topology

namespace DOZZ.Proofs

/-- The field derivative of one Wick weight times a scalar test derivative. -/
noncomputable def finiteChaosVectorTestScore
    {ι : Type*} [Fintype ι]
    (a v : ι → ℝ) (γ : ℝ) (F' : ℝ → ℝ)
    (x : ι → ℝ) (i : ι) : ℝ :=
  finiteChaosVectorWeight a v γ x i * F' (finiteChaosVectorMass a v γ x)

/-- The coordinate derivative of `finiteChaosVectorTestScore`. -/
noncomputable def finiteChaosVectorTestScoreDerivative
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a v : ι → ℝ) (γ : ℝ) (F' F'' : ℝ → ℝ)
    (x : ι → ℝ) (i j : ι) : ℝ :=
  γ * (if i = j then
      finiteChaosVectorWeight a v γ x i * F' (finiteChaosVectorMass a v γ x) else 0) +
    γ * finiteChaosVectorWeight a v γ x i * finiteChaosVectorWeight a v γ x j *
      F'' (finiteChaosVectorMass a v γ x)

end DOZZ.Proofs
