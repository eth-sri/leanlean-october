/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GMC.FiniteChaosGaussianLaplace
import Batteries.Tactic.Alias

/-! Finite Laplace Kahane comparison for arbitrary finite index types. -/

public section

open MeasureTheory ProbabilityTheory
open scoped Distributions ENNReal

namespace DOZZ.Proofs

/-- Reindexing a finite family preserves centered joint Gaussianity. -/
theorem centeredJointlyGaussian_reindex
    {Ω κ ι : Type*} [MeasurableSpace Ω] [Fintype κ] [Fintype ι]
    (P : Measure Ω) (e : κ ≃ ι) (Z : Ω → ι → ℝ)
    (hZ : DOZZ.IsCenteredJointlyGaussian P Z) :
    DOZZ.IsCenteredJointlyGaussian P (fun ω k => Z ω (e k)) := by
  refine ⟨hZ.1, fun k => hZ.2.1 (e k), fun a => ?_⟩
  simpa only [← e.sum_comp, e.symm_apply_apply] using hZ.2.2 (fun i => a (e.symm i))

/-- The finite Laplace Kahane comparison for arbitrary finite families of coordinates. -/
alias kahane_finite_laplace_lintegral_fintype := kahane_finite_laplace_lintegral

end DOZZ.Proofs
