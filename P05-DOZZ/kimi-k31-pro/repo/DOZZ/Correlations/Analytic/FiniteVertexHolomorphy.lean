/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import DOZZ.Correlations.Analytic.RetainedMassMoments
import DOZZ.Correlations.Analytic.FiniteVertexGaussian
import DOZZ.Complex.Charge

/-! Holomorphy of finite-radius Wick vertices with a retained, charge-independent GMC mass. -/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal
namespace DOZZ.Proofs

/-- Sum of the complex charges as a continuous linear functional. -/
noncomputable def chargeSumCLM (N : ℕ) : (Fin N → ℂ) →L[ℂ] ℂ :=
  ∑ i : Fin N, ContinuousLinearMap.proj i

/-- The continuous linear charge sum has the expected coordinate formula. -/
theorem chargeSumCLM_apply {N : ℕ} (α : Fin N → ℂ) :
    chargeSumCLM N α = ∑ i, α i := by
  simp [chargeSumCLM]

end DOZZ.Proofs
