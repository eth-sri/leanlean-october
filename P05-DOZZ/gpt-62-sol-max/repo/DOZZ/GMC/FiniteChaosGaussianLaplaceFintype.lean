/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GMC.FiniteChaosSmoothEndpoint
import DOZZ.GMC.FiniteChaosMean

/-! Finite Laplace Kahane comparison for arbitrary finite index types. -/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped Distributions ENNReal

namespace DOZZ.Proofs

/-- Reindexing a finite family preserves centered joint Gaussianity. -/
theorem centeredJointlyGaussian_reindex
    {Ω κ ι : Type*} [MeasurableSpace Ω] [Fintype κ] [Fintype ι]
    (P : Measure Ω) (e : κ ≃ ι) (Z : Ω → ι → ℝ)
    (hZ : DOZZ.IsCenteredJointlyGaussian P Z) :
    DOZZ.IsCenteredJointlyGaussian P (fun ω k => Z ω (e k)) := by
  refine ⟨hZ.1, ?_, ?_⟩
  · intro k
    exact hZ.2.1 (e k)
  · intro a
    let b  := fun i => a (e.symm i)
    have hsum (ω : Ω) :
        (∑ k, a k * Z ω (e k)) = ∑ i, b i * Z ω i := by
      calc
        ∑ k, a k * Z ω (e k) = ∑ i, (a (e.symm i) * Z ω (e (e.symm i))) :=
          (e.symm.sum_comp (fun k => a k * Z ω (e k))).symm
        _ = ∑ i, b i * Z ω i := by simp [b]
    have hsumFun := funext hsum
    obtain ⟨v, hmap⟩ := (hZ.2.2 b).2
    refine ⟨hsumFun ▸ (hZ.2.2 b).1, v, ?_⟩
    rwa [hsumFun]

end DOZZ.Proofs
