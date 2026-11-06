/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.FourPoint.Dual.FullInverseWitness
public import DOZZ.FourPoint.Dual.FullFusionAssembly
public import DOZZ.FourPoint.Contracts
/-! The corrected dual full fusion formula and same-source asymptotic. -/
public section
open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace Set
open scoped ENNReal NNReal Topology
namespace DOZZ.Proofs

universe u

/-- The actual stochastic full-kernel limit and the physical classification give the
literal dual fusion conclusions on one source reflection family. -/
theorem dual_full_fusion_and_asymptotic : Contract.dualFullFusion.{u} := by
  intro Ω inst H hH P M X γ μ α₁ α₂ α₃ η ξ hγ hγ₂ hμ hη hη₂ hξ hξ₂
    hαlo hαhi hα₂ hα₃ hs hslack₁ hslack₂ hX hM
  obtain ⟨B, Z, hSource, hData, hLimit⟩ := dual_source_full_inverse_fusion_witness
    P M X γ α₁ α₂ α₃ η ξ hγ hγ₂ hη hη₂ hξ hξ₂ hαlo hαhi hα₂ hα₃ hs
      hslack₁ hslack₂ hX hM
  refine ⟨B, Z, hSource, hData, ?_⟩
  exact dual_full_fusion_of_normalized_inverse_limit hH P M X γ μ α₁ α₂ α₃ η ξ
    hγ hγ₂ hμ hη hη₂ hξ hξ₂ hαlo hαhi hα₂ hα₃ hs hslack₁ hslack₂ hX hM B Z hData hLimit

end DOZZ.Proofs
