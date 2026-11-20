/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.ShiftEquations.Shifts.Seeds.Extraction
import DOZZ.Correlations.Tails.ReflectionWitness
public import DOZZ.ShiftEquations.Representatives

/-! # The second dual crossing seed -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal Topology

universe u

namespace DOZZ.Proofs

/-- The second dual crossing seed, obtained by applying the dual fusion identity twice. -/
theorem dual_crossing_seed_two
    {Ω : Type u} [MeasurableSpace Ω]
    (P : Measure Ω) (M : Ω → Measure ℂ) (X : Ω → Distr)
    (γ μ α ε α' : ℝ)
    (hγ : 0 < γ) (hγ₂ : γ < 2) (hμ : 0 < μ)
    (hα : α < Q γ) (hε : ε < Q γ) (hα' : α' < Q γ)
    (hs : 2 * Q γ + 2 / γ < α + ε + α')
    (hX : IsEquatorGFF P X) (hM : IsGMCOf P X γ M) :
    DualCrossingRelation P X M γ μ α ε α' := by
  obtain ⟨B, Z, hSLP, hB⟩ := exists_source_reflection_witness P X M γ hγ hγ₂ hX hM
  refine ⟨B ε, B α, Z, hSLP, hB ε hε, hB α hα, ?_⟩
  exact dual_seed_two_identity P X M γ μ α ε α' hγ hγ₂ hμ hα hε hα' hs hX hM (B ε) (B α) Z
    (dual_reflection_identity_of_fusion P X M γ μ α ε α' hγ hγ₂ hμ hα hε hα' hs hX hM
      (B α) Z (hB α hα))
    (dual_reflection_identity_of_fusion P X M γ μ ε α α' hγ hγ₂ hμ hε hα hα' (by linarith)
      hX hM (B ε) Z (hB ε hε))

end DOZZ.Proofs

end
