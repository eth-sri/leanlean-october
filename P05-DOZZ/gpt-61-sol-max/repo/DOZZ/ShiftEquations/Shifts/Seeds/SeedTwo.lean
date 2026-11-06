/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.ShiftEquations.Shifts.Seeds.Extraction
import DOZZ.Correlations.Tails.ReflectionWitness
public import DOZZ.FourPoint.Contracts

/-!
# The second dual crossing seed from the dual fusion

On the whole seed domain `α, ε, α' < Q`, `α + ε + α' > 2Q + 2/γ`, one has
`R(ε) C(2Q - ε - 2/γ, α, α') = L(ε, α, α') R(α) C(ε, 2Q - α - 2/γ, α')` with `dualCrossingL`, two
reflection witnesses `B(ε)`, `B(α)` and one lateral measure from the supplied space. The only input
is the complete statement of `dual_full_fusion_and_asymptotic`.
-/

public section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal Topology

universe u

namespace DOZZ.Proofs

/-- **The second dual crossing seed** from the statement of the dual fusion
(`dual_full_fusion_and_asymptotic`, quantified over `Ω : Type u`). The conclusion is that of
`dual_crossing_seed_two`. -/
theorem dual_crossing_seed_two_of_fusion
    (hFusion : Contract.dualFullFusion.{u})
    {Ω : Type u} [MeasurableSpace Ω]
    (P : Measure Ω) (M : Ω → Measure ℂ) (X : Ω → Distr)
    (γ μ α ε α' : ℝ)
    (hγ : 0 < γ) (hγ₂ : γ < 2) (hμ : 0 < μ)
    (hα : α < Q γ) (hε : ε < Q γ) (hα' : α' < Q γ)
    (hs : 2 * Q γ + 2 / γ < α + ε + α')
    (hX : IsEquatorGFF P X) (hM : IsGMCOf P X γ M) :
    ∃ Bε Bα : Ω → BrownianPath × BrownianPath,
      ∃ Z : Ω → Measure ℝ,
        IsSourceLateralProjection P X γ M Z ∧
        IsReflectionData P γ ε Bε Z ∧
        IsReflectionData P γ α Bα Z ∧
        reflectionR P γ μ ε Bε Z *
            structureConstant P M γ μ (2 * Q γ - ε - 2 / γ) α α' =
          dualCrossingL γ ε α α' *
            reflectionR P γ μ α Bα Z *
              structureConstant P M γ μ ε (2 * Q γ - α - 2 / γ) α' := by
  obtain ⟨B, Z, hSLP, hB⟩ := exists_source_reflection_witness P X M γ hγ hγ₂ hX hM
  refine ⟨B ε, B α, Z, hSLP, hB ε hε, hB α hα, ?_⟩
  exact dual_seed_two_identity P X M γ μ α ε α' hγ hγ₂ hμ hα hε hα' hs hX hM (B ε) (B α) Z
    (dual_reflection_identity_of_fusion P X M γ μ α ε α' hγ hγ₂ hμ hα hε hα' hs hX hM
      (B α) Z (hB α hα) hFusion)
    (dual_reflection_identity_of_fusion P X M γ μ ε α α' hγ hγ₂ hμ hε hα hα' (by linarith)
      hX hM (B ε) Z (hB ε hε) hFusion)

end DOZZ.Proofs

end
