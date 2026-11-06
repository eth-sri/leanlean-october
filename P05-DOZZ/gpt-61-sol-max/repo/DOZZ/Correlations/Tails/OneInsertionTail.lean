/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Correlations.Tails.OneInsertionEstimate
public import DOZZ.Correlations.Tails.ReflectionWitness
public import DOZZ.Statements.GFFStructure.ExistsContinuousCircleAverage
public import DOZZ.Correlations.TailContracts

/-! The uniform one-insertion tail with one source reflection witness chosen before the error exponent. -/

public section
open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace Set
open scoped ENNReal NNReal Topology

namespace DOZZ.Proofs

theorem oneInsertion_tail_uniform
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr)
    (M : Ω → Measure ℂ) (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2)
    (hX : IsEquatorGFF P X) (hM : IsGMCOf P X γ M)
    (Kz : Set ℂ) (hKz : IsCompact Kz) (hz : ∀ z ∈ Kz, 2 ≤ ‖z‖)
    (Kα : Set ℝ) (hKα : IsCompact Kα)
    (hα : ∀ α ∈ Kα, γ / 2 < α ∧ α < Q γ)
    (Family : ℂ → Set (ℂ → ℝ)) (radius supBound derivBound lowerBound : ℝ)
    (hFamily : UniformPositiveC1Family Kz Family radius supBound derivBound lowerBound) :
    Contract.oneInsertionTail P X M γ Kz Kα Family := by
  obtain ⟨B,Z,hsource,hData⟩ := exists_source_reflection_witness P X M γ hγ hγ2 hX hM
  have hhalf : γ/2 < Q γ := by
    unfold Q
    have hpos : 0 < 2/γ := div_pos (by norm_num) hγ
    linarith only [hpos]
  have hZ : IsLateralGMCOf P γ Z := (hData (γ/2) hhalf).2.1
  obtain ⟨Xc,hc,_⟩ := hM.2
  obtain ⟨Y,hY,hmY,hcontY,_⟩ := exists_continuous_circleAverage P X Xc hX hc
  refine ⟨B,Z,hsource,fun α hαk => hData α (hα α hαk).2,?_⟩
  intro η hη hceil
  simpa only [Real.rpow_eq_pow] using oneInsertion_estimate_uniform P X Y hX hY hmY hcontY
    M γ hγ hγ2 hM Kz hKz hz Kα hKα hα Family radius supBound derivBound lowerBound hFamily
    B Z hZ (fun α hαk => hData α (hα α hαk).2) η hη hceil


end DOZZ.Proofs
