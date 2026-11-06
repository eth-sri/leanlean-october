/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Brownian.Coupling.Assembly
public import Mathlib.MeasureTheory.Measure.Prokhorov
public import Mathlib.MeasureTheory.Measure.Portmanteau
public import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Topology.Sequences
public import Mathlib.Topology.ContinuousMap.SecondCountableSpace
public import Mathlib.Topology.Metrizable.ContinuousMap

/-!
# Countable-product tightness and the ordered entrance joint limit

Marginal tightness is enough for joint tightness: choose compact coordinate sets with a summable
error budget and apply the union bound. Prokhorov gives a joint subsequential limit, its coordinate
laws are preserved by continuous evaluation, and its support retains every closed order constraint.
No independence of the drift coordinates is assumed or asserted.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace Set
open scoped ENNReal NNReal Topology

namespace DOZZ.Proofs

/-- The summable probability budget used for the compact coordinate sets. -/
noncomputable def couplingCompactBudget (ε : ℝ≥0∞) (j : ℕ) : ℝ≥0∞ :=
  ε * 2 ^ (-1 - j : ℤ)






/-- Joint tightness on a countable product follows from tightness of each marginal family. -/
theorem isTightMeasureSet_countable_product_of_marginals
    {E : ℕ → Type*} [∀ j, TopologicalSpace (E j)] [∀ j, T2Space (E j)]
    [∀ j, MeasurableSpace (E j)] [∀ j, BorelSpace (E j)]
    (S : Set (Measure (∀ j, E j)))
    (hmarginal : ∀ j, IsTightMeasureSet ((fun μ => μ.map (fun x => x j)) '' S)) :
    IsTightMeasureSet S := by
  classical
  have measure_countable_compact_product_compl_le_budget (μ : Measure (∀ j, E j)) (K : ∀ j, Set (E j)) (ε : ℝ≥0∞) (hK : ∀ j, MeasurableSet (K j)) (hbudget : ∀ j, (μ.map (fun x => x j)) (K j)ᶜ ≤ couplingCompactBudget ε j) : μ (Set.pi univ K)ᶜ ≤ ε := by
    have measure_countable_compact_product_compl_le : μ (Set.pi univ K)ᶜ ≤ ∑' j, μ ((fun x : ∀ j, E j => x j) ⁻¹' (K j)ᶜ) := by
      have countable_compact_product_compl (K : ∀ j, Set (E j)) : (Set.pi univ K)ᶜ = ⋃ j, (fun x : ∀ j, E j => x j) ⁻¹' (K j)ᶜ := by
        ext x
        simp only [mem_compl_iff, Set.mem_pi, mem_univ, forall_const, mem_iUnion, mem_preimage]
        exact not_forall
      rw [countable_compact_product_compl]
      exact measure_iUnion_le _
    calc
      μ (Set.pi univ K)ᶜ ≤
          ∑' j, μ ((fun x : ∀ j, E j => x j) ⁻¹' (K j)ᶜ) :=
        measure_countable_compact_product_compl_le
      _ = ∑' j, (μ.map (fun x => x j)) (K j)ᶜ := by
        apply tsum_congr
        intro j
        exact (Measure.map_apply (measurable_pi_apply j) (hK j).compl).symm
      _ ≤ ∑' j, couplingCompactBudget ε j := ENNReal.tsum_le_tsum hbudget
      _ = ε := (by simp only [couplingCompactBudget]; rw [ENNReal.tsum_mul_left, ENNReal.tsum_two_zpow_neg_add_one, mul_one])
  have couplingCompactBudget_pos {ε : ℝ≥0∞} (hε : 0 < ε) j : 0 < couplingCompactBudget ε j := by
    apply ENNReal.mul_pos hε.ne'
    exact (ENNReal.zpow_pos (by norm_num) (by norm_num) _).ne'
  apply isTightMeasureSet_iff_exists_isCompact_measure_compl_le.mpr
  intro ε hε
  have hchoice : ∀ j, ∃ K : Set (E j), IsCompact K ∧
      ∀ μ ∈ S, (μ.map (fun x => x j)) Kᶜ ≤ couplingCompactBudget ε j := by
    intro j
    obtain ⟨K, hK, htail⟩ :=
      isTightMeasureSet_iff_exists_isCompact_measure_compl_le.mp (hmarginal j)
        (couplingCompactBudget ε j) (couplingCompactBudget_pos hε j)
    exact ⟨K, hK, fun μ hμ => htail _ ⟨μ, hμ, rfl⟩⟩
  choose K hK htail using hchoice
  refine ⟨Set.pi univ K, ?_, ?_⟩
  · have heq : Set.pi univ K = {x | ∀ j, x j ∈ K j} := by
      ext x
      simp
    rw [heq]
    exact isCompact_pi_infinite hK
  intro μ hμ
  exact measure_countable_compact_product_compl_le_budget μ K ε
    (fun j => (hK j).measurableSet) (fun j => htail j μ hμ)

/-- Prokhorov supplies a joint probability limit along one subsequence on a Polish carrier. -/
theorem coupling_subsequence_of_tight
    {E : Type*} [TopologicalSpace E] [PolishSpace E] [MeasurableSpace E] [BorelSpace E]
    (μ : ℕ → ProbabilityMeasure E)
    (htight : IsTightMeasureSet {Q : Measure E | ∃ n, Q = (μ n : Measure E)}) :
    ∃ Q : ProbabilityMeasure E, ∃ φ : ℕ → ℕ,
      StrictMono φ ∧ Tendsto (μ ∘ φ) atTop (𝓝 Q) := by
  let _ := upgradeIsCompletelyMetrizable E
  have hcompact : IsCompact (closure (range μ)) := by
    apply isCompact_closure_of_isTightMeasureSet
    convert htight using 1
    ext Q
    simp only [mem_ofPred_eq, mem_range]
    constructor
    · rintro ⟨R, ⟨n, rfl⟩, rfl⟩
      exact ⟨n, rfl⟩
    · rintro ⟨n, rfl⟩
      exact ⟨μ n, ⟨n, rfl⟩, rfl⟩
  obtain ⟨Q, _, φ, hφ, hQ⟩ := hcompact.tendsto_subseq
    (fun n => subset_closure (mem_range_self n))
  exact ⟨Q, φ, hφ, hQ⟩

/-- A weak limit of probabilities supported on a closed set is supported there. -/
theorem coupling_ae_closed_of_tendsto
    {E : Type*} [TopologicalSpace E] [PolishSpace E] [MeasurableSpace E] [BorelSpace E]
    {μ : ℕ → ProbabilityMeasure E} {Q : ProbabilityMeasure E}
    (hμQ : Tendsto μ atTop (𝓝 Q)) {S} (hS : IsClosed S)
    (hμS : ∀ n, ∀ᵐ x ∂(μ n : Measure E), x ∈ S) :
    ∀ᵐ x ∂(Q : Measure E), x ∈ S := by
  let _ := upgradeIsCompletelyMetrizable E
  have hmass : ∀ n, (μ n : Measure E) S = 1 := by
    intro n
    have := (ae_mem_iff_measure_eq hS.measurableSet.nullMeasurableSet).mp (hμS n)
    simpa using this
  apply (ae_mem_iff_measure_eq hS.measurableSet.nullMeasurableSet).mpr
  exact le_antisymm (measure_mono (subset_univ S)) (by simpa using (show (1 : ℝ≥0∞) ≤ (Q : Measure E) S by simpa only [hmass, limsup_const] using (ProbabilityMeasure.limsup_measure_closed_le_of_tendsto hμQ hS)))


/-- A prescribed marginal limit identifies the corresponding marginal of every joint limit. -/
theorem coupling_coordinate_eq_of_tendsto
    {J E : Type*} [Countable J] [TopologicalSpace E] [PolishSpace E]
    [MeasurableSpace E] [BorelSpace E]
    {μ : ℕ → ProbabilityMeasure (J → E)} {Q : ProbabilityMeasure (J → E)}
    (hμQ : Tendsto μ atTop (𝓝 Q)) j (R : ProbabilityMeasure E)
    (hmarginal : Tendsto (fun n => (μ n).map (fun x => x j)) atTop (𝓝 R)) :
    Q.map (fun x => x j) = R := by
  let _ := upgradeIsCompletelyMetrizable E
  exact tendsto_nhds_unique ((ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous μ Q hμQ (continuous_apply j))) hmarginal


/-- Coordinate weak convergence yields a single joint convergent subsequence for countably many
coordinates. There is no consistency requirement between successive grid couplings. -/
theorem coupling_joint_subsequence_of_coordinate_tendsto
    {E : Type*} [TopologicalSpace E] [PolishSpace E] [MeasurableSpace E] [BorelSpace E]
    (μ : ℕ → ProbabilityMeasure (ℕ → E)) (R : ℕ → ProbabilityMeasure E)
    (hmarginal : ∀ j, Tendsto (fun n => (μ n).map (fun x => x j)) atTop (𝓝 (R j))) :
    ∃ Q : ProbabilityMeasure (ℕ → E), ∃ φ : ℕ → ℕ,
      StrictMono φ ∧ Tendsto (μ ∘ φ) atTop (𝓝 Q) ∧
        ∀ j, Q.map (fun x => x j) = R j := by
  have coupling_isTightMeasureSet_of_tendsto {μ : ℕ → ProbabilityMeasure E} {Q : ProbabilityMeasure E} (hμQ : Tendsto μ atTop (𝓝 Q)) : IsTightMeasureSet {R : Measure E | ∃ n, R = (μ n : Measure E)} := by
    let _ := upgradeIsCompletelyMetrizable E
    convert (isTightMeasureSet_of_isCompact_closure (hμQ.isCompact_insert_range.of_isClosed_subset isClosed_closure (hμQ.isCompact_insert_range.isClosed.closure_subset_iff.mpr (subset_insert Q (range μ))))) using 1
    ext R
    simp only [mem_ofPred_eq, mem_range]
    constructor
    · rintro ⟨n, rfl⟩
      exact ⟨μ n, ⟨n, rfl⟩, rfl⟩
    · rintro ⟨R, ⟨n, rfl⟩, rfl⟩
      exact ⟨n, rfl⟩
  let _ := upgradeIsCompletelyMetrizable E
  have htight : IsTightMeasureSet
      {Q : Measure (ℕ → E) | ∃ n, Q = (μ n : Measure (ℕ → E))} := by
    apply isTightMeasureSet_countable_product_of_marginals
    intro j
    convert (coupling_isTightMeasureSet_of_tendsto (hmarginal j)) using 1
    ext Q
    simp only [mem_image, mem_ofPred_eq]
    constructor
    · rintro ⟨Q, ⟨n, rfl⟩, rfl⟩
      exact ⟨n, rfl⟩
    · rintro ⟨n, rfl⟩
      exact ⟨(μ n : Measure (ℕ → E)), ⟨n, rfl⟩, rfl⟩
  obtain ⟨Q, φ, hφ, hQ⟩ := coupling_subsequence_of_tight μ htight
  refine ⟨Q, φ, hφ, hQ, ?_⟩
  intro j
  exact coupling_coordinate_eq_of_tendsto hQ j (R j)
    ((hmarginal j).comp hφ.tendsto_atTop)

/-- The same extraction retains support in any closed subset of the product path carrier. -/
theorem coupling_joint_limit_with_closed_support
    {E : Type*} [TopologicalSpace E] [PolishSpace E] [MeasurableSpace E] [BorelSpace E]
    (μ : ℕ → ProbabilityMeasure (ℕ → E)) (R : ℕ → ProbabilityMeasure E)
    (hmarginal : ∀ j, Tendsto (fun n => (μ n).map (fun x => x j)) atTop (𝓝 (R j)))
    S (hS : IsClosed S)
    (hμS : ∀ n, ∀ᵐ x ∂(μ n : Measure (ℕ → E)), x ∈ S) :
    ∃ Q : ProbabilityMeasure (ℕ → E), ∃ φ : ℕ → ℕ,
      StrictMono φ ∧ Tendsto (μ ∘ φ) atTop (𝓝 Q) ∧
        (∀ j, Q.map (fun x => x j) = R j) ∧
          ∀ᵐ x ∂(Q : Measure (ℕ → E)), x ∈ S := by
  obtain ⟨Q, φ, hφ, hQ, hmarginalQ⟩ :=
    coupling_joint_subsequence_of_coordinate_tendsto μ R hmarginal
  refine ⟨Q, φ, hφ, hQ, hmarginalQ, ?_⟩
  exact coupling_ae_closed_of_tendsto hQ (hS := hS) (fun n => hμS (φ n))

/-- The countable continuous-path coupling limit. Each prescribed marginal is a
whole continuous-path probability law, and every all-time order constraint survives. -/
theorem conditioned_countable_ordered_path_limit
    v (μ : ℕ → ProbabilityMeasure (ℕ → BrownianPath))
    (R : ℕ → ProbabilityMeasure BrownianPath)
    (hmarginal : ∀ j, Tendsto (fun n => (μ n).map (fun x => x j)) atTop (𝓝 (R j)))
    (horder : ∀ n, ∀ᵐ x ∂(μ n : Measure (ℕ → BrownianPath)),
      x ∈ negativeEntranceOrderSet v) :
    ∃ Q : ProbabilityMeasure (ℕ → BrownianPath),
      (∀ j, Q.map (fun x => x j) = R j) ∧
        ∀ᵐ x ∂(Q : Measure (ℕ → BrownianPath)), x ∈ negativeEntranceOrderSet v := by
  obtain ⟨Q, _, _, _, hQR, hQorder⟩ :=
    coupling_joint_limit_with_closed_support μ R hmarginal
      (negativeEntranceOrderSet v) (isClosed_negativeEntranceOrderSet v) horder
  exact ⟨Q, hQR, hQorder⟩

end DOZZ.Proofs
