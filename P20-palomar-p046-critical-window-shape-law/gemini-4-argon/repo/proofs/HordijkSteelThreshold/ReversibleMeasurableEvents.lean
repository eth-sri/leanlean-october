module

public import proofs.HordijkSteelThreshold.ReversibleClosureDock

@[expose] public section

namespace HordijkSteelThreshold
open Classical MeasureTheory RAF.Polymer RAF.Concrete

theorem measurable_splitRestriction (N : ℕ) :
    Measurable (fun (field : InfiniteSplitEnvironment) (r : Reaction N) =>
      field (moleculeWord (reactionProduct r)) (reactionLeftLength r)) :=
  Measurable.of_eval fun _ => (measurable_pi_apply _).comp (measurable_pi_apply _)

theorem measurableSet_finiteReversibleGenerated (N L : ℕ) (w : List Bool) :
    MeasurableSet {field : InfiniteSplitEnvironment | FiniteReversibleGenerated N L field w} := by
  rw [show {field : InfiniteSplitEnvironment | FiniteReversibleGenerated N L field w} =
    (fun field r => field (moleculeWord (reactionProduct r)) (reactionLeftLength r)) ⁻¹'
      {ω : Reaction N → Prop | ∃ x ∈ temporaryReactionClosure L (Finset.univ.filter ω), moleculeWord x = w} from
    Set.ext fun field => finiteReversible_iff_literalClosure field w]
  exact (Set.toFinite _).measurableSet.preimage (measurable_splitRestriction N)

theorem measurableSet_infiniteReversibleGenerated (L : ℕ) (w : List Bool) :
    MeasurableSet {field : InfiniteSplitEnvironment | InfiniteReversibleGenerated L field w} := by
  rw [show {field : InfiniteSplitEnvironment | InfiniteReversibleGenerated L field w} =
    ⋃ N : ℕ, {field | FiniteReversibleGenerated N L field w} by
      ext; simp [infiniteReversibleGenerated_iff_finite_certificate]]
  exact MeasurableSet.iUnion fun N => measurableSet_finiteReversibleGenerated N L w

theorem measurableSet_finite_seed (N L : ℕ) (seed : Finset (List Bool)) :
    MeasurableSet {field : InfiniteSplitEnvironment |
      ∀ w ∈ seed, FiniteReversibleGenerated N L field w} := by
  rw [show {field : InfiniteSplitEnvironment | ∀ w ∈ seed, FiniteReversibleGenerated N L field w} =
    ⋂ w ∈ seed, {field | FiniteReversibleGenerated N L field w} by ext; simp]
  exact MeasurableSet.biInter seed.countable_toSet fun w _ => measurableSet_finiteReversibleGenerated N L w

theorem finite_seed_probability_tendsto (μ : Measure InfiniteSplitEnvironment)
    (L : ℕ) (seed : Finset (List Bool)) :
    Filter.Tendsto (fun N => μ {field | ∀ w ∈ seed, FiniteReversibleGenerated N L field w})
      Filter.atTop (nhds (μ {field | ∀ w ∈ seed, InfiniteReversibleGenerated L field w})) := by
  have hcap (field : InfiniteSplitEnvironment) :
      (∀ w ∈ seed, InfiniteReversibleGenerated L field w) ↔
        ∃ N, ∀ w ∈ seed, FiniteReversibleGenerated N L field w := by
    refine ⟨?_, fun ⟨N, hN⟩ w hw => finiteReversibleGenerated_to_infinite (hN w hw)⟩
    induction seed using Finset.induction_on with
    | empty => exact fun _ => ⟨0, by simp⟩
    | @insert w seed _ ih =>
      intro h
      obtain ⟨N, hN⟩ := infiniteReversibleGenerated_finite_certificate (h w (Finset.mem_insert_self _ _))
      obtain ⟨M, hM⟩ := ih fun v hv => h v (Finset.mem_insert_of_mem hv)
      refine ⟨max N M, fun v hv => ?_⟩
      rcases Finset.mem_insert.mp hv with rfl | hv
      · exact finiteReversibleGenerated_mono_cap (Nat.le_max_left _ _) hN
      · exact finiteReversibleGenerated_mono_cap (Nat.le_max_right _ _) (hM v hv)
  have ht := tendsto_measure_iUnion_atTop (μ := μ)
    (s := fun N => {field | ∀ w ∈ seed, FiniteReversibleGenerated N L field w})
    fun _ _ hNM _ hf w hw => finiteReversibleGenerated_mono_cap hNM (hf w hw)
  rwa [show (⋃ N, {field | ∀ w ∈ seed, FiniteReversibleGenerated N L field w}) =
    {field | ∀ w ∈ seed, InfiniteReversibleGenerated L field w} by ext; simp [hcap]] at ht

end HordijkSteelThreshold
