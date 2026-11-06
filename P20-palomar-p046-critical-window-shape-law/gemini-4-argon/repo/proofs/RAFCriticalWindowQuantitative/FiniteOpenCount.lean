module

public import proofs.HordijkSteelThreshold.StaticEventContinuity
public import proofs.RAFCriticalWindowQuantitative.SparseClosure

@[expose] public section

namespace RAFCriticalWindowQuantitative
open Classical HordijkSteelThreshold MeasureTheory ProbabilityTheory unitInterval
open scoped ENNReal

theorem finite_many_open_probability (J : Type*) [Fintype J] (a : I) (r : ℕ) :
    (Measure.pi (fun _ : J => ambientCoordLaw a))
      {ω | r ≤ (Finset.univ.filter (fun j : J => ω j)).card} ≤
      ((Fintype.card J).choose r : ENNReal)*(toNNReal a : ENNReal)^r := by
  let P := (Finset.univ : Finset J).powersetCard r
  refine ((measure_mono (t := ⋃ T ∈ P, {ω : J → Prop | ∀ j ∈ T, ω j}) fun ω hω => ?_).trans
    (measure_biUnion_finset_le _ _)).trans
    ((Finset.sum_le_sum (g := fun _ => (toNNReal a : ENNReal)^r) fun T hT => ?_).trans_eq (by simp [P]))
  · obtain ⟨T, hT, hcard⟩ := Finset.exists_subset_card_eq hω
    exact Set.mem_iUnion₂.mpr ⟨T, Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hcard⟩,
      fun j hj => (Finset.mem_filter.mp (hT hj)).2⟩
  · rw [show {ω : J → Prop | ∀ j ∈ T, ω j} = (T : Set J).pi fun _ => {True} by ext; simp, Measure.pi_pi_finset]
    simp [ambientCoordLaw, (Finset.mem_powersetCard.mp hT).2]

end RAFCriticalWindowQuantitative
