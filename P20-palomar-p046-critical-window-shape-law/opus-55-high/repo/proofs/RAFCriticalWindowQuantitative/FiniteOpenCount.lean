module

public import proofs.HordijkSteelThreshold.StaticEventContinuity
public import proofs.RAFCriticalWindowQuantitative.SparseClosure

public section

set_option Elab.async false
set_option maxHeartbeats 100000

namespace RAFCriticalWindowQuantitative
open Classical HordijkSteelThreshold MeasureTheory ProbabilityTheory unitInterval
open scoped ENNReal

variable (J : Type*) [Fintype J] (a : I)

theorem finite_support_open_probability  (T : Finset J) :
    (Measure.pi (fun _ : J => ambientCoordLaw a)) {ω | ∀ j ∈ T, ω j} = (toNNReal a : ENNReal)^T.card := by
  have he : {ω : J → Prop | ∀ j ∈ T, ω j} =
      (T : Set J).pi (fun _ => ({True})) := by
    grind
  rw [he]
  simp [ambientCoordLaw]
theorem finite_many_open_probability  (r : ℕ) :
    (Measure.pi (fun _ : J => ambientCoordLaw a))
      {ω | r ≤ (Finset.univ.filter (fun j : J => ω j)).card} ≤
      ((Fintype.card J).choose r : ENNReal)*(toNNReal a : ENNReal)^r := by
  let μ := Measure.pi (fun _ : J => ambientCoordLaw a)
  let P := (Finset.univ : Finset J).powersetCard r
  have hs : {ω : J → Prop | r ≤ (Finset.univ.filter (fun j : J => ω j)).card} ⊆
      ⋃ T ∈ P, {ω | ∀ j ∈ T, ω j} := by
    intro ω hω
    obtain ⟨T,hT,hcard⟩ := Finset.exists_subset_card_eq hω
    refine Set.mem_iUnion.mpr ⟨T,Set.mem_iUnion.mpr ⟨?_,?_⟩⟩
    · grind
    grind
  calc
    _ ≤ μ (⋃ T ∈ P, {ω | ∀ j ∈ T, ω j}) := measure_mono hs
    _ ≤ ∑ T ∈ P, μ {ω | ∀ j ∈ T, ω j} := measure_biUnion_finset_le _ _
    _ = ∑ _T ∈ P, (toNNReal a : ENNReal)^r := by
      apply Finset.sum_congr rfl
      intro T hT
      rw [finite_support_open_probability, (Finset.mem_powersetCard.mp hT).2]
    _ = _ := by aesop

end RAFCriticalWindowQuantitative
