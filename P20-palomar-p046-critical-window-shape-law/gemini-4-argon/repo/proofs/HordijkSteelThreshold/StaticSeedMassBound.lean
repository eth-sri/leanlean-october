module

public import proofs.HordijkSteelThreshold.SprinkledSeedLowerBound
public import proofs.HordijkSteelThreshold.StaticBulk

@[expose] public section

namespace HordijkSteelThreshold
open Classical MeasureTheory RAF.Polymer RAF.Concrete unitInterval Filter
open scoped ENNReal

theorem seed_mass_union_bound {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (N L m : ℕ) (f : Ω → Finset (Reaction N)) (E : Set Ω)
    (hE : ∀ ω ∈ E, binaryFood N L ⊆ temporaryReactionClosure 2 (f ω)) :
    μ E ≤ μ {ω | (m-1)*Fintype.card (Molecule N) ≤ m*(temporaryReactionClosure 2 (f ω)).card} +
      μ {ω | m*(temporaryReactionClosure L (f ω)).card < (m-1)*Fintype.card (Molecule N)} := by
  refine (measure_mono fun ω hω => ?_).trans (measure_union_le _ _)
  by_cases hb : m*(temporaryReactionClosure L (f ω)).card < (m-1)*Fintype.card (Molecule N)
  · exact Or.inr hb
  · refine Or.inl ((Nat.le_of_not_gt hb).trans (Nat.mul_le_mul_left m (Finset.card_le_card ?_)))
    exact temporaryReactionClosure_seed_transfer Finset.Subset.rfl fun x hx =>
      hE ω hω (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx⟩)

theorem binaryFood_subset_of_words {N L : ℕ} {C : Finset (Molecule N)}
    (h : ∀ w ∈ actualBinaryWords L, ∃ x ∈ C, moleculeWord x = w) : binaryFood N L ⊆ C := by
  intro x hx
  obtain ⟨y, hy, he⟩ := h (moleculeWord x) ((mem_actualBinaryWords _ _).mpr
    ⟨moleculeWord_nonempty x, by rw [moleculeWord_length]; exact (Finset.mem_filter.mp hx).2⟩)
  exact moleculeWord_injective he ▸ hy

theorem same_field_seed_mass_bound (N L m : ℕ) (a : I) :
    staticReactionMeasure N a {ω | ∀ w ∈ actualBinaryWords L,
      ∃ x ∈ temporaryReactionClosure 2 (staticOpenReactions ω), moleculeWord x = w} ≤
    staticReactionMeasure N a {ω | (m-1)*Fintype.card (Molecule N) ≤
      m*(temporaryReactionClosure 2 (staticOpenReactions ω)).card} +
    staticReactionMeasure N a {ω | m*(temporaryReactionClosure L (staticOpenReactions ω)).card <
      (m-1)*Fintype.card (Molecule N)} :=
  seed_mass_union_bound _ N L m staticOpenReactions _ fun _ => binaryFood_subset_of_words

end HordijkSteelThreshold
