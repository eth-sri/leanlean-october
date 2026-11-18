module

public import proofs.HordijkSteelThreshold.SprinkledSeedLowerBound
public import proofs.HordijkSteelThreshold.StaticBulk

@[expose] public section

namespace HordijkSteelThreshold
open Classical MeasureTheory RAF.Polymer RAF.Concrete unitInterval Filter
open scoped ENNReal

/-- Seed and supplied-seed bulk are evaluated in the same field. Their
dependence is harmless: seed probability is bounded by success plus bulk error. -/
theorem same_field_seed_mass_bound (N L m : ℕ) (a : I) :
    staticReactionMeasure N a {ω | ∀ w ∈ actualBinaryWords L,
      ∃ x ∈ temporaryReactionClosure 2 (staticOpenReactions ω), moleculeWord x = w} ≤
    staticReactionMeasure N a {ω | (m-1)*Fintype.card (Molecule N) ≤
      m*(temporaryReactionClosure 2 (staticOpenReactions ω)).card} +
    staticReactionMeasure N a {ω | m*(temporaryReactionClosure L (staticOpenReactions ω)).card <
      (m-1)*Fintype.card (Molecule N)} := by
  have hsub : {ω : Reaction N → Prop | ∀ w ∈ actualBinaryWords L,
      ∃ x ∈ temporaryReactionClosure 2 (staticOpenReactions ω), moleculeWord x = w} ⊆
      {ω | (m-1)*Fintype.card (Molecule N) ≤ m*(temporaryReactionClosure 2 (staticOpenReactions ω)).card} ∪
      {ω | m*(temporaryReactionClosure L (staticOpenReactions ω)).card < (m-1)*Fintype.card (Molecule N)} := by
    intro ω hseed
    by_cases hb : m*(temporaryReactionClosure L (staticOpenReactions ω)).card <
        (m-1)*Fintype.card (Molecule N)
    · exact Or.inr hb
    · left
      have hcontain : temporaryReactionClosure L (staticOpenReactions ω) ⊆
          temporaryReactionClosure 2 (staticOpenReactions ω) := by
        apply temporaryReactionClosure_seed_transfer Finset.Subset.rfl
        intro x hx
        have hw : moleculeWord x ∈ actualBinaryWords L :=
          (mem_actualBinaryWords _ _).mpr ⟨moleculeWord_nonempty x, by rwa [moleculeWord_length]⟩
        obtain ⟨y, hy, he⟩ := hseed _ hw
        exact moleculeWord_injective he ▸ hy
      exact (Nat.le_of_not_gt hb).trans (Nat.mul_le_mul_left m (Finset.card_le_card hcontain))
  exact (measure_mono hsub).trans (measure_union_le _ _)

end HordijkSteelThreshold
