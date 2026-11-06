module

public import proofs.HordijkSteelThreshold.PeelingStabilization
public import proofs.HordijkSteelThreshold.TerminalReactionClosure
public import proofs.HordijkSteelThreshold.FixedPoolReactionLaw
public import proofs.HordijkSteelThreshold.StaticSeedClosure
public import proofs.HordijkSteelThreshold.StaticClosureMass

public section

namespace HordijkSteelThreshold
open Classical Filter MeasureTheory RAF RAF.Polymer RAF.Concrete
open scoped ENNReal

/-- Reindex actual food molecules into the finite cutoff universe. This is the
same bounded-word injection used in the repository's reversible trace counts. -/
theorem binaryFood_card_le_cutoff (n L : ℕ) :
    (binaryFood n L).card ≤ Fintype.card (Molecule L) := by
  let f : ↥(binaryFood n L) → Molecule L := fun x =>
    ⟨⟨x.val.1.val, by
      have h := (Finset.mem_filter.mp x.property).2
      dsimp [molLength] at h
      omega⟩, x.val.2⟩
  have hf : Function.Injective f := by
    rintro ⟨⟨ai,aw⟩,ha⟩ ⟨⟨bi,bw⟩,hb⟩ h
    grind
  simpa using Fintype.card_le_of_injective f hf

theorem exists_long_of_card {n : ℕ} {S : Finset $ Molecule n} (h : 6 < S.card) :
    ∃ x ∈ S, 2 < molLength x := by
  by_contra hc
  have := (Finset.card_le_card $ show S ⊆ binaryFood n 2 from fun x hx =>
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, by grind⟩).trans $ binaryFood_card_le_cutoff n 2
  have : Fintype.card (Molecule 2) = 6 := by decide
  omega

end HordijkSteelThreshold
