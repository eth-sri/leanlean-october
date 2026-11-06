module

public import proofs.HordijkSteelThreshold.PeelingStabilization
public import proofs.HordijkSteelThreshold.TerminalReactionClosure
public import proofs.HordijkSteelThreshold.SourceBulkMass

@[expose] public section

namespace HordijkSteelThreshold
open Classical Filter MeasureTheory RAF RAF.Polymer RAF.Concrete
open scoped ENNReal

/-- Reindex actual food molecules into the finite cutoff universe. This is the
same bounded-word injection used in the repository's reversible trace counts. -/
theorem binaryFood_card_le_cutoff (n L : ℕ) :
    (binaryFood n L).card ≤ Fintype.card (Molecule L) := by
  rw [← Fintype.card_coe]
  refine Fintype.card_le_of_injective (fun x : ↥(binaryFood n L) =>
    (⟨⟨x.1.1.1, by have := (Finset.mem_filter.mp x.2).2; dsimp [molLength] at this; omega⟩, x.1.2⟩ : Molecule L)) ?_
  rintro ⟨⟨⟨a, _⟩, aw⟩, _⟩ ⟨⟨⟨b, _⟩, bw⟩, _⟩ h
  cases h; rfl

theorem source_terminal_hasRAF {n : ℕ} (ω : AmbientCoord n → Prop)
    (hmass : 6 < (temporaryReactionClosure 2 (peelingActiveAt (catalystActive ω)
      (temporaryReactionClosure 2) (Fintype.card (Reaction n)))).card) :
    ∃ S : Finset (Reaction n), IsRevRAF (binaryPolymerCRS n 2) (fun x r => ω (x,r)) S := by
  let A := peelingActiveAt (catalystActive ω) (temporaryReactionClosure 2) (Fintype.card (Reaction n))
  have hstable : catalystActive ω (temporaryReactionClosure 2 A) = A :=
    peelingActiveAt_stable_card (catalystActive ω) (temporaryReactionClosure 2)
      (catalystActive_mono ω) fun _ _ h => temporaryReactionClosure_mono h
  refine ⟨usableClosureReactions 2 A, usableClosureReactions_isRAF A (fun x r => ω (x,r))
    (fun r hr => (mem_catalystActive ω _ r).mp (hstable.symm ▸ hr)) ?_⟩
  by_contra! h
  have hs : temporaryReactionClosure 2 A ⊆ binaryFood n 2 :=
    fun x hx => Finset.mem_filter.mpr ⟨Finset.mem_univ _, h x hx⟩
  have hb : (binaryFood n 2).card ≤ 6 := by
    simpa only [show Fintype.card (Molecule 2) = 6 by decide] using binaryFood_card_le_cutoff n 2
  exact ((Finset.card_le_card hs).trans hb).not_gt hmass

end HordijkSteelThreshold
