module

public import RequestProject.OrderPosetCovering

@[expose] public section

/-! A poset covering restricts to the actual preimage of any induced subposet. -/
namespace FiniteChains.Comb
universe u
variable {P Q : Type u} [PartialOrder P] [PartialOrder Q] (f : P → Q) (S : Set Q)

def posetCoverRestriction : {p : P // f p ∈ S} → S := fun p => ⟨f p.1, p.2⟩

theorem IsPosetCover.restriction (hf : IsPosetCover f) :
    IsPosetCover (posetCoverRestriction f S) := by
  refine ⟨fun _ _ h => hf.mono h, ?_, ?_, ?_⟩
  · intro q
    obtain ⟨p, hp⟩ := hf.surj q.1 <;> aesop
  · intro a q h
    obtain ⟨b, ⟨hab, hfb⟩, huniq⟩ := hf.up a.1 q.1 h
    refine ⟨⟨b, (by rw [hfb]; exact q.2)⟩, ⟨hab, Subtype.ext hfb⟩, ?_⟩
    intro c hc
    exact Subtype.ext (huniq c.1 ⟨hc.1, congrArg Subtype.val hc.2⟩)
  · intro a q h
    obtain ⟨b, ⟨hba, hfb⟩, huniq⟩ := hf.down a.1 q.1 h
    refine ⟨⟨b, (by rw [hfb]; exact q.2)⟩, ⟨hba, Subtype.ext hfb⟩, ?_⟩
    intro c hc
    exact Subtype.ext (huniq c.1 ⟨hc.1, congrArg Subtype.val hc.2⟩)

end FiniteChains.Comb
