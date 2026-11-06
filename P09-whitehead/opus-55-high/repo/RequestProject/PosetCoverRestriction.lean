import RequestProject.OrderPosetCovering


/-! A poset covering restricts to the actual preimage of any induced subposet. -/
namespace FiniteChains.Comb
universe u
variable {P Q : Type u} [PartialOrder P] [PartialOrder Q] (f : P → Q) (S : Set Q)

def posetCoverRestriction : {p : P // f p ∈ S} → S := fun p => ⟨f p.1, p.2⟩

theorem IsPosetCover.restriction (hf : IsPosetCover f) :
    IsPosetCover (posetCoverRestriction f S) := by
  refine ⟨fun _ _ h => hf.mono h, ?_, ?_, ?_⟩
  · intro q
    cases' hf.surj q.1 with p hp
    aesop
  · intro a q h
    obtain ⟨b, ⟨hab, hfb⟩, huniq⟩ := hf.up a.1 q.1 h
    have hb : f b ∈ S := by simp_all
    refine ⟨⟨b, hb⟩, ⟨hab, Subtype.ext hfb⟩, ?_⟩
    intro c hc
    exact Subtype.ext (huniq c.1 ⟨hc.1, congrArg Subtype.val hc.2⟩)
  · intro a q h
    obtain ⟨b, ⟨hba, hfb⟩, huniq⟩ := hf.down a.1 q.1 h
    have hb : f b ∈ S := by simp_all
    refine ⟨⟨b, hb⟩, ⟨hba, Subtype.ext hfb⟩, ?_⟩
    intro c hc
    exact Subtype.ext (huniq c.1 ⟨hc.1, congrArg Subtype.val hc.2⟩)
