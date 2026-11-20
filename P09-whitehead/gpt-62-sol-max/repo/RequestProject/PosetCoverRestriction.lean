module

public import RequestProject.OrderPosetCovering

@[expose] public section

/-! A poset covering restricts to the actual preimage of any induced subposet. -/
namespace FiniteChains.Comb
universe u
variable {P Q : Type u} [PartialOrder P] [PartialOrder Q] (f : P → Q) (S : Set Q)

def posetCoverRestriction : {p : P // f p ∈ S} → S := fun p => ⟨f p.1, p.2⟩

private theorem posetCoverRestriction_up (hf : IsPosetCover f)
    (a : {p : P // f p ∈ S}) (q : S) (h : f a.1 ≤ q.1) :
    ∃! b : {p : P // f p ∈ S}, a ≤ b ∧ posetCoverRestriction f S b = q := by
  obtain ⟨b, ⟨hab, hfb⟩, huniq⟩ := hf.up a.1 q.1 h
  refine ⟨⟨b, hfb ▸ q.2⟩, ⟨hab, Subtype.ext hfb⟩, ?_⟩
  rintro c ⟨hc, hq⟩
  exact Subtype.ext (huniq c.1 ⟨hc, congrArg Subtype.val hq⟩)

theorem IsPosetCover.restriction (hf : IsPosetCover f) :
    IsPosetCover (posetCoverRestriction f S) :=
  ⟨fun _ _ h => hf.mono h, fun q => by
    obtain ⟨p, hp⟩ := hf.surj q.1
    exact ⟨⟨p, hp ▸ q.2⟩, Subtype.ext hp⟩,
    posetCoverRestriction_up f S hf, posetCoverRestriction_up (P := Pᵒᵈ) (Q := Qᵒᵈ) f S hf.dual⟩

end FiniteChains.Comb
