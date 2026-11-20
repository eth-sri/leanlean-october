module

public import RequestProject.OrderPosetCovering

@[expose] public section

/-! The actual fiber product of a poset covering along a monotone map. -/
namespace FiniteChains.Comb
universe u
variable {P Q R : Type u} [Preorder P] [Preorder Q] [Preorder R]

variable (f : P → Q) (g : R → Q)

def PosetCoverPullback :=
  {x : P × R // f x.1 = g x.2}

instance : Preorder (PosetCoverPullback f g) :=
  Subtype.preorder _

instance {P Q R : Type u} [PartialOrder P] [Preorder Q] [PartialOrder R]
    (f : P → Q) (g : R → Q) : PartialOrder (PosetCoverPullback f g) :=
  Subtype.partialOrder _

variable (f : P → Q) (g : R → Q)

variable (x : PosetCoverPullback f g)

def posetPullbackProjection := x.1.2

def posetPullbackOriginal := x.1.1

omit [Preorder Q] in
theorem posetPullbackProjection_monotone :
    Monotone (posetPullbackProjection f g) := fun _ _ h => h.2

omit [Preorder Q] in
theorem posetPullbackOriginal_monotone :
    Monotone (posetPullbackOriginal f g) := fun _ _ h => h.1

/-- No injectivity assumption on the map used to pull back the covering is needed. -/
theorem IsPosetCover.pullback {f : P → Q} (hf : IsPosetCover f)
    (g : R → Q) (hg : Monotone g) : IsPosetCover (posetPullbackProjection f g) := by
  refine ⟨posetPullbackProjection_monotone f g, ?_, ?_, ?_⟩
  · intro r
    obtain ⟨p, hp⟩ := hf.surj (g r)
    exact ⟨⟨(p, r), hp⟩, rfl⟩
  · intro a r h
    obtain ⟨b, hb, huniq⟩ := hf.up _ _ (a.2 ▸ hg h)
    refine ⟨⟨(b, r), hb.2⟩, ⟨⟨hb.1, h⟩, rfl⟩, ?_⟩
    intro c hc
    apply Subtype.ext
    exact Prod.ext (huniq c.1.1 ⟨hc.1.1, c.2.trans (congrArg g hc.2)⟩) hc.2
  · intro a r h
    obtain ⟨b, hb, huniq⟩ := hf.down _ _ (a.2 ▸ hg h)
    refine ⟨⟨(b, r), hb.2⟩, ⟨⟨hb.1, h⟩, rfl⟩, ?_⟩
    intro c hc
    apply Subtype.ext
    exact Prod.ext (huniq c.1.1 ⟨hc.1.1, c.2.trans (congrArg g hc.2)⟩) hc.2

end FiniteChains.Comb
