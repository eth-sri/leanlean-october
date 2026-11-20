module

public import RequestProject.OrderPosetCovering

@[expose] public section

/-! The actual fiber product of a poset covering along a monotone map. -/
namespace FiniteChains.Comb
universe u
variable {P Q R : Type u} [Preorder P] [Preorder Q] [Preorder R]

def PosetCoverPullback (f : P → Q) (g : R → Q) :=
  {x : P × R // f x.1 = g x.2}

instance (f : P → Q) (g : R → Q) : Preorder (PosetCoverPullback f g) :=
  Subtype.preorder _

instance {P Q R : Type u} [PartialOrder P] [Preorder Q] [PartialOrder R]
    (f : P → Q) (g : R → Q) : PartialOrder (PosetCoverPullback f g) :=
  Subtype.partialOrder _

def posetPullbackProjection (f : P → Q) (g : R → Q) (x : PosetCoverPullback f g) : R := x.1.2

def posetPullbackOriginal (f : P → Q) (g : R → Q) (x : PosetCoverPullback f g) : P := x.1.1

omit [Preorder Q] in
theorem posetPullbackProjection_monotone (f : P → Q) (g : R → Q) :
    Monotone (posetPullbackProjection f g) := fun _ _ h => h.2

omit [Preorder Q] in
theorem posetPullbackOriginal_monotone (f : P → Q) (g : R → Q) :
    Monotone (posetPullbackOriginal f g) := fun _ _ h => h.1

private theorem posetPullback_up {f : P → Q} (hf : IsPosetCover f)
    (g : R → Q) (hg : Monotone g) (a : PosetCoverPullback f g) (r : R) (h : a.1.2 ≤ r) :
    ∃! b : PosetCoverPullback f g, a ≤ b ∧ b.1.2 = r := by
  obtain ⟨b, hb, huniq⟩ := hf.up a.1.1 (g r) (a.2 ▸ hg h)
  refine ⟨⟨(b, r), hb.2⟩, ⟨⟨hb.1, h⟩, rfl⟩, ?_⟩
  intro c hc
  exact Subtype.ext (Prod.ext (huniq c.1.1 ⟨hc.1.1, c.2.trans (congrArg g hc.2)⟩) hc.2)

/-- No injectivity assumption on the map used to pull back the covering is needed. -/
theorem IsPosetCover.pullback {f : P → Q} (hf : IsPosetCover f)
    (g : R → Q) (hg : Monotone g) : IsPosetCover (posetPullbackProjection f g) :=
  ⟨posetPullbackProjection_monotone f g, fun r => by
    obtain ⟨p, hp⟩ := hf.surj (g r)
    exact ⟨⟨(p, r), hp⟩, rfl⟩,
    posetPullback_up hf g hg, posetPullback_up (R := Rᵒᵈ) hf.dual g hg.dual⟩

end FiniteChains.Comb
