module

public import RequestProject.OrderComplexGluing
public import RequestProject.CombCoveringLift

@[expose] public section

/-!
# A combinatorial criterion for a monotone map to induce a covering of order complexes

`RequestProject/CellComplex.lean` defines combinatorial coverings `Comb.IsCovering`.  This file
proves the criterion that is used for the projection of the complex of modified chambers onto
its quotient: a monotone map of preorders which is onto and which identifies, for every element,
the set of elements above it with the set of elements above its image, and likewise below,
induces a covering of the two-skeletons of the order complexes.

* `FiniteChains.Comb.IsPosetCover f` — the three conditions (surjectivity and *unique lifting*
  of the upper and lower intervals);
* `FiniteChains.Comb.isCovering_orderCxMap` — such an `f` induces a combinatorial covering
  `orderCx P → orderCx Q`.

Both the germ condition and the two-cell condition of `Comb.IsCovering` are verified from the
interval bijections; no finiteness, connectivity or freeness of a group action is used.
-/

namespace FiniteChains
namespace Comb

universe u

variable {P Q : Type u} [Preorder P] [Preorder Q]

/-- **A covering of preorders.**  `f` is monotone, onto, and the elements above (resp. below) an
element `a` are carried bijectively onto the elements above (resp. below) `f a`. -/
structure IsPosetCover (f : P → Q) : Prop where
  /-- `f` is monotone. -/
  mono : Monotone f
  /-- `f` is onto. -/
  surj : Function.Surjective f
  /-- Unique lifting of the upper interval. -/
  up : ∀ (a : P) (q : Q), f a ≤ q → ∃! b : P, a ≤ b ∧ f b = q
  /-- Unique lifting of the lower interval. -/
  down : ∀ (a : P) (q : Q), q ≤ f a → ∃! b : P, b ≤ a ∧ f b = q

namespace IsPosetCover

variable {f : P → Q} (hf : IsPosetCover f)

include hf

/-- Reversing both orders exchanges the two interval lifting properties. -/
theorem dual : @IsPosetCover Pᵒᵈ Qᵒᵈ _ _ f :=
  ⟨hf.mono.dual, hf.surj, hf.down, hf.up⟩

/-- The vertex in the upper sheet with the given projection. -/
noncomputable def liftUp (a : P) (b : Q) (h : f a ≤ b) : {p // a ≤ p ∧ f p = b} :=
  ⟨Classical.choose (hf.up a b h), (Classical.choose_spec (hf.up a b h)).1⟩

theorem liftUp_strict (a : P) (b : Q) (h : f a < b) : a < (hf.liftUp a b h.le).1 :=
  lt_of_le_not_ge (hf.liftUp a b h.le).2.1
    (fun e => h.not_ge ((hf.liftUp a b h.le).2.2 ▸ hf.mono e))

/-- Two elements above `a` with the same image agree. -/
theorem up_inj {a b b' : P} (hb : a ≤ b) (hb' : a ≤ b') (h : f b = f b') : b = b' :=
  (hf.up a (f b) (hf.mono hb)).unique ⟨hb, rfl⟩ ⟨hb', h.symm⟩

/-- Two elements below `a` with the same image agree. -/
theorem down_inj {a b b' : P} (hb : b ≤ a) (hb' : b' ≤ a) (h : f b = f b') : b = b' :=
  (hf.down a (f b) (hf.mono hb)).unique ⟨hb, rfl⟩ ⟨hb', h.symm⟩

/-- Covering of two-skeleta for a pair of compatible transitive relations.
The relations refine the order; the target relation lifts on comparable pairs. -/
theorem isCovering_chainCxMap {r : P → P → Prop} {s : Q → Q → Prop}
    {hr : IsTrans P r} {hs : IsTrans Q s}
    (hP : ∀ {a b}, r a b → a ≤ b) (hQ : ∀ {a b}, s a b → a ≤ b)
    (hmap : ∀ {a b}, r a b → s (f a) (f b))
    (hlift : ∀ {a b}, a ≤ b → s (f a) (f b) → r a b) :
    IsCovering (chainCxMap (hr := hr) (hs := hs) f hmap) := by
  refine ⟨hf.surj, fun a => ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · rintro ⟨⟨e, b⟩, he⟩ ⟨⟨e', b'⟩, he'⟩ h
    have hb : b = b' := congrArg (·.val.2) h
    subst b'
    have h₁  := congrArg (·.val.1.val.1) h
    have h₂  := congrArg (·.val.1.val.2) h
    have heq : e = e' := by
      clear h
      apply Subtype.ext
      cases b with
      | false =>
          have he : e.val.2 = a := he
          have he'  := he'
          exact Prod.ext (hf.down_inj (he ▸ hP e.2) (he' ▸ hP e'.2) h₁) (he.trans he'.symm)
      | true =>
          have he  := he
          have he' : e'.val.1 = a := he'
          exact Prod.ext (he.trans he'.symm) (hf.up_inj (he ▸ hP e.2) (he' ▸ hP e'.2) h₂)
    exact Subtype.ext (Prod.ext heq rfl)
  · rintro ⟨⟨d, b⟩, hd⟩
    cases b
    · have hd : d.val.2 = f a := hd
      obtain ⟨c, ⟨hc, hfc⟩, -⟩ := hf.down a d.val.1 (hd ▸ hQ d.2)
      have hca  := hlift hc (hfc.symm ▸ hd ▸ d.2)
      exact ⟨⟨(⟨(c, a), hca⟩, false), rfl⟩,
        Subtype.ext (Prod.ext (Subtype.ext (Prod.ext hfc hd.symm)) rfl)⟩
    · have hd : d.val.1 = f a := hd
      obtain ⟨c, ⟨hc, hfc⟩, -⟩ := hf.up a d.val.2 (hd ▸ hQ d.2)
      have hac  := hlift hc (hfc.symm ▸ hd ▸ d.2)
      exact ⟨⟨(⟨(a, c), hac⟩, true), rfl⟩,
        Subtype.ext (Prod.ext (Subtype.ext (Prod.ext hd.symm hfc)) rfl)⟩
  · intro t t' h
    have ha : t.val.1 = t'.val.1 := congrArg (·.val.2) h
    have hb  := congrArg (·.val.1.val.2.1) h
    have hc  := congrArg (·.val.1.val.2.2) h
    have he := hf.up_inj (hP t.2.1) (ha.symm ▸ hP t'.2.1) hb
    exact Subtype.ext (Prod.ext ha (Prod.ext he
      (hf.up_inj (hP t.2.2) (he.symm ▸ hP t'.2.2) hc)))
  · rintro ⟨⟨t, a⟩, ha⟩
    have ha' : t.val.1 = f a := ha
    obtain ⟨b, ⟨hab, hb⟩, -⟩ := hf.up a t.val.2.1 (ha' ▸ hQ t.2.1)
    obtain ⟨c, ⟨hbc, hc⟩, -⟩ := hf.up b t.val.2.2 (hb.symm ▸ hQ t.2.2)
    exact ⟨⟨(a, b, c), hlift hab (hb.symm ▸ ha' ▸ t.2.1),
      hlift hbc (hc.symm ▸ hb.symm ▸ t.2.2)⟩,
      Subtype.ext (Prod.ext (Subtype.ext (Prod.ext ha'.symm (Prod.ext hb hc))) rfl)⟩

end IsPosetCover

/-- A covering of preorders induces a covering of their order complexes. -/
theorem isCovering_orderCxMap {f : P → Q} (hf : IsPosetCover f) :
    IsCovering (orderCxMap f hf.mono) :=
  hf.isCovering_chainCxMap (r := (· ≤ ·)) (s := (· ≤ ·))
    (hr := ⟨fun _ _ _ => le_trans⟩) (hs := ⟨fun _ _ _ => le_trans⟩)
    (fun h => h) (fun h => h) (fun h => hf.mono h) (fun h _ => h)

end Comb
end FiniteChains
