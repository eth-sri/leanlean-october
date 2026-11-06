import RequestProject.OrderComplexGluing
import RequestProject.CombCoveringLift


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

namespace FiniteChains.Comb

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

/-- Two elements above `a` with the same image agree. -/
theorem up_inj (hb : a ≤ b) (hb' : a ≤ b') (h : f b = f b') : b = b' := by
  obtain ⟨c, -, huniq⟩ := hf.up a _ (hf.mono hb)
  grind

/-- Two elements below `a` with the same image agree. -/
theorem down_inj {a b b'} (hb : b ≤ a) (hb' : b' ≤ a) (h : f b = f b') : b = b' := by
  obtain ⟨c, -, huniq⟩ := hf.down a _ (hf.mono hb)
  grind

end IsPosetCover

/-- **The criterion.**  A covering of preorders induces a combinatorial covering of the
two-skeletons of the order complexes. -/
theorem isCovering_orderCxMap {f : P → Q} (hf : IsPosetCover f) :
    IsCovering (orderCxMap f hf.mono) := by
  refine ⟨hf.surj, ?_, ?_⟩
  · -- germs
    intro a
    constructor
    · rintro ⟨⟨e, b⟩, he⟩ ⟨⟨e', b'⟩, he'⟩ hEq
      have hb := congrArg (·.1.2) hEq
      subst hb
      have hE :=
        congrArg (fun g => (g.1.1.1.1, g.1.1.1.2)) hEq
      have h1 := congrArg Prod.fst hE
      have h2 := congrArg Prod.snd hE
      refine Subtype.ext (Prod.ext ?_ rfl)
      cases b with
      | false =>
          -- both edges end at `a`
          have hae : e.1.2 = a := he
          have hae' : e'.1.2 = a := he'
          have hfst :=
            hf.down_inj (a := a) (by grind) (by grind) h1
          exact Subtype.ext (by grind)
      | true =>
          have hae : e.1.1 = a := he
          have hae' : e'.1.1 = a := he'
          have hsnd :=
            hf.up_inj (a := a) (by grind) (by grind) h2
          exact Subtype.ext (by grind)
    · rintro ⟨⟨d, b⟩, hd⟩
      cases b with
      | true =>
          have hfa : f a = d.1.1 := hd.symm
          have hle : f a ≤ d.1.2 := by grind
          obtain ⟨c, ⟨hac, hfc⟩, -⟩ := hf.up a d.1.2 hle
          refine ⟨⟨(⟨(a, c), hac⟩, true), rfl⟩, ?_⟩
          refine Subtype.ext (Prod.ext ?_ rfl)
          exact Subtype.ext (Prod.ext hfa hfc)
      | false =>
          have hfa : f a = d.1.2 := hd.symm
          have hle : d.1.1 ≤ f a := by grind
          obtain ⟨c, ⟨hca, hfc⟩, -⟩ := hf.down a d.1.1 hle
          refine ⟨⟨(⟨(c, a), hca⟩, false), rfl⟩, ?_⟩
          refine Subtype.ext (Prod.ext ?_ rfl)
          exact Subtype.ext (Prod.ext hfc hfa)
  · -- two-cells
    constructor
    · rintro t t' hEq
      have hbase : t.1.1 = t'.1.1 :=
        congrArg (·.1.2) hEq
      have hT : ((f t.1.1, f t.1.2.1, f t.1.2.2))
          = (f t'.1.1, f t'.1.2.1, f t'.1.2.2) :=
        congrArg (·.1.1.1) hEq
      have h2 : f t.1.2.1 = f t'.1.2.1 := by simp_all
      have h3 : f t.1.2.2 = f t'.1.2.2 := by simp_all
      have hmid :=
        hf.up_inj t.2.1 (by grind) h2
      have htop :=
        hf.up_inj (t.2.1.trans t.2.2) (by grind) h3
      exact Subtype.ext (by grind)
    · rintro ⟨⟨s, a⟩, hs⟩
      have hfa : f a = s.1.1 := hs.symm
      obtain ⟨b, ⟨hab, hfb⟩, -⟩ := hf.up a s.1.2.1 (by grind)
      obtain ⟨c, ⟨hbc, hfc⟩, -⟩ := hf.up b s.1.2.2 (by grind)
      refine ⟨⟨(a, b, c), hab, hbc⟩, ?_⟩
      refine Subtype.ext (Prod.ext ?_ rfl)
      exact Subtype.ext (by aesop)
