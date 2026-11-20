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

section Relations
variable {P Q : Type u}

/-- Lifting criterion for the nerve of any relation: every arrow with
prescribed source or prescribed target lifts uniquely. -/
structure RelCover (r : P → P → Prop) (s : Q → Q → Prop) (f : P → Q) : Prop where
  mono : ∀ ⦃a b⦄, r a b → s (f a) (f b)
  surj : Function.Surjective f
  up : ∀ a q, s (f a) q → ∃! b, r a b ∧ f b = q
  down : ∀ a q, s q (f a) → ∃! b, r b a ∧ f b = q

namespace RelCover
variable {aRel : P → P → Prop} {bRel : Q → Q → Prop} {f : P → Q} (hf : RelCover aRel bRel f) {a b b' : P}
include hf

theorem up_inj (hb : aRel a b) (hb' : aRel a b') (h : f b = f b') : b = b' := by
  obtain ⟨_, _, hi⟩ := hf.up a _ (hf.mono hb); grind

theorem down_inj (hb : aRel b a) (hb' : aRel b' a) (h : f b = f b') : b = b' := by
  obtain ⟨_, _, hi⟩ := hf.down a _ (hf.mono hb); grind

theorem isCovering [Trans aRel aRel aRel] [Trans bRel bRel bRel] :
    IsCovering (relSkeletonMap (r := aRel) (s := bRel) f hf.mono) := by
  refine ⟨hf.surj, ?_, ?_⟩
  · -- germs
    intro a
    constructor
    · rintro ⟨⟨e, b⟩, he⟩ ⟨⟨e', b'⟩, he'⟩ hEq
      have hb := congrArg (fun g : Germ _ _ => g.1.2) hEq
      subst hb
      have hE :=
        congrArg (fun g : Germ (relSkeleton bRel) _ => (g.1.1.1.1, g.1.1.1.2)) hEq
      refine Subtype.ext (Prod.ext ?_ rfl)
      cases b with
      | false =>
          -- both edges end at `a`
          have hae : e.1.2 = a := he
          have hae' : e'.1.2 = a := he'
          have hfst :=
            hf.down_inj (a := a) (by grind) (by grind) (congrArg Prod.fst hE)
          exact Subtype.ext (Prod.ext hfst (hae.trans hae'.symm))
      | true =>
          have hae : e.1.1 = a := he
          have hae' : e'.1.1 = a := he'
          have hsnd :=
            hf.up_inj (a := a) (by grind) (by grind) (congrArg Prod.snd hE)
          exact Subtype.ext (Prod.ext (hae.trans hae'.symm) hsnd)
    · rintro ⟨⟨d, b⟩, hd⟩
      cases b with
      | true =>
          have hfa : f a = d.1.1 := hd.symm
          obtain ⟨c, ⟨hac, hfc⟩, -⟩ := hf.up a _ (by rw [hfa]; exact d.2)
          refine ⟨⟨(⟨(a, c), hac⟩, true), rfl⟩, ?_⟩
          refine Subtype.ext (Prod.ext ?_ rfl)
          exact Subtype.ext (Prod.ext hfa hfc)
      | false =>
          have hfa : f a = d.1.2 := hd.symm
          obtain ⟨c, ⟨hca, hfc⟩, -⟩ := hf.down a _ (by rw [hfa]; exact d.2)
          refine ⟨⟨(⟨(c, a), hca⟩, false), rfl⟩, ?_⟩
          refine Subtype.ext (Prod.ext ?_ rfl)
          exact Subtype.ext (Prod.ext hfc hfa)
  · -- two-cells
    constructor
    · rintro t t' hEq
      have hbase : t.1.1 = t'.1.1 :=
        congrArg (fun g : {gv : (relSkeleton bRel).F × (relSkeleton aRel).V //
          (relSkeleton bRel).base gv.1 = f gv.2} => g.1.2) hEq
      have hT :=
        congrArg (fun g : {gv : (relSkeleton bRel).F × (relSkeleton aRel).V //
          (relSkeleton bRel).base gv.1 = f gv.2} => g.1.1.1) hEq
      have hmid :=
        hf.up_inj t.2.1 (by grind) (congrArg (fun z : Q × Q × Q => z.2.1) hT)
      have htop :=
        hf.up_inj (Trans.trans t.2.1 t.2.2) (by grind) (congrArg (fun z : Q × Q × Q => z.2.2) hT)
      exact Subtype.ext (Prod.ext hbase (Prod.ext hmid htop))
    · rintro ⟨⟨s, a⟩, hs⟩
      obtain ⟨b, ⟨hab, hfb⟩, -⟩ := hf.up a s.1.2.1 (by grind)
      obtain ⟨c, ⟨hbc, hfc⟩, -⟩ := hf.up b s.1.2.2 (by grind)
      refine ⟨⟨(a, b, c), hab, hbc⟩, ?_⟩
      refine Subtype.ext (Prod.ext ?_ rfl)
      exact Subtype.ext (Prod.ext hs.symm (Prod.ext hfb hfc))

end RelCover
end Relations

variable {P Q : Type u} [Preorder P] [Preorder Q] {f : P → Q}
abbrev IsPosetCover (f : P → Q) := RelCover (· ≤ ·) (· ≤ ·) f

theorem isCovering_orderCxMap (hf : IsPosetCover f) : IsCovering (orderCxMap f hf.mono) := hf.isCovering

end Comb
end FiniteChains
