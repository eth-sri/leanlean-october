module

public import Mathlib.GroupTheory.Transfer
public import Mathlib.GroupTheory.Abelianization.Defs

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/




set_option autoImplicit false

namespace ClassFormation

/-!
# Naturality of transfer under a quotient

This file supplies the group-theoretic source used in transfer--norm naturality. If a surjection
has kernel contained in a finite-index subgroup, it identifies the two left-coset spaces and
transfer commutes with the induced maps on abelianizations.
-/

noncomputable section

open Function
open scoped Pointwise

variable {P : Type*} {Q : Type*} [Group P] [Group Q]

/-- A surjection identifies left cosets of `H` with left cosets of its image
when its kernel is contained in `H`. -/
noncomputable def leftCosetEquivMapOfSurjective
    (f : P →* Q) (hf : Function.Surjective f)
    (H : Subgroup P) (hker : f.ker ≤ H) :
    P ⧸ H ≃ Q ⧸ H.map f := by
  let mapCoset : P ⧸ H → Q ⧸ H.map f :=
    Quotient.map' f fun x y hxy => by
      rw [QuotientGroup.leftRel_apply]
      rw [← f.map_inv, ← f.map_mul]
      exact ⟨x⁻¹ * y, (QuotientGroup.leftRel_apply).1 hxy, rfl⟩
  apply Equiv.ofBijective mapCoset
  constructor
  · refine Quotient.ind' fun x => ?_
    refine Quotient.ind' fun y hxy => ?_
    apply Quotient.sound'
    rw [QuotientGroup.leftRel_apply]
    have hrel : QuotientGroup.leftRel (H.map f) (f x) (f y) :=
      Quotient.eq''.1 hxy
    have hmap : f (x⁻¹ * y) ∈ H.map f := by
      rw [f.map_mul, f.map_inv]
      exact (QuotientGroup.leftRel_apply).1 hrel
    have hcomap : x⁻¹ * y ∈ (H.map f).comap f := hmap
    rwa [Subgroup.comap_map_eq_self hker] at hcomap
  · refine Quotient.ind' fun q => ?_
    obtain ⟨p, rfl⟩ := hf q
    exact ⟨QuotientGroup.mk p, rfl⟩

/--
Establishes the identity `leftCosetEquivMapOfSurjective f hf H hker (QuotientGroup.mk p) =
QuotientGroup.mk (f p)`.
-/
@[simp]
theorem leftCosetEquivMapOfSurjective_mk
    (f : P →* Q) (hf : Function.Surjective f)
    (H : Subgroup P) (hker : f.ker ≤ H) (p : P) :
    leftCosetEquivMapOfSurjective f hf H hker (QuotientGroup.mk p) =
      QuotientGroup.mk (f p) :=
  rfl

/--
Establishes the identity `leftCosetEquivMapOfSurjective f hf H hker (p • q) = f p •
leftCosetEquivMapOfSurjective f hf H hker q`.
-/
@[simp]
theorem leftCosetEquivMapOfSurjective_smul
    (f : P →* Q) (hf : Function.Surjective f)
    (H : Subgroup P) (hker : f.ker ≤ H)
    (p : P) (q : P ⧸ H) :
    leftCosetEquivMapOfSurjective f hf H hker (p • q) =
      f p • leftCosetEquivMapOfSurjective f hf H hker q := by
  refine Quotient.inductionOn' q ?_
  intro x
  simp only [MulAction.Quotient.smul_mk, leftCosetEquivMapOfSurjective_mk,
    smul_eq_mul, map_mul]

/-- A left transversal descends along the same quotient map.  It is built
from the induced equivalence of left-coset spaces, so its chosen
representatives are literally the images of the original representatives. -/
noncomputable def leftTransversalMapOfSurjective
    (f : P →* Q) (hf : Function.Surjective f)
    (H : Subgroup P) (hker : f.ker ≤ H)
    (T : H.LeftTransversal) : (H.map f).LeftTransversal := by
  let e := leftCosetEquivMapOfSurjective f hf H hker
  let u : Q ⧸ H.map f → Q := fun q =>
    f (T.2.leftQuotientEquiv (e.symm q) : P)
  have hu (q : Q ⧸ H.map f) : (u q : Q ⧸ H.map f) = q := by
    change e (QuotientGroup.mk
      (T.2.leftQuotientEquiv (e.symm q) : P)) = q
    have hrep : QuotientGroup.mk
        (T.2.leftQuotientEquiv (e.symm q) : P) = e.symm q :=
      T.2.quotientGroupMk_leftQuotientEquiv (e.symm q)
    exact (congrArg e hrep).trans (e.apply_symm_apply q)
  exact ⟨Set.range u, Subgroup.isComplement_range_left hu⟩

/--
The defining evaluation formula for `leftTransversalMapOfSurjective` is
`((leftTransversalMapOfSurjective f hf H hker T).2.leftQuotientEquiv q : Q) = f
(T.2.leftQuotientEquiv ((leftCosetEquivMapOfSurjective f hf H hker).symm q) : P)`.
-/
@[simp]
theorem leftTransversalMapOfSurjective_apply
    (f : P →* Q) (hf : Function.Surjective f)
    (H : Subgroup P) (hker : f.ker ≤ H)
    (T : H.LeftTransversal) (q : Q ⧸ H.map f) :
    ((leftTransversalMapOfSurjective f hf H hker T).2.leftQuotientEquiv q : Q) =
      f (T.2.leftQuotientEquiv
        ((leftCosetEquivMapOfSurjective f hf H hker).symm q) : P) := by
  let e := leftCosetEquivMapOfSurjective f hf H hker
  let u : Q ⧸ H.map f → Q := fun r =>
    f (T.2.leftQuotientEquiv (e.symm r) : P)
  have hu (r : Q ⧸ H.map f) : (u r : Q ⧸ H.map f) = r := by
    change e (QuotientGroup.mk
      (T.2.leftQuotientEquiv (e.symm r) : P)) = r
    have hrep : QuotientGroup.mk
        (T.2.leftQuotientEquiv (e.symm r) : P) = e.symm r :=
      T.2.quotientGroupMk_leftQuotientEquiv (e.symm r)
    exact (congrArg e hrep).trans (e.apply_symm_apply r)
  change ((Subgroup.isComplement_range_left hu).leftQuotientEquiv q : Q) = u q
  exact Subgroup.IsComplement.leftQuotientEquiv_apply hu q













end
end ClassFormation
