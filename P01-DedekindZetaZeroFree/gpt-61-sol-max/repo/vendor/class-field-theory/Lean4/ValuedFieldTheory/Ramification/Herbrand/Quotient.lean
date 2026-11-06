module

public import Mathlib

public import Mathlib.SetTheory.Cardinal.Finite
public import ValuedFieldTheory.Ramification.Herbrand.Function
public import Mathlib.GroupTheory.Index

@[expose] public section


/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/





set_option autoImplicit false

/-!
# Pure group theory for Herbrand towers

This file contains the completion-free finite-group bookkeeping used in
the Herbrand quotient theorem and the quotient and tower filtration theorems.  It packages
the filtrations induced on a subgroup and on its quotient image, proves the
exact cardinality factorization at every level, and records compatibility of
Herbrand functions with transport along group equivalences.

The valued-field inputs of the quotient-depth and upper-numbering identities do not occur here.
Valued-field endpoints combine these structural lemmas with ramification-number
averaging; the inverse-function and upper-numbering statements are proved directly
in the Hilbert-ramification Herbrand theorem module.
-/

noncomputable section

universe u v

namespace RamificationTheory.DiscreteValuationField
namespace AntitoneNormalSubgroupFiltration

variable {G : Type u} [Group G]

section
variable (F : AntitoneNormalSubgroupFiltration G) (H : Subgroup G)
include F H
/-- The filtration induced on a subgroup by intersection with every ambient
lower group. -/
def subgroupFiltration   :
    AntitoneNormalSubgroupFiltration H where
  lower n := (F.lower n).comap H.subtype
  lower_normal n := (F.lower_normal n).comap H.subtype
  antitone := by
    intro m n hmn
    exact Subgroup.comap_mono (F.antitone hmn)

/-- States the theorem `subgroupFiltration_lower`. -/
@[simp] theorem subgroupFiltration_lower
      (n : ℕ) :
    (subgroupFiltration F H).lower n = (F.lower n).comap H.subtype :=
  rfl








/-- The pointwise image filtration on a quotient by a normal subgroup.  This
is not asserted to be the actual lower filtration of a valued quotient; that
identification is precisely the content supplied by Herbrand's theorem. -/
def quotientImageFiltration   [H.Normal] :
    AntitoneNormalSubgroupFiltration (G ⧸ H) where
  lower n := (F.lower n).map (QuotientGroup.mk' H)
  lower_normal n := (F.lower_normal n).map
    (QuotientGroup.mk' H) (QuotientGroup.mk'_surjective H)
  antitone := by
    intro m n hmn
    exact Subgroup.map_mono (F.antitone hmn)
end


section
variable (F : AntitoneNormalSubgroupFiltration G) (H : Subgroup G) [H.Normal]
    (n : ℕ)
include F H n
/-- States the theorem `quotientImageFiltration_lower`. -/
@[simp] theorem quotientImageFiltration_lower
      :
    (quotientImageFiltration F H).lower n =
      (F.lower n).map (QuotientGroup.mk' H) :=
  rfl

/-- At each level, the subgroup filtration is the kernel of the quotient map
restricted to the corresponding ambient lower group. -/
def lowerToQuotientImageHom   :
    F.lower n →* (quotientImageFiltration F H).lower n where
  toFun sigma :=
    ⟨QuotientGroup.mk' H (sigma : G), ⟨sigma, sigma.property, rfl⟩⟩
  map_one' := by
    apply Subtype.ext
    simp
  map_mul' sigma tau := by
    rfl

/-- States the theorem `lowerToQuotientImageHom_surjective`. -/
theorem lowerToQuotientImageHom_surjective
      :
    Function.Surjective (lowerToQuotientImageHom F H n) := by
  rintro ⟨q, hq⟩
  rcases hq with ⟨sigma, hsigma, hsigmaq⟩
  refine ⟨⟨sigma, hsigma⟩, ?_⟩
  apply Subtype.ext
  exact hsigmaq

/-- The kernel of the restricted quotient map is canonically the intersection
filtration on `H`. -/
def lowerToQuotientImageKerEquiv   :
    (lowerToQuotientImageHom F H n).ker ≃
      (subgroupFiltration F H).lower n where
  toFun sigma := by
    let sigmaLower : F.lower n := sigma
    have hmk : QuotientGroup.mk' H ((sigma : F.lower n) : G) = 1 := congrArg Subtype.val sigma.property
    have hsigmaH  :=
      (QuotientGroup.eq_one_iff (N := H)
        (x := ((sigma : F.lower n) : G))).1 hmk
    exact ⟨⟨((sigma : F.lower n) : G), hsigmaH⟩, sigmaLower.property⟩
  invFun h := by
    refine ⟨⟨((h : H) : G), h.property⟩, ?_⟩
    apply Subtype.ext
    exact (QuotientGroup.eq_one_iff (N := H) (x := ((h : H) : G))).2 h.val.property
  left_inv sigma := by
    apply Subtype.ext
    apply Subtype.ext
    rfl
  right_inv h := by
    apply Subtype.ext
    apply Subtype.ext
    rfl
end


/-- Exact level-cardinality factorization
`|F_n| = |F_n ∩ H| * |image(F_n)|`. -/
theorem card_subgroupFiltration_mul_card_quotientImageFiltration
    [Finite G] (F : AntitoneNormalSubgroupFiltration G)
    (H : Subgroup G) [H.Normal] (n : ℕ) :
    Nat.card ((subgroupFiltration F H).lower n) *
        Nat.card ((quotientImageFiltration F H).lower n) =
      Nat.card (F.lower n) := by
  let f := lowerToQuotientImageHom F H n
  have hker : Nat.card f.ker =
      Nat.card ((subgroupFiltration F H).lower n) :=
    Nat.card_congr (lowerToQuotientImageKerEquiv F H n)
  have hrange : Nat.card f.range =
      Nat.card ((quotientImageFiltration F H).lower n) := by
    rw [MonoidHom.range_eq_top.mpr
      (lowerToQuotientImageHom_surjective F H n)]
    exact Subgroup.card_top
  rw [← hker, ← hrange, ← Subgroup.index_ker]
  exact Subgroup.card_mul_index f.ker

variable {G' : Type v} [Group G']

section
variable (F : AntitoneNormalSubgroupFiltration G) (e : G ≃* G')
include F e
/-- Transport a lower ramification filtration across a group equivalence. -/
def transportEquiv   :
    AntitoneNormalSubgroupFiltration G' where
  lower n := (F.lower n).comap e.symm.toMonoidHom
  lower_normal n := (F.lower_normal n).comap e.symm.toMonoidHom
  antitone := by
    intro m n hmn
    exact Subgroup.comap_mono (F.antitone hmn)

/-- States the theorem `transportEquiv_lower`. -/
@[simp] theorem transportEquiv_lower
      (n : ℕ) :
    (transportEquiv F e).lower n =
      (F.lower n).comap e.symm.toMonoidHom :=
  rfl








/-- Every integral level is carried to the corresponding transported level. -/
def lowerEquivTransportEquiv
      (n : ℕ) :
    F.lower n ≃ (transportEquiv F e).lower n where
  toFun sigma := ⟨e (sigma : G), by simp⟩
  invFun tau := ⟨e.symm (tau : G'), tau.property⟩
  left_inv sigma := by
    apply Subtype.ext
    simp
  right_inv tau := by
    apply Subtype.ext
    simp
end


/-- States the theorem `card_lower_transportEquiv`. -/
def card_lower_transportEquiv
    [Finite G] [Finite G']
    (F : AntitoneNormalSubgroupFiltration G) (e : G ≃* G') (n : ℕ)  := Nat.card_congr (lowerEquivTransportEquiv F e n).symm

/-- The Herbrand function is invariant under transport across a group
equivalence. -/
theorem herbrandFunction_transportEquiv
    [Finite G] [Finite G']
    (F : AntitoneNormalSubgroupFiltration G) (e : G ≃* G') (s : ℝ) :
    (RamificationTheory.DiscreteValuationField.AntitoneNormalSubgroupFiltration.herbrandFunction (transportEquiv F e)) s = (RamificationTheory.DiscreteValuationField.AntitoneNormalSubgroupFiltration.herbrandFunction F) s := by
  apply RamificationTheory.DiscreteValuationField.AntitoneNormalSubgroupFiltration.herbrandFunction_eq_of_card_lower_eq (transportEquiv F e) F
  intro n
  apply card_lower_transportEquiv












section
variable (F : AntitoneNormalSubgroupFiltration G) (H : Subgroup G) [H.Normal]
    (e : (G ⧸ H) ≃* G')
include F H e
/-- The quotient-image filtration, transported to any isomorphic model of
the quotient group. -/
def quotientImageTransport
       :=
  transportEquiv (quotientImageFiltration F H) e

/-- States the theorem `quotientImageTransport_lower`. -/
@[simp] theorem quotientImageTransport_lower
      (n : ℕ) :
    (quotientImageTransport F H e).lower n =
      ((F.lower n).map (QuotientGroup.mk' H)).comap e.symm.toMonoidHom :=
  rfl
end


/-- Mapping a subgroup across a group equivalence is inverse to pulling it
back.  This orientation is the one used by the fixed-field quotient map. -/
theorem subgroup_map_equiv_eq_iff_eq_comap
    (e : G ≃* G') (A : Subgroup G) (B : Subgroup G') :
    A.map e.toMonoidHom = B ↔
      A = B.comap e.toMonoidHom := by
  constructor
  · intro h
    rw [← h]
    exact (Subgroup.comap_map_eq_self_of_injective
      (f := e.toMonoidHom) e.injective A).symm
  · intro h
    rw [h]
    exact Subgroup.map_comap_eq_self_of_surjective
      (f := e.toMonoidHom) e.surjective B

/-- States the theorem `transportEquiv_lower_eq_map`. -/
theorem transportEquiv_lower_eq_map
    (F : AntitoneNormalSubgroupFiltration G) (e : G ≃* G') (n : ℕ) :
    (transportEquiv F e).lower n = (F.lower n).map e.toMonoidHom := by
  ext sigma
  constructor
  · intro hsigma
    exact ⟨e.symm sigma, hsigma, e.apply_symm_apply sigma⟩
  · rintro ⟨tau, htau, rfl⟩
    simpa using htau


/-- States the theorem `transportEquiv_lower_eq_iff`. -/
theorem transportEquiv_lower_eq_iff
    (F : AntitoneNormalSubgroupFiltration G) (e : G ≃* G')
    (n : ℕ) (B : Subgroup G') :
    (transportEquiv F e).lower n = B ↔
      F.lower n = B.comap e.toMonoidHom := by
  rw [transportEquiv_lower_eq_map F e n]
  apply subgroup_map_equiv_eq_iff_eq_comap

/-- Equality with a transported quotient-image level is exactly the usual
map/comap formulation of a lower-quotient theorem. -/
def quotientImageTransport_lower_eq_iff
    (F : AntitoneNormalSubgroupFiltration G) (H : Subgroup G) [H.Normal]
    (e : (G ⧸ H) ≃* G') (n : ℕ) (B : Subgroup G')  := transportEquiv_lower_eq_iff (quotientImageFiltration F H) e n B


/-- Exact level-cardinality factorization after replacing the abstract
quotient by any isomorphic group model. -/
theorem card_subgroupFiltration_mul_card_quotientImageTransport
    [Finite G] [Finite G'] (F : AntitoneNormalSubgroupFiltration G)
    (H : Subgroup G) [H.Normal] (e : (G ⧸ H) ≃* G') (n : ℕ) :
    Nat.card ((subgroupFiltration F H).lower n) *
        Nat.card ((quotientImageTransport F H e).lower n) =
      Nat.card (F.lower n) := by
  change Nat.card ((subgroupFiltration F H).lower n) *
      Nat.card ((transportEquiv (quotientImageFiltration F H) e).lower n) = _
  rw [card_lower_transportEquiv (quotientImageFiltration F H) e n]
  apply card_subgroupFiltration_mul_card_quotientImageFiltration





















end AntitoneNormalSubgroupFiltration
end RamificationTheory.DiscreteValuationField

end
