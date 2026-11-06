module

public import Mathlib

public import Mathlib.GroupTheory.QuotientGroup.Finite

@[expose] public section


/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/



set_option autoImplicit false

/-!
# Named quotients of antitone normal-subgroup filtrations

This module owns the opaque quotient carriers of a lower ramification
filtration and their construction, elimination, lifting, and mapping API.
Arithmetic Herbrand functions and valuation-action specializations live in
`RamificationTheory.GaloisValuation.Ramification`.
-/

noncomputable section

universe u v

namespace RamificationTheory
namespace DiscreteValuationField

/-- A generic antitone filtration by normal subgroups.  This interface contains
only the group-theoretic laws; arithmetic lower ramification filtrations are
canonical values constructed from valued extensions. -/
structure AntitoneNormalSubgroupFiltration (G : Type u) [Group G] where
  /-- The subgroup at each lower-filtration index. -/
  lower : ℕ → Subgroup G
  /-- Every subgroup in the lower filtration is normal. -/
  lower_normal : ∀ n : ℕ, (lower n).Normal
  /-- The lower filtration decreases as its index increases. -/
  antitone : ∀ {m n : ℕ}, m ≤ n → lower n ≤ lower m

namespace AntitoneNormalSubgroupFiltration

variable {G : Type u} [Group G] (F : AntitoneNormalSubgroupFiltration G)

/-- Provides the instance `lower_normal_instance`. -/
instance lower_normal_instance (n : ℕ) : (F.lower n).Normal :=
  F.lower_normal n

/-- The quotient by the `n`th lower ramification group. -/
def quotient (n : ℕ)  :=
  G ⧸ F.lower n

/-- The subquotient `G_m / G_n`, used for ramification graded pieces when
`m ≤ n`.  The type is available for all `m,n`; under `m ≤ n`, `G_n` is a
subgroup of `G_m` by antitonicity. -/
def subquotient (m n : ℕ)  :=
  F.lower m ⧸ (F.lower n).subgroupOf (F.lower m)

/-- The lower ramification graded piece `G_n/G_{n+1}`. -/
def gradedPiece (n : ℕ)  :=
  F.subquotient n (n + 1)

/-- The inertia subgroup `G_0` of a lower ramification filtration. -/
abbrev inertiaSubgroup  :=
  F.lower 0






/-- The wild inertia subgroup `G_1` of a lower ramification filtration. -/
abbrev wildInertiaSubgroup  :=
  F.lower 1

/-- The tame quotient `G_0/G_1`. -/
def tameQuotient  :=
  F.gradedPiece 0






/-- Provides the instance `wildInertiaSubgroup_normal`. -/
instance wildInertiaSubgroup_normal : F.wildInertiaSubgroup.Normal := by
  change (F.lower 1).Normal
  infer_instance






/-- Provides the instance `wildInertiaSubgroup_subgroupOf_inertiaSubgroup_normal`. -/
instance wildInertiaSubgroup_subgroupOf_inertiaSubgroup_normal :
    ((F.wildInertiaSubgroup).subgroupOf F.inertiaSubgroup).Normal := by
  change ((F.lower 1).subgroupOf (F.lower 0)).Normal
  infer_instance

/-! ### Named quotient boundaries

The four ramification quotient carriers are opaque public objects.  Raw
`QuotientGroup` presentations occur only in the concrete equivalences and in
the implementation of the operations below. -/

/-- Provides the instance `quotientGroup`. -/
instance quotientGroup (n : ℕ) : Group (F.quotient n) := by
  change Group (G ⧸ F.lower n)
  infer_instance

/-- Provides the instance `subquotientGroup`. -/
instance subquotientGroup (m n : ℕ) : Group (F.subquotient m n) := by
  change Group
    (F.lower m ⧸ (F.lower n).subgroupOf (F.lower m))
  infer_instance

/-- Provides the instance `gradedPieceGroup`. -/
instance gradedPieceGroup (n : ℕ) : Group (F.gradedPiece n) := by
  change Group
    (F.lower n ⧸
      (F.lower (n + 1)).subgroupOf (F.lower n))
  infer_instance

/-- Provides the instance `tameQuotientGroup`. -/
instance tameQuotientGroup : Group F.tameQuotient := by
  change Group
    (F.inertiaSubgroup ⧸
      (F.wildInertiaSubgroup).subgroupOf F.inertiaSubgroup)
  infer_instance

/-- Concrete presentation of `G/G_n`. -/
def quotientConcreteMulEquiv (n : ℕ) :
    F.quotient n ≃* G ⧸ F.lower n :=
  MulEquiv.refl _

/-- Concrete presentation of `G_m/G_n`. -/
def subquotientConcreteMulEquiv (m n : ℕ) :
    F.subquotient m n ≃*
      F.lower m ⧸ (F.lower n).subgroupOf (F.lower m) :=
  MulEquiv.refl _

/-- The graded piece as its adjacent named subquotient. -/
def gradedPieceEquivSubquotient (n : ℕ) :
    F.gradedPiece n ≃* F.subquotient n (n + 1) :=
  MulEquiv.refl _

/-- Concrete presentation of `G_n/G_{n+1}`. -/
def gradedPieceConcreteMulEquiv (n : ℕ)  :=
  (F.gradedPieceEquivSubquotient n).trans
    (F.subquotientConcreteMulEquiv n (n + 1))

/-- The tame quotient as the zeroth named graded piece. -/
def tameQuotientEquivGradedPiece :
    F.tameQuotient ≃* F.gradedPiece 0 :=
  MulEquiv.refl _

/-- Concrete presentation of `G_0/G_1`. -/
def tameQuotientConcreteMulEquiv  :=
  (F.tameQuotientEquivGradedPiece).trans
    (F.gradedPieceConcreteMulEquiv 0)

/-- Canonical projection to `G/G_n`. -/
def quotientMk (n : ℕ)  :=
  (F.quotientConcreteMulEquiv n).symm.toMonoidHom.comp
    (QuotientGroup.mk' (F.lower n))

/-- States the theorem `quotientMk_apply`. -/
@[simp]
theorem quotientMk_apply (n : ℕ) (σ : G) :
    F.quotientConcreteMulEquiv n (F.quotientMk n σ) =
      QuotientGroup.mk' (F.lower n) σ :=
  rfl

/-- States the theorem `quotientMk_eq_one_iff`. -/
@[simp]
theorem quotientMk_eq_one_iff (n : ℕ) (σ : G) :
    F.quotientMk n σ = 1 ↔ σ ∈ F.lower n := by
  constructor
  · intro h
    have h' := congrArg (F.quotientConcreteMulEquiv n) h
    rw [F.quotientMk_apply, map_one] at h'
    exact (QuotientGroup.eq_one_iff σ).1 h'
  · intro h
    apply (F.quotientConcreteMulEquiv n).injective
    rw [F.quotientMk_apply, map_one]
    exact (QuotientGroup.eq_one_iff σ).2 h















/-- Eliminate a named ramification quotient through canonical
representatives. -/
protected theorem quotient_inductionOn (n : ℕ)
    {motive : F.quotient n → Prop} (q : F.quotient n)
    (h : ∀ σ : G, motive (F.quotientMk n σ)) :
    motive q := by
  obtain ⟨σ, rfl⟩ :=
    ((F.quotientConcreteMulEquiv n).symm.surjective.comp
      (QuotientGroup.mk'_surjective (F.lower n))) q
  exact h σ

section
variable {H : Type v} [Group H] (n : ℕ)
    (f : G →* H) (h : F.lower n ≤ f.ker)
include H n f h
/-- Descend a homomorphism that kills the `n`th lower group. -/
def quotientLift    :=
  (QuotientGroup.lift (F.lower n) f h).comp
    (F.quotientConcreteMulEquiv n).toMonoidHom

/-- States the theorem `quotientLift_mk`. -/
@[simp]
theorem quotientLift_mk   (σ : G) :
    F.quotientLift n f h (F.quotientMk n σ) = f σ :=
  rfl
end


section
variable {H : Type v} [Group H]
    (E : AntitoneNormalSubgroupFiltration H) (n m : ℕ)
    (f : G →* H)
    (h : ∀ σ : G, σ ∈ F.lower n → f σ ∈ E.lower m)
include H E n m f h
/-- Map between named ramification quotients induced by a group
homomorphism. -/
def quotientMap   :
    F.quotient n →* E.quotient m :=
  F.quotientLift n ((E.quotientMk m).comp f) (by
    intro σ hσ
    rw [MonoidHom.mem_ker]
    exact (E.quotientMk_eq_one_iff m (f σ)).2 (h σ hσ))

/-- States the theorem `quotientMap_apply_mk`. -/
@[simp]
theorem quotientMap_apply_mk   (σ : G) :
    F.quotientMap E n m f h (F.quotientMk n σ) =
      E.quotientMk m (f σ) :=
  rfl
end


/-- Canonical projection to `G_m/G_n`. -/
def subquotientMk (m n : ℕ)  :=
  (F.subquotientConcreteMulEquiv m n).symm.toMonoidHom.comp
    (QuotientGroup.mk' ((F.lower n).subgroupOf (F.lower m)))

/-- States the theorem `subquotientMk_apply`. -/
@[simp]
theorem subquotientMk_apply (m n : ℕ) (σ : F.lower m) :
    F.subquotientConcreteMulEquiv m n (F.subquotientMk m n σ) =
      QuotientGroup.mk' ((F.lower n).subgroupOf (F.lower m)) σ :=
  rfl

/-- States the theorem `subquotientMk_eq_one_iff`. -/
@[simp]
theorem subquotientMk_eq_one_iff (m n : ℕ) (σ : F.lower m) :
    F.subquotientMk m n σ = 1 ↔ (σ : G) ∈ F.lower n := by
  constructor
  · intro h
    have h' := congrArg (F.subquotientConcreteMulEquiv m n) h
    rw [F.subquotientMk_apply, map_one] at h'
    simpa [Subgroup.mem_subgroupOf] using
      ((QuotientGroup.eq_one_iff
        (N := (F.lower n).subgroupOf (F.lower m)) σ).1 h')
  · intro h
    apply (F.subquotientConcreteMulEquiv m n).injective
    rw [F.subquotientMk_apply, map_one]
    apply (QuotientGroup.eq_one_iff
      (N := (F.lower n).subgroupOf (F.lower m)) σ).2
    simpa [Subgroup.mem_subgroupOf] using h

































section
variable {H : Type v} [Group H] (m n : ℕ)
    (f : F.lower m →* H)
    (h : (F.lower n).subgroupOf (F.lower m) ≤ f.ker)
include H m n f h
/-- Descend a homomorphism from `G_m` that kills the copy of `G_n`. -/
def subquotientLift    :=
  (QuotientGroup.lift
    ((F.lower n).subgroupOf (F.lower m)) f h).comp
      (F.subquotientConcreteMulEquiv m n).toMonoidHom

/-- States the theorem `subquotientLift_mk`. -/
@[simp]
theorem subquotientLift_mk  
    (σ : F.lower m) :
    F.subquotientLift m n f h (F.subquotientMk m n σ) = f σ :=
  rfl
end


section
variable {H : Type v} [Group H]
    (E : AntitoneNormalSubgroupFiltration H)
    (m n p q : ℕ) (f : F.lower m →* E.lower p)
    (h : ∀ σ : F.lower m, (σ : G) ∈ F.lower n →
      ((f σ : E.lower p) : H) ∈ E.lower q)
include H E m n p q f h
/-- Map between named subquotients induced by a homomorphism of their upper
groups which sends the lower relation into the target lower group. -/
def subquotientMap   :
    F.subquotient m n →* E.subquotient p q :=
  F.subquotientLift m n ((E.subquotientMk p q).comp f) (by
    intro σ hσ
    rw [MonoidHom.mem_ker]
    exact (E.subquotientMk_eq_one_iff p q (f σ)).2 (h σ hσ))

/-- States the theorem `subquotientMap_apply_mk`. -/
@[simp]
theorem subquotientMap_apply_mk  
    (σ : F.lower m) :
    F.subquotientMap E m n p q f h (F.subquotientMk m n σ) =
      E.subquotientMk p q (f σ) :=
  rfl
end


/-- Canonical projection to `G_n/G_{n+1}`. -/
def gradedPieceMk (n : ℕ)  :=
  (F.gradedPieceConcreteMulEquiv n).symm.toMonoidHom.comp
    (QuotientGroup.mk'
      ((F.lower (n + 1)).subgroupOf (F.lower n)))

/-- States the theorem `gradedPieceMk_apply`. -/
@[simp]
theorem gradedPieceMk_apply (n : ℕ) (σ : F.lower n) :
    F.gradedPieceConcreteMulEquiv n (F.gradedPieceMk n σ) =
      QuotientGroup.mk'
        ((F.lower (n + 1)).subgroupOf (F.lower n)) σ :=
  rfl

/-- States the theorem `gradedPieceMk_eq_one_iff`. -/
@[simp]
theorem gradedPieceMk_eq_one_iff (n : ℕ) (σ : F.lower n) :
    F.gradedPieceMk n σ = 1 ↔ (σ : G) ∈ F.lower (n + 1) := by
  constructor
  · intro h
    have h' := congrArg (F.gradedPieceConcreteMulEquiv n) h
    rw [F.gradedPieceMk_apply, map_one] at h'
    simpa [Subgroup.mem_subgroupOf] using
      ((QuotientGroup.eq_one_iff
        (N := (F.lower (n + 1)).subgroupOf (F.lower n)) σ).1 h')
  · intro h
    apply (F.gradedPieceConcreteMulEquiv n).injective
    rw [F.gradedPieceMk_apply, map_one]
    apply (QuotientGroup.eq_one_iff
      (N := (F.lower (n + 1)).subgroupOf (F.lower n)) σ).2
    simpa [Subgroup.mem_subgroupOf] using h

































section
variable {H : Type v} [Group H] (n : ℕ)
    (f : F.lower n →* H)
    (h : (F.lower (n + 1)).subgroupOf (F.lower n) ≤ f.ker)
include H n f h
/-- Descend a homomorphism from `G_n` that kills `G_{n+1}`. -/
def gradedPieceLift    :=
  (QuotientGroup.lift
    ((F.lower (n + 1)).subgroupOf (F.lower n)) f h).comp
      (F.gradedPieceConcreteMulEquiv n).toMonoidHom

/-- States the theorem `gradedPieceLift_mk`. -/
@[simp]
theorem gradedPieceLift_mk  
    (σ : F.lower n) :
    F.gradedPieceLift n f h (F.gradedPieceMk n σ) = f σ :=
  rfl
end


section
variable {H : Type v} [Group H]
    (E : AntitoneNormalSubgroupFiltration H) (n m : ℕ)
    (f : F.lower n →* E.lower m)
    (h : ∀ σ : F.lower n, (σ : G) ∈ F.lower (n + 1) →
      ((f σ : E.lower m) : H) ∈ E.lower (m + 1))
include H E n m f h
/-- Map between named graded pieces. -/
def gradedPieceMap   :
    F.gradedPiece n →* E.gradedPiece m :=
  F.gradedPieceLift n ((E.gradedPieceMk m).comp f) (by
    intro σ hσ
    rw [MonoidHom.mem_ker]
    exact (E.gradedPieceMk_eq_one_iff m (f σ)).2 (h σ hσ))

/-- States the theorem `gradedPieceMap_apply_mk`. -/
@[simp]
theorem gradedPieceMap_apply_mk  
    (σ : F.lower n) :
    F.gradedPieceMap E n m f h (F.gradedPieceMk n σ) =
      E.gradedPieceMk m (f σ) :=
  rfl
end


/-- Canonical projection to `G_0/G_1`. -/
def tameQuotientMk  :=
  F.tameQuotientConcreteMulEquiv.symm.toMonoidHom.comp
    (QuotientGroup.mk'
      ((F.wildInertiaSubgroup).subgroupOf F.inertiaSubgroup))

/-- States the theorem `tameQuotientMk_apply`. -/
@[simp]
theorem tameQuotientMk_apply (σ : F.inertiaSubgroup) :
    F.tameQuotientConcreteMulEquiv (F.tameQuotientMk σ) =
      QuotientGroup.mk'
        ((F.wildInertiaSubgroup).subgroupOf F.inertiaSubgroup) σ :=
  rfl

/-- States the theorem `tameQuotientMk_eq_one_iff`. -/
@[simp]
theorem tameQuotientMk_eq_one_iff (σ : F.inertiaSubgroup) :
    F.tameQuotientMk σ = 1 ↔ (σ : G) ∈ F.wildInertiaSubgroup := by
  constructor
  · intro h
    have h' := congrArg F.tameQuotientConcreteMulEquiv h
    rw [F.tameQuotientMk_apply, map_one] at h'
    simpa [Subgroup.mem_subgroupOf] using
      ((QuotientGroup.eq_one_iff
        (N := (F.wildInertiaSubgroup).subgroupOf F.inertiaSubgroup) σ).1 h')
  · intro h
    apply F.tameQuotientConcreteMulEquiv.injective
    rw [F.tameQuotientMk_apply, map_one]
    apply (QuotientGroup.eq_one_iff
      (N := (F.wildInertiaSubgroup).subgroupOf F.inertiaSubgroup) σ).2
    simpa [Subgroup.mem_subgroupOf] using h

































section
variable {H : Type v} [Group H]
    (f : F.inertiaSubgroup →* H)
    (h : (F.wildInertiaSubgroup).subgroupOf F.inertiaSubgroup ≤ f.ker)
include H f h
/-- Descend an inertia homomorphism which kills wild inertia. -/
def tameQuotientLift    :=
  (QuotientGroup.lift
    ((F.wildInertiaSubgroup).subgroupOf F.inertiaSubgroup) f h).comp
      F.tameQuotientConcreteMulEquiv.toMonoidHom

/-- States the theorem `tameQuotientLift_mk`. -/
@[simp]
theorem tameQuotientLift_mk  
    (σ : F.inertiaSubgroup) :
    F.tameQuotientLift f h (F.tameQuotientMk σ) = f σ :=
  rfl
end


section
variable {H : Type v} [Group H]
    (E : AntitoneNormalSubgroupFiltration H)
    (f : F.inertiaSubgroup →* E.inertiaSubgroup)
    (h : ∀ σ : F.inertiaSubgroup, (σ : G) ∈ F.wildInertiaSubgroup →
      ((f σ : E.inertiaSubgroup) : H) ∈ E.wildInertiaSubgroup)
include H E f h
/-- Map between named tame quotients. -/
def tameQuotientMap   :
    F.tameQuotient →* E.tameQuotient :=
  F.tameQuotientLift (E.tameQuotientMk.comp f) (by
    intro σ hσ
    rw [MonoidHom.mem_ker]
    exact (E.tameQuotientMk_eq_one_iff (f σ)).2 (h σ hσ))

/-- States the theorem `tameQuotientMap_apply_mk`. -/
@[simp]
theorem tameQuotientMap_apply_mk  
    (σ : F.inertiaSubgroup) :
    F.tameQuotientMap E f h (F.tameQuotientMk σ) =
      E.tameQuotientMk (f σ) :=
  rfl
end

































end AntitoneNormalSubgroupFiltration

end DiscreteValuationField
end RamificationTheory

end
