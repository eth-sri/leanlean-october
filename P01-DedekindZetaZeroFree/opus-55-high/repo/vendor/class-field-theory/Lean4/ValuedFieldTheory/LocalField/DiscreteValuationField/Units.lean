module

public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.GroupTheory.Index
public import Mathlib.GroupTheory.QuotientGroup.Basic

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/


namespace LocalFieldTheory

/-!
# Principal-unit filtrations

This file provides a theorem API for antitone principal-unit filtrations used by
ramification and norm arguments.
-/

universe u v

open scoped BigOperators

namespace DiscreteValuationField

/-- A generic antitone filtration by subgroups of a group.  No valued-field
semantics are asserted by this interface alone. -/
structure AntitoneSubgroupFiltration (G : Type u) [Group G] where
  /-- The subgroup at each natural-number filtration level. -/
  subgroup : ℕ → Subgroup G
  /-- Higher filtration levels are contained in lower ones. -/
  antitone : ∀ {m n : ℕ}, m ≤ n → subgroup n ≤ subgroup m

namespace AntitoneSubgroupFiltration

variable {G : Type u} [Group G] (U : AntitoneSubgroupFiltration G)

/-- The `n`-th principal-unit subgroup. -/
def principalUnitSubgroup (n : ℕ) : Subgroup G :=
  U.subgroup n

/-- Characterizes `x ∈ U.principalUnitSubgroup n` by the equivalent condition `x ∈ U.subgroup n`. -/
@[simp] theorem mem_principalUnitSubgroup_iff (n : ℕ) (x : G) :
    x ∈ U.principalUnitSubgroup n ↔ x ∈ U.subgroup n :=
  Iff.rfl

/-- Higher filtration levels are contained in lower levels. -/
theorem principalUnitSubgroup_antitone {m n : ℕ} (h : m ≤ n) :
    U.principalUnitSubgroup n ≤ U.principalUnitSubgroup m :=
  U.antitone h

/-- Establishes the membership statement `x ∈ U.principalUnitSubgroup m`. -/
theorem mem_of_mem_of_le {m n : ℕ} (h : m ≤ n) {x : G}
    (hx : x ∈ U.principalUnitSubgroup n) :
    x ∈ U.principalUnitSubgroup m :=
  U.principalUnitSubgroup_antitone h hx

/-- The natural map from a finer filtration quotient to a coarser filtration
quotient.  If `m ≤ n`, then `U^n ≤ U^m`, so quotienting by `U^n` maps to
quotienting by `U^m`. -/
def quotient_principalUnitSubgroup_mapOfLe {m n : ℕ} (hmn : m ≤ n)
    [(U.principalUnitSubgroup n).Normal]
    [(U.principalUnitSubgroup m).Normal] :
    G ⧸ U.principalUnitSubgroup n →*
      G ⧸ U.principalUnitSubgroup m :=
  QuotientGroup.map (U.principalUnitSubgroup n) (U.principalUnitSubgroup m)
    (MonoidHom.id G) (by
      intro x hx
      exact U.mem_of_mem_of_le hmn hx)

/--
The defining evaluation formula for `quotient_principalUnitSubgroup_mapOfLe` is
`U.quotient_principalUnitSubgroup_mapOfLe hmn (QuotientGroup.mk x) = QuotientGroup.mk x`.
-/
@[simp] theorem quotient_principalUnitSubgroup_mapOfLe_apply_mk
    {m n : ℕ} (hmn : m ≤ n)
    [(U.principalUnitSubgroup n).Normal]
    [(U.principalUnitSubgroup m).Normal] (x : G) :
    U.quotient_principalUnitSubgroup_mapOfLe hmn (QuotientGroup.mk x) =
      QuotientGroup.mk x :=
  rfl

/--
Establishes the identity `U.quotient_principalUnitSubgroup_mapOfLe hmn (QuotientGroup.mk'
(U.principalUnitSubgroup n) x) = QuotientGroup.mk' (U.principalUnitSubgroup m) x`.
-/
@[simp] theorem quotient_principalUnitSubgroup_mapOfLe_apply_mk'
    {m n : ℕ} (hmn : m ≤ n)
    [(U.principalUnitSubgroup n).Normal]
    [(U.principalUnitSubgroup m).Normal] (x : G) :
    U.quotient_principalUnitSubgroup_mapOfLe hmn
        (QuotientGroup.mk' (U.principalUnitSubgroup n) x) =
      QuotientGroup.mk' (U.principalUnitSubgroup m) x :=
  rfl

/-- The class of `U^m` inside `G ⧸ U^n`.  For `m ≤ n`, this is the kernel of
the natural map `G ⧸ U^n →* G ⧸ U^m`. -/
def principalUnitSubgroupClassInQuotient (m n : ℕ)
    [(U.principalUnitSubgroup n).Normal] :
    Subgroup (G ⧸ U.principalUnitSubgroup n) :=
  Subgroup.map (QuotientGroup.mk' (U.principalUnitSubgroup n))
    (U.principalUnitSubgroup m)

/-- The subgroup appearing in `(U.principalUnitSubgroupClassInQuotient m n).Normal` is normal. -/
instance principalUnitSubgroupClassInQuotient_normal
    (m n : ℕ) [(U.principalUnitSubgroup n).Normal]
    [(U.principalUnitSubgroup m).Normal] :
    (U.principalUnitSubgroupClassInQuotient m n).Normal := by
  dsimp [principalUnitSubgroupClassInQuotient]
  infer_instance

/--
Characterizes `q ∈ U.principalUnitSubgroupClassInQuotient m n` by the equivalent condition `∃ x :
G, x ∈ U.principalUnitSubgroup m ∧ QuotientGroup.mk' (U.principalUnitSubgroup n) x = q`.
-/
theorem mem_principalUnitSubgroupClassInQuotient_iff
    (m n : ℕ) [(U.principalUnitSubgroup n).Normal]
    (q : G ⧸ U.principalUnitSubgroup n) :
    q ∈ U.principalUnitSubgroupClassInQuotient m n ↔
      ∃ x : G, x ∈ U.principalUnitSubgroup m ∧
        QuotientGroup.mk' (U.principalUnitSubgroup n) x = q :=
  Iff.rfl

/--
Establishes the membership statement `QuotientGroup.mk' (U.principalUnitSubgroup n) x ∈
U.principalUnitSubgroupClassInQuotient m n`.
-/
theorem principalUnitSubgroupClassInQuotient_mk_mem
    {m n : ℕ} [(U.principalUnitSubgroup n).Normal] {x : G}
    (hx : x ∈ U.principalUnitSubgroup m) :
    QuotientGroup.mk' (U.principalUnitSubgroup n) x ∈
      U.principalUnitSubgroupClassInQuotient m n :=
  Subgroup.mem_map_of_mem
    (QuotientGroup.mk' (U.principalUnitSubgroup n)) hx

/-- The subquotient `U^m/U^n` of a principal-unit filtration.  Under
`m ≤ n`, antitonicity makes this the usual quotient of `U^m` by `U^n`. -/
def principalUnitSubquotient (m n : ℕ) : Type u :=
  U.principalUnitSubgroup m ⧸
    (U.principalUnitSubgroup n).subgroupOf (U.principalUnitSubgroup m)

/--
Equips the target with its canonical `Group` structure, namely `Group (U.principalUnitSubquotient
m n)`.
-/
instance principalUnitSubquotientGroup
    (m n : ℕ) [(U.principalUnitSubgroup n).Normal] :
    Group (U.principalUnitSubquotient m n) := by
  change Group
    (U.principalUnitSubgroup m ⧸
      (U.principalUnitSubgroup n).subgroupOf
        (U.principalUnitSubgroup m))
  infer_instance

/-- Explicit access to the concrete quotient representation. -/
def principalUnitSubquotientConcreteEquiv
    (m n : ℕ) [(U.principalUnitSubgroup n).Normal] :
    U.principalUnitSubquotient m n ≃*
      (U.principalUnitSubgroup m ⧸
        (U.principalUnitSubgroup n).subgroupOf
          (U.principalUnitSubgroup m)) := by
  change
    (U.principalUnitSubgroup m ⧸
        (U.principalUnitSubgroup n).subgroupOf
          (U.principalUnitSubgroup m)) ≃*
      (U.principalUnitSubgroup m ⧸
        (U.principalUnitSubgroup n).subgroupOf
          (U.principalUnitSubgroup m))
  exact MulEquiv.refl _

/-- A subquotient of a commutative principal-unit filtration retains the
commutative group structure of its concrete quotient representation. -/
instance principalUnitSubquotientCommGroup
    {H : Type u} [CommGroup H] (V : AntitoneSubgroupFiltration H)
    (m n : ℕ) [(V.principalUnitSubgroup n).Normal] :
    CommGroup (V.principalUnitSubquotient m n) :=
  { (inferInstance : Group (V.principalUnitSubquotient m n)) with
    mul_comm := fun x y => by
      apply (V.principalUnitSubquotientConcreteEquiv m n).injective
      simp only [map_mul]
      exact mul_comm _ _ }

/-- The canonical class map `U^m → U^m/U^n`. -/
def principalUnitSubquotientMk
    (m n : ℕ) [(U.principalUnitSubgroup n).Normal] :
    U.principalUnitSubgroup m →* U.principalUnitSubquotient m n := by
  change U.principalUnitSubgroup m →*
    (U.principalUnitSubgroup m ⧸
      (U.principalUnitSubgroup n).subgroupOf
        (U.principalUnitSubgroup m))
  exact QuotientGroup.mk'
    ((U.principalUnitSubgroup n).subgroupOf
      (U.principalUnitSubgroup m))

/--
Establishes the identity `U.principalUnitSubquotientConcreteEquiv m n
(U.principalUnitSubquotientMk m n x) = QuotientGroup.mk x`.
-/
@[simp]
theorem principalUnitSubquotientConcreteEquiv_mk
    (m n : ℕ) [(U.principalUnitSubgroup n).Normal]
    (x : U.principalUnitSubgroup m) :
    U.principalUnitSubquotientConcreteEquiv m n
        (U.principalUnitSubquotientMk m n x) =
      QuotientGroup.mk x :=
  rfl

/-- Eliminate a principal-unit subquotient through its canonical map. -/
protected theorem principalUnitSubquotient.inductionOn
    (m n : ℕ) [(U.principalUnitSubgroup n).Normal]
    {motive : U.principalUnitSubquotient m n → Prop}
    (q : U.principalUnitSubquotient m n)
    (h : ∀ x : U.principalUnitSubgroup m,
      motive (U.principalUnitSubquotientMk m n x)) :
    motive q := by
  change motive
    (show U.principalUnitSubgroup m ⧸
      (U.principalUnitSubgroup n).subgroupOf
        (U.principalUnitSubgroup m) from q)
  refine QuotientGroup.induction_on q ?_
  intro x
  exact h x

/-- Descend a homomorphism that kills `U^n` inside `U^m`. -/
def principalUnitSubquotientLift
    {H : Type*} [Group H] (m n : ℕ)
    [(U.principalUnitSubgroup n).Normal]
    (f : U.principalUnitSubgroup m →* H)
    (h : (U.principalUnitSubgroup n).subgroupOf
      (U.principalUnitSubgroup m) ≤ f.ker) :
    U.principalUnitSubquotient m n →* H := by
  change
    (U.principalUnitSubgroup m ⧸
      (U.principalUnitSubgroup n).subgroupOf
        (U.principalUnitSubgroup m)) →* H
  exact QuotientGroup.lift
    ((U.principalUnitSubgroup n).subgroupOf
      (U.principalUnitSubgroup m)) f h

/--
Establishes the identity `U.principalUnitSubquotientLift m n f h (U.principalUnitSubquotientMk m n
x) = f x`.
-/
@[simp]
theorem principalUnitSubquotientLift_mk
    {H : Type*} [Group H] (m n : ℕ)
    [(U.principalUnitSubgroup n).Normal]
    (f : U.principalUnitSubgroup m →* H)
    (h : (U.principalUnitSubgroup n).subgroupOf
      (U.principalUnitSubgroup m) ≤ f.ker)
    (x : U.principalUnitSubgroup m) :
    U.principalUnitSubquotientLift m n f h
        (U.principalUnitSubquotientMk m n x) = f x :=
  rfl

/-- The principal-unit graded piece `U^n/U^{n+1}`. -/
def principalUnitGradedPiece (n : ℕ) : Type u :=
  U.principalUnitSubquotient n (n + 1)

/--
Equips the target with its canonical `Group` structure, namely `Group (U.principalUnitGradedPiece
n)`.
-/
instance principalUnitGradedPieceGroup
    (n : ℕ) [(U.principalUnitSubgroup (n + 1)).Normal] :
    Group (U.principalUnitGradedPiece n) := by
  change Group (U.principalUnitSubquotient n (n + 1))
  infer_instance

/-- Explicit identification of a graded piece with its named adjacent
subquotient. -/
def principalUnitGradedPieceEquivSubquotient
    (n : ℕ) [(U.principalUnitSubgroup (n + 1)).Normal] :
    U.principalUnitGradedPiece n ≃*
      U.principalUnitSubquotient n (n + 1) := by
  change U.principalUnitSubquotient n (n + 1) ≃*
    U.principalUnitSubquotient n (n + 1)
  exact MulEquiv.refl _

/-- The type in `Finite (U.principalUnitGradedPiece n)` is finite. -/
noncomputable instance principalUnitGradedPieceFinite
    (n : ℕ) [(U.principalUnitSubgroup (n + 1)).Normal]
    [Finite (U.principalUnitSubquotient n (n + 1))] :
    Finite (U.principalUnitGradedPiece n) :=
  Finite.of_equiv (U.principalUnitSubquotient n (n + 1))
    (U.principalUnitGradedPieceEquivSubquotient n).symm.toEquiv

/-- Cardinality bridge between the adjacent named subquotient and the graded
piece wrapper. -/
theorem card_principalUnitSubquotient_succ_eq_gradedPiece
    (n : ℕ) [(U.principalUnitSubgroup (n + 1)).Normal]
    [Finite (U.principalUnitSubquotient n (n + 1))] :
    Nat.card (U.principalUnitSubquotient n (n + 1)) =
      Nat.card (U.principalUnitGradedPiece n) :=
  by rfl

/-- Representative criterion for the identity in `U^m/U^n`. -/
theorem principalUnitSubquotient_mk_eq_one_iff
    {m n : ℕ} [(U.principalUnitSubgroup n).Normal]
    (x : U.principalUnitSubgroup m) :
    U.principalUnitSubquotientMk m n x = 1 ↔
      (x : G) ∈ U.principalUnitSubgroup n := by
  change (QuotientGroup.mk x :
      U.principalUnitSubgroup m ⧸
        (U.principalUnitSubgroup n).subgroupOf
          (U.principalUnitSubgroup m)) =
    1 ↔ x ∈ (U.principalUnitSubgroup n).subgroupOf
      (U.principalUnitSubgroup m)
  simp

/-- Representative equality criterion in `U^m/U^n`, in right-quotient form. -/
theorem principalUnitSubquotient_mk_eq_iff_div_mem
    {m n : ℕ} [(U.principalUnitSubgroup n).Normal]
    (x y : U.principalUnitSubgroup m) :
    U.principalUnitSubquotientMk m n x =
      U.principalUnitSubquotientMk m n y ↔
      ((x / y : U.principalUnitSubgroup m) : G) ∈
        U.principalUnitSubgroup n := by
  change (QuotientGroup.mk x :
      U.principalUnitSubgroup m ⧸
        (U.principalUnitSubgroup n).subgroupOf
          (U.principalUnitSubgroup m)) =
    QuotientGroup.mk y ↔ _
  simpa [Subgroup.mem_subgroupOf] using
    (QuotientGroup.eq_iff_div_mem
      (N := (U.principalUnitSubgroup n).subgroupOf
        (U.principalUnitSubgroup m)) (x := x) (y := y))

/-- The map from `U^m` into `G/U^n`. -/
def principalUnitSubgroupToQuotient {m n : ℕ} (_hmn : m ≤ n)
    [(U.principalUnitSubgroup n).Normal] :
    U.principalUnitSubgroup m →* G ⧸ U.principalUnitSubgroup n :=
  (QuotientGroup.mk' (U.principalUnitSubgroup n)).comp
    (U.principalUnitSubgroup m).subtype

/--
The defining evaluation formula for `principalUnitSubgroupToQuotient` is
`U.principalUnitSubgroupToQuotient hmn x = QuotientGroup.mk' (U.principalUnitSubgroup n) (x : G)`.
-/
@[simp] theorem principalUnitSubgroupToQuotient_apply
    {m n : ℕ} (hmn : m ≤ n) [(U.principalUnitSubgroup n).Normal]
    (x : U.principalUnitSubgroup m) :
    U.principalUnitSubgroupToQuotient hmn x =
      QuotientGroup.mk' (U.principalUnitSubgroup n) (x : G) :=
  rfl

/-- The kernel of `U^m → G/U^n` is `U^n` inside `U^m`. -/
theorem principalUnitSubgroupToQuotient_ker_eq
    {m n : ℕ} (hmn : m ≤ n) [(U.principalUnitSubgroup n).Normal] :
    (U.principalUnitSubgroupToQuotient hmn).ker =
      (U.principalUnitSubgroup n).subgroupOf
        (U.principalUnitSubgroup m) := by
  ext x
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
  simp

/-- The range of `U^m → G/U^n` is the class of `U^m` in `G/U^n`. -/
theorem principalUnitSubgroupToQuotient_range_eq_classInQuotient
    {m n : ℕ} (hmn : m ≤ n) [(U.principalUnitSubgroup n).Normal] :
    (U.principalUnitSubgroupToQuotient hmn).range =
      U.principalUnitSubgroupClassInQuotient m n := by
  ext q
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨(x : G), x.property, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨⟨x, hx⟩, rfl⟩

/-- The subquotient `U^m/U^n` as the class of `U^m` inside `G/U^n`. -/
noncomputable def principalUnitSubquotientEquivClassInQuotientOfLe
    {m n : ℕ} (hmn : m ≤ n) [(U.principalUnitSubgroup n).Normal] :
    U.principalUnitSubquotient m n ≃*
      U.principalUnitSubgroupClassInQuotient m n :=
  (U.principalUnitSubquotientConcreteEquiv m n).trans
    ((QuotientGroup.quotientMulEquivOfEq
        (U.principalUnitSubgroupToQuotient_ker_eq hmn).symm).trans
      ((QuotientGroup.quotientKerEquivRange
        (U.principalUnitSubgroupToQuotient hmn)).trans
          (MulEquiv.subgroupCongr
            (U.principalUnitSubgroupToQuotient_range_eq_classInQuotient hmn))))

/--
Establishes the identity `((U.principalUnitSubquotientEquivClassInQuotientOfLe hmn
(U.principalUnitSubquotientMk m n x) : U.principalUnitSubgroupClassInQuotient m n) : G ⧸
U.principalUnitSubgroup n) = QuotientGroup.mk' (U.principalUnitSubgroup n) (x : G)`.
-/
@[simp] theorem coe_principalUnitSubquotientEquivClassInQuotientOfLe_mk
    {m n : ℕ} (hmn : m ≤ n) [(U.principalUnitSubgroup n).Normal]
    (x : U.principalUnitSubgroup m) :
    ((U.principalUnitSubquotientEquivClassInQuotientOfLe hmn
        (U.principalUnitSubquotientMk m n x) :
      U.principalUnitSubgroupClassInQuotient m n) :
      G ⧸ U.principalUnitSubgroup n) =
      QuotientGroup.mk' (U.principalUnitSubgroup n) (x : G) := by
  rfl

/-- The kernel of `G ⧸ U^n →* G ⧸ U^m` is the image of `U^m` in
`G ⧸ U^n`. -/
theorem quotient_principalUnitSubgroup_mapOfLe_ker_eq_classInQuotient
    {m n : ℕ} (hmn : m ≤ n)
    [(U.principalUnitSubgroup n).Normal]
    [(U.principalUnitSubgroup m).Normal] :
    (U.quotient_principalUnitSubgroup_mapOfLe hmn).ker =
      U.principalUnitSubgroupClassInQuotient m n := 
  (QuotientGroup.ker_map (U.principalUnitSubgroup n)
    (U.principalUnitSubgroup m) (MonoidHom.id G) (by
      intro x hx
      exact U.mem_of_mem_of_le hmn hx)).trans
    (congrArg (Subgroup.map (QuotientGroup.mk' (U.principalUnitSubgroup n)))
      (Subgroup.comap_id (U.principalUnitSubgroup m)))

/-- Level-change maps send the class of `U^l` in `G/U^n` into the class of
`U^l` in `G/U^m`, for `l ≤ m ≤ n`. -/
theorem quotient_principalUnitSubgroup_mapOfLe_mem_classInQuotient
    {l m n : ℕ} (_hlm : l ≤ m) (hmn : m ≤ n)
    [(U.principalUnitSubgroup n).Normal]
    [(U.principalUnitSubgroup m).Normal]
    {q : G ⧸ U.principalUnitSubgroup n}
    (hq : q ∈ U.principalUnitSubgroupClassInQuotient l n) :
    U.quotient_principalUnitSubgroup_mapOfLe hmn q ∈
      U.principalUnitSubgroupClassInQuotient l m := by
  rcases (U.mem_principalUnitSubgroupClassInQuotient_iff l n q).1 hq with
    ⟨x, hx, hxq⟩
  rw [← hxq, U.quotient_principalUnitSubgroup_mapOfLe_apply_mk']
  exact U.principalUnitSubgroupClassInQuotient_mk_mem hx

/-- The level-change map restricted to principal-unit classes:
`U^l/U^n → U^l/U^m`, for `l ≤ m ≤ n`. -/
def principalUnitClassMapOfLe {l m n : ℕ} (hlm : l ≤ m) (hmn : m ≤ n)
    [(U.principalUnitSubgroup n).Normal]
    [(U.principalUnitSubgroup m).Normal] :
    U.principalUnitSubgroupClassInQuotient l n →*
      U.principalUnitSubgroupClassInQuotient l m :=
  ((U.quotient_principalUnitSubgroup_mapOfLe hmn).domRestrict
      (U.principalUnitSubgroupClassInQuotient l n)).codRestrict
    (U.principalUnitSubgroupClassInQuotient l m)
    (by
      intro q
      exact U.quotient_principalUnitSubgroup_mapOfLe_mem_classInQuotient
        hlm hmn q.property)

/--
The defining evaluation formula for `principalUnitClassMapOfLe` is `((U.principalUnitClassMapOfLe
hlm hmn q : U.principalUnitSubgroupClassInQuotient l m) : G ⧸ U.principalUnitSubgroup m) =
U.quotient_principalUnitSubgroup_mapOfLe hmn (q : G ⧸ U.principalUnitSubgroup n)`.
-/
@[simp] theorem principalUnitClassMapOfLe_apply {l m n : ℕ}
    (hlm : l ≤ m) (hmn : m ≤ n)
    [(U.principalUnitSubgroup n).Normal]
    [(U.principalUnitSubgroup m).Normal]
    (q : U.principalUnitSubgroupClassInQuotient l n) :
    ((U.principalUnitClassMapOfLe hlm hmn q :
      U.principalUnitSubgroupClassInQuotient l m) :
      G ⧸ U.principalUnitSubgroup m) =
      U.quotient_principalUnitSubgroup_mapOfLe hmn
        (q : G ⧸ U.principalUnitSubgroup n) :=
  rfl

/-- The restricted map `U^l/U^n → U^l/U^m` has kernel `U^m/U^n`. -/
theorem principalUnitClassMapOfLe_ker_eq {l m n : ℕ}
    (hlm : l ≤ m) (hmn : m ≤ n)
    [(U.principalUnitSubgroup n).Normal]
    [(U.principalUnitSubgroup m).Normal] :
    (U.principalUnitClassMapOfLe hlm hmn).ker =
      (U.principalUnitSubgroupClassInQuotient m n).subgroupOf
        (U.principalUnitSubgroupClassInQuotient l n) := by
  ext q
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
  constructor
  · intro hq
    have hq' := congrArg Subtype.val hq
    change
      U.quotient_principalUnitSubgroup_mapOfLe hmn
          (q : G ⧸ U.principalUnitSubgroup n) = 1 at hq'
    rw [← U.quotient_principalUnitSubgroup_mapOfLe_ker_eq_classInQuotient hmn,
      MonoidHom.mem_ker]
    exact hq'
  · intro hq
    apply Subtype.ext
    change
      U.quotient_principalUnitSubgroup_mapOfLe hmn
          (q : G ⧸ U.principalUnitSubgroup n) = 1
    rw [← MonoidHom.mem_ker,
      U.quotient_principalUnitSubgroup_mapOfLe_ker_eq_classInQuotient hmn]
    exact hq

/-- The restricted map `U^l/U^n → U^l/U^m` is surjective. -/
theorem principalUnitClassMapOfLe_surjective {l m n : ℕ}
    (hlm : l ≤ m) (hmn : m ≤ n)
    [(U.principalUnitSubgroup n).Normal]
    [(U.principalUnitSubgroup m).Normal] :
    Function.Surjective (U.principalUnitClassMapOfLe hlm hmn) := by
  intro q
  rcases q with ⟨q, hq⟩
  rcases (U.mem_principalUnitSubgroupClassInQuotient_iff l m q).1 hq with
    ⟨x, hx, hxq⟩
  refine ⟨⟨QuotientGroup.mk' (U.principalUnitSubgroup n) x,
    U.principalUnitSubgroupClassInQuotient_mk_mem hx⟩, ?_⟩
  apply Subtype.ext
  simp_all

/-- First isomorphism theorem inside principal-unit classes:
`(U^l/U^n)/ker(U^l/U^n → U^l/U^m) ≃ U^l/U^m`, for `l ≤ m ≤ n`.
The kernel is identified with `U^m/U^n` by
`principalUnitClassMapOfLe_ker_eq`. -/
noncomputable def principalUnitClassQuotientKerEquivClassOfLe {l m n : ℕ}
    (hlm : l ≤ m) (hmn : m ≤ n)
    [(U.principalUnitSubgroup n).Normal]
    [(U.principalUnitSubgroup m).Normal] :
    U.principalUnitSubgroupClassInQuotient l n ⧸
        (U.principalUnitClassMapOfLe hlm hmn).ker ≃*
      U.principalUnitSubgroupClassInQuotient l m :=
  QuotientGroup.quotientKerEquivOfSurjective
    (U.principalUnitClassMapOfLe hlm hmn)
    (U.principalUnitClassMapOfLe_surjective hlm hmn)

/-- The subgroup of `U^l/U^n` represented by `U^m/U^n` is canonically
the class of `U^m` in `G/U^n`. -/
noncomputable def principalUnitClassSubgroupOfEquivClassOfLe {l m n : ℕ}
    (hlm : l ≤ m) [(U.principalUnitSubgroup n).Normal] :
    (U.principalUnitSubgroupClassInQuotient m n).subgroupOf
        (U.principalUnitSubgroupClassInQuotient l n) ≃*
      U.principalUnitSubgroupClassInQuotient m n where
  toFun q :=
    ⟨((q : U.principalUnitSubgroupClassInQuotient l n) :
        G ⧸ U.principalUnitSubgroup n), 
      q.property⟩
  invFun q :=
    ⟨⟨(q : G ⧸ U.principalUnitSubgroup n), by
        rcases (U.mem_principalUnitSubgroupClassInQuotient_iff m n
            (q : G ⧸ U.principalUnitSubgroup n)).1 q.property with
          ⟨x, hx, hxq⟩
        exact ⟨x, U.mem_of_mem_of_le hlm hx, hxq⟩⟩, by
      change (q : G ⧸ U.principalUnitSubgroup n) ∈
        U.principalUnitSubgroupClassInQuotient m n
      exact q.property⟩
  left_inv q := by
    ext
    rfl
  right_inv q := by
    ext
    rfl
  map_mul' q r := by
    ext
    rfl

/-- Kernel form of `principalUnitClassMapOfLe_ker_eq`, with the kernel
identified as the class `U^m/U^n`. -/
noncomputable def principalUnitClassMapOfLeKerEquivClass {l m n : ℕ}
    (hlm : l ≤ m) (hmn : m ≤ n)
    [(U.principalUnitSubgroup n).Normal]
    [(U.principalUnitSubgroup m).Normal] :
    (U.principalUnitClassMapOfLe hlm hmn).ker ≃*
      U.principalUnitSubgroupClassInQuotient m n :=
  (MulEquiv.subgroupCongr
      (U.principalUnitClassMapOfLe_ker_eq hlm hmn)).trans
    (U.principalUnitClassSubgroupOfEquivClassOfLe hlm)

/-- Cardinality multiplication for three levels of a principal-unit
filtration: `#(U^l/U^n) = #(U^m/U^n) * #(U^l/U^m)`. -/
theorem card_principalUnitClassInQuotient_eq_mul_of_le {l m n : ℕ}
    (hlm : l ≤ m) (hmn : m ≤ n)
    [(U.principalUnitSubgroup n).Normal]
    [(U.principalUnitSubgroup m).Normal]
    [Finite (U.principalUnitSubgroupClassInQuotient l n)]
    [Finite (U.principalUnitSubgroupClassInQuotient m n)]
    [Finite (U.principalUnitSubgroupClassInQuotient l m)] :
    Nat.card (U.principalUnitSubgroupClassInQuotient l n) =
      Nat.card (U.principalUnitSubgroupClassInQuotient m n) *
        Nat.card (U.principalUnitSubgroupClassInQuotient l m) := by
  let φ := U.principalUnitClassMapOfLe hlm hmn
  calc
    Nat.card (U.principalUnitSubgroupClassInQuotient l n) =
        Nat.card φ.ker * φ.ker.index := 
          (Subgroup.card_mul_index φ.ker).symm
    _ =
        Nat.card (U.principalUnitSubgroupClassInQuotient m n) *
          Nat.card ((U.principalUnitSubgroupClassInQuotient l n) ⧸ φ.ker) := by
          rw [Subgroup.index_eq_card]
          rw [Nat.card_congr
            (U.principalUnitClassMapOfLeKerEquivClass hlm hmn).toEquiv]
    _ =
        Nat.card (U.principalUnitSubgroupClassInQuotient m n) *
          Nat.card (U.principalUnitSubgroupClassInQuotient l m) := by
          rw [Nat.card_congr
            (U.principalUnitClassQuotientKerEquivClassOfLe hlm hmn).toEquiv]

/-- Cardinality form of the class/subquotient identification. -/
theorem card_principalUnitSubquotient_eq_classInQuotient_of_le
    {m n : ℕ} (hmn : m ≤ n) [(U.principalUnitSubgroup n).Normal]
    [Finite (U.principalUnitSubquotient m n)]
    [Finite (U.principalUnitSubgroupClassInQuotient m n)] :
    Nat.card (U.principalUnitSubquotient m n) =
      Nat.card (U.principalUnitSubgroupClassInQuotient m n) := by
  rw [Nat.card_congr
    (U.principalUnitSubquotientEquivClassInQuotientOfLe hmn).toEquiv]

/-- The degenerate subquotient `U^n/U^n` has cardinality one. -/
theorem card_principalUnitSubquotient_self
    (n : ℕ) [(U.principalUnitSubgroup n).Normal]
    [Finite (U.principalUnitSubquotient n n)] :
    Nat.card (U.principalUnitSubquotient n n) = 1 := by
  have htop :
      (U.principalUnitSubgroup n).subgroupOf
          (U.principalUnitSubgroup n) = ⊤ := by
    simp
  change Nat.card
    (U.principalUnitSubgroup n ⧸
      (U.principalUnitSubgroup n).subgroupOf
        (U.principalUnitSubgroup n)) = 1
  simp

/-- Cardinality multiplication for principal-unit subquotients:
`#(U^l/U^n) = #(U^m/U^n) * #(U^l/U^m)`. -/
theorem card_principalUnitSubquotient_eq_mul_of_le {l m n : ℕ}
    (hlm : l ≤ m) (hmn : m ≤ n)
    [(U.principalUnitSubgroup n).Normal]
    [(U.principalUnitSubgroup m).Normal]
    [Finite (U.principalUnitSubquotient l n)]
    [Finite (U.principalUnitSubquotient m n)]
    [Finite (U.principalUnitSubquotient l m)] :
    Nat.card (U.principalUnitSubquotient l n) =
      Nat.card (U.principalUnitSubquotient m n) *
      Nat.card (U.principalUnitSubquotient l m) := by
  let : Finite (U.principalUnitSubgroupClassInQuotient l n) :=
    Finite.of_injective
      (U.principalUnitSubquotientEquivClassInQuotientOfLe
        (le_trans hlm hmn)).symm
      (U.principalUnitSubquotientEquivClassInQuotientOfLe
        (le_trans hlm hmn)).symm.injective
  let : Finite (U.principalUnitSubgroupClassInQuotient m n) :=
    Finite.of_injective
      (U.principalUnitSubquotientEquivClassInQuotientOfLe hmn).symm
      (U.principalUnitSubquotientEquivClassInQuotientOfLe hmn).symm.injective
  let : Finite (U.principalUnitSubgroupClassInQuotient l m) :=
    Finite.of_injective
      (U.principalUnitSubquotientEquivClassInQuotientOfLe hlm).symm
      (U.principalUnitSubquotientEquivClassInQuotientOfLe hlm).symm.injective
  rw [U.card_principalUnitSubquotient_eq_classInQuotient_of_le
      (le_trans hlm hmn)]
  rw [U.card_principalUnitSubquotient_eq_classInQuotient_of_le hmn]
  rw [U.card_principalUnitSubquotient_eq_classInQuotient_of_le hlm]
  exact U.card_principalUnitClassInQuotient_eq_mul_of_le hlm hmn

/-- Iterated cardinality form of the filtration counting argument:
`#(U^l/U^(l+r))` is the product of the adjacent graded-piece cardinalities. -/
theorem card_principalUnitSubquotient_eq_prod_gradedPiece
    (hN : ∀ i : ℕ, (U.principalUnitSubgroup i).Normal)
    [∀ i j : ℕ, Finite (U.principalUnitSubquotient i j)]
    (l r : ℕ) :
    Nat.card (U.principalUnitSubquotient l (l + r)) =
      ∏ i ∈ Finset.range r,
        Nat.card (U.principalUnitGradedPiece (l + i)) := by
  induction r with
  | zero =>
      let := hN l
      exact U.card_principalUnitSubquotient_self l
  | succ r ih =>
      let := hN (l + r)
      let := hN ((l + r) + 1)
      calc
        Nat.card (U.principalUnitSubquotient l (l + Nat.succ r)) =
            Nat.card (U.principalUnitSubquotient l ((l + r) + 1)) := by
              rw [Nat.add_succ]
        _ =
            Nat.card (U.principalUnitSubquotient (l + r) ((l + r) + 1)) *
              Nat.card (U.principalUnitSubquotient l (l + r)) := 
              U.card_principalUnitSubquotient_eq_mul_of_le
                (Nat.le_add_right l r) (Nat.le_succ (l + r))
        _ =
            Nat.card (U.principalUnitGradedPiece (l + r)) *
              (∏ i ∈ Finset.range r,
                Nat.card (U.principalUnitGradedPiece (l + i))) := by
              rw [ih,
                U.card_principalUnitSubquotient_succ_eq_gradedPiece]
        _ =
            ∏ i ∈ Finset.range (Nat.succ r),
              Nat.card (U.principalUnitGradedPiece (l + i)) := by
              rw [Finset.prod_range_succ]
              rw [Nat.mul_comm]

/-- The third-isomorphism equivalence for principal-unit filtration quotients:
`(G / U^n) / (U^m / U^n) ≃ G / U^m` when `m ≤ n`. -/
noncomputable def quotientModuloPrincipalUnitClassEquivQuotientOfLe
    {m n : ℕ} (hmn : m ≤ n)
    [(U.principalUnitSubgroup n).Normal]
    [(U.principalUnitSubgroup m).Normal] :
    (G ⧸ U.principalUnitSubgroup n) ⧸
        U.principalUnitSubgroupClassInQuotient m n ≃*
      G ⧸ U.principalUnitSubgroup m :=
  QuotientGroup.quotientQuotientEquivQuotient
    (U.principalUnitSubgroup n) (U.principalUnitSubgroup m)
    (U.principalUnitSubgroup_antitone hmn)
