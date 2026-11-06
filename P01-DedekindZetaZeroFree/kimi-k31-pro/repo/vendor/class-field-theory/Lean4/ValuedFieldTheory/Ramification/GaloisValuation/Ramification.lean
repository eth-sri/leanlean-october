module

public import Mathlib.SetTheory.Cardinal.Finite
public import ValuedFieldTheory.Ramification.GaloisValuation.RamificationQuotients
public import ValuedFieldTheory.LocalField.DiscreteValuationField.PrincipalUnits.Core
public import Mathlib.Data.Rat.Lemmas

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/






set_option autoImplicit false

namespace RamificationTheory

open LocalFieldTheory

/-!
# Ramification filtrations

This file provides the group-theoretic lower ramification APIs used by local CFT.
Concrete valued extensions supply the action quotient estimates; the subgroup
and normality/antitonicity consequences are proved here.
-/

noncomputable section

universe u v

namespace DiscreteValuationField

namespace AntitoneNormalSubgroupFiltration

variable {G : Type u} [Group G] (F : AntitoneNormalSubgroupFiltration G)

/-- The finite-level Herbrand step
`|G_i| / |G_0|`, written with `Nat.card` so it can be used before a global
fintype instance has been installed.  Positivity theorems below carry the
finite-level hypotheses needed to rule out the infinite-cardinality fallback
of `Nat.card`. -/
noncomputable def herbrandStep (i : Nat) : Rat :=
  (Nat.card (F.lower i) : Rat) / (Nat.card (F.lower 0) : Rat)

/-- The natural-index lower Herbrand function as the cumulative sum of the
finite-level steps through `0, ..., n - 1`. -/
noncomputable def herbrandFunctionNat (n : Nat) : Rat :=
  Finset.sum (Finset.range n) fun i => F.herbrandStep i

/-- States the theorem `herbrandFunctionNat_zero`. -/
@[simp] theorem herbrandFunctionNat_zero :
    F.herbrandFunctionNat 0 = 0 := by
  simp [herbrandFunctionNat]













/-- The natural quotient map `G/G_n → G/G_m` for `m ≤ n`. -/
def quotientMapOfLe {m n : ℕ} (hmn : m ≤ n) :
    F.quotient n →* F.quotient m :=
  F.quotientMap F n m (MonoidHom.id G) (by
    intro σ hσ
    simpa using F.antitone hmn hσ)

/-- States the theorem `quotientMapOfLe_apply_mk`. -/
@[simp] theorem quotientMapOfLe_apply_mk {m n : ℕ} (hmn : m ≤ n)
    (σ : G) :
    F.quotientMapOfLe hmn (F.quotientMk n σ) =
      F.quotientMk m σ :=
  rfl

/-- Level-change quotient maps compose transitively. -/
theorem quotientMapOfLe_comp {l m n : ℕ}
    (hlm : l ≤ m) (hmn : m ≤ n) :
    (F.quotientMapOfLe hlm).comp (F.quotientMapOfLe hmn) =
      F.quotientMapOfLe (le_trans hlm hmn) := by
  apply MonoidHom.ext
  intro q
  refine F.quotient_inductionOn n
    (motive := fun q =>
      ((F.quotientMapOfLe hlm).comp (F.quotientMapOfLe hmn)) q =
        F.quotientMapOfLe (le_trans hlm hmn) q) q ?_
  intro σ
  change F.quotientMapOfLe hlm
      (F.quotientMapOfLe hmn (F.quotientMk n σ)) =
    F.quotientMapOfLe (le_trans hlm hmn) (F.quotientMk n σ)
  rw [F.quotientMapOfLe_apply_mk, F.quotientMapOfLe_apply_mk,
    F.quotientMapOfLe_apply_mk]



/-- The subgroup of `G/G_n` represented by the coarser ramification group
`G_m`, for `m ≤ n`. -/
def quotientKernelOfLe {m n : ℕ} (_hmn : m ≤ n) :
    Subgroup (F.quotient n) :=
  (F.quotientMapOfLe _hmn).ker

/-- The map from the `m`th lower ramification group into `G/G_n`. -/
def levelSubgroupToQuotient {m n : ℕ} (_hmn : m ≤ n) :
    F.lower m →* F.quotient n :=
  (F.quotientMk n).comp (F.lower m).subtype

/-- States the theorem `levelSubgroupToQuotient_apply`. -/
@[simp] theorem levelSubgroupToQuotient_apply {m n : ℕ} (hmn : m ≤ n)
    (σ : F.lower m) :
    F.levelSubgroupToQuotient hmn σ =
      F.quotientMk n (σ : G) :=
  rfl

/-- The kernel of `G_m → G/G_n` is `G_n` inside `G_m`. -/
theorem levelSubgroupToQuotient_ker_eq {m n : ℕ} (hmn : m ≤ n) :
    (F.levelSubgroupToQuotient hmn).ker =
      (F.lower n).subgroupOf (F.lower m) := by
  ext σ
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
  exact F.quotientMk_eq_one_iff n (σ : G)

/-- The range of `G_m → G/G_n` is the kernel subgroup of
`G/G_n → G/G_m`. -/
theorem levelSubgroupToQuotient_range_eq_quotientKernelOfLe {m n : ℕ}
    (hmn : m ≤ n) :
    (F.levelSubgroupToQuotient hmn).range = F.quotientKernelOfLe hmn := by
  ext q
  constructor
  · rintro ⟨σ, rfl⟩
    rw [quotientKernelOfLe, MonoidHom.mem_ker,
      F.levelSubgroupToQuotient_apply, F.quotientMapOfLe_apply_mk,
      F.quotientMk_eq_one_iff]
    exact σ.property
  · intro hq
    revert hq
    refine F.quotient_inductionOn n
      (motive := fun q =>
        q ∈ F.quotientKernelOfLe hmn →
          q ∈ (F.levelSubgroupToQuotient hmn).range) q ?_
    intro σ hq
    rw [quotientKernelOfLe, MonoidHom.mem_ker,
      F.quotientMapOfLe_apply_mk, F.quotientMk_eq_one_iff] at hq
    exact ⟨⟨σ, hq⟩, rfl⟩

/-- The kernel of `G/G_n → G/G_m` is the image of `G_m` in `G/G_n`. -/
theorem quotientMapOfLe_ker_eq_quotientKernelOfLe {m n : ℕ}
    (hmn : m ≤ n) :
    (F.quotientMapOfLe hmn).ker = F.quotientKernelOfLe hmn :=
  rfl

/-- The named kernel subgroup `G_m/G_n` is normal in `G/G_n`. -/
instance quotientKernelOfLe_normal {m n : ℕ} (hmn : m ≤ n) :
    (F.quotientKernelOfLe hmn).Normal := by
  rw [← F.quotientMapOfLe_ker_eq_quotientKernelOfLe hmn]
  infer_instance









/-- Arbitrary class kernel criterion for `G/G_n → G/G_m`. -/
theorem quotientMapOfLe_eq_one_iff_exists_mem_repr {m n : ℕ}
    (hmn : m ≤ n) (q : F.quotient n) :
    F.quotientMapOfLe hmn q = 1 ↔
      ∃ σ : G, σ ∈ F.lower m ∧
        F.quotientMk n σ = q := by
  rw [← MonoidHom.mem_ker,
    F.quotientMapOfLe_ker_eq_quotientKernelOfLe hmn]
  rw [← F.levelSubgroupToQuotient_range_eq_quotientKernelOfLe hmn]
  constructor
  · rintro ⟨σ, rfl⟩
    exact ⟨(σ : G), σ.property, rfl⟩
  · rintro ⟨σ, hσ, rfl⟩
    exact ⟨⟨σ, hσ⟩, rfl⟩

/-- Kernel-membership criterion for an arbitrary class in `G/G_n → G/G_m`,
expanded by a representative from `G_m`. -/
theorem quotientMapOfLe_mem_ker_iff_exists_mem_repr {m n : ℕ}
    (hmn : m ≤ n) (q : F.quotient n) :
    q ∈ (F.quotientMapOfLe hmn).ker ↔
      ∃ σ : G, σ ∈ F.lower m ∧
        F.quotientMk n σ = q := by
  rw [MonoidHom.mem_ker]
  exact F.quotientMapOfLe_eq_one_iff_exists_mem_repr hmn q

/-- Membership in the named kernel subgroup of `G/G_n → G/G_m`, expanded by a
representative from `G_m`. -/
theorem mem_quotientKernelOfLe_iff_exists_mem_repr {m n : ℕ}
    (hmn : m ≤ n) (q : F.quotient n) :
    q ∈ F.quotientKernelOfLe hmn ↔
      ∃ σ : G, σ ∈ F.lower m ∧
        F.quotientMk n σ = q := by
  rw [← F.quotientMapOfLe_ker_eq_quotientKernelOfLe hmn]
  exact F.quotientMapOfLe_mem_ker_iff_exists_mem_repr hmn q

/-- Membership in the named kernel subgroup is the same as mapping to `1`
under the corresponding level-change map. -/
theorem mem_quotientKernelOfLe_iff_quotientMap_eq_one {m n : ℕ}
    (hmn : m ≤ n) (q : F.quotient n) :
    q ∈ F.quotientKernelOfLe hmn ↔
      F.quotientMapOfLe hmn q = 1 := by
  rw [← F.quotientMapOfLe_ker_eq_quotientKernelOfLe hmn,
    MonoidHom.mem_ker]



/-- Membership in the coarser kernel after applying a level-change map is
equivalent to membership in the corresponding direct kernel. -/
theorem quotientMapOfLe_mem_quotientKernelOfLe_iff {l m n : ℕ}
    (hlm : l ≤ m) (hmn : m ≤ n) (q : F.quotient n) :
    F.quotientMapOfLe hmn q ∈ F.quotientKernelOfLe hlm ↔
      q ∈ F.quotientKernelOfLe (le_trans hlm hmn) := by
  rw [F.mem_quotientKernelOfLe_iff_quotientMap_eq_one hlm,
    F.mem_quotientKernelOfLe_iff_quotientMap_eq_one (le_trans hlm hmn)]
  change ((F.quotientMapOfLe hlm).comp (F.quotientMapOfLe hmn)) q = 1 ↔
    F.quotientMapOfLe (le_trans hlm hmn) q = 1
  rw [F.quotientMapOfLe_comp hlm hmn]









/-- Level-change maps send the larger kernel subgroup `G_l/G_n` onto the
corresponding kernel subgroup `G_l/G_m`, for `l ≤ m ≤ n`. -/
theorem quotientMapOfLe_map_quotientKernelOfLe_eq {l m n : ℕ}
    (hlm : l ≤ m) (hmn : m ≤ n) :
    Subgroup.map (F.quotientMapOfLe hmn)
        (F.quotientKernelOfLe (le_trans hlm hmn)) =
      F.quotientKernelOfLe hlm := by
  ext q
  constructor
  · rintro ⟨x, hx, hxq⟩
    rcases
      (F.mem_quotientKernelOfLe_iff_exists_mem_repr
        (le_trans hlm hmn) x).1 hx with
      ⟨σ, hσ, hxσ⟩
    rw [← hxq, ← hxσ, F.quotientMapOfLe_apply_mk]
    exact (F.mem_quotientKernelOfLe_iff_exists_mem_repr hlm _).2
      ⟨σ, hσ, rfl⟩
  · intro hq
    rcases
      (F.mem_quotientKernelOfLe_iff_exists_mem_repr hlm q).1 hq with
      ⟨σ, hσ, hqσ⟩
    refine ⟨F.quotientMk n σ, ?_, ?_⟩
    · exact
        (F.mem_quotientKernelOfLe_iff_exists_mem_repr
          (le_trans hlm hmn) _).2 ⟨σ, hσ, rfl⟩
    · rw [F.quotientMapOfLe_apply_mk]
      exact hqσ



/-- The level-change map restricted to kernel subgroups:
`G_l/G_n → G_l/G_m`, for `l ≤ m ≤ n`. -/
def quotientKernelMapOfLe {l m n : ℕ} (hlm : l ≤ m) (hmn : m ≤ n) :
    F.quotientKernelOfLe (le_trans hlm hmn) →*
      F.quotientKernelOfLe hlm :=
  ((F.quotientMapOfLe hmn).domRestrict
      (F.quotientKernelOfLe (le_trans hlm hmn))).codRestrict
    (F.quotientKernelOfLe hlm)
    (by
      intro q
      exact
        (F.quotientMapOfLe_mem_quotientKernelOfLe_iff hlm hmn q).2 q.property)

/-- States the theorem `quotientKernelMapOfLe_apply`. -/
@[simp] theorem quotientKernelMapOfLe_apply {l m n : ℕ}
    (hlm : l ≤ m) (hmn : m ≤ n)
    (q : F.quotientKernelOfLe (le_trans hlm hmn)) :
    ((F.quotientKernelMapOfLe hlm hmn q :
      F.quotientKernelOfLe hlm) : F.quotient m) =
      F.quotientMapOfLe hmn (q : F.quotient n) :=
  rfl





/-- The restricted map `G_l/G_n → G_l/G_m` has kernel `G_m/G_n`. -/
theorem quotientKernelMapOfLe_ker_eq {l m n : ℕ}
    (hlm : l ≤ m) (hmn : m ≤ n) :
    (F.quotientKernelMapOfLe hlm hmn).ker =
      (F.quotientKernelOfLe hmn).subgroupOf
        (F.quotientKernelOfLe (le_trans hlm hmn)) := by
  ext q
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
  constructor
  · intro hq
    have hq' := congrArg Subtype.val hq
    change F.quotientMapOfLe hmn (q : F.quotient n) = 1 at hq'
    exact (F.mem_quotientKernelOfLe_iff_quotientMap_eq_one hmn
      (q : F.quotient n)).2 hq'
  · intro hq
    apply Subtype.ext
    change F.quotientMapOfLe hmn (q : F.quotient n) = 1
    exact (F.mem_quotientKernelOfLe_iff_quotientMap_eq_one hmn
      (q : F.quotient n)).1 hq

/-- The restricted map `G_l/G_n → G_l/G_m` is surjective. -/
theorem quotientKernelMapOfLe_surjective {l m n : ℕ}
    (hlm : l ≤ m) (hmn : m ≤ n) :
    Function.Surjective (F.quotientKernelMapOfLe hlm hmn) := by
  intro q
  rcases q with ⟨q, hq⟩
  have hq' :
      q ∈ Subgroup.map (F.quotientMapOfLe hmn)
        (F.quotientKernelOfLe (le_trans hlm hmn)) := by
    rw [F.quotientMapOfLe_map_quotientKernelOfLe_eq hlm hmn]
    exact hq
  rcases hq' with ⟨r, hr, hrq⟩
  refine ⟨⟨r, hr⟩, ?_⟩
  apply Subtype.ext
  exact hrq

/-- First isomorphism theorem inside ramification kernels:
`(G_l/G_n)/ker(G_l/G_n → G_l/G_m) ≃ G_l/G_m`, for `l ≤ m ≤ n`.
The kernel is identified with `G_m/G_n` by
`quotientKernelMapOfLe_ker_eq`. -/
def quotientKernelQuotientKerEquivQuotientKernelOfLe {l m n : ℕ}
    (hlm : l ≤ m) (hmn : m ≤ n) :
    F.quotientKernelOfLe (le_trans hlm hmn) ⧸
        (F.quotientKernelMapOfLe hlm hmn).ker ≃*
      F.quotientKernelOfLe hlm :=
  QuotientGroup.quotientKerEquivOfSurjective
    (F.quotientKernelMapOfLe hlm hmn)
    (F.quotientKernelMapOfLe_surjective hlm hmn)

/-- States the theorem `quotientKernelQuotientKerEquivQuotientKernelOfLe_mk'`. -/
@[simp] theorem quotientKernelQuotientKerEquivQuotientKernelOfLe_mk'
    {l m n : ℕ} (hlm : l ≤ m) (hmn : m ≤ n)
    (q : F.quotientKernelOfLe (le_trans hlm hmn)) :
    F.quotientKernelQuotientKerEquivQuotientKernelOfLe hlm hmn
        (QuotientGroup.mk'
          (F.quotientKernelMapOfLe hlm hmn).ker q) =
      F.quotientKernelMapOfLe hlm hmn q := by
  exact QuotientGroup.kerLift_mk (F.quotientKernelMapOfLe hlm hmn) q

/-- Second-isomorphism-style form of the ramification-kernel quotient:
`(G_l/G_n)/(G_m/G_n) ≃ G_l/G_m`, for `l ≤ m ≤ n`. -/
def quotientKernelQuotientSubgroupOfEquivQuotientKernelOfLe {l m n : ℕ}
    (hlm : l ≤ m) (hmn : m ≤ n) :
    F.quotientKernelOfLe (le_trans hlm hmn) ⧸
        (F.quotientKernelOfLe hmn).subgroupOf
          (F.quotientKernelOfLe (le_trans hlm hmn)) ≃*
      F.quotientKernelOfLe hlm :=
  (QuotientGroup.quotientMulEquivOfEq
    (F.quotientKernelMapOfLe_ker_eq hlm hmn).symm).trans
      (F.quotientKernelQuotientKerEquivQuotientKernelOfLe hlm hmn)

/-- States the theorem `quotientKernelQuotientSubgroupOfEquivQuotientKernelOfLe_mk'`. -/
@[simp] theorem quotientKernelQuotientSubgroupOfEquivQuotientKernelOfLe_mk'
    {l m n : ℕ} (hlm : l ≤ m) (hmn : m ≤ n)
    (q : F.quotientKernelOfLe (le_trans hlm hmn)) :
    F.quotientKernelQuotientSubgroupOfEquivQuotientKernelOfLe hlm hmn
        (QuotientGroup.mk'
          ((F.quotientKernelOfLe hmn).subgroupOf
            (F.quotientKernelOfLe (le_trans hlm hmn))) q) =
      F.quotientKernelMapOfLe hlm hmn q := by
  simpa [quotientKernelQuotientSubgroupOfEquivQuotientKernelOfLe] using
    F.quotientKernelQuotientKerEquivQuotientKernelOfLe_mk' hlm hmn q





/-- The ramification subquotient `G_m/G_n` is canonically the kernel of
`G/G_n → G/G_m`. -/
def subquotientEquivQuotientKernelOfLe {m n : ℕ} (hmn : m ≤ n) :
    F.subquotient m n ≃*
      F.quotientKernelOfLe hmn :=
  (F.subquotientConcreteMulEquiv m n).trans
    ((QuotientGroup.quotientMulEquivOfEq
        (F.levelSubgroupToQuotient_ker_eq hmn).symm).trans
      ((QuotientGroup.quotientKerEquivRange
        (F.levelSubgroupToQuotient hmn)).trans
          (MulEquiv.subgroupCongr
            (F.levelSubgroupToQuotient_range_eq_quotientKernelOfLe hmn))))

/-- States the theorem `coe_subquotientEquivQuotientKernelOfLe_mk`. -/
@[simp] theorem coe_subquotientEquivQuotientKernelOfLe_mk
    {m n : ℕ} (hmn : m ≤ n) (σ : F.lower m) :
    ((F.subquotientEquivQuotientKernelOfLe hmn
        (F.subquotientMk m n σ) :
      F.quotientKernelOfLe hmn) : F.quotient n) =
      F.quotientMk n (σ : G) := by
  simp [subquotientEquivQuotientKernelOfLe]
  rfl

/-- The graded piece `G_n/G_{n+1}` as the kernel of
`G/G_{n+1} → G/G_n`. -/
def gradedPieceEquivQuotientKernel (n : ℕ) :
    F.gradedPiece n ≃*
      F.quotientKernelOfLe (Nat.le_succ n) :=
  (F.gradedPieceEquivSubquotient n).trans
    (F.subquotientEquivQuotientKernelOfLe (Nat.le_succ n))

/-- States the theorem `coe_gradedPieceEquivQuotientKernel_mk`. -/
@[simp] theorem coe_gradedPieceEquivQuotientKernel_mk
    (n : ℕ) (σ : F.lower n) :
    ((F.gradedPieceEquivQuotientKernel n
        (F.gradedPieceMk n σ) :
      F.quotientKernelOfLe (Nat.le_succ n)) : F.quotient (n + 1)) =
      F.quotientMk (n + 1) (σ : G) := by
  exact F.coe_subquotientEquivQuotientKernelOfLe_mk (Nat.le_succ n) σ

/-- At every finite level `N ≥ n + 1`, the `n`th graded piece is the quotient
of finite-level kernels `(G_n/G_N)/(G_{n+1}/G_N)`. -/
def quotientKernelByNextKernelEquivGradedPiece {n N : ℕ} (hN : n + 1 ≤ N) :
    F.quotientKernelOfLe (le_trans (Nat.le_succ n) hN) ⧸
        (F.quotientKernelOfLe hN).subgroupOf
          (F.quotientKernelOfLe (le_trans (Nat.le_succ n) hN)) ≃*
      F.gradedPiece n :=
  (F.quotientKernelQuotientSubgroupOfEquivQuotientKernelOfLe
      (Nat.le_succ n) hN).trans (F.gradedPieceEquivQuotientKernel n).symm

/-- States the theorem `gradedPieceEquivQuotientKernel_quotientKernelByNextKernel_mk'`. -/
@[simp] theorem gradedPieceEquivQuotientKernel_quotientKernelByNextKernel_mk'
    {n N : ℕ} (hN : n + 1 ≤ N)
    (q : F.quotientKernelOfLe (le_trans (Nat.le_succ n) hN)) :
    F.gradedPieceEquivQuotientKernel n
        (F.quotientKernelByNextKernelEquivGradedPiece hN
          (QuotientGroup.mk'
            ((F.quotientKernelOfLe hN).subgroupOf
              (F.quotientKernelOfLe (le_trans (Nat.le_succ n) hN))) q)) =
      F.quotientKernelMapOfLe (Nat.le_succ n) hN q := by
  simpa [quotientKernelByNextKernelEquivGradedPiece] using
    F.quotientKernelQuotientSubgroupOfEquivQuotientKernelOfLe_mk'
      (Nat.le_succ n) hN q



/-- The natural level-change map `G/G_n → G/G_m` is surjective. -/
theorem quotientMapOfLe_surjective {m n : ℕ} (hmn : m ≤ n) :
    Function.Surjective (F.quotientMapOfLe hmn) := by
  intro q
  refine F.quotient_inductionOn m
    (motive := fun q => ∃ r, F.quotientMapOfLe hmn r = q) q ?_
  intro σ
  exact ⟨F.quotientMk n σ, F.quotientMapOfLe_apply_mk hmn σ⟩



/-- The tame quotient `G_0/G_1` as the kernel of `G/G_1 → G/G_0`. -/
def tameQuotientEquivQuotientKernel :
    F.tameQuotient ≃* F.quotientKernelOfLe (Nat.zero_le 1) :=
  F.tameQuotientEquivGradedPiece.trans
    (F.gradedPieceEquivQuotientKernel 0)

/-- States the theorem `coe_tameQuotientEquivQuotientKernel_mk`. -/
@[simp] theorem coe_tameQuotientEquivQuotientKernel_mk
    (σ : F.inertiaSubgroup) :
    ((F.tameQuotientEquivQuotientKernel
        (F.tameQuotientMk σ) :
      F.quotientKernelOfLe (Nat.zero_le 1)) : F.quotient 1) =
      F.quotientMk 1 (σ : G) := by
  exact F.coe_gradedPieceEquivQuotientKernel_mk 0 σ

/-- At every finite level `n ≥ 1`, the tame quotient is the quotient of
finite-level inertia by finite-level wild inertia:
`(G_0/G_n)/(G_1/G_n) ≃ G_0/G_1`. -/
def quotientInertiaByWildKernelEquivTameQuotient {n : ℕ} (hn : 1 ≤ n) :
    F.quotientKernelOfLe (le_trans (Nat.zero_le 1) hn) ⧸
        (F.quotientKernelOfLe hn).subgroupOf
          (F.quotientKernelOfLe (le_trans (Nat.zero_le 1) hn)) ≃*
      F.tameQuotient :=
  (F.quotientKernelQuotientSubgroupOfEquivQuotientKernelOfLe
      (Nat.zero_le 1) hn).trans F.tameQuotientEquivQuotientKernel.symm

/-- States the theorem `tameQuotientEquivQuotientKernel_quotientInertiaByWildKernel_mk'`. -/
@[simp] theorem tameQuotientEquivQuotientKernel_quotientInertiaByWildKernel_mk'
    {n : ℕ} (hn : 1 ≤ n)
    (q : F.quotientKernelOfLe (le_trans (Nat.zero_le 1) hn)) :
    F.tameQuotientEquivQuotientKernel
        (F.quotientInertiaByWildKernelEquivTameQuotient hn
          (QuotientGroup.mk'
            ((F.quotientKernelOfLe hn).subgroupOf
              (F.quotientKernelOfLe (le_trans (Nat.zero_le 1) hn))) q)) =
      F.quotientKernelMapOfLe (Nat.zero_le 1) hn q := by
  simpa [quotientInertiaByWildKernelEquivTameQuotient] using
    F.quotientKernelQuotientSubgroupOfEquivQuotientKernelOfLe_mk'
      (Nat.zero_le 1) hn q





/-- First isomorphism theorem for level-change maps:
`(G/G_n)/(G_m/G_n) ≃ G/G_m`. -/
def quotientQuotientKernelOfLeEquivQuotient {m n : ℕ} (hmn : m ≤ n) :
    F.quotient n ⧸ F.quotientKernelOfLe hmn ≃* F.quotient m :=
  (QuotientGroup.quotientMulEquivOfEq
      (F.quotientMapOfLe_ker_eq_quotientKernelOfLe hmn).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective
      (F.quotientMapOfLe hmn) (F.quotientMapOfLe_surjective hmn))

/-- States the theorem `quotientQuotientKernelOfLeEquivQuotient_mk'`. -/
@[simp] theorem quotientQuotientKernelOfLeEquivQuotient_mk'
    {m n : ℕ} (hmn : m ≤ n) (q : F.quotient n) :
    F.quotientQuotientKernelOfLeEquivQuotient hmn
        (QuotientGroup.mk' (F.quotientKernelOfLe hmn) q) =
      F.quotientMapOfLe hmn q := by
  exact QuotientGroup.kerLift_mk (F.quotientMapOfLe hmn) q

/-- States the theorem `quotientQuotientKernelOfLeEquivQuotient_mk'_mk'`. -/
@[simp] theorem quotientQuotientKernelOfLeEquivQuotient_mk'_mk'
    {m n : ℕ} (hmn : m ≤ n) (σ : G) :
    F.quotientQuotientKernelOfLeEquivQuotient hmn
        (QuotientGroup.mk' (F.quotientKernelOfLe hmn)
          (F.quotientMk n σ)) =
      F.quotientMk m σ := by
  rw [F.quotientQuotientKernelOfLeEquivQuotient_mk',
    F.quotientMapOfLe_apply_mk]



end AntitoneNormalSubgroupFiltration

/-- A depth function whose threshold subgroups form a lower ramification filtration. -/
structure LowerRamificationDepth (G : Type u) [Group G] where
  /-- The lower ramification depth of each group element. -/
  depth : G → WithTop ℕ
  /-- The identity has infinite ramification depth. -/
  depth_one : depth 1 = ⊤
  /-- Each depth threshold is closed under multiplication. -/
  depth_mul_mem :
    ∀ {n : ℕ} {σ τ : G},
      (n : WithTop ℕ) ≤ depth σ →
      (n : WithTop ℕ) ≤ depth τ →
      (n : WithTop ℕ) ≤ depth (σ * τ)
  /-- Each depth threshold is closed under inversion. -/
  depth_inv_mem :
    ∀ {n : ℕ} {σ : G},
      (n : WithTop ℕ) ≤ depth σ →
      (n : WithTop ℕ) ≤ depth σ⁻¹
  /-- Each depth threshold is preserved under conjugation. -/
  depth_conj_mem :
    ∀ {n : ℕ} {γ σ : G},
      (n : WithTop ℕ) ≤ depth σ →
      (n : WithTop ℕ) ≤ depth (γ * σ * γ⁻¹)

namespace LowerRamificationDepth

variable {G : Type u} [Group G] (D : LowerRamificationDepth G)

/-- The threshold subgroup cut out by a ramification depth function. -/
def lowerRamificationGroup (n : ℕ) : Subgroup G where
  carrier := {σ | (n : WithTop ℕ) ≤ D.depth σ}
  one_mem' := by
    change (n : WithTop ℕ) ≤ D.depth 1
    rw [D.depth_one]
    exact le_top
  mul_mem' := by
    intro σ τ hσ hτ
    exact D.depth_mul_mem hσ hτ
  inv_mem' := by
    intro σ hσ
    exact D.depth_inv_mem hσ

/-- States the theorem `mem_lowerRamificationGroup_iff`. -/
@[simp] theorem mem_lowerRamificationGroup_iff (n : ℕ) (σ : G) :
    σ ∈ D.lowerRamificationGroup n ↔ (n : WithTop ℕ) ≤ D.depth σ :=
  Iff.rfl

/-- States the theorem `lowerRamificationGroup_normal`. -/
theorem lowerRamificationGroup_normal (n : ℕ) :
    (D.lowerRamificationGroup n).Normal where
  conj_mem := by
    intro σ hσ γ
    exact D.depth_conj_mem (γ := γ) hσ

/-- Provides the instance `lowerRamificationGroup_normal_instance`. -/
instance lowerRamificationGroup_normal_instance (n : ℕ) :
    (D.lowerRamificationGroup n).Normal :=
  D.lowerRamificationGroup_normal n

/-- States the theorem `lowerRamificationGroup_antitone`. -/
theorem lowerRamificationGroup_antitone {m n : ℕ} (hmn : m ≤ n) :
    D.lowerRamificationGroup n ≤ D.lowerRamificationGroup m := by
  intro σ hσ
  change (m : WithTop ℕ) ≤ D.depth σ
  have hmn' : (m : WithTop ℕ) ≤ (n : WithTop ℕ) := by
    exact_mod_cast hmn
  exact le_trans hmn' hσ



/-- Package a depth function as a lower ramification filtration. -/
def toLowerRamificationFiltration : AntitoneNormalSubgroupFiltration G where
  lower := D.lowerRamificationGroup
  lower_normal := D.lowerRamificationGroup_normal
  antitone := by
    intro m n hmn
    exact D.lowerRamificationGroup_antitone hmn

/-- States the theorem `toLowerRamificationFiltration_apply`. -/
@[simp] theorem toLowerRamificationFiltration_apply (n : ℕ) :
    D.toLowerRamificationFiltration.lower n = D.lowerRamificationGroup n :=
  rfl

/-- Herbrand step attached to a depth-defined lower filtration. -/
noncomputable def herbrandStep (i : Nat) : Rat :=
  D.toLowerRamificationFiltration.herbrandStep i

/-- Natural-index Herbrand function attached to a depth-defined lower
filtration. -/
noncomputable def herbrandFunctionNat (n : Nat) : Rat :=
  D.toLowerRamificationFiltration.herbrandFunctionNat n





end LowerRamificationDepth

/-- A ramification filtration coming from an action quotient tested against
principal units. -/
structure ValuationActionRamification (G : Type u) [Group G]
    (K : Type v) [Group K] where
  /-- The principal-unit filtration used to test action quotients. -/
  principalUnits : LocalFieldTheory.DiscreteValuationField.AntitoneSubgroupFiltration K
  /-- The action of `G` on `K` by multiplicative automorphisms. -/
  action : G →* MulAut K
  /-- The element of `K` on which action quotients are evaluated. -/
  probe : K
  /-- Membership of action quotients at a fixed level is closed under multiplication. -/
  quotient_mul_mem :
    ∀ {n : ℕ} {σ τ : G},
      ((action σ) probe / probe) ∈ principalUnits.subgroup n →
      ((action τ) probe / probe) ∈ principalUnits.subgroup n →
      ((action (σ * τ)) probe / probe) ∈ principalUnits.subgroup n
  /-- Membership of action quotients at a fixed level is closed under inversion. -/
  quotient_inv_mem :
    ∀ {n : ℕ} {σ : G},
      ((action σ) probe / probe) ∈ principalUnits.subgroup n →
      ((action σ⁻¹) probe / probe) ∈ principalUnits.subgroup n
  /-- Membership of action quotients at a fixed level is preserved under conjugation. -/
  quotient_conj_mem :
    ∀ {n : ℕ} {γ σ : G},
      ((action σ) probe / probe) ∈ principalUnits.subgroup n →
      ((action (γ * σ * γ⁻¹)) probe / probe) ∈ principalUnits.subgroup n

namespace ValuationActionRamification

variable {G : Type u} [Group G] {K : Type v} [Group K]
variable (A : ValuationActionRamification G K)

/-- The action quotient used to test ramification depth. -/
def actionQuotient (σ : G) : K :=
  (A.action σ) A.probe / A.probe

/-- States the theorem `actionQuotient_one`. -/
@[simp] theorem actionQuotient_one :
    A.actionQuotient 1 = 1 := by
  simp [actionQuotient]

/-- Defines `actionDepthAtLeast`. -/
def actionDepthAtLeast (n : ℕ) (σ : G) : Prop :=
  A.actionQuotient σ ∈ A.principalUnits.subgroup n

/-- States the theorem `actionDepthAtLeast_iff`. -/
@[simp] theorem actionDepthAtLeast_iff (n : ℕ) (σ : G) :
    A.actionDepthAtLeast n σ ↔
      A.actionQuotient σ ∈ A.principalUnits.subgroup n :=
  Iff.rfl

/-- States the theorem `actionDepthAtLeast_one`. -/
theorem actionDepthAtLeast_one (n : ℕ) :
    A.actionDepthAtLeast n 1 := by
  rw [A.actionDepthAtLeast_iff, A.actionQuotient_one]
  exact (A.principalUnits.subgroup n).one_mem

/-- States the theorem `actionDepthAtLeast_mul`. -/
theorem actionDepthAtLeast_mul {n : ℕ} {σ τ : G}
    (hσ : A.actionDepthAtLeast n σ) (hτ : A.actionDepthAtLeast n τ) :
    A.actionDepthAtLeast n (σ * τ) :=
  A.quotient_mul_mem hσ hτ

/-- States the theorem `actionDepthAtLeast_inv`. -/
theorem actionDepthAtLeast_inv {n : ℕ} {σ : G}
    (hσ : A.actionDepthAtLeast n σ) :
    A.actionDepthAtLeast n σ⁻¹ :=
  A.quotient_inv_mem hσ

/-- States the theorem `actionDepthAtLeast_conj`. -/
theorem actionDepthAtLeast_conj {n : ℕ} {γ σ : G}
    (hσ : A.actionDepthAtLeast n σ) :
    A.actionDepthAtLeast n (γ * σ * γ⁻¹) :=
  A.quotient_conj_mem hσ

/-- The action-defined lower ramification group. -/
def lowerRamificationGroup (n : ℕ) : Subgroup G where
  carrier := {σ | A.actionDepthAtLeast n σ}
  one_mem' := A.actionDepthAtLeast_one n
  mul_mem' := by
    intro σ τ hσ hτ
    exact A.actionDepthAtLeast_mul hσ hτ
  inv_mem' := by
    intro σ hσ
    exact A.actionDepthAtLeast_inv hσ

/-- States the theorem `mem_lowerRamificationGroup_iff`. -/
@[simp] theorem mem_lowerRamificationGroup_iff (n : ℕ) (σ : G) :
    σ ∈ A.lowerRamificationGroup n ↔ A.actionDepthAtLeast n σ :=
  Iff.rfl



/-- States the theorem `lowerRamificationGroup_normal`. -/
theorem lowerRamificationGroup_normal (n : ℕ) :
    (A.lowerRamificationGroup n).Normal where
  conj_mem := by
    intro σ hσ γ
    exact A.actionDepthAtLeast_conj (γ := γ) hσ

/-- Provides the instance `lowerRamificationGroup_normal_instance`. -/
instance lowerRamificationGroup_normal_instance (n : ℕ) :
    (A.lowerRamificationGroup n).Normal :=
  A.lowerRamificationGroup_normal n

/-- States the theorem `lowerRamificationGroup_antitone`. -/
theorem lowerRamificationGroup_antitone {m n : ℕ} (hmn : m ≤ n) :
    A.lowerRamificationGroup n ≤ A.lowerRamificationGroup m := by
  intro σ hσ
  exact A.principalUnits.antitone hmn hσ

/-- Package the action-defined groups as a lower ramification filtration. -/
def toLowerRamificationFiltration : AntitoneNormalSubgroupFiltration G where
  lower := A.lowerRamificationGroup
  lower_normal := A.lowerRamificationGroup_normal
  antitone := by
    intro m n hmn
    exact A.lowerRamificationGroup_antitone hmn

/-- States the theorem `toLowerRamificationFiltration_apply`. -/
@[simp] theorem toLowerRamificationFiltration_apply (n : ℕ) :
    A.toLowerRamificationFiltration.lower n = A.lowerRamificationGroup n :=
  rfl

/-- Herbrand step attached to an action-defined lower filtration. -/
noncomputable def herbrandStep (i : Nat) : Rat :=
  A.toLowerRamificationFiltration.herbrandStep i

/-- Natural-index Herbrand function attached to an action-defined lower
filtration. -/
noncomputable def herbrandFunctionNat (n : Nat) : Rat :=
  A.toLowerRamificationFiltration.herbrandFunctionNat n





/-- The inertia subgroup `G_0` for an action-defined filtration. -/
abbrev inertiaSubgroup : Subgroup G :=
  A.lowerRamificationGroup 0



/-- The wild inertia subgroup `G_1` for an action-defined filtration. -/
abbrev wildInertiaSubgroup : Subgroup G :=
  A.lowerRamificationGroup 1

/-- The tame quotient `G_0/G_1` for an action-defined filtration. -/
def tameQuotient : Type u :=
  A.toLowerRamificationFiltration.tameQuotient

/-- Provides the instance `tameQuotientGroup`. -/
instance tameQuotientGroup : Group A.tameQuotient := by
  change Group A.toLowerRamificationFiltration.tameQuotient
  infer_instance

/-- The action-defined tame quotient is canonically identified with the
underlying lower-filtration model. -/
def tameQuotientEquivLowerFiltration :
    A.tameQuotient ≃*
      A.toLowerRamificationFiltration.tameQuotient :=
  MulEquiv.refl _

/-- Provides the instance `tameQuotientFinite`. -/
instance tameQuotientFinite [Finite G] : Finite A.tameQuotient :=
  Finite.of_equiv A.toLowerRamificationFiltration.tameQuotient
    A.tameQuotientEquivLowerFiltration.symm.toEquiv

/-- Canonical projection to the action-defined tame quotient. -/
def tameQuotientMk : A.inertiaSubgroup →* A.tameQuotient :=
  A.tameQuotientEquivLowerFiltration.symm.toMonoidHom.comp
    A.toLowerRamificationFiltration.tameQuotientMk

/-- States the theorem `tameQuotientEquivLowerFiltration_apply_mk`. -/
@[simp]
theorem tameQuotientEquivLowerFiltration_apply_mk
    (σ : A.inertiaSubgroup) :
    A.tameQuotientEquivLowerFiltration (A.tameQuotientMk σ) =
      A.toLowerRamificationFiltration.tameQuotientMk σ :=
  rfl

/-- States the theorem `tameQuotientMk_surjective`. -/
theorem tameQuotientMk_surjective :
    Function.Surjective A.tameQuotientMk := by
  intro q
  let q' := A.tameQuotientEquivLowerFiltration q
  obtain ⟨σ, hσ⟩ :=
    A.toLowerRamificationFiltration.tameQuotient_inductionOn
      (motive := fun q' => ∃ σ,
        A.toLowerRamificationFiltration.tameQuotientMk σ = q')
      q' (fun σ => ⟨σ, rfl⟩)
  refine ⟨σ, A.tameQuotientEquivLowerFiltration.injective ?_⟩
  exact (A.tameQuotientEquivLowerFiltration_apply_mk
    (show A.inertiaSubgroup from σ)).trans hσ

/-- States the theorem `tameQuotientMk_eq_one_iff`. -/
@[simp]
theorem tameQuotientMk_eq_one_iff (σ : A.inertiaSubgroup) :
    A.tameQuotientMk σ = 1 ↔ (σ : G) ∈ A.wildInertiaSubgroup := by
  constructor
  · intro h
    have h' := congrArg A.tameQuotientEquivLowerFiltration h
    rw [A.tameQuotientEquivLowerFiltration_apply_mk, map_one] at h'
    simpa only [toLowerRamificationFiltration_apply] using
      (A.toLowerRamificationFiltration.tameQuotientMk_eq_one_iff σ).1 h'
  · intro h
    apply A.tameQuotientEquivLowerFiltration.injective
    rw [A.tameQuotientEquivLowerFiltration_apply_mk, map_one]
    apply
      (A.toLowerRamificationFiltration.tameQuotientMk_eq_one_iff σ).2
    simpa only [toLowerRamificationFiltration_apply] using h

/-- States the theorem `tameQuotientMk_eq_iff`. -/
@[simp]
theorem tameQuotientMk_eq_iff (σ τ : A.inertiaSubgroup) :
    A.tameQuotientMk σ = A.tameQuotientMk τ ↔
      ((σ / τ : A.inertiaSubgroup) : G) ∈ A.wildInertiaSubgroup := by
  constructor
  · intro h
    have h' := congrArg A.tameQuotientEquivLowerFiltration h
    rw [A.tameQuotientEquivLowerFiltration_apply_mk,
      A.tameQuotientEquivLowerFiltration_apply_mk] at h'
    change ((σ / τ : A.inertiaSubgroup) : G) ∈
      A.lowerRamificationGroup 1
    exact
      (A.toLowerRamificationFiltration.tameQuotientMk_eq_iff σ τ).1 h'
  · intro h
    apply A.tameQuotientEquivLowerFiltration.injective
    rw [A.tameQuotientEquivLowerFiltration_apply_mk,
      A.tameQuotientEquivLowerFiltration_apply_mk]
    apply
      (A.toLowerRamificationFiltration.tameQuotientMk_eq_iff σ τ).2
    change ((σ / τ : A.inertiaSubgroup) : G) ∈
      A.lowerRamificationGroup 1 at h
    exact h

/-- Eliminate the action-defined tame quotient through inertia
representatives. -/
protected theorem tameQuotient_inductionOn
    {motive : A.tameQuotient → Prop} (q : A.tameQuotient)
    (h : ∀ σ : A.inertiaSubgroup, motive (A.tameQuotientMk σ)) :
    motive q := by
  obtain ⟨σ, rfl⟩ := A.tameQuotientMk_surjective q
  exact h σ

/-- The tame character attached to the chosen action probe.

For valued-extension applications the probe is the chosen uniformizer and the
action quotient is `σ ϖ / ϖ`; at this abstraction level the target is the
tame quotient `G_0/G_1`.  Residue-field unit realizations can be composed on
top once the concrete unit quotient has been constructed. -/
def tameCharacterOfUniformizer : A.inertiaSubgroup →* A.tameQuotient :=
  A.tameQuotientMk

/-- States the theorem `tameCharacterOfUniformizer_apply`. -/
@[simp] theorem tameCharacterOfUniformizer_apply (σ : A.inertiaSubgroup) :
    A.tameCharacterOfUniformizer σ =
      A.tameQuotientMk σ :=
  rfl













/-- Defines `tameQuotientEquivQuotientKernel`. -/
def tameQuotientEquivQuotientKernel :
    A.tameQuotient ≃*
      A.toLowerRamificationFiltration.quotientKernelOfLe (Nat.zero_le 1) :=
  A.tameQuotientEquivLowerFiltration.trans
    A.toLowerRamificationFiltration.tameQuotientEquivQuotientKernel

/-- States the theorem `coe_tameQuotientEquivQuotientKernel_mk`. -/
@[simp] theorem coe_tameQuotientEquivQuotientKernel_mk
    (σ : A.inertiaSubgroup) :
    ((A.tameQuotientEquivQuotientKernel
        (A.tameQuotientMk σ) :
      A.toLowerRamificationFiltration.quotientKernelOfLe (Nat.zero_le 1)) :
      A.toLowerRamificationFiltration.quotient 1) =
      A.toLowerRamificationFiltration.quotientMk 1 (σ : G) := by
  exact
    A.toLowerRamificationFiltration.coe_tameQuotientEquivQuotientKernel_mk σ

/-- At every finite level `n ≥ 1`, the action-defined tame quotient is the
quotient of finite-level inertia by finite-level wild inertia:
`(G_0/G_n)/(G_1/G_n) ≃ G_0/G_1`. -/
def quotientInertiaByWildKernelEquivTameQuotient {n : ℕ} (hn : 1 ≤ n) :
    A.toLowerRamificationFiltration.quotientKernelOfLe
        (le_trans (Nat.zero_le 1) hn) ⧸
        (A.toLowerRamificationFiltration.quotientKernelOfLe hn).subgroupOf
          (A.toLowerRamificationFiltration.quotientKernelOfLe
            (le_trans (Nat.zero_le 1) hn)) ≃*
      A.tameQuotient :=
  (AntitoneNormalSubgroupFiltration.quotientInertiaByWildKernelEquivTameQuotient
    A.toLowerRamificationFiltration hn).trans
      A.tameQuotientEquivLowerFiltration.symm

/-- States the theorem `tameQuotientEquivQuotientKernel_quotientInertiaByWildKernel_mk'`. -/
@[simp] theorem tameQuotientEquivQuotientKernel_quotientInertiaByWildKernel_mk'
    {n : ℕ} (hn : 1 ≤ n)
    (q :
      A.toLowerRamificationFiltration.quotientKernelOfLe
        (le_trans (Nat.zero_le 1) hn)) :
    A.tameQuotientEquivQuotientKernel
        (A.quotientInertiaByWildKernelEquivTameQuotient hn
          (QuotientGroup.mk'
            ((A.toLowerRamificationFiltration.quotientKernelOfLe hn).subgroupOf
              (A.toLowerRamificationFiltration.quotientKernelOfLe
                (le_trans (Nat.zero_le 1) hn))) q)) =
      A.toLowerRamificationFiltration.quotientKernelMapOfLe
        (Nat.zero_le 1) hn q :=
  AntitoneNormalSubgroupFiltration.tameQuotientEquivQuotientKernel_quotientInertiaByWildKernel_mk'
    A.toLowerRamificationFiltration hn q







/-- Provides the instance `lowerRamificationGroup_subgroupOf_normal_instance`. -/
instance lowerRamificationGroup_subgroupOf_normal_instance (n : ℕ) :
    ((A.lowerRamificationGroup (n + 1)).subgroupOf
      (A.lowerRamificationGroup n)).Normal := by
  change ((A.toLowerRamificationFiltration.lower (n + 1)).subgroupOf
    (A.toLowerRamificationFiltration.lower n)).Normal
  infer_instance

































/-- First isomorphism theorem inside action-defined ramification kernels:
`(G_l/G_n)/ker(G_l/G_n → G_l/G_m) ≃ G_l/G_m`, for `l ≤ m ≤ n`.
The kernel is identified with `G_m/G_n` by
`AntitoneNormalSubgroupFiltration.quotientKernelMapOfLe_ker_eq`. -/
def quotientKernelQuotientKerEquivQuotientKernelOfLe {l m n : ℕ}
    (hlm : l ≤ m) (hmn : m ≤ n) :
      A.toLowerRamificationFiltration.quotientKernelOfLe
        (le_trans hlm hmn) ⧸
        (A.toLowerRamificationFiltration.quotientKernelMapOfLe hlm hmn).ker ≃*
      A.toLowerRamificationFiltration.quotientKernelOfLe hlm :=
  AntitoneNormalSubgroupFiltration.quotientKernelQuotientKerEquivQuotientKernelOfLe
    A.toLowerRamificationFiltration hlm hmn

/-- States the theorem `quotientKernelQuotientKerEquivQuotientKernelOfLe_mk'`. -/
@[simp] theorem quotientKernelQuotientKerEquivQuotientKernelOfLe_mk'
    {l m n : ℕ} (hlm : l ≤ m) (hmn : m ≤ n)
    (q :
      A.toLowerRamificationFiltration.quotientKernelOfLe
        (le_trans hlm hmn)) :
    A.quotientKernelQuotientKerEquivQuotientKernelOfLe hlm hmn
        (QuotientGroup.mk'
          (A.toLowerRamificationFiltration.quotientKernelMapOfLe hlm hmn).ker q) =
      A.toLowerRamificationFiltration.quotientKernelMapOfLe hlm hmn q :=
  AntitoneNormalSubgroupFiltration.quotientKernelQuotientKerEquivQuotientKernelOfLe_mk'
    A.toLowerRamificationFiltration hlm hmn q

/-- Second-isomorphism-style form for action-defined ramification kernels:
`(G_l/G_n)/(G_m/G_n) ≃ G_l/G_m`, for `l ≤ m ≤ n`. -/
def quotientKernelQuotientSubgroupOfEquivQuotientKernelOfLe {l m n : ℕ}
    (hlm : l ≤ m) (hmn : m ≤ n) :
      A.toLowerRamificationFiltration.quotientKernelOfLe
        (le_trans hlm hmn) ⧸
        (A.toLowerRamificationFiltration.quotientKernelOfLe hmn).subgroupOf
          (A.toLowerRamificationFiltration.quotientKernelOfLe
            (le_trans hlm hmn)) ≃*
      A.toLowerRamificationFiltration.quotientKernelOfLe hlm :=
  AntitoneNormalSubgroupFiltration.quotientKernelQuotientSubgroupOfEquivQuotientKernelOfLe
    A.toLowerRamificationFiltration hlm hmn

/-- States the theorem `quotientKernelQuotientSubgroupOfEquivQuotientKernelOfLe_mk'`. -/
@[simp] theorem quotientKernelQuotientSubgroupOfEquivQuotientKernelOfLe_mk'
    {l m n : ℕ} (hlm : l ≤ m) (hmn : m ≤ n)
    (q :
      A.toLowerRamificationFiltration.quotientKernelOfLe
        (le_trans hlm hmn)) :
    A.quotientKernelQuotientSubgroupOfEquivQuotientKernelOfLe hlm hmn
        (QuotientGroup.mk'
          ((A.toLowerRamificationFiltration.quotientKernelOfLe hmn).subgroupOf
            (A.toLowerRamificationFiltration.quotientKernelOfLe
              (le_trans hlm hmn))) q) =
      A.toLowerRamificationFiltration.quotientKernelMapOfLe hlm hmn q :=
  AntitoneNormalSubgroupFiltration.quotientKernelQuotientSubgroupOfEquivQuotientKernelOfLe_mk'
    A.toLowerRamificationFiltration hlm hmn q



/-- First isomorphism theorem for action-defined level-change maps:
`(G/G_n)/(G_m/G_n) ≃ G/G_m`. -/
def quotientQuotientKernelOfLeEquivQuotient
    {m n : ℕ} (hmn : m ≤ n) :
    A.toLowerRamificationFiltration.quotient n ⧸
        A.toLowerRamificationFiltration.quotientKernelOfLe hmn ≃*
      A.toLowerRamificationFiltration.quotient m :=
  A.toLowerRamificationFiltration.quotientQuotientKernelOfLeEquivQuotient hmn

/-- States the theorem `quotientQuotientKernelOfLeEquivQuotient_mk'`. -/
@[simp] theorem quotientQuotientKernelOfLeEquivQuotient_mk'
    {m n : ℕ} (hmn : m ≤ n)
    (q : A.toLowerRamificationFiltration.quotient n) :
    A.quotientQuotientKernelOfLeEquivQuotient hmn
        (QuotientGroup.mk'
          (A.toLowerRamificationFiltration.quotientKernelOfLe hmn) q) =
      A.toLowerRamificationFiltration.quotientMapOfLe hmn q :=
  A.toLowerRamificationFiltration.quotientQuotientKernelOfLeEquivQuotient_mk'
    hmn q

/-- States the theorem `quotientQuotientKernelOfLeEquivQuotient_mk'_mk'`. -/
@[simp] theorem quotientQuotientKernelOfLeEquivQuotient_mk'_mk'
    {m n : ℕ} (hmn : m ≤ n) (σ : G) :
    A.quotientQuotientKernelOfLeEquivQuotient hmn
        (QuotientGroup.mk'
          (A.toLowerRamificationFiltration.quotientKernelOfLe hmn)
          (A.toLowerRamificationFiltration.quotientMk n σ)) =
      A.toLowerRamificationFiltration.quotientMk m σ :=
  A.toLowerRamificationFiltration.quotientQuotientKernelOfLeEquivQuotient_mk'_mk'
    hmn σ









/-- At every finite level `N ≥ n + 1`, the action-defined `n`th graded piece
is the quotient of finite-level kernels `(G_n/G_N)/(G_{n+1}/G_N)`. -/
def quotientKernelByNextKernelEquivGradedPiece {n N : ℕ} (hN : n + 1 ≤ N) :
    A.toLowerRamificationFiltration.quotientKernelOfLe
        (le_trans (Nat.le_succ n) hN) ⧸
        (A.toLowerRamificationFiltration.quotientKernelOfLe hN).subgroupOf
          (A.toLowerRamificationFiltration.quotientKernelOfLe
            (le_trans (Nat.le_succ n) hN)) ≃*
      A.toLowerRamificationFiltration.gradedPiece n :=
  A.toLowerRamificationFiltration.quotientKernelByNextKernelEquivGradedPiece hN

/-- States the theorem `gradedPieceEquivQuotientKernel_quotientKernelByNextKernel_mk'`. -/
@[simp] theorem gradedPieceEquivQuotientKernel_quotientKernelByNextKernel_mk'
    {n N : ℕ} (hN : n + 1 ≤ N)
    (q :
      A.toLowerRamificationFiltration.quotientKernelOfLe
        (le_trans (Nat.le_succ n) hN)) :
    A.toLowerRamificationFiltration.gradedPieceEquivQuotientKernel n
        (A.quotientKernelByNextKernelEquivGradedPiece hN
          (QuotientGroup.mk'
            ((A.toLowerRamificationFiltration.quotientKernelOfLe hN).subgroupOf
              (A.toLowerRamificationFiltration.quotientKernelOfLe
                (le_trans (Nat.le_succ n) hN))) q)) =
      A.toLowerRamificationFiltration.quotientKernelMapOfLe (Nat.le_succ n) hN q :=
  AntitoneNormalSubgroupFiltration.gradedPieceEquivQuotientKernel_quotientKernelByNextKernel_mk'
    A.toLowerRamificationFiltration hN q















end ValuationActionRamification

end DiscreteValuationField

end

end RamificationTheory
