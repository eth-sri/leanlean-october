module

public import Mathlib

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
def quotientKernelOfLe {m n : ℕ} (_hmn : m ≤ n)  :=
  (F.quotientMapOfLe _hmn).ker

/-- The map from the `m`th lower ramification group into `G/G_n`. -/
def levelSubgroupToQuotient {m n : ℕ} (_hmn : m ≤ n)  :=
  (F.quotientMk n).comp (F.lower m).subtype

section
variable {m n : ℕ} (hmn : m ≤ n)
include m n hmn
/-- States the theorem `levelSubgroupToQuotient_apply`. -/
@[simp] theorem levelSubgroupToQuotient_apply  
    (σ : F.lower m) :
    F.levelSubgroupToQuotient hmn σ =
      F.quotientMk n (σ : G) :=
  rfl
































/-- The kernel of `G/G_n → G/G_m` is the image of `G_m` in `G/G_n`. -/
theorem quotientMapOfLe_ker_eq_quotientKernelOfLe   :
    (F.quotientMapOfLe hmn).ker = F.quotientKernelOfLe hmn :=
  rfl












































































/-- Membership in the named kernel subgroup is the same as mapping to `1`
under the corresponding level-change map. -/
theorem mem_quotientKernelOfLe_iff_quotientMap_eq_one   (q : F.quotient n) :
    q ∈ F.quotientKernelOfLe hmn ↔
      F.quotientMapOfLe hmn q = 1 := by
  rw [← F.quotientMapOfLe_ker_eq_quotientKernelOfLe hmn,
    MonoidHom.mem_ker]
end














section
variable {l m n : ℕ}
    (hlm : l ≤ m) (hmn : m ≤ n)
include l m n hlm hmn
/-- Membership in the coarser kernel after applying a level-change map is
equivalent to membership in the corresponding direct kernel. -/
theorem quotientMapOfLe_mem_quotientKernelOfLe_iff   (q : F.quotient n) :
    F.quotientMapOfLe hmn q ∈ F.quotientKernelOfLe hlm ↔
      q ∈ F.quotientKernelOfLe (le_trans hlm hmn) := by
  rw [F.mem_quotientKernelOfLe_iff_quotientMap_eq_one hlm,
    F.mem_quotientKernelOfLe_iff_quotientMap_eq_one (le_trans hlm hmn)]
  change ((F.quotientMapOfLe hlm).comp (F.quotientMapOfLe hmn)) q = 1 ↔
    F.quotientMapOfLe (le_trans hlm hmn) q = 1
  rw [F.quotientMapOfLe_comp hlm hmn]
























































































/-- The level-change map restricted to kernel subgroups:
`G_l/G_n → G_l/G_m`, for `l ≤ m ≤ n`. -/
def quotientKernelMapOfLe   :
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
@[simp] theorem quotientKernelMapOfLe_apply  
    (q : F.quotientKernelOfLe (le_trans hlm hmn)) :
    ((F.quotientKernelMapOfLe hlm hmn q :
      F.quotientKernelOfLe hlm) : F.quotient m) =
      F.quotientMapOfLe hmn (q : F.quotient n) :=
  rfl
end






































































































































































































































































































































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






/-- States the theorem `lowerRamificationGroup_normal`. -/
theorem lowerRamificationGroup_normal (n : ℕ) :
    (D.lowerRamificationGroup n).Normal where
  conj_mem := by
    intro σ hσ γ
    apply D.depth_conj_mem <;> assumption






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
def actionQuotient (σ : G)  :=
  (A.action σ) A.probe / A.probe

/-- States the theorem `actionQuotient_one`. -/
@[simp] theorem actionQuotient_one :
    A.actionQuotient 1 = 1 := by
  simp [actionQuotient]

/-- Defines `actionDepthAtLeast`. -/
def actionDepthAtLeast (n : ℕ) (σ : G)  :=
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
def actionDepthAtLeast_mul {n : ℕ} {σ τ : G}
    (hσ : A.actionDepthAtLeast n σ) (hτ : A.actionDepthAtLeast n τ)  :=
  A.quotient_mul_mem hσ hτ

/-- States the theorem `actionDepthAtLeast_inv`. -/
def actionDepthAtLeast_inv {n : ℕ} {σ : G}
    (hσ : A.actionDepthAtLeast n σ)  :=
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














/-- States the theorem `lowerRamificationGroup_normal`. -/
theorem lowerRamificationGroup_normal (n : ℕ) :
    (A.lowerRamificationGroup n).Normal where
  conj_mem := by
    intro σ hσ γ
    apply A.actionDepthAtLeast_conj <;> assumption






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






























/-- The inertia subgroup `G_0` for an action-defined filtration. -/
abbrev inertiaSubgroup  :=
  A.lowerRamificationGroup 0










/-- The tame quotient `G_0/G_1` for an action-defined filtration. -/
def tameQuotient  :=
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






/-- Canonical projection to the action-defined tame quotient. -/
def tameQuotientMk  :=
  A.tameQuotientEquivLowerFiltration.symm.toMonoidHom.comp
    A.toLowerRamificationFiltration.tameQuotientMk

/-- States the theorem `tameQuotientEquivLowerFiltration_apply_mk`. -/
@[simp]
theorem tameQuotientEquivLowerFiltration_apply_mk
    (σ : A.inertiaSubgroup) :
    A.tameQuotientEquivLowerFiltration (A.tameQuotientMk σ) =
      A.toLowerRamificationFiltration.tameQuotientMk σ :=
  rfl

































































/-- The tame character attached to the chosen action probe.

For valued-extension applications the probe is the chosen uniformizer and the
action quotient is `σ ϖ / ϖ`; at this abstraction level the target is the
tame quotient `G_0/G_1`.  Residue-field unit realizations can be composed on
top once the concrete unit quotient has been constructed. -/
def tameCharacterOfUniformizer  :=
  A.tameQuotientMk

/-- States the theorem `tameCharacterOfUniformizer_apply`. -/
@[simp] theorem tameCharacterOfUniformizer_apply (σ : A.inertiaSubgroup) :
    A.tameCharacterOfUniformizer σ =
      A.tameQuotientMk σ :=
  rfl






















































































































































































































































































































































































































































































































































































































end ValuationActionRamification

end DiscreteValuationField

end

end RamificationTheory
