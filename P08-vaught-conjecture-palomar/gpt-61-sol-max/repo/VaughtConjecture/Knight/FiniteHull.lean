/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/

import Mathlib.Tactic

import VaughtConjecture.AmalgamationPlan.ClosedGeometry
import VaughtConjecture.Knight.VisibleFaceOneStep
import VaughtConjecture.Order.FiniteSupportClosure
import VaughtConjecture.Knight.Directedness

/-!
# Canonical finite hulls of actual chart supports

Adapted from the newsimple14 canonical-hulls draft, using the verified finite-plan geometry.
Assumptions throughout are exact consistency and
covering only.  The DecidableEq instance is only Finset bookkeeping and can
always be supplied classically.  This module must initially sit ABOVE
Directedness: using its common-cover theorem to build hulls, and then importing
hulls back into Directedness, would create a cycle.
-/

namespace VaughtConjecture.Knight.KnightRealization.FiniteHull

open TypeTower StageType

variable {α : LimitStage} {M : Type*} [DecidableEq M]
variable {R : KnightRealization α M}

noncomputable section

/-- Finite support, without choosing an order on the carrier. -/
def support {n : ℕ} (t : Fin n ↪ M) := Finset.univ.image t

@[simp] theorem mem_support {n : ℕ} {t : Fin n ↪ M} {x : M} :
    x ∈ support t ↔ ∃ i, t i = x := by
  simp [support]

@[simp] theorem support_trans {n m : ℕ} (f : Fin n ↪ Fin m) (t : Fin m ↪ M) :
    support (f.trans t) = (support f).image t := by aesop

/-- An enumeration adapter. The support, not this enumeration, is canonical. -/
def enumerate (S : Finset M) : Fin S.card ↪ M :=
  ⟨fun i => (S.equivFin.symm i),
    fun _ _ h => S.equivFin.symm.injective (Subtype.coe_injective h)⟩

@[simp] theorem support_enumerate (S : Finset M) : support (enumerate S) = S := by
  ext x
  rw [mem_support]
  constructor
  · rintro ⟨i, rfl⟩
    exact (S.equivFin.symm i).2
  · intro hx
    refine ⟨S.equivFin ⟨x, hx⟩, ?_⟩
    exact congrArg Subtype.val (S.equivFin.symm_apply_apply ⟨x, hx⟩)

theorem factor_of_support_subset {n m : ℕ} (t : Fin n ↪ M) (u : Fin m ↪ M)
    (h : support t ⊆ support u) :
    ∃ f : Fin n ↪ Fin m, f.trans u = t := by
  
  have hex  := fun i =>
    (mem_support).mp (h ((mem_support).mpr ⟨i, rfl⟩))
  choose f hf using hex
  refine ⟨⟨f, ?_⟩, ?_⟩
  · intro i j hij
    apply t.injective
    rw [← hf i, ← hf j, hij]
  · ext i
    exact hf i

/-- A finite closed set is the support of an actual chart. -/
def IsActualSupport (R : KnightRealization α M) S :=
  ∃ x : R.LabelledExt, support x.tuple = S

/-- Every visible coordinate face of an actual chart is an actual support. -/
theorem actual_of_face (hcons : R.IsExactParentConsistent)
    (x : R.LabelledExt) {F}
    (hF : F ∈ x.type.scheme.scheme.plan) :
    IsActualSupport R (F.image x.tuple) := by
  let f := enumerate F
  have hf : Finset.univ.image f ∈ x.type.scheme.scheme.plan := by
    change support f ∈ x.type.scheme.scheme.plan
    rw [support_enumerate]
    exact hF
  let p := x.type.restrictFace f hf
  have hp : R.eval (f.trans x.tuple) = some p := by
    have h := hcons x.tuple x.type f x.eval_eq
    change R.eval (f.trans x.tuple) = typeMap f x.type at h
    rw [h, typeMap_eq_some f x.type hf]
  refine ⟨⟨_, f.trans x.tuple, p, hp⟩, ?_⟩
  rw [support_trans, support_enumerate]

/-- Structural covering is cofinality of the actual finite supports. -/
theorem exists_actual_superset (hcov : R.IsInitialSegmentCovering) (S : Finset M) :
    ∃ A, IsActualSupport R A ∧ S ⊆ A := by
  obtain ⟨k, u, hu, hsome⟩ := hcov (enumerate S)
  obtain ⟨p, hp⟩ := Option.isSome_iff_exists.mp hsome
  refine ⟨support u, ⟨⟨_, u, p, hp⟩, rfl⟩, ?_⟩
  intro z hz
  have hz' : z ∈ support (enumerate S) := by simp_all
  obtain ⟨i, hi⟩ := (mem_support).mp hz'
  apply (mem_support).mpr
  refine ⟨Fin.castAddEmb k i, ?_⟩
  exact (congrArg (fun t => t i) hu).trans hi

/-- Intersection is performed inside one actual common chart. -/
theorem actual_inter (hcons : R.IsExactParentConsistent)
    (hcov : R.IsInitialSegmentCovering) A B
    (hA : IsActualSupport R A) (hB : IsActualSupport R B) :
    IsActualSupport R (A ∩ B) := by
  rcases hA with ⟨x, rfl⟩
  rcases hB with ⟨y, rfl⟩
  obtain ⟨z, hxz, hyz⟩ := directed_labelledExt hcons hcov x y
  obtain ⟨f, hft, hfp⟩ := hxz
  obtain ⟨g, hgt, hgp⟩ := hyz
  have hF : support f ∈ z.type.scheme.scheme.plan :=
    (typeMap_isSome_iff).mp (by rw [hfp]; rfl)
  have hG : support g ∈ z.type.scheme.scheme.plan :=
    (typeMap_isSome_iff).mp (by rw [hgp]; rfl)
  have hFG := z.type.scheme.scheme.isPlan.inter_mem hF hG
  have hactual := actual_of_face hcons z hFG
  have heq : (support f ∩ support g).image z.tuple =
      support x.tuple ∩ support y.tuple := by
    grind [support_trans]
  simpa only [heq] using hactual

/-- The canonical least actual finite support. Not a chosen enumeration. -/
def hull (hcons : R.IsExactParentConsistent) (hcov : R.IsInitialSegmentCovering) :=
  FiniteSupportClosure.ofCofinalInterClosed (IsActualSupport R)
    (actual_inter hcons hcov) (exists_actual_superset hcov)

theorem hull_actual (hcons : R.IsExactParentConsistent)
    (hcov : R.IsInitialSegmentCovering) S :
    IsActualSupport R (hull hcons hcov S) :=
  (hull hcons hcov).isClosed_closure S

def subset_hull (hcons : R.IsExactParentConsistent)
    (hcov : R.IsInitialSegmentCovering) S := (hull hcons hcov).le_closure S

/-- The old tuple-facing interface is recovered with literal occurrence maps. -/
theorem exists_hull_chart (hcons : R.IsExactParentConsistent)
    (hcov : R.IsInitialSegmentCovering) {n} t :
    ∃ (x : R.LabelledExt) (f : Fin n ↪ Fin x.arity),
      f.trans x.tuple = t ∧ support x.tuple = hull hcons hcov (support t) := by
  obtain ⟨x, hx⟩ := hull_actual hcons hcov (support t)
  have ht : support t ⊆ support x.tuple := by
    simp_all [subset_hull]
  obtain ⟨f, hf⟩ := factor_of_support_subset t x.tuple ht
  exact ⟨x, f, hf, hx⟩

