/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.CoatomBoundaryPresentation
public import VaughtConjecture.Knight.CanonicalRecursiveInitialized

@[expose] public section

namespace VaughtConjecture.Knight.CanonicalRecursiveCoverage
open AmalgamationPlan Transform Value ExtOrd
noncomputable section

def bottomProfile {ι X : Type*} [DecidableEq ι] [Fintype X]
    {A : Finset ι} {D : CellScheme A} (sem : Semantics D) (j : ℕ) (occ : Cell D → X) :
    CanonicalFieldLayer.Profile sem j X occ := by
  refine ⟨fun _ => ⊥, ⟨?_, ?_, ?_⟩, rfl, fun _ => bot_ne_top⟩
  · intro d
    exact (extVisibilityReplace_bot _ _).symm
  · intro c
    simpa only [Function.comp_apply, min_self] using TransformsTo.to_bot (sem.E c)
  · intro _ b _ _
    exact ⟨b, rfl, le_rfl⟩

variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A}
variable (sem : Semantics D)

def bottom (j : ℕ) : CanonicalRecursiveInventory.Profile sem j := by
  rcases j with _ | _ | _ | j
  · exact PUnit.unit
  · exact bottomProfile _ _ _
  · exact bottomProfile _ _ _
  · exact bottomProfile _ _ _

theorem full_index (n : ℕ) (hn : n ≤ A.card) (j : ℕ) (hj : 0 < j) (hjn : j ≤ n) :
    ∃ d : Cell (CanonicalRecursiveInventory.scheme sem n hn),
      (CanonicalRecursiveInventory.scheme sem n hn).cell d = (A, j) := by
  obtain ⟨i, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hj)
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hjn
  exact ⟨RecursiveSourceCarrier.retained D (CanonicalRecursiveInventory.Profile sem)
    i t hn (bottom sem (i + 1)),
    RecursiveSourceCarrier.retained_cell D (CanonicalRecursiveInventory.Profile sem)
      i t hn (bottom sem (i + 1))⟩

theorem grade_bound (n : ℕ) (hn : n ≤ A.card)
    (hg : ∀ d : Cell D, D.grade d ≤ n)
    (d : Cell (CanonicalRecursiveInventory.scheme sem n hn)) :
    (CanonicalRecursiveInventory.scheme sem n hn).grade d ≤ n := by
  rcases RecursiveSourceCarrier.classify D (CanonicalRecursiveInventory.Profile sem) n hn d
    with ⟨c, rfl⟩ | ⟨j, _, hj, he⟩
  · exact (congrArg Prod.snd
      (CanonicalRecursiveInventory.boundary_cell sem n hn c)).le.trans (hg c)
  · exact (congrArg Prod.snd he).le.trans hj

/-- Completeness through the constructed height, not at the still absent apex. -/
theorem complete_through (n : ℕ) (hn : n ≤ A.card)
    (hc : ∀ J ∈ Plan.gradedPlan D.plan, J.1 ≠ A → ∃ d : Cell D, D.cell d = J)
    (J : Finset ι × ℕ)
    (hJ : J ∈ Plan.gradedPlan (CanonicalRecursiveInventory.scheme sem n hn).plan)
    (hj : J.2 ≤ n) :
    ∃ d, (CanonicalRecursiveInventory.scheme sem n hn).cell d = J := by
  have hm : J ∈ Plan.gradedPlan D.plan := by
    simpa only [CanonicalRecursiveBoundaryTransport.plan_eq] using hJ
  by_cases hs : J.1 = A
  · obtain ⟨d, hd⟩ := full_index sem n hn J.2 (Plan.mem_gradedPlan.mp hm).2.1 hj
    exact ⟨d, hd.trans (Prod.ext hs.symm rfl)⟩
  · obtain ⟨d, hd⟩ := hc J hm hs
    exact ⟨CanonicalRecursiveInventory.boundary sem n hn d,
      (CanonicalRecursiveInventory.boundary_cell sem n hn d).trans hd⟩

end
end VaughtConjecture.Knight.CanonicalRecursiveCoverage

namespace VaughtConjecture.Knight.CoatomRecursiveInput
open AmalgamationPlan AmalgamatedBoundaryPlan SemSchemeBoundaryInput
open Transform Value ExtOrd CoatomBoundaryExtension
noncomputable section

variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {s : Step A}

theorem oldLifts {m nL nR : ℕ} (I : Input s m nL nR) :
    CanonicalCoatomBountiful.OldLifts I.rows := by
  intro CI BJ hCI hBJ hB h
  by_cases he : CI = BJ
  · subst BJ
    exact lift_refl
  · exact I.proper_lift hCI hBJ h he hB

variable {m n : ℕ} (I : Input s m (n + 3) (n + 3))

include I in
theorem height_le : n + 3 ≤ A.card := by
  rw [← I.card_left]
  exact Finset.card_le_card (Finset.erase_subset _ _)

abbrev scheme := CanonicalRecursiveContract.carrier I.rows n (height_le I)
abbrev rows := CanonicalRecursiveSemantics.rows I.rows I.proper n (height_le I)

theorem ready : CanonicalRecursiveRecurrence.Ready I.rows I.proper n (height_le I) := by
  apply CanonicalRecursiveInitialized.ready I.rows I.proper I.consistent (oldLifts I)
    I.left_visible I.right_visible
    (fun h => Finset.notMem_erase s.a A (h.symm ▸ s.ha))
    (fun h => Finset.notMem_erase s.b A (h.symm ▸ s.hb))
    I.intersection_visible (fun _ hC hCA => I.proper_scope_cover hC hCA)
    n (height_le I) (by rw [I.card_left]) (by rw [I.card_right])
  intro C hC hCA j hj hjC _
  exact I.complete_proper (Plan.mem_gradedPlan.mpr ⟨hC, hj, hjC⟩) hCA

theorem consistent : (rows I).IsConsistent :=
  CanonicalRecursiveSemantics.consistent I.rows I.proper I.consistent n (height_le I)

theorem grade_bound (d : Cell (scheme I)) : (scheme I).grade d ≤ n + 3 :=
  CanonicalRecursiveCoverage.grade_bound I.rows (n + 3) (height_le I)
    (fun d => by simpa only [max_self] using I.grade_le d) d

/-- Effective nominal grades are included; no cap is raised. -/
theorem bountiful : (rows I).IsBountiful := by
  apply EffectiveGradeLifting.bountiful_of_bounded_same_grade (grade_bound I) (by omega)
  intro C B j hC hB hj hCB
  apply (GradeCutLifting.lift_iff (rows I) (n + 3)
    (I := (C, j)) (J := (B, j)) ⟨hCB, le_rfl⟩ hj).mp
  exact lift_of_bountiful (ready I).2 hC hB ⟨hCB, le_rfl⟩

theorem complete_through (J : Finset ι × ℕ)
    (hJ : J ∈ Plan.gradedPlan (scheme I).plan) (hj : J.2 ≤ n + 3) :
    ∃ d, (scheme I).cell d = J :=
  CanonicalRecursiveCoverage.complete_through I.rows (n + 3) (height_le I)
    (fun _ h hA => I.complete_proper h hA) J hJ hj

end
end VaughtConjecture.Knight.CoatomRecursiveInput
