/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.WholeDonorBoundary
public import VaughtConjecture.Knight.AmalgamatedBoundaryPlan

@[expose] public section

namespace VaughtConjecture.Knight.SemSchemeBoundaryInput

open AmalgamationPlan AmalgamatedBoundaryPlan CoatomBoundaryExtension

noncomputable section

variable {ι : Type*} [DecidableEq ι] {A : Finset ι}

/-- The common boundary input specialized to the two coatoms of a step. -/
abbrev Input (s : Step A) (m nL nR : ℕ) :=
  WholeDonorBoundary.Input A (A.erase s.a) (A.erase s.b) s.plan m nL nR

namespace Input

variable {s : Step A} {m nL nR : ℕ} (I : Input s m nL nR)

theorem proper (d : Cell I.boundary) : I.boundary.scope d ≠ A := by
  rcases I.covered d with ⟨c, rfl⟩ | ⟨c, rfl⟩
  · have hs := I.leftScheme.scope_subset c
    change (I.leftScheme.cell c).1 ⊆ A.erase s.a at hs
    rw [← I.leftFace.index c] at hs
    intro h
    change (I.boundary.cell (I.leftFace.map c)).1 = A at h
    rw [h] at hs
    exact Finset.notMem_erase _ _ (hs s.ha)
  · have hs := I.rightScheme.scope_subset c
    change (I.rightScheme.cell c).1 ⊆ A.erase s.b at hs
    rw [← I.rightFace.index c] at hs
    intro h
    change (I.boundary.cell (I.rightFace.map c)).1 = A at h
    rw [h] at hs
    exact Finset.notMem_erase _ _ (hs s.hb)

theorem left_visible : A.erase s.a ∈ I.boundary.plan :=
  Finset.mem_union_left _ (Finset.mem_union_left _ s.left_plan.domain_mem)

theorem right_visible : A.erase s.b ∈ I.boundary.plan :=
  Finset.mem_union_left _ (Finset.mem_union_right _ s.right_plan.domain_mem)

theorem intersection_visible : A.erase s.a ∩ A.erase s.b ∈ I.boundary.plan := by
  rw [AmalgamatedBoundaryPlan.erased_inter s]
  exact Finset.mem_union_left _ (Finset.mem_union_left _ s.common_left)

include I in
theorem complete_proper {J : Finset ι × ℕ} (hJ : J ∈ Plan.gradedPlan I.boundary.plan)
    (hproper : J.1 ≠ A) : ∃ d, I.boundary.cell d = J :=
  (I.occupied_iff hJ).mpr (proper_scope_cover s (Plan.mem_gradedPlan.mp hJ).1 hproper)

theorem proper_lift {CI BJ : Finset ι × ℕ}
    (hCI : CI ∈ Plan.gradedPlan s.plan) (hBJ : BJ ∈ Plan.gradedPlan s.plan)
    (h : GradedLe CI BJ) (hB : BJ.1 ≠ A) : CappedLift I.rows h :=
  I.installed_lift I.leftFace I.rightFace hCI hBJ h (proper_scope_cover s (Plan.mem_gradedPlan.mp hBJ).1 hB)

end Input

end

end VaughtConjecture.Knight.SemSchemeBoundaryInput
