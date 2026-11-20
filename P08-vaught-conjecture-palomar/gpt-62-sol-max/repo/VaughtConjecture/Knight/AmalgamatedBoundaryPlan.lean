/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.Cell

@[expose] public section

namespace VaughtConjecture.Knight.AmalgamatedBoundaryPlan

open AmalgamationPlan

variable {ι : Type*} [DecidableEq ι]

structure Step (A : Finset ι) where
  a : ι
  b : ι
  ha : a ∈ A
  hb : b ∈ A
  different : a ≠ b
  left : Finset (Finset ι)
  right : Finset (Finset ι)
  left_plan : Plan.IsPlan (A.erase a) left
  right_plan : Plan.IsPlan (A.erase b) right
  common_left : (A.erase a).erase b ∈ left
  common_right : (A.erase a).erase b ∈ right
  common : Plan.restrictPlan left ((A.erase a).erase b) =
    Plan.restrictPlan right ((A.erase a).erase b)

variable {A : Finset ι} (s : Step A)

def Step.plan : Finset (Finset ι) := s.left ∪ s.right ∪ {A}

theorem isPlan : Plan.IsPlan A s.plan :=
  Plan.IsPlan.step s.ha s.hb s.different s.left_plan s.right_plan
    ⟨s.common_left, s.common_right⟩ s.common rfl

private theorem restrict_union {A B C : Finset ι} {Q R : Finset (Finset ι)}
    (hQ : Plan.IsPlan B Q) (hR : Plan.IsPlan C R) (hne : ¬ A ⊆ B)
    (hcommon : Plan.restrictPlan Q (B ∩ C) = Plan.restrictPlan R (B ∩ C)) :
    Plan.restrictPlan (Q ∪ R ∪ {A}) B = Q := by
  ext S
  simp only [Plan.restrictPlan, Finset.mem_inter, Finset.mem_union,
    Finset.mem_singleton, Finset.mem_powerset]
  constructor
  · rintro ⟨(hS | hS) | rfl, hSB⟩
    · exact hS
    · have hc : S ∈ Plan.restrictPlan R (B ∩ C) :=
        Finset.mem_inter.mpr ⟨hS, Finset.mem_powerset.mpr
          (Finset.subset_inter hSB (hR.subset_of_mem hS))⟩
      rw [← hcommon] at hc
      exact (Finset.mem_inter.mp hc).1
    lia
  · intro hS
    exact ⟨Or.inl (Or.inl hS), hQ.subset_of_mem hS⟩

theorem erased_inter : A.erase s.a ∩ A.erase s.b = (A.erase s.a).erase s.b := by grind

theorem restrict_left : Plan.restrictPlan s.plan (A.erase s.a) = s.left := by
  apply restrict_union s.left_plan s.right_plan
  · intro h
    exact Finset.notMem_erase s.a A (h s.ha)
  · rw [erased_inter]
    exact s.common

theorem restrict_right : Plan.restrictPlan s.plan (A.erase s.b) = s.right := by
  have h := restrict_union s.right_plan s.left_plan (A := A) (by
    intro h
    exact Finset.notMem_erase s.b A (h s.hb))
  have hc : Plan.restrictPlan s.right (A.erase s.b ∩ A.erase s.a) =
      Plan.restrictPlan s.left (A.erase s.b ∩ A.erase s.a) := by
    rw [Finset.inter_comm, erased_inter]
    exact s.common.symm
  grind +locals

theorem proper_scope_cover {B : Finset ι} (hB : B ∈ s.plan) (hne : B ≠ A) :
    B ⊆ A.erase s.a ∨ B ⊆ A.erase s.b := by
  rcases Finset.mem_union.mp hB with hB | hB
  · exact (Finset.mem_union.mp hB).imp s.left_plan.subset_of_mem s.right_plan.subset_of_mem
  simp_all

/-- The uniform step data are available for every nontrivial support plan. -/
theorem exists_step {P : Finset (Finset ι)} (hP : Plan.IsPlan A P) (hA : 2 ≤ A.card) :
    ∃ s : Step A, s.plan = P := by
  cases hP with
  | empty => simp at hA
  | singleton x => simp at hA
  | step ha hb hab hQ hR hmem heq hP =>
    exact ⟨⟨_, _, ha, hb, hab, _, _, hQ, hR, hmem.1, hmem.2, heq⟩, hP.symm⟩

end VaughtConjecture.Knight.AmalgamatedBoundaryPlan
