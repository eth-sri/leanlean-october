
import VaughtConjecture.Knight.PointwiseLabels
/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/

import Mathlib.Tactic

import VaughtConjecture.Knight.CanonicalRecursiveBoundaryTransport

/-! # Actual index coverage of the recursive canonical inventory

Every positive constructed full grade has a controller, constructed from the
bottom profile. Proper indices retain their original witnesses. No catalogue
nonemptiness or output completeness is an additional assumption.
-/

namespace VaughtConjecture.Knight.CanonicalRecursiveCoverage
open AmalgamationPlan Transform  
noncomputable section

def bottomProfile {ι X : Type*} [DecidableEq ι] [Fintype X]
    {A : Finset ι} {D : CellScheme A} (sem : Semantics D) (j : ℕ) (occ : Cell D → X) :
    CanonicalFieldLayer.Profile sem j X occ := by
  refine ⟨fun _ => ⊥, ⟨?_, ?_, ?_⟩, rfl, fun _ => bot_ne_top⟩
  · solve_by_elim
  · intro c
    simpa only [Function.comp_apply, min_self] using TransformsTo.to_bot
  · grind

variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A}
variable (sem : Semantics D)

def bottom (j : ℕ) : CanonicalRecursiveInventory.Profile sem j := by
  rcases j with _ | _ | _ | j
  · exact PUnit.unit
  · exact bottomProfile _ _ _
  · exact bottomProfile _ _ _
  · exact bottomProfile _ _ _

theorem full_index n (hn : n ≤ A.card) j (hj : 0 < j) (hjn : j ≤ n) :
    ∃ d ,
      (CanonicalRecursiveInventory.scheme sem n hn).cell d = (A, j) := by
  obtain ⟨i, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hj)
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hjn
  exact ⟨RecursiveSourceCarrier.retained D (CanonicalRecursiveInventory.Profile sem)
    i t hn (bottom sem (i + 1)),
    RecursiveSourceCarrier.retained_cell D (CanonicalRecursiveInventory.Profile sem)
      i t hn (bottom sem (i + 1))⟩

theorem grade_bound {n} {hn : n ≤ A.card}
    (hg : BoundedBy D.grade n)
    d :
    (CanonicalRecursiveInventory.scheme sem n hn).grade d ≤ n := by
  rcases RecursiveSourceCarrier.classify D (CanonicalRecursiveInventory.Profile sem) n hn d
    with ⟨c, rfl⟩ | ⟨j, _, hj, he⟩
  · exact (congrArg Prod.snd
      (CanonicalRecursiveInventory.boundary_cell sem n hn c)).le.trans (hg c)
  · simp_all

/-- Completeness through the constructed height, not at the still absent apex. -/
theorem complete_through n (hn : n ≤ A.card)
    (hc : ∀ J ∈ Plan.gradedPlan D.plan, J.1 ≠ A → ∃ d , D.cell d = J)
    J
    (hJ : J ∈ Plan.gradedPlan (CanonicalRecursiveInventory.scheme sem n hn).plan)
    (hj : J.2 ≤ n) :
    ∃ d, (CanonicalRecursiveInventory.scheme sem n hn).cell d = J := by
  have hm  := by
    simpa only [CanonicalRecursiveBoundaryTransport.plan_eq] using hJ
  by_cases hs : J.1 = A
  · obtain ⟨d, hd⟩ := full_index sem n hn J.2 (Plan.mem_gradedPlan.mp hm).2.1 hj
    exact ⟨d, hd.trans (Prod.ext hs.symm rfl)⟩
  · obtain ⟨d, hd⟩ := hc J hm hs
    exact ⟨CanonicalRecursiveInventory.boundary sem n hn d,
      (CanonicalRecursiveInventory.boundary_cell sem n hn d).trans hd⟩

