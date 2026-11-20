/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.CanonicalRecursiveBoundaryTransport

@[expose] public section

namespace VaughtConjecture.Knight.CanonicalRecursiveCoverage

open AmalgamationPlan Transform Value ExtOrd

noncomputable section

variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A}

variable (sem : Semantics D)

def bottom (j : ℕ) : CanonicalRecursiveInventory.Profile sem j := by
  rcases j with _ | _ | _ | j
  · exact PUnit.unit
  all_goals exact CanonicalFieldLayer.Profile.bot _ _ _ _

theorem coverage (n : ℕ) (hn : n ≤ A.card) (d : Cell (CanonicalRecursiveInventory.scheme sem n hn)) :
    (∃ c, CanonicalRecursiveInventory.boundary sem n hn c = d) ∨
      (CanonicalRecursiveInventory.scheme sem n hn).scope d = A := by
  rcases RecursiveSourceCarrier.classify D (CanonicalRecursiveInventory.Profile sem) n hn d
    with h | ⟨j, _, _, e⟩
  · exact Or.inl h
  · exact Or.inr (congrArg Prod.fst e)

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
  aesop

/-- Completeness through the constructed height, not at the still absent apex. -/
theorem complete_through (n : ℕ) (hn : n ≤ A.card)
    (hc : ∀ J ∈ Plan.gradedPlan D.plan, J.1 ≠ A → ∃ d : Cell D, D.cell d = J)
    (J : Finset ι × ℕ)
    (hJ : J ∈ Plan.gradedPlan (CanonicalRecursiveInventory.scheme sem n hn).plan)
    (hj : J.2 ≤ n) :
    ∃ d, (CanonicalRecursiveInventory.scheme sem n hn).cell d = J := by
  have hm : J ∈ Plan.gradedPlan D.plan := by
    simpa [CanonicalRecursiveBoundaryTransport.plan_eq] using hJ
  by_cases hs : J.1 = A
  · obtain ⟨d, hd⟩ := full_index sem n hn J.2 (Plan.mem_gradedPlan.mp hm).2.1 hj
    grind
  · obtain ⟨d, hd⟩ := hc J hm hs
    exact ⟨CanonicalRecursiveInventory.boundary sem n hn d,
      (CanonicalRecursiveInventory.boundary_cell sem n hn d).trans hd⟩

end

end VaughtConjecture.Knight.CanonicalRecursiveCoverage
