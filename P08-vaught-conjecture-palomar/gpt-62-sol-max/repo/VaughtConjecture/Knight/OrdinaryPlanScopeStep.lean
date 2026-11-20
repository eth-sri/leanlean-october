/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.OrdinaryScopeOperator

@[expose] public section

namespace VaughtConjecture.Knight.OrdinaryPlanScopeStep

open AmalgamationPlan Transform Value ExtOrd AmalgamatedBoundaryPlan OrdinaryScopeOperator

noncomputable section

variable {ι : Type*} [DecidableEq ι] {A : Finset ι} (s : Step A)

theorem left_proper : A.erase s.a ≠ A :=
  fun he => Finset.notMem_erase s.a A (he.symm ▸ s.ha)

theorem right_proper : A.erase s.b ≠ A :=
  fun he => Finset.notMem_erase s.b A (he.symm ▸ s.hb)

/-- Includes the empty scope; no positive-grade witness is needed for coverage. -/
theorem coverage (T : Finset ι) (hT : T ∈ s.plan) (hTA : T ≠ A) :
    T ⊆ A.erase s.a ∨ T ⊆ A.erase s.b := by
  rcases Finset.mem_union.mp hT with hT | hT
  · rcases Finset.mem_union.mp hT with hT | hT
    · exact Or.inl (s.left_plan.subset_of_mem hT)
    · exact Or.inr (s.right_plan.subset_of_mem hT)
  aesop

theorem left_height {k : ℕ} (hcard : A.card = k + 1) : (A.erase s.a).card = k := by
  rw [Finset.card_erase_of_mem s.ha, hcard]
  omega

theorem right_height {k : ℕ} (hcard : A.card = k + 1) : (A.erase s.b).card = k := by
  rw [Finset.card_erase_of_mem s.hb, hcard]
  omega

end

end VaughtConjecture.Knight.OrdinaryPlanScopeStep
