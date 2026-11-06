/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.ScopeReplicationSemantics
public import VaughtConjecture.Knight.AmbientGradeCharts

/-! # Maximal charts directly on a mixed lower domain

No whole-section extension is used. An actual chart at a mixed index has a
full-scope prototype, and reads the original prototype row through erasure.
-/

@[expose] public noncomputable section

namespace VaughtConjecture.Knight.ScopeReplicationCharts
open AmalgamationPlan Transform Value ExtOrd ScopeReplicationCarrier ScopeReplicationSemantics AmbientGradeCharts

variable {ι : Type*} [DecidableEq ι] {A : Finset ι}
  (D : CellScheme A) (B C : Finset ι)
  (hcover : ∀ c : Cell D, D.scope c ≠ A → D.scope c ⊆ B ∨ D.scope c ⊆ C)
  (sem : Semantics D)

include hcover in
theorem erase_index {U : Finset ι} {j : ℕ} (hm : U = A ∨ Mixed B C U)
    (c : Cell (scheme D B C)) (hc : (scheme D B C).cell c = (U, j)) :
    D.cell (erase D B C c) = (A, j) := by
  apply Prod.ext
  · change D.scope (erase D B C c) = A
    by_contra hne
    have hs : D.scope (erase D B C c) = U :=
      (erase_scope_of_ne D B C c hne).trans (congrArg Prod.fst hc)
    rcases hm with rfl | hm
    · exact hne hs
    · rcases hcover _ hne with hb | hc'
      · exact hm.1 (hs ▸ hb)
      · exact hm.2 (hs ▸ hc')
  · change D.grade (erase D B C c) = j
    exact (erase_grade D B C c).trans (congrArg Prod.snd hc)
