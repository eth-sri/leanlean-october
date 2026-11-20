/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.RecursiveSourceCarrier
public import VaughtConjecture.Knight.GradeCutBoundary
public import VaughtConjecture.Knight.CanonicalFieldLayer

/-! # Canonical catalogues on a genuinely recursive occurrence inventory

The catalogues use all original fields at every grade. Lawfulness is checked on the grade cut.
No completed output is passed back as a proper boundary. Row coupling and
successor bountifulness remain separate from this constructed geometry.
-/

@[expose] public section

namespace VaughtConjecture.Knight.CanonicalRecursiveInventory
open Transform Value ExtOrd SourcePrefixRows PairedSlotEncoding
noncomputable section

variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A}
variable (sem : Semantics D)

abbrev Profile (j : ℕ) := CanonicalFieldLayer.Profile (GradeCutBoundary.rows D j sem)
  j (Cell D) (GradeCutBoundary.toCell D j)

abbrev scheme n (hn : n ≤ A.card) := RecursiveSourceCarrier.scheme D (Profile sem) n hn
abbrev boundary n (hn : n ≤ A.card) :=
  RecursiveSourceCarrier.boundary D (Profile sem) n hn

theorem boundary_cell n (hn : n ≤ A.card) d :
    (scheme sem n hn).cell (boundary sem n hn d) = D.cell d :=
  RecursiveSourceCarrier.boundary_cell D (Profile sem) n hn d

/-- Normalize from the actual current old lower domain; future fields are
retained in the vector but are not required to be lawful at absent owners. -/
def encode n {p : D.Labelling}
    (hp : RespectsSemanticsBelow sem (A, n) (fun d => p d.1)) (ht : ∀ d, p d ≠ ⊤) :
    Profile sem n := by
  let j := n
  have hr := GradeCutBoundary.pullback_respects D j sem le_rfl hp
  apply CanonicalFieldLayer.encode (GradeCutBoundary.rows D j sem) j (Cell D)
    (GradeCutBoundary.toCell D j) (GradeCutBoundary.grade_bound D j) _ ht
  exact hr.toRespects (fun d =>
    ⟨D.isPlan.subset_of_mem (D.scope_mem_plan _), GradeCutBoundary.grade_bound D j d⟩)

theorem separated (hp : D.AvoidsScope A)
    n (hn : n ≤ A.card) d :
    ¬ GradedLe (A, n + 1) ((scheme sem n hn).cell d) :=
  RecursiveSourceCarrier.separated D (Profile sem) hp n hn d

end
end VaughtConjecture.Knight.CanonicalRecursiveInventory
