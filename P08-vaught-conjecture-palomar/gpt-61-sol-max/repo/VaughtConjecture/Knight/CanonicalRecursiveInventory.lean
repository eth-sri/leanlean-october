
import VaughtConjecture.Knight.PointwiseLabels
/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/

import VaughtConjecture.Knight.RecursiveSourceCarrier
import VaughtConjecture.Knight.CanonicalPairBoundary

/-! # Canonical catalogues on a genuinely recursive occurrence inventory

The first two catalogues are exactly the checked seed pair. Higher catalogues
use the entire original field inventory, including future proper-boundary
fields. Lawfulness is checked on the grade actually present.
No completed output is passed back as a proper boundary. Row coupling and
successor bountifulness remain separate from this constructed geometry.
-/

namespace VaughtConjecture.Knight.CanonicalRecursiveInventory

noncomputable section

variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A}
variable (sem : Semantics D)

abbrev UpperProfile j := CanonicalFieldLayer.Profile (GradeCutBoundary.rows D j sem)
  j (Cell D) (GradeCutBoundary.toCell D j)

def Profile : ℕ → Type 1
  | 0 => PUnit
  | 1 => CanonicalPairBoundary.firstProfiles sem 1 2
  | 2 => CanonicalPairBoundary.secondProfiles sem 2
  | n + 3 => UpperProfile sem (n + 3)

instance (j : ℕ) : Fintype (Profile sem j) := by
  rcases j with _ | _ | _ | j <;> dsimp only [Profile] <;> infer_instance

abbrev scheme n (hn : n ≤ A.card) := RecursiveSourceCarrier.scheme D (Profile sem) n hn
abbrev boundary n (hn : n ≤ A.card) :=
  RecursiveSourceCarrier.boundary D (Profile sem) n hn

theorem boundary_cell n (hn : n ≤ A.card) d :
    (scheme sem n hn).cell (boundary sem n hn d) = D.cell d :=
  RecursiveSourceCarrier.boundary_cell D (Profile sem) n hn d

/-- Normalize from the actual current old lower domain; future fields are
retained in the vector but are not required to be lawful at absent owners. -/
def encode {n : ℕ} {p : CellLabels D}
    (hp : RespectsSemanticsBelow sem (A, n + 3) (fun d => p d.1)) (ht : AvoidsValue p ⊤) :
    Profile sem (n + 3) := by
  let j := n + 3
  have hr := GradeCutBoundary.pullback_respects le_rfl hp
  apply CanonicalFieldLayer.encode (GradeCutBoundary.grade_bound) _ ht
  exact hr.toRespects (fun d =>
    ⟨D.scope_subset _, GradeCutBoundary.grade_bound d⟩)

theorem separated (hp : AvoidsValue D.scope A)
    n (hn : n ≤ A.card) d :
    ¬ GradedLe (A, n + 1) ((scheme sem n hn).cell d) :=
  RecursiveSourceCarrier.separated D (Profile sem) hp n hn d

