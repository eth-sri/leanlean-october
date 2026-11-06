/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/

import Mathlib.Tactic

import VaughtConjecture.Knight.LowOnlyPaddedStepDecode
import VaughtConjecture.Knight.LowOnlyPaddedLiftingReady

/-! # Literal original faces through the padded tower

Each original face retains its entire old domain and rows. Lower target-grade
lifting transports through the actual installation, without a global grade
bound on retained proper owners.
-/

namespace VaughtConjecture.Knight.LowOnlyPaddedStepFaces
open     LowOnly 
open LowOnlyPaddedContract LowOnlyPaddedStepRows LowOnlyOrderedLadder
open LowOnlyPaddedDecode (grid_fixed_below)
noncomputable section
variable {ι : Type*} [DecidableEq ι] {A B C : Finset ι}
  {R : VaughtConjecture.AmalgamationPlan.SupportFamily ι} {m n K : ℕ}
  {I : WholeDonorBoundary.Input A B C R m n n} {F : LowOnly.Family I.left I.right K}
  {hroot : F.root.Covers I.shared.f I.shared.g}
  {hA : 2 ≤ A.card} {hB : B ⊂ A} {hC : C ⊂ A} {k : ℕ}
  (P : Layer I F hroot hA hB hC k) (hk : 2 ≤ k) (hnext : k + 1 ≤ A.card)

/-- Literal faces survive the entire installed tower, not just its field readings. -/
def layerFace {T : Finset ι} {E : CellScheme T} {oldRows : Semantics E}
    (G : ExactSemanticFace oldRows I.rows) (hT : ¬ A ⊆ T) :
    ExactSemanticFace oldRows P.rows := by
  let L := SeparatedLayerFace.face
    (RelativeLadderLayer.inherited_row I.boundary I.rows (by omega)
      (field I) (F.fields 1) (LowOnlyOrderedLadder.proper hB hC)) G hT
  exact {
    map := L.map.trans ⟨P.baseMap, P.base_mono.injective⟩
    index := fun d => (P.base_index _).trans (L.index d)
    exhaustive := fun z hz => by
      rcases P.cases z with ⟨d, rfl⟩ | ⟨hs, _, _⟩
      · obtain ⟨c, rfl⟩ := L.exhaustive d (by
          change (P.carrier.cell (P.baseMap d)).1 ⊆ T at hz
          rwa [P.base_index] at hz)
        exact ⟨c, rfl⟩
      · exact False.elim (hT (hs ▸ hz))
    row := fun c d => (P.base_row (L.map c)
      ⟨L.map d.1, by rw [L.index, L.index]; exact d.2⟩).trans (L.row c d) }

local notation "rows₀" => rows P hk hnext

def face {T : Finset ι} {E : CellScheme T} {oldRows : Semantics E}
    (G : ExactSemanticFace oldRows I.rows) (hT : ¬ A ⊆ T) :
    ExactSemanticFace oldRows (rows₀) :=
  SeparatedLayerFace.face
    (inherited_row P hk hnext) (layerFace P G hT) hT

def privateFace :=
  face P hk hnext I.rightFace hC.not_ge

def donorFace :=
  face P hk hnext I.leftFace hB.not_ge

/-- Every lower pair transfers through these actual installed rows. -/
theorem lower_lifting (hprev : TargetGradeLifting.Through P.rows k) :
    TargetGradeLifting.Through (rows₀) k :=
  TargetGradeLifting.through_separated P.rows (F.Anchor (k + 1)) (k + 1)
    (Nat.succ_pos k) hnext (P.separated I F hroot hA hB hC (by omega))
    (rows₀) (inherited_row P hk hnext) (Nat.lt_succ_self k) hprev

