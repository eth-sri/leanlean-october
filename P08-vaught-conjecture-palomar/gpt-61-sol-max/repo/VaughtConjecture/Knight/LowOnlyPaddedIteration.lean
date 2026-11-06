/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/

import VaughtConjecture.Knight.LowOnlyPaddedStepRendering

/-! # Iterated actual padded LOW rows and incoming renderings

Each successor returns the invariant it consumes. Starting at the unchanged
checked grade-two carrier therefore constructs the actual one-scope rows and
renderings through every available finite height. This is not a bountifulness
or model-receiving theorem.
-/

namespace VaughtConjecture.Knight.LowOnlyPaddedIteration
open     LowOnly  LowOnlyPaddedContract

noncomputable section
variable {ι : Type*} [DecidableEq ι] {A B C : Finset ι}
  {R : VaughtConjecture.AmalgamationPlan.SupportFamily ι} {m n K : ℕ}
  {I : WholeDonorBoundary.Input A B C R m n n} {F : LowOnly.Family I.left I.right K}
  {hroot : F.root.Covers I.shared.f I.shared.g}
  {hA : 2 ≤ A.card} {hB : B ⊂ A} {hC : C ⊂ A} {k : ℕ}

local notation "Layer₀" => Layer I F hroot hA hB hC

def successor (P : Layer₀ k) (hk : 2 ≤ k) (hnext : k + 1 ≤ A.card) :
    Layer₀ (k + 1) where
  carrier := LowOnlyPaddedStepRows.carrier P hnext
  rows := LowOnlyPaddedStepRows.rows P hk hnext
  consistent := LowOnlyPaddedStepRows.consistent P hk hnext
  baseMap := LowOnlyPaddedStepRendering.baseMap P hnext
  base_mono := (SourceLayerCarrier.old_order).comp P.base_mono
  base_index := LowOnlyPaddedStepRendering.base_index P hnext
  base_row := LowOnlyPaddedStepRendering.base_row P hk hnext
  base_respects := LowOnlyPaddedStepRendering.base_respects P hk hnext
  cases := LowOnlyPaddedStepRendering.cell_cases P hk hnext
  higher_short := LowOnlyPaddedStepRendering.higher_short P hk hnext
  render := LowOnlyPaddedStepRendering.render P hk hnext
  birth := LowOnlyPaddedStepRendering.birth P
  birth_ranks := LowOnlyPaddedStepRendering.birth_ranks P
  render_base := LowOnlyPaddedStepRendering.render_base P hk hnext
  lawful := LowOnlyPaddedStepRendering.render_lawful P hk hnext
  bound := LowOnlyPaddedStepRendering.render_bound P hk hnext
  supported := LowOnlyPaddedStepRendering.render_supported P hk hnext
  agreement {_j} hj S _T hS hT hp ht :=
    LowOnlyPaddedStepRendering.render_agreement P hk hnext hj S hS hp hT ht
  ceiling_at := LowOnlyPaddedStepRendering.render_ceiling_at P hk hnext

variable (I F hroot hA hB hC)

/-- Closed finite recursion: no layer-readiness or source-lawfulness premise. -/
def build : (t : ℕ) → t + 2 ≤ A.card → Layer₀ (t + 2)
  | 0, _ => initial I F hroot hA hB hC
  | t + 1, ht => successor (build t (by omega)) (by omega) (by omega)

local notation "build₀" => build I F hroot hA hB hC

theorem build_plan t (ht : t + 2 ≤ A.card) :
    (build₀ t ht).carrier.plan = I.boundary.plan := by
  induction t with
  | zero => rfl
  | succ t ih => exact ih (by omega)

def build_consistent t (ht : t + 2 ≤ A.card) :=
  (build₀ t ht).consistent

