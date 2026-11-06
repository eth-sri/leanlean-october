/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.GrowthPaddedStepRendering

/-! # Iterated actual padded growth rows and incoming renderings

Each successor returns the invariant it consumes. Starting at the unchanged
checked grade-two carrier therefore constructs the actual one-scope rows and
renderings through every available finite height. This is not a bountifulness
or model-receiving theorem. The recursion is specialized from the checked LOW
construction, with separate donor/private arities and growth admission.
-/

@[expose] public noncomputable section

namespace VaughtConjecture.Knight.GrowthPaddedIteration
open Transform Value ExtOrd Growth GrowthOrderedBase GrowthHigherSources GrowthPaddedContract
open SourcePrefixRows SharpWitnessComposition PairedSlotComparison

variable {ι : Type*} [DecidableEq ι] {A B C : Finset ι}
  {R : Finset (Finset ι)} {m n J : ℕ}
  {I : WholeDonorBoundary.Input A B C R m (n + 1) J}
  {X : RelativeData I.right.scheme I.right.rows I.left.scheme I.left.rows}
  {attach : RootAttachment I.common I.commonLeft I.visibleLeft I.faceLeft
    I.commonRight I.visibleRight I.faceRight X}
  {hA : 2 ≤ A.card} {hB : B ⊂ A} {hC : C ⊂ A} {k : ℕ}

def successor (P : Layer I X attach hA hB hC k) (hk : 2 ≤ k) (hnext : k + 1 ≤ A.card) :
    Layer I X attach hA hB hC (k + 1) where
  carrier := GrowthPaddedStepRows.carrier P hnext
  rows := GrowthPaddedStepRows.rows P hk hnext
  consistent := GrowthPaddedStepRows.consistent P hk hnext
  baseMap := GrowthPaddedStepRendering.baseMap P hnext
  base_mono := (SourceLayerCarrier.old_order _ _ _ _ _).comp P.base_mono
  base_index := GrowthPaddedStepRendering.base_index P hnext
  base_row := GrowthPaddedStepRendering.base_row P hk hnext
  base_respects := GrowthPaddedStepRendering.base_respects P hk hnext
  cases := GrowthPaddedStepRendering.cell_cases P hk hnext
  higher_short := GrowthPaddedStepRendering.higher_short P hk hnext
  render := GrowthPaddedStepRendering.render P hk hnext
  birth := GrowthPaddedStepRendering.birth P
  birth_ranks := GrowthPaddedStepRendering.birth_ranks P
  render_base := GrowthPaddedStepRendering.render_base P hk hnext
  lawful := GrowthPaddedStepRendering.render_lawful P hk hnext
  bound := GrowthPaddedStepRendering.render_bound P hk hnext
  supported := GrowthPaddedStepRendering.render_supported P hk hnext
  agreement {_j} hj S _T hS hT hp ht :=
    GrowthPaddedStepRendering.render_agreement P hk hnext hj S hS hp hT ht
  ceiling_at := GrowthPaddedStepRendering.render_ceiling_at P hk hnext

variable (I X attach hA hB hC)

/-- Closed finite recursion: no layer-readiness or source-lawfulness premise. -/
def build : (t : ℕ) → t + 2 ≤ A.card → Layer I X attach hA hB hC (t + 2)
  | 0, _ => initial I X attach hA hB hC
  | t + 1, ht => successor (build t (by omega)) (by omega) (by omega)

theorem build_plan (t : ℕ) (ht : t + 2 ≤ A.card) :
    (build I X attach hA hB hC t ht).carrier.plan = I.boundary.plan := by
  induction t with
  | zero => rfl
  | succ t ih => exact ih (by omega)
