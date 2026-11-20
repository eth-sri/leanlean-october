/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.PaddedStepRendering

@[expose] public section

namespace VaughtConjecture.Knight.Padded

noncomputable section

variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {K : Spec A} {k : ℕ}

def successor (P : Layer K k) (hk : 2 ≤ k) (hnext : k + 1 ≤ A.card) :
    Layer K (k + 1) where
  carrier := StepRows.carrier P hnext
  rows := StepRows.rows P hk hnext
  consistent := StepRows.consistent P hk hnext
  baseMap := StepRendering.baseMap P hnext
  base_mono := (SourceLayerCarrier.old_order _ _ _ _ _).comp P.base_mono
  base_index := StepRendering.base_index P hnext
  base_row := StepRendering.base_row P hk hnext
  base_respects := StepRendering.base_respects P hk hnext
  cases := StepRendering.cell_cases P hk hnext
  higher_short := StepRendering.higher_short P hk hnext
  pos := Nat.succ_pos k
  source := StepRows.source P hk hnext
  controller := StepRows.controller P hnext
  controller_row a := ScopedSourcePrefixLayer.Data.row_new _ (StepRows.controller P hnext a)
  source_leaf := StepRows.source_leaf P hk hnext
  baseAnchor := StepRendering.sourceBirth P
  anchor_ranks := StepRendering.sourceBirth_ranks P
  source_base := StepRendering.source_base P hk hnext
  source_chart := fun {_} => StepRows.exists_chart P hk hnext
  source_lawful := StepRows.source_lawful P hk hnext
  source_supported := StepRows.source_supported P hk hnext
  source_prefix := StepRows.source_agreement P hk hnext
  source_ceiling_at := StepRendering.source_ceiling_at P hk hnext

/-- The entire finite ladder is obtained by iterating the same successor. -/
def build (initial : Layer K 2) : (t : ℕ) → t + 2 ≤ A.card → Layer K (t + 2)
  | 0, _ => initial
  | t + 1, ht => successor (build initial t (by omega)) (by omega) ht

theorem build_plan (initial : Layer K 2) (h : initial.carrier.plan = K.boundary.plan)
    (t : ℕ) (ht : t + 2 ≤ A.card) :
    (build initial t ht).carrier.plan = K.boundary.plan := by
  induction t with
  | zero => exact h
  | succ t ih => tauto

end

end VaughtConjecture.Knight.Padded
