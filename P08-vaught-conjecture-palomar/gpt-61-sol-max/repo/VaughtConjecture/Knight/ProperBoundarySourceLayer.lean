
import VaughtConjecture.Knight.PointwiseLabels
/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/

import VaughtConjecture.Knight.SeparatedSourceLayerCarrier

/-! # Common-prefix rows over a genuinely mixed proper boundary

The old inventory may contain active owners at the new grade. Every old
occurrence is a boundary coordinate, so the lower section is constructed by
literal readback, not supplied as a future completion. This installs the
full-grade layer; it does not fill missing indices of the support plan.
-/

namespace VaughtConjecture.Knight.ProperBoundarySourceLayer


open SourceLayerCarrier

variable {ι : Type*} [DecidableEq ι] {A : Finset ι}
variable (D : CellScheme A) (sem : Semantics D)
variable (Q : Type*) [Fintype Q] (k : ℕ) (hk : 0 < k) (hA : k ≤ A.card)
variable (hproper : AvoidsValue D.scope A)
noncomputable abbrev carrier := SourceLayerCarrier.scheme D Q k hk hA

noncomputable abbrev old (d : Cell D) : Cell (carrier D Q k hk hA) :=
  toCell D Q k hk hA (.inl d)

noncomputable abbrev ownerEquiv c :=
  SeparatedSourceLayerCarrier.ownerEquiv D Q k hk hA
    (SeparatedSourceLayerCarrier.separated_of_proper D k hproper) c

noncomputable abbrev base : Semantics (carrier D Q k hk hA) :=
  SeparatedSourceLayerCarrier.base D Q k hk hA
    (SeparatedSourceLayerCarrier.separated_of_proper D k hproper) sem

noncomputable def member c :=
  (SeparatedSourceLayerCarrier.controllerEquiv D Q k hk hA
    (SeparatedSourceLayerCarrier.separated_of_proper D k hproper)).symm c

theorem member_controller q :
    member D Q k hk hA hproper (controller D Q k hk hA q) = q :=
  (SeparatedSourceLayerCarrier.controllerEquiv D Q k hk hA
    (SeparatedSourceLayerCarrier.separated_of_proper D k hproper)).symm_apply_apply q

noncomputable def lower (p : Q → CellLabels D) (q : Q)
    (d : Cell (carrier D Q k hk hA)) :=
  match toOcc D Q k hk hA d with
  | .inl x => p q x
  | .inr _ => ⊥

theorem lower_old (p : Q → CellLabels D) (q : Q) (d : Cell D) :
    lower D Q k hk hA p q (old D Q k hk hA d) = p q d := by
  simp  [lower,  ]

variable (p : Q → CellLabels D)
