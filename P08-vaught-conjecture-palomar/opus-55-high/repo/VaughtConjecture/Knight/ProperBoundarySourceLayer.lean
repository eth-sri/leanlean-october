/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.SeparatedSourceLayerCarrier

/-! # Common-prefix rows over a genuinely mixed proper boundary

The old inventory may contain active owners at the new grade. Every old
occurrence is a boundary coordinate, so the lower section is constructed by
literal readback, not supplied as a future completion. This installs the
full-grade layer; it does not fill missing indices of the support plan.
-/

@[expose] public section

namespace VaughtConjecture.Knight.ProperBoundarySourceLayer

open Transform Value ExtOrd SourcePrefixRows
open SourceLayerCarrier

variable {ι : Type*} [DecidableEq ι] {A : Finset ι}
variable (D : CellScheme A) (sem : Semantics D)
variable (Q : Type*) [Fintype Q] (k : ℕ) (hk : 0 < k) (hA : k ≤ A.card)
variable (hproper : ∀ d : Cell D, D.scope d ≠ A)

noncomputable abbrev carrier := SourceLayerCarrier.scheme D Q k hk hA

noncomputable abbrev old (d : Cell D) : Cell (carrier D Q k hk hA) :=
  toCell D Q k hk hA (.inl d)

noncomputable abbrev ownerEquiv (c : Cell D) :=
  SeparatedSourceLayerCarrier.ownerEquiv D Q k hk hA
    (SeparatedSourceLayerCarrier.separated_of_proper D k hproper) c

noncomputable abbrev base : Semantics (carrier D Q k hk hA) :=
  SeparatedSourceLayerCarrier.base D Q k hk hA
    (SeparatedSourceLayerCarrier.separated_of_proper D k hproper) sem

noncomputable def member (c : SourcePrefixLayer.Controller (carrier D Q k hk hA) k) : Q :=
  (SeparatedSourceLayerCarrier.controllerEquiv D Q k hk hA
    (SeparatedSourceLayerCarrier.separated_of_proper D k hproper)).symm c

theorem member_controller q :
    member D Q k hk hA hproper (controller D Q k hk hA q) = q :=
  (SeparatedSourceLayerCarrier.controllerEquiv D Q k hk hA
    (SeparatedSourceLayerCarrier.separated_of_proper D k hproper)).symm_apply_apply q

section
variable (p : Q → Cell D → ExtOrd) (q : Q)

noncomputable def lower (d : Cell (carrier D Q k hk hA)) : ExtOrd :=
  match toOcc D Q k hk hA d with
  | .inl x => p q x
  | .inr _ => ⊥

theorem lower_old d :
    lower D Q k hk hA p q (old D Q k hk hA d) = p q d := by
  simp only [lower, old, toOcc_toCell]

end

end VaughtConjecture.Knight.ProperBoundarySourceLayer
