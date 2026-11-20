/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.LowFrame
public import VaughtConjecture.Knight.LowOnlyPaddedIteration
public import VaughtConjecture.Knight.LowOnlyOrderedSources
public import VaughtConjecture.Knight.CanonicalCodingSupport

/-! # Coding and literal ordered faces of the recursive padded LOW carrier

Each recursive output retains both original semantic faces, with their actual
ordered occurrences and exhaustive lower domains. Coding is derived from the
canonical fields and supported native grid, not merely from shortness. Under
the two-original scope cover, completeness holds through the installed height.
No bountifulness of higher outputs is claimed.
-/

@[expose] public section

namespace VaughtConjecture.Knight.LowOnlyPaddedInstallation
open Transform Value ExtOrd CappedDonor LowOnly LowOnlyOrderedLadder
open LowOnlyPaddedContract LowOnlyPaddedIteration PaddedTower.Step
open AmalgamationPlan CoatomBoundaryExtension
noncomputable section

variable {ι : Type*} [DecidableEq ι] {A B C : Finset ι}
  {R : Finset (Finset ι)} {m n K : ℕ}
  {I : WholeDonorBoundary.Input A B C R m n n} {F : LowOnly.Family I.left I.right K}
  (frame : I.LowFrame F)

theorem build_coded (t : ℕ) (ht : t+2 ≤ A.card) : (build frame t ht).rows.IsCoded :=
  PaddedTower.Layer.build_coded (F := system frame) I.coded _ _

def face {T : Finset ι} {E : CellScheme T} {oldRows : Semantics E}
    (G : ExactSemanticFace oldRows I.rows) (hT : ¬ A ⊆ T) (t : ℕ) (ht : t+2 ≤ A.card) :=
  (build frame t ht).face G hT

def donorFace (t : ℕ) (ht : t + 2 ≤ A.card) :
    ExactSemanticFace I.leftRows (build frame t ht).rows :=
  face frame I.leftFace frame.leftProper.not_ge t ht

def privateFace (t : ℕ) (ht : t + 2 ≤ A.card) :
    ExactSemanticFace I.rightRows (build frame t ht).rows :=
  face frame I.rightFace frame.rightProper.not_ge t ht

theorem donor_order (t : ℕ) (ht : t + 2 ≤ A.card) :
    StrictMono (donorFace frame t ht).map :=
  (build frame t ht).base_mono.comp
    ((SourceLayerCarrier.old_order _ _ _ _ _).comp I.left_order)

theorem private_order (t : ℕ) (ht : t + 2 ≤ A.card) :
    StrictMono (privateFace frame t ht).map :=
  (build frame t ht).base_mono.comp
    ((SourceLayerCarrier.old_order _ _ _ _ _).comp I.right_order)

end
end VaughtConjecture.Knight.LowOnlyPaddedInstallation
