/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.GrowthFrame
public import VaughtConjecture.Knight.GrowthPaddedIteration
public import VaughtConjecture.Knight.GrowthGradeOneLift
public import VaughtConjecture.Knight.CanonicalCodingSupport

/-! # Coding and literal ordered faces of the recursive padded growth carrier

Each recursive output retains both original semantic faces, with their actual
ordered occurrences and exhaustive lower domains. Coding is derived from the
canonical fields and supported native grid, not merely from shortness. Under
the two-original scope cover, completeness holds through the installed height.
No bountifulness of higher outputs is claimed.
-/

@[expose] public section

namespace VaughtConjecture.Knight.GrowthPaddedInstallation
open Transform Value ExtOrd CappedDonor Growth GrowthOrderedBase GrowthHigherSources
open GrowthPaddedContract GrowthPaddedIteration PaddedTower.Step
open AmalgamationPlan CoatomBoundaryExtension
noncomputable section

variable {ι : Type*} [DecidableEq ι] {A B C : Finset ι}
  {R : Finset (Finset ι)} {m n J : ℕ}
  {I : WholeDonorBoundary.Input A B C R m (n + 1) J}
  {X : I.GrowthData}
  (frame : I.GrowthFrame X)

theorem build_coded t (ht : t+2 ≤ A.card) : (build frame t ht).rows.IsCoded :=
  PaddedTower.Layer.build_coded (F := system frame) I.coded _ _

def face {T} {E : CellScheme T} {oldRows : Semantics E}
    (G : ExactSemanticFace oldRows I.rows) (hT : ¬ A ⊆ T) t (ht : t+2 ≤ A.card) :=
  (build frame t ht).face G hT

def donorFace t (ht : t + 2 ≤ A.card) :
    ExactSemanticFace I.leftRows (build frame t ht).rows :=
  face frame I.leftFace frame.leftProper.not_ge t ht

def privateFace t (ht : t + 2 ≤ A.card) :
    ExactSemanticFace I.rightRows (build frame t ht).rows :=
  face frame I.rightFace frame.rightProper.not_ge t ht

theorem donor_order t (ht : t + 2 ≤ A.card) :
    StrictMono (donorFace frame t ht).map :=
  (build frame t ht).base_mono.comp
    ((SourceLayerCarrier.old_order _ _ _ _ _).comp I.left_order)

theorem private_order t (ht : t + 2 ≤ A.card) :
    StrictMono (privateFace frame t ht).map :=
  (build frame t ht).base_mono.comp
    ((SourceLayerCarrier.old_order _ _ _ _ _).comp I.right_order)

/-- Every installed full-scope grade has an actual owner, obtained from the
constructed ceiling receipt rather than an assumed completeness contract. -/
theorem full_occupied t (ht : t + 2 ≤ A.card) j
    (hj : 1 ≤ j) (hjt : j ≤ t + 2) :
    ∃ d, (build frame t ht).carrier.cell d = (A, j) := by
  exact (build frame t ht).occupied j hj hjt

end
end VaughtConjecture.Knight.GrowthPaddedInstallation
