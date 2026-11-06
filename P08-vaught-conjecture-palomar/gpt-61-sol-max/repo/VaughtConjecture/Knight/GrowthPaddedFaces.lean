/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/

import VaughtConjecture.Knight.GrowthPaddedSuccessor
import VaughtConjecture.Knight.SeparatedLayerFace

/-! # Actual inherited faces of the padded growth successor

Both source layers retain each proper semantic face, including every inherited
owner domain. No bound on the grades of the old schemes is used.
-/

namespace VaughtConjecture.Knight.GrowthPaddedFaces
open    Growth GrowthHigherSources  
open GrowthPaddedSuccessor
noncomputable section

variable {ι : Type*} [DecidableEq ι] {A B C : Finset ι}
  {R : VaughtConjecture.AmalgamationPlan.SupportFamily ι} {m n J : ℕ}
  (I : WholeDonorBoundary.Input A B C R m (n + 1) J)
  (X : I.GrowthData)
  (attach : I.GrowthAttachment X)
  (hA : 2 ≤ A.card) (hB : B ⊂ A) (hC : C ⊂ A)

def face {T : Finset ι} {E : CellScheme T} {oldRows : Semantics E}
    (G : ExactSemanticFace oldRows I.rows) (hT : ¬ A ⊆ T) :
    ExactSemanticFace oldRows (rows I X attach hA hB hC) := by
  let J := input I X attach hA hB hC
  let lowerFace := SeparatedLayerFace.face
    (RelativeLadderLayer.inherited_row I.boundary I.rows (by omega)
      (GrowthOrderedBase.field I) (fields X 1) (GrowthOrderedBase.proper hB hC)) G hT
  exact SeparatedLayerFace.face J.inherited_row lowerFace hT

