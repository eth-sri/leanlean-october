/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.GrowthPaddedSuccessor
public import VaughtConjecture.Knight.SeparatedLayerFace

/-! # Actual inherited faces of the padded growth successor

Both source layers retain each proper semantic face, including every inherited
owner domain. No bound on the grades of the old schemes is used.
-/

@[expose] public section

set_option autoImplicit false
namespace VaughtConjecture.Knight.GrowthPaddedFaces
open Transform Value ExtOrd Growth GrowthHigherSources AmalgamationPlan CoatomBoundaryExtension
open GrowthPaddedSuccessor
noncomputable section

variable {ι : Type*} [DecidableEq ι] {A B C : Finset ι}
  {R : Finset (Finset ι)} {m n J : ℕ}
  (I : WholeDonorBoundary.Input A B C R m (n + 1) J)
  (X : RelativeData I.right.scheme I.right.rows I.left.scheme I.left.rows)
  (attach : RootAttachment I.common I.commonLeft I.visibleLeft I.faceLeft
    I.commonRight I.visibleRight I.faceRight X)
  (hA : 2 ≤ A.card) (hB : B ⊂ A) (hC : C ⊂ A)

def face {T : Finset ι} {E : CellScheme T} {oldRows : Semantics E}
    (G : ExactSemanticFace oldRows I.rows) (hT : ¬ A ⊆ T) :
    ExactSemanticFace oldRows (rows I X attach hA hB hC) := by
  let J := input I X attach hA hB hC
  let lowerFace := SeparatedLayerFace.face I.boundary
    (RelativeLadderLayer.Point (X := Field I.right.scheme I.left.scheme) (Q := Catalogue X 1))
    1 Nat.one_pos (by omega) (RelativeLadderLayer.separated I.boundary
      (GrowthOrderedBase.proper I hB hC)) I.rows J.lowerRows
    (RelativeLadderLayer.inherited_row I.boundary I.rows (by omega)
      (GrowthOrderedBase.field I) (fields X 1) (GrowthOrderedBase.proper I hB hC)) G hT
  exact SeparatedLayerFace.face J.lower
    (LadderWeightedSuccessor.Input.Node (U := Catalogue X 2) (V := Empty)) 2
    (by decide) hA J.separation J.lowerRows J.rows J.inherited_row lowerFace hT

