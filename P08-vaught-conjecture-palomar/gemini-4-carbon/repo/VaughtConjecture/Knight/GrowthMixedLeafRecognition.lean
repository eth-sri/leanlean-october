/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.GrowthLeafRecognition
public import VaughtConjecture.Knight.GrowthReplicatedRows
public import VaughtConjecture.Knight.ScopeReplicationCharts

/-! # Grade-two recognition directly on an actual mixed scope

Extract the maximal chart on the mixed lower domain itself. The old full-scope
carrier is used only to name source prototypes and reuse their row identities;
no lawful section or extension on that carrier is assumed. Hidden and future
fields are read through the complete physical shadow family at this scope.
-/

@[expose] public section

set_option autoImplicit false
namespace VaughtConjecture.Knight.GrowthMixedLeafRecognition
open AmalgamationPlan Transform Value ExtOrd Growth GrowthHigherSources
open SupportLadderRows LadderScalarRendering SharpWitnessComposition
noncomputable section

variable {ι : Type*} [DecidableEq ι] {A B C : Finset ι}
  {R : Finset (Finset ι)} {m n J : ℕ}
  (I : WholeDonorBoundary.Input A B C R m (n + 1) J)
  (X : RelativeData I.right.scheme I.right.rows I.left.scheme I.left.rows)
  (T : RootAttachment I.common I.commonLeft I.visibleLeft I.faceLeft
    I.commonRight I.visibleRight I.faceRight X)
  (hA : 2 ≤ A.card) (hB : B ⊂ A) (hC : C ⊂ A)

abbrev layer := GrowthPaddedContract.initial I X T hA hB hC
abbrev carrier := GrowthReplicatedRows.carrier (layer I X T hA hB hC)
abbrev rows := GrowthReplicatedRows.rows (layer I X T hA hB hC)

variable (U : Finset ι) (hU : U ∈ R)
  (hm : U = A ∨ ScopeReplicationCarrier.Mixed B C U) (hu : 2 ≤ U.card)

local notation "Fld" => Field I.right.scheme I.left.scheme
local notation "Pt" => RelativeLadderLayer.Point (X := Fld) (Q := Catalogue X 1)
local notation "ranks₁" => RelativeLadderLayer.ranks (fields X 1)
local notation "rungs" => RelativeLadderLayer.rungs (X := Fld)
local notation "ceil" => RecursiveRungRendering.ceiling Fld 2
local notation "Occ" => CellScheme.below (carrier I X T hA hB hC) (U, 2)
local notation "Rows" => rows I X T hA hB hC

variable (p : (carrier I X T hA hB hC).below (U, 2) → ExtOrd)

variable {p}

section Chart
variable {a : Catalogue X 2} {σ : ExtOrd → ExtOrd} (hσ : Witness (gTop 2) σ)

include hσ

end Chart

end
end VaughtConjecture.Knight.GrowthMixedLeafRecognition
