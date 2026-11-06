/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.GrowthMixedLeafRecognition
public import VaughtConjecture.Knight.GrowthSpareRecognition

set_option linter.privateModule false

/-! # Uncapped recognition on an actual mixed scope

The spare chart is extracted locally, before any hidden original is assigned
a value. Its rank-coded boundary is lawful on the whole ordered boundary.
Together with the independent grade-two leaf chart this gives lawful original
prefixes without a full-scope extension or an admission hypothesis on the input.
The one-scope argument is due to the V-C checkpoint d667dfd; the local assembly
follows growth3 and keeps the installed rows unchanged.
-/

@[expose] public section

set_option autoImplicit false
namespace VaughtConjecture.Knight.GrowthMixedSpareRecognition
open AmalgamationPlan Transform Value ExtOrd Growth GrowthHigherSources GrowthMixedLeafRecognition
open SupportLadderRows LadderScalarRendering SharpWitnessComposition
noncomputable section

variable {ι : Type*} [DecidableEq ι] {A B C : Finset ι}
  {R : Finset (Finset ι)} {m n J : ℕ}
  (I : WholeDonorBoundary.Input A B C R m (n + 1) J)
  (X : RelativeData I.right.scheme I.right.rows I.left.scheme I.left.rows)
  (T : RootAttachment I.common I.commonLeft I.visibleLeft I.faceLeft
    I.commonRight I.visibleRight I.faceRight X)
  (hA : 2 ≤ A.card) (hB : B ⊂ A) (hC : C ⊂ A)

local notation "Fld" => Field I.right.scheme I.left.scheme
local notation "Pt" => RelativeLadderLayer.Point (X := Fld) (Q := Catalogue X 1)
local notation "ranks₁" => RelativeLadderLayer.ranks (fields X 1)
local notation "rungs" => RelativeLadderLayer.rungs (X := Fld)
local notation "spare" => SupportLadderRows.leaf (GrowthLeafRecognition.rungs_pos I)
local notation "Native" => GrowthPaddedSuccessor.carrier I X T hA hB hC
local notation "Carrier" => carrier I X T hA hB hC
local notation "Rows" => rows I X T hA hB hC

variable (U : Finset ι) (hU : U ∈ R)
  (hm : U = A ∨ ScopeReplicationCarrier.Mixed B C U) (hu : 2 ≤ U.card)
local notation "Occ" => CellScheme.below (carrier I X T hA hB hC) (U, 2)
variable {p : CellScheme.below (carrier I X T hA hB hC) (U, 2) → ExtOrd}

section Chart
variable {a : Catalogue X 1} {τ : ExtOrd → ExtOrd} (hτ : Witness (gTop 1) τ)

include hτ

end Chart

end
end VaughtConjecture.Knight.GrowthMixedSpareRecognition
