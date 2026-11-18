/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.GrowthMixedSpareRecognition
public import VaughtConjecture.Knight.ScopeReplicationRestriction

set_option linter.privateModule false

/-! # Injective restriction on the actual mixed grade-two growth carrier

Individual auxiliary copies determine the shadow and leaf maxima. Exact
original readback then determines every original coordinate. Thus two lawful
sections equal on a smaller eligible mixed scope are equal on the target.
Lawful capping yields every permitted-cap version without a new repair.
This does not assert existence of a lawful extension.
-/

@[expose] public section

set_option autoImplicit false
namespace VaughtConjecture.Knight.GrowthMixedRestriction
open AmalgamationPlan Transform Value ExtOrd Growth GrowthHigherSources
open GrowthMixedLeafRecognition
noncomputable section
variable {ι : Type*} [DecidableEq ι] {A B C : Finset ι}
  {R : Finset (Finset ι)} {m n J : ℕ}
  (I : WholeDonorBoundary.Input A B C R m (n + 1) J)
  (X : RelativeData I.right.scheme I.right.rows I.left.scheme I.left.rows)
  (T : RootAttachment I.common I.commonLeft I.visibleLeft I.faceLeft
    I.commonRight I.visibleRight I.faceRight X)
  (hA : 2 ≤ A.card) (hB : B ⊂ A) (hC : C ⊂ A)

local notation "Native" => GrowthPaddedSuccessor.carrier I X T hA hB hC
local notation "Carrier" => carrier I X T hA hB hC
local notation "Rows" => rows I X T hA hB hC

variable (U V : Finset ι) (hU : U ∈ R) (hV : V ∈ R)
  (hmU : U = A ∨ ScopeReplicationCarrier.Mixed B C U)
  (hmV : V = A ∨ ScopeReplicationCarrier.Mixed B C V)
  (hu : 2 ≤ U.card) (hv : 2 ≤ V.card) (hUV : U ⊆ V)
  {p q : CellScheme.below (carrier I X T hA hB hC) (V, 2) → ExtOrd}

include hU hV hmU hmV hu hv

end
end VaughtConjecture.Knight.GrowthMixedRestriction
