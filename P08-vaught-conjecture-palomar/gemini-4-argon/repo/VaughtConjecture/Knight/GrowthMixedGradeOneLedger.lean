/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.GrowthMixedGradeOne
public import VaughtConjecture.Knight.GrowthReplicatedAllCutoff

set_option linter.privateModule false

/-! # The complete same-grade-one ledger on every built growth carrier

Three steps close grade one on the replicated growth carrier.

* **Mixed to mixed** (`cappedLift_to`): for eligible scopes `U ⊆ V`, extend the prescription to the
  full scope (`GrowthMixedGradeOne.lawfulExtension`) and restrict back to `V`; two lawful sections
  below `(V, 1)` agreeing on the `U`-copies agree everywhere, by the same recognition at `V`.
  `ExtensionInjectivity` then gives the capped lift `(U, 1) ≤ (V, 1)`.
* **Original-contained source, mixed target** (`face_to_mixed`): extend the target ambient to the
  full scope, lift the prescription there by KVC's fixed-carrier original-face lift
  (`GrowthReplicatedAllCutoff`, with the explicit strict donor-arity bound on the donor side),
  and restrict the result back to the target; every cap and the literal prescription survive.
* **The ledger** (`ledger`): every grade-one graded pair of the plan on every built carrier —
  original-contained targets by the inherited face lifts, mixed targets by the two steps above.

No row changes, no higher grade, no admission or activation hypothesis beyond KVC's explicit
donor-arity bound. -/

@[expose] public section

set_option autoImplicit false

namespace VaughtConjecture.Knight.GrowthMixedGradeOneLedger

open AmalgamationPlan Transform Value ExtOrd Growth GrowthHigherSources
open GrowthPaddedContract ScopeReplicationCarrier CoatomBoundaryExtension GrowthMixedGradeOne

noncomputable section

variable {ι : Type*} [DecidableEq ι] {A B C : Finset ι}
  {R : Finset (Finset ι)} {m n J : ℕ}
  (I : WholeDonorBoundary.Input A B C R m (n + 1) J)
  (X : RelativeData I.right.scheme I.right.rows I.left.scheme I.left.rows)
  (T : RootAttachment I.common I.commonLeft I.visibleLeft I.faceLeft
    I.commonRight I.visibleRight I.faceRight X)
  (hA : 2 ≤ A.card) (hB : B ⊂ A) (hC : C ⊂ A)

/-! ## Mixed source, mixed target, on any installed layer -/

section Layer

variable {k : ℕ} (P : Layer I X T hA hB hC k)
  (U V : Finset ι) (hU : U ∈ P.carrier.plan) (hV : V ∈ P.carrier.plan)
  (hmU : U = A ∨ Mixed B C U) (hmV : V = A ∨ Mixed B C V) (hUV : U ⊆ V)

local notation "Carrier" => GrowthReplicatedRows.carrier P
local notation "Rows" => GrowthReplicatedRows.rows P

end Layer

/-! ## Original-contained source, mixed target, on a built carrier -/

section Fixed

variable (t : ℕ) (ht : t + 2 ≤ A.card)

local notation "Built" => GrowthPaddedIteration.build I X T hA hB hC t ht
local notation "BRows" =>
  GrowthReplicatedRows.rows (GrowthPaddedIteration.build I X T hA hB hC t ht)

/-! ## The ledger -/

end Fixed

end
end VaughtConjecture.Knight.GrowthMixedGradeOneLedger
