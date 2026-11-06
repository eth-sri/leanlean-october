/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/

import VaughtConjecture.Knight.GrowthPaddedAllCutoff
import VaughtConjecture.Knight.GrowthReplicatedRows

/-! # Fixed-carrier original-contained lifting on the replicated growth rows

KVC's literal lower-domain transport and all-cutoff producers at 3cfacaf are
consumed without changes. Replication retains the cap at each actual copy.
Mixed prescriptions and proper mixed targets remain separate obligations.
-/

namespace VaughtConjecture.Knight.GrowthReplicatedAllCutoff
open AmalgamationPlan    Growth 
open GrowthPaddedIteration GrowthReplicatedRows

variable {ι : Type*} [DecidableEq ι] {A B C : Finset ι}
  {R : VaughtConjecture.AmalgamationPlan.SupportFamily ι} {m n J : ℕ}
  (I : WholeDonorBoundary.Input A B C R m (n + 1) J)
  (X : I.GrowthData)
  (T : I.GrowthAttachment X)
  (hA : 2 ≤ A.card) (hB : B ⊂ A) (hC : C ⊂ A)
  (t : ℕ) (ht : t + 2 ≤ A.card)

def private_subface {S} {i j}
    (hS : (S, i) ∈ Plan.gradedPlan R) (hSC : S ⊆ C) (hij : i ≤ j) (hj : j ≤ t + 2) :=
  lift_to_full (build I X T hA hB hC t ht) _ (Or.inr hSC)
    (GrowthPaddedAllCutoff.private_subface I X T hA hB hC t ht hS hSC hij hj)

def donor_subface (hsmall : n + 1 < X.req.N) {S} {i j}
    (hS : (S, i) ∈ Plan.gradedPlan R) (hSB : S ⊆ B) (hij : i ≤ j) (hj : j ≤ t + 2) :=
  lift_to_full (build I X T hA hB hC t ht) _ (Or.inl hSB)
    (GrowthPaddedAllCutoff.donor_subface I X T hA hB hC hsmall t ht hS hSB hij hj)


