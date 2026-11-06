/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.GrowthPaddedAllCutoff
public import VaughtConjecture.Knight.GrowthReplicatedRows

/-! # Fixed-carrier original-contained lifting on the replicated growth rows

KVC's literal lower-domain transport and all-cutoff producers at 3cfacaf are
consumed without changes. Replication retains the cap at each actual copy.
Mixed prescriptions and proper mixed targets remain separate obligations.
-/

@[expose] public section

set_option autoImplicit false
namespace VaughtConjecture.Knight.GrowthReplicatedAllCutoff
open AmalgamationPlan Transform Value ExtOrd Growth CoatomBoundaryExtension
open GrowthPaddedIteration GrowthReplicatedRows
noncomputable section
variable {ι : Type*} [DecidableEq ι] {A B C : Finset ι}
  {R : Finset (Finset ι)} {m n J : ℕ}
  (I : WholeDonorBoundary.Input A B C R m (n + 1) J)
  (X : RelativeData I.right.scheme I.right.rows I.left.scheme I.left.rows)
  (T : RootAttachment I.common I.commonLeft I.visibleLeft I.faceLeft
    I.commonRight I.visibleRight I.faceRight X)
  (hA : 2 ≤ A.card) (hB : B ⊂ A) (hC : C ⊂ A)
  (t : ℕ) (ht : t + 2 ≤ A.card)

theorem private_subface {S : Finset ι} {i j : ℕ}
    (hS : (S, i) ∈ Plan.gradedPlan R) (hSC : S ⊆ C) (hij : i ≤ j) (hj : j ≤ t + 2) :
    CappedLift (rows (build I X T hA hB hC t ht))
      (show GradedLe (S, i) (A, j) from ⟨hSC.trans hC.subset, hij⟩) :=
  lift_to_full (build I X T hA hB hC t ht) _ (Or.inr hSC)
    (GrowthPaddedAllCutoff.private_subface I X T hA hB hC t ht hS hSC hij hj)

theorem donor_subface (hsmall : n + 1 < X.req.N) {S : Finset ι} {i j : ℕ}
    (hS : (S, i) ∈ Plan.gradedPlan R) (hSB : S ⊆ B) (hij : i ≤ j) (hj : j ≤ t + 2) :
    CappedLift (rows (build I X T hA hB hC t ht))
      (show GradedLe (S, i) (A, j) from ⟨hSB.trans hB.subset, hij⟩) :=
  lift_to_full (build I X T hA hB hC t ht) _ (Or.inl hSB)
    (GrowthPaddedAllCutoff.donor_subface I X T hA hB hC hsmall t ht hS hSB hij hj)

