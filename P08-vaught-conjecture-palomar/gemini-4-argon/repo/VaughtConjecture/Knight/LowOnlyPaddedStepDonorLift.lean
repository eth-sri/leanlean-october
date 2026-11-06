/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.LowOnlyPaddedStepDonorRepair
public import VaughtConjecture.Knight.LowOnlyPaddedStepFaces

/-! # Higher active donor lifting from the lower invariant

Donor source repair and independent lower lifting restore the entire donor
prescription, including distinct lower values above the owner and literal top.
-/

@[expose] public noncomputable section

namespace VaughtConjecture.Knight.LowOnlyPaddedStepDonorLift
open Transform Value ExtOrd CappedDonor LowOnly CanonicalPairedInverse LowOnlyPaddedContract LowOnlyPaddedStepRows LowOnlyOrderedLadder
open LowOnlyPaddedStepDecode LowOnlyPaddedStepFaces LowOnlyPaddedStepDonorRepair
open LowOnlyPaddedFaces (fullEquiv full_respects_iff)
open AmalgamationPlan

variable {ι : Type*} [DecidableEq ι] {A B C : Finset ι}
  {R : Finset (Finset ι)} {m n K : ℕ}
  {I : WholeDonorBoundary.Input A B C R m n n} {F : LowOnly.Family I.left I.right K}
  {hroot : ∀ i : Cell I.common.scheme,
    ∃ a : I.left.scheme.below (F.root.A, F.root.A.card),
      a.1 = I.shared.f i ∧ (F.root.face a).1 = I.shared.g i}
  {hA : 2 ≤ A.card} {hB : B ⊂ A} {hC : C ⊂ A} {k : ℕ}
  (P : Layer I F hroot hA hB hC k) (hk : 2 ≤ k) (hnext : k + 1 ≤ A.card)

theorem active_donor_lift
    (hplan : P.carrier.plan = R) (hprev : TargetGradeLifting.Through P.rows k)
    {p : I.left.scheme.below (effC n (k + 1)) → ExtOrd}
    {q : (carrier P hnext).below (A, (k + 1)) → ExtOrd}
    (hp : RespectsSemanticsBelow I.left.rows (effC n (k + 1)) p)
    (hq : RespectsSemanticsBelow (rows P hk hnext) (A, (k + 1)) q)
    {γ : ExtOrd} (hγ : SelfVis (k + 1) γ) (hpos : ⊥ < γ)
    (hactive : ∃ d, I.left.scheme.grade d.1 = (k + 1) ∧ γ < p d)
    (hag : ∀ d, min (q (donorAt P hnext d)) γ = min (p d) γ) :
    ∃ r, RespectsSemanticsBelow (rows P hk hnext) (A, (k + 1)) r ∧
      (∀ d, r (donorAt P hnext d) = p d) ∧
      ∀ d, min (r d) γ = min (q d) γ :=
  active_step_lift P hk hnext hplan hprev hB
    (I.leftPlan_le I.leftScheme.isPlan.domain_mem) I.imageLeft
    (donorFace P hk hnext) hp hq hpos hactive
    fun c hci hg hpc => owner_capped P hk hnext c hci hg hp hq hγ hpos hpc hag
