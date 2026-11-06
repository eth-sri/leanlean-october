/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.GrowthPaddedStepOriginalLifts

/-! # Closed single-scope growth original-face lifting induction

The unchanged grade-two lifts initialize the actual installed recursion.
Strict donor arity excludes active donor owners at or above activation;
no activated donor fibre, mixed-scope lifting, or output bountifulness is used.
-/

@[expose] public section

set_option autoImplicit false
namespace VaughtConjecture.Knight.GrowthPaddedOriginalInduction
open Transform Value ExtOrd Growth
open GrowthPaddedContract GrowthPaddedIteration
open GrowthPaddedStepPrivateLift (PrivateLowerLift previousPrivateAt)
open GrowthPaddedStepDonorLift (DonorLowerLift previousDonorAt)
noncomputable section

variable {ι : Type*} [DecidableEq ι] {A B C : Finset ι}
  {R : Finset (Finset ι)} {m n J : ℕ}
  (I : WholeDonorBoundary.Input A B C R m (n + 1) J)
  (X : RelativeData I.right.scheme I.right.rows I.left.scheme I.left.rows)
  (T : RootAttachment I.common I.commonLeft I.visibleLeft I.faceLeft
    I.commonRight I.visibleRight I.faceRight X)
  (hA : 2 ≤ A.card) (hB : B ⊂ A) (hC : C ⊂ A)

/-- Strict donor arity, not `2 < N`, suffices for the actual initial carrier.
If a grade-two donor owner exists, its own grade bound supplies `2 < N`.
Otherwise the inactive branch handles every cap, including bottom. -/
theorem initial_donor (hsmall : n + 1 < X.req.N) :
    DonorLowerLift (initial I X T hA hB hC) := by
  intro p q γ hp hq hγ hag
  by_cases hi : ∀ d, I.left.scheme.grade d.1 = 2 → p d ≤ γ
  · exact GrowthPaddedOriginalLifts.donor_inactive I X T hA hB hC
      (by omega) hp hq hγ hi hag
  obtain ⟨d, hd⟩ := not_forall.mp hi
  obtain ⟨hg, _⟩ := not_imp.mp hd
  have hN : 2 < X.req.N := hg ▸ Growth.donor_grade_lt I.left hsmall d.1
  exact GrowthPaddedOriginalLifts.donor_lift I X T hA hB hC hN hp hq hγ hag

section Successor
variable {I X T hA hB hC} {k : ℕ}
  (P : Layer I X T hA hB hC k) (hk : 2 ≤ k) (hnext : k + 1 ≤ A.card)

/-- The next output satisfies the same original-private lifting contract. -/
theorem successor_private (hprev : PrivateLowerLift P) :
    PrivateLowerLift (successor P hk hnext) := fun p q γ hp hq hγ hag => GrowthPaddedStepOriginalLifts.private_lift P hk hnext hprev hp hq hγ hag

/-- The donor recurrence keeps the strict arity bound, not an upward admission
or an activated donor repair assumption. -/
theorem successor_donor (hsmall : n + 1 < X.req.N) (hprev : DonorLowerLift P) :
    DonorLowerLift (successor P hk hnext) := fun p q γ hp hq hγ hag => GrowthPaddedStepOriginalLifts.donor_lift P hk hnext hsmall hprev hp hq hγ hag

end Successor

/-- All-cap private lifting at every constructed height, with no supplied
predecessor lifting or physical rendering premise. -/
theorem build_private (t : ℕ) (ht : t + 2 ≤ A.card) :
    PrivateLowerLift (build I X T hA hB hC t ht) := by
  induction t with
  | zero => exact GrowthPaddedStepPrivateLift.initial_private I X T hA hB hC
  | succ t ih =>
    exact successor_private (build I X T hA hB hC t (by omega))
      (by omega) (by omega) (ih (by omega))

/-- All-cap donor lifting at every constructed height, even at and above
activation. Only the actual donor arity is restricted. -/
theorem build_donor (hsmall : n + 1 < X.req.N) (t : ℕ) (ht : t + 2 ≤ A.card) :
    DonorLowerLift (build I X T hA hB hC t ht) := by
  induction t with
  | zero => exact initial_donor I X T hA hB hC hsmall
  | succ t ih =>
    exact successor_donor (build I X T hA hB hC t (by omega))
      (by omega) (by omega) hsmall (ih (by omega))

