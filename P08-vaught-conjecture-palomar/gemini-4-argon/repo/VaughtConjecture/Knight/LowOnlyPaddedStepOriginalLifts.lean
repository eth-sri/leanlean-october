/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.LowOnlyPaddedStepPrivateLift
public import VaughtConjecture.Knight.LowOnlyPaddedStepDonorLift
public import VaughtConjecture.Knight.LowOnlyPaddedStepSupply

/-! # Both all-cap original-face successor lifts

Independent bottom supply, asymmetric active repairs, and inactive pasting
cover all caps. The lower target-grade invariant is the induction input.
The face-height condition is derived from plan membership in the pair ledger.
-/

@[expose] public noncomputable section

namespace VaughtConjecture.Knight.LowOnlyPaddedStepOriginalLifts
open Transform Value ExtOrd CappedDonor LowOnly CanonicalPairedInverse LowOnlyPaddedContract LowOnlyPaddedStepRows LowOnlyOrderedLadder
open LowOnlyPaddedStepDecode LowOnlyPaddedStepFaces
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

  (hplan : P.carrier.plan = R) (hprev : TargetGradeLifting.Through P.rows k)
include hplan hprev

theorem step_face_lift (hface : k ≤ n) {D : Finset ι} (hD : D ⊂ A) (hDR : D ∈ R)
    {S : SemScheme n} {place : Fin n ↪ ι} (himg : Finset.image place Finset.univ = D)
    (Fface : ExactSemanticFace (PointImageSemantics.rows S.scheme place himg S.rows)
      (rows P hk hnext))
    {faceAt : S.scheme.below (effC n (k + 1)) → (carrier P hnext).below (A, k + 1)}
    {p : S.scheme.below (effC n (k + 1)) → ExtOrd}
    {q : (carrier P hnext).below (A, k + 1) → ExtOrd}
    (hp : RespectsSemanticsBelow S.rows (effC n (k + 1)) p)
    (hq : RespectsSemanticsBelow (rows P hk hnext) (A, k + 1) q)
    {γ : ExtOrd} (hγ : SelfVis (k + 1) γ)
    (hag : ∀ d, min (q (faceAt d)) γ = min (p d) γ)
    (hbot : ∃ r, RespectsSemanticsBelow (rows P hk hnext) (A, k + 1) r ∧
      ∀ d, r (faceAt d) = p d)
    (hact : ⊥ < γ → (∃ d, S.scheme.grade d.1 = k + 1 ∧ γ < p d) →
      ∃ r, RespectsSemanticsBelow (rows P hk hnext) (A, k + 1) r ∧
        (∀ d, r (faceAt d) = p d) ∧ ∀ d, min (r d) γ = min (q d) γ)
    (hid : ∀ d, CellScheme.below.mono
      (show GradedLe (D, k + 1) (A, k + 1) from ⟨hD.subset, le_rfl⟩)
      (fullEquiv S place himg Fface (k + 1) d) = faceAt d :=
      by intro; apply Subtype.ext; rfl) :
    ∃ r, RespectsSemanticsBelow (rows P hk hnext) (A, k + 1) r ∧
      (∀ d, r (faceAt d) = p d) ∧ ∀ d, min (r d) γ = min (q d) γ := by
  by_cases hz : γ = ⊥
  · obtain ⟨r, hr, hread⟩ := hbot
    exact ⟨r, hr, hread, fun _ => by simp only [hz, min_bot_right]⟩
  by_cases ha : ∃ d, S.scheme.grade d.1 = k + 1 ∧ γ < p d
  · exact hact (bot_lt_iff_ne_bot.mpr hz) ha
  let e := fullEquiv S place himg Fface (k + 1)
  let p' := p ∘ e.symm
  have hp' : RespectsSemanticsBelow (rows P hk hnext) (D, k + 1) p' := by
    apply (full_respects_iff S place himg Fface (k + 1) p').mpr
    simpa only [p', e, Function.comp_def, Equiv.symm_apply_apply] using hp
  have hcard : D.card = n := by
    rw [← himg, Finset.card_image_of_injective _ place.injective]
    simp only [Finset.card_univ, Fintype.card_fin]
  have hDmem : (D, k) ∈ Plan.gradedPlan (carrier P hnext).plan := by
    change (D, k) ∈ Plan.gradedPlan P.carrier.plan; rw [hplan]
    exact Plan.mem_gradedPlan.mpr ⟨hDR, by omega, by change k ≤ D.card; omega⟩
  have hAmem : (A, k) ∈ Plan.gradedPlan (carrier P hnext).plan :=
    Plan.mem_gradedPlan.mpr
      ⟨(carrier P hnext).isPlan.domain_mem, by omega, by change k ≤ A.card; omega⟩
  obtain ⟨r, hr, hrc, hrr⟩ := SingleFaceTailRestoration.exists_inactive
    (rows P hk hnext) hD.subset
    (lower_lifting P hk hnext hprev hDmem hAmem ⟨hD.subset, le_rfl⟩ le_rfl)
    hp' hq hγ
    (fun d => by
      obtain ⟨x, rfl⟩ := e.surjective d
      simpa only [p', e, Function.comp_apply, Equiv.symm_apply_apply, hid] using hag x)
    (fun d hd => by
      obtain ⟨x, rfl⟩ := e.surjective d
      simpa only [p', Function.comp_apply, Equiv.symm_apply_apply] using
        le_of_not_gt (fun h => ha ⟨x, ((congrArg Prod.snd (Fface.index x.1)).symm.trans hd), h⟩))
  exact ⟨r, hr, fun d => by
    simpa only [p', e, Function.comp_apply, Equiv.symm_apply_apply, hid] using hrr (e d), hrc⟩

theorem private_lift (hface : k ≤ n)
    {p : I.right.scheme.below (effC n (k + 1)) → ExtOrd}
    {q : (carrier P hnext).below (A, k + 1) → ExtOrd}
    (hp : RespectsSemanticsBelow I.right.rows (effC n (k + 1)) p)
    (hq : RespectsSemanticsBelow (rows P hk hnext) (A, k + 1) q)
    {γ : ExtOrd} (hγ : SelfVis (k + 1) γ)
    (hag : ∀ d, min (q (privateAt P hnext d)) γ = min (p d) γ) :
    ∃ r, RespectsSemanticsBelow (rows P hk hnext) (A, k + 1) r ∧
      (∀ d, r (privateAt P hnext d) = p d) ∧
      ∀ d, min (r d) γ = min (q d) γ :=
  step_face_lift P hk hnext hplan hprev hface hC
    (I.rightPlan_le I.rightScheme.isPlan.domain_mem) I.imageRight
    (privateFace P hk hnext) hp hq hγ hag
    (LowOnlyPaddedStepSupply.private_bottom_supply P hk hnext hp)
    fun hpos ha =>
      LowOnlyPaddedStepPrivateLift.active_private_lift P hk hnext hplan hprev hp hq hγ hpos ha hag

theorem donor_lift (hface : k ≤ n)
    {p : I.left.scheme.below (effC n (k + 1)) → ExtOrd}
    {q : (carrier P hnext).below (A, k + 1) → ExtOrd}
    (hp : RespectsSemanticsBelow I.left.rows (effC n (k + 1)) p)
    (hq : RespectsSemanticsBelow (rows P hk hnext) (A, k + 1) q)
    {γ : ExtOrd} (hγ : SelfVis (k + 1) γ)
    (hag : ∀ d, min (q (donorAt P hnext d)) γ = min (p d) γ) :
    ∃ r, RespectsSemanticsBelow (rows P hk hnext) (A, k + 1) r ∧
      (∀ d, r (donorAt P hnext d) = p d) ∧
      ∀ d, min (r d) γ = min (q d) γ :=
  step_face_lift P hk hnext hplan hprev hface hB
    (I.leftPlan_le I.leftScheme.isPlan.domain_mem) I.imageLeft
    (donorFace P hk hnext) hp hq hγ hag
    (LowOnlyPaddedStepSupply.donor_bottom_supply P hk hnext hp)
    fun hpos ha =>
      LowOnlyPaddedStepDonorLift.active_donor_lift P hk hnext hplan hprev hp hq hγ hpos ha hag
