
import VaughtConjecture.Knight.PointwiseLabels
/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/

import Mathlib.Tactic

import VaughtConjecture.Knight.LowOnlyPaddedStepPrivateLift
import VaughtConjecture.Knight.LowOnlyPaddedStepDonorLift
import VaughtConjecture.Knight.LowOnlyPaddedStepSupply

/-! # Both all-cap original-face successor lifts

Independent bottom supply, asymmetric active repairs, and inactive pasting
cover all caps. The lower target-grade invariant is the induction input.
The face-height condition is derived from plan membership in the pair ledger.
-/

namespace VaughtConjecture.Knight.LowOnlyPaddedStepOriginalLifts
open    CappedDonor LowOnly 
open LowOnlyPaddedContract LowOnlyPaddedStepRows 
open LowOnlyPaddedStepDecode LowOnlyPaddedStepFaces
open LowOnlyPaddedFaces (fullEquiv full_respects_iff)
open AmalgamationPlan

variable {ι : Type*} [DecidableEq ι] {A B C : Finset ι}
  {R : VaughtConjecture.AmalgamationPlan.SupportFamily ι} {m n K : ℕ}
  {I : WholeDonorBoundary.Input A B C R m n n} {F : LowOnly.Family I.left I.right K}
  {hroot : F.root.Covers I.shared.f I.shared.g}
  {hA : 2 ≤ A.card} {hB : B ⊂ A} {hC : C ⊂ A} {k : ℕ}
  (P : Layer I F hroot hA hB hC k) (hk : 2 ≤ k) (hnext : k + 1 ≤ A.card)

variable (hplan : P.carrier.plan = R) (hprev : TargetGradeLifting.Through P.rows k)
include hplan hprev

local notation "RespectsSemanticsBelow₀" => RespectsSemanticsBelow (rows P hk hnext) (A, k + 1)

local notation "SelfVis₀" => SelfVis (k + 1)

local notation "effC₀" => effC n (k + 1)

theorem private_inactive (hface : k ≤ n)
    {p}
    {q}
    (hp : RespectsSemanticsBelow I.right.rows (effC₀) p)
    (hq : RespectsSemanticsBelow₀ q)
    {γ} (hγ : SelfVis₀ γ)
    (hinactive : ∀ d, I.right.scheme.grade d.1 = k + 1 → p d ≤ γ)
    (hag : ∀ d, min (q (privateAt P hnext d)) γ = min (p d) γ) :
    ∃ r, RespectsSemanticsBelow₀ r ∧
      (∀ d, r (privateAt P hnext d) = p d) ∧
      CappedEq r q γ := by
  let e := fullEquiv I.right I.placeRight I.imageRight (privateFace P hk hnext) (k + 1)
  let p' := p ∘ e.symm
  have hid (d) : CellScheme.below.mono
      (show GradedLe (C, k + 1) (A, k + 1) from ⟨hC.subset, le_rfl⟩) (e d) =
      privateAt P hnext d := by
    apply Subtype.ext
    rfl
  have hp'  := by
    apply (full_respects_iff I.right I.placeRight I.imageRight
      (privateFace P hk hnext) (k + 1) p').mpr
    change RespectsSemanticsBelow I.right.rows effC₀ ((p ∘ e.symm) ∘ e)
    simpa only [Function.comp_def, Equiv.symm_apply_apply] using hp
  have hcard : C.card = n := by
    rw [← I.imageRight, Finset.card_image_of_injective _ I.placeRight.injective]
    simp only [Finset.card_univ, Fintype.card_fin]
  have hCmem  := by
    change (C, k) ∈ Plan.gradedPlan P.carrier.plan
    rw [hplan]
    exact Plan.mem_gradedPlan.mpr
      ⟨I.rightPlan_le I.rightScheme.isPlan.domain_mem, by omega, by change k ≤ C.card; omega⟩
  have hAmem : (A, k) ∈ Plan.gradedPlan (carrier P hnext).plan :=
    Plan.mem_gradedPlan.mpr
      ⟨(carrier P hnext).isPlan.domain_mem, by omega, by change k ≤ A.card; omega⟩
  obtain ⟨r, hr, hrc, hrr⟩ := SingleFaceTailRestoration.exists_inactive
    (rows P hk hnext) hC.subset
    (lower_lifting P hk hnext hprev hCmem hAmem ⟨hC.subset, le_rfl⟩ le_rfl)
    hp' hq hγ
    (fun d => by
      grind)
    (fun d hd => by
      obtain ⟨x, rfl⟩ := e.surjective d
      have hg'  :=
        (congrArg Prod.snd ((privateFace P hk hnext).index x.1)).symm.trans hd
      simpa only [p', Function.comp_apply, Equiv.symm_apply_apply] using hinactive x hg')
  refine ⟨r, hr, ?_, hrc⟩
  intro d
  simpa only [p', Function.comp_apply, Equiv.symm_apply_apply, hid] using hrr (e d)

theorem private_lift (hface : k ≤ n)
    {p}
    {q}
    (hp : RespectsSemanticsBelow I.right.rows (effC₀) p)
    (hq : RespectsSemanticsBelow₀ q)
    {γ} (hγ : SelfVis₀ γ)
    (hag : ∀ d, min (q (privateAt P hnext d)) γ = min (p d) γ) :
    ∃ r, RespectsSemanticsBelow₀ r ∧
      (∀ d, r (privateAt P hnext d) = p d) ∧
      CappedEq r q γ := by
  by_cases hz : γ = ⊥
  · obtain ⟨r, hr, hread⟩ := LowOnlyPaddedStepSupply.private_bottom_supply P hk hnext hp
    exact ⟨r, hr, hread, fun _ => by simp only [hz, min_bot_right]⟩
  by_cases ha : ∃ d, I.right.scheme.grade d.1 = k + 1 ∧ γ < p d
  · exact LowOnlyPaddedStepPrivateLift.active_private_lift P hk hnext hplan hprev hp hq hγ
      (bot_lt_iff_ne_bot.mpr hz) ha hag
  · grind [private_inactive]

theorem donor_inactive (hface : k ≤ n)
    {p}
    {q}
    (hp : RespectsSemanticsBelow I.left.rows (effC₀) p)
    (hq : RespectsSemanticsBelow₀ q)
    {γ} (hγ : SelfVis₀ γ)
    (hinactive : ∀ d, I.left.scheme.grade d.1 = k + 1 → p d ≤ γ)
    (hag : ∀ d, min (q (donorAt P hnext d)) γ = min (p d) γ) :
    ∃ r, RespectsSemanticsBelow₀ r ∧
      (∀ d, r (donorAt P hnext d) = p d) ∧
      CappedEq r q γ := by
  let e := fullEquiv I.left I.placeLeft I.imageLeft (donorFace P hk hnext) (k + 1)
  let p' := p ∘ e.symm
  have hid (d) : CellScheme.below.mono
      (show GradedLe (B, k + 1) (A, k + 1) from ⟨hB.subset, le_rfl⟩) (e d) =
      donorAt P hnext d := by
    apply Subtype.ext
    rfl
  have hp'  := by
    apply (full_respects_iff I.left I.placeLeft I.imageLeft
      (donorFace P hk hnext) (k + 1) p').mpr
    change RespectsSemanticsBelow I.left.rows effC₀ ((p ∘ e.symm) ∘ e)
    simpa only [Function.comp_def, Equiv.symm_apply_apply] using hp
  have hcard : B.card = n := by
    rw [← I.imageLeft, Finset.card_image_of_injective _ I.placeLeft.injective]
    simp only [Finset.card_univ, Fintype.card_fin]
  have hCmem  := by
    change (B, k) ∈ Plan.gradedPlan P.carrier.plan
    rw [hplan]
    exact Plan.mem_gradedPlan.mpr
      ⟨I.leftPlan_le I.leftScheme.isPlan.domain_mem, by omega, by change k ≤ B.card; omega⟩
  have hAmem : (A, k) ∈ Plan.gradedPlan (carrier P hnext).plan :=
    Plan.mem_gradedPlan.mpr
      ⟨(carrier P hnext).isPlan.domain_mem, by omega, by change k ≤ A.card; omega⟩
  obtain ⟨r, hr, hrc, hrr⟩ := SingleFaceTailRestoration.exists_inactive
    (rows P hk hnext) hB.subset
    (lower_lifting P hk hnext hprev hCmem hAmem ⟨hB.subset, le_rfl⟩ le_rfl)
    hp' hq hγ
    (fun d => by
      grind)
    (fun d hd => by
      obtain ⟨x, rfl⟩ := e.surjective d
      have hg'  :=
        (congrArg Prod.snd ((donorFace P hk hnext).index x.1)).symm.trans hd
      simpa only [p', Function.comp_apply, Equiv.symm_apply_apply] using hinactive x hg')
  refine ⟨r, hr, ?_, hrc⟩
  intro d
  simpa only [p', Function.comp_apply, Equiv.symm_apply_apply, hid] using hrr (e d)

theorem donor_lift (hface : k ≤ n)
    {p}
    {q}
    (hp : RespectsSemanticsBelow I.left.rows (effC₀) p)
    (hq : RespectsSemanticsBelow₀ q)
    {γ} (hγ : SelfVis₀ γ)
    (hag : ∀ d, min (q (donorAt P hnext d)) γ = min (p d) γ) :
    ∃ r, RespectsSemanticsBelow₀ r ∧
      (∀ d, r (donorAt P hnext d) = p d) ∧
      CappedEq r q γ := by
  by_cases hz : γ = ⊥
  · obtain ⟨r, hr, hread⟩ := LowOnlyPaddedStepSupply.donor_bottom_supply P hk hnext hp
    exact ⟨r, hr, hread, fun _ => by simp only [hz, min_bot_right]⟩
  by_cases ha : ∃ d, I.left.scheme.grade d.1 = k + 1 ∧ γ < p d
  · exact LowOnlyPaddedStepDonorLift.active_donor_lift P hk hnext hplan hprev hp hq hγ
      (bot_lt_iff_ne_bot.mpr hz) ha hag
  · grind [donor_inactive]


