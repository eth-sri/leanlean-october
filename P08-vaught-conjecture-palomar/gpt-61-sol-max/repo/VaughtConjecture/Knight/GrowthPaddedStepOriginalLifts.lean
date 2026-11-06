
import VaughtConjecture.Knight.PointwiseLabels
/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/

import Mathlib.Tactic

import VaughtConjecture.Knight.GrowthPaddedStepPrivateLift
import VaughtConjecture.Knight.GrowthPaddedStepDonorLift
import VaughtConjecture.Knight.GrowthPaddedStepSupply

/-! # All-cap original-face successor lifting on unchanged growth rows

Bottom supply is independent. Inactive prescriptions use the capped ambient
and the predecessor's original-face lift; active ones use their own scalar fibre.
Donor inactivity is tested before bottom supply: strict arity makes the
activated branch inactive without any activated donor repair assumption.
No pair ledger or higher successor is constructed here. The proof structure
follows GrowthPaddedOriginalLifts, consuming the actual higher growth rows.
-/

namespace VaughtConjecture.Knight.GrowthPaddedStepOriginalLifts
open     Growth
open GrowthPaddedContract GrowthPaddedStepRows GrowthPaddedStepDecode


variable {ι : Type*} [DecidableEq ι] {A B C : Finset ι}
  {R : VaughtConjecture.AmalgamationPlan.SupportFamily ι} {m n J : ℕ}
  {I : WholeDonorBoundary.Input A B C R m (n + 1) J}
  {X : I.GrowthData}
  {T : I.GrowthAttachment X}
  {hA : 2 ≤ A.card} {hB : B ⊂ A} {hC : C ⊂ A} {k : ℕ}
  (P : Layer I X T hA hB hC k) (hk : 2 ≤ k) (hnext : k + 1 ≤ A.card)

local notation "RespectsSemanticsBelow₀" => RespectsSemanticsBelow (rows P hk hnext) (A, k + 1)

local notation "SelfVis₀" => SelfVis (k + 1)

theorem private_inactive (hprev : GrowthPaddedStepPrivateLift.PrivateLowerLift P)
    {p}
    {q}
    (hp : RespectsSemanticsBelow I.right.rows (Finset.univ, k + 1) p)
    (hq : RespectsSemanticsBelow₀ q)
    {γ} (hγ : SelfVis₀ γ)
    (hinactive : ∀ d, I.right.scheme.grade d.1 = k + 1 → p d ≤ γ)
    (hag : ∀ d, min (q (privateAt P hnext d)) γ = min (p d) γ) :
    ∃ r, RespectsSemanticsBelow₀ r ∧
      (∀ d, r (privateAt P hnext d) = p d) ∧
      CappedEq r q γ := by
  obtain ⟨r, hr, hread, hcap⟩ := GrowthPaddedStepPrivateLift.restore P hk hnext hprev hp
    (hq.cap hγ) hγ hag (fun _ => min_le_right _ _) hinactive
  exact ⟨r, hr, hread, fun d => (hcap d).trans (by rw [min_assoc, min_self])⟩

/-- All permitted original caps, including bottom and top. The prescription
and ambient are arbitrary lawful inputs; every physical cap is retained. -/
theorem private_lift (hprev : GrowthPaddedStepPrivateLift.PrivateLowerLift P)
    {p}
    {q}
    (hp : RespectsSemanticsBelow I.right.rows (Finset.univ, k + 1) p)
    (hq : RespectsSemanticsBelow₀ q)
    {γ} (hγ : SelfVis₀ γ)
    (hag : ∀ d, min (q (privateAt P hnext d)) γ = min (p d) γ) :
    ∃ r, RespectsSemanticsBelow₀ r ∧
      (∀ d, r (privateAt P hnext d) = p d) ∧
      CappedEq r q γ := by
  by_cases hz : γ = ⊥
  · obtain ⟨r, hr, hread⟩ := GrowthPaddedStepSupply.private_bottom_supply P hk hnext hp
    exact ⟨r, hr, hread, fun _ => by simp only [hz, min_bot_right]⟩
  by_cases ha : ∃ d, I.right.scheme.grade d.1 = k + 1 ∧ γ < p d
  · exact GrowthPaddedStepPrivateLift.active_private_lift P hk hnext hprev hp hq hγ
      (bot_lt_iff_ne_bot.mpr hz) ha hag
  · grind [private_inactive]

theorem donor_inactive (hprev : GrowthPaddedStepDonorLift.DonorLowerLift P)
    {p}
    {q}
    (hp : RespectsSemanticsBelow I.left.rows (Finset.univ, k + 1) p)
    (hq : RespectsSemanticsBelow₀ q)
    {γ} (hγ : SelfVis₀ γ)
    (hinactive : ∀ d, I.left.scheme.grade d.1 = k + 1 → p d ≤ γ)
    (hag : ∀ d, min (q (donorAt P hnext d)) γ = min (p d) γ) :
    ∃ r, RespectsSemanticsBelow₀ r ∧
      (∀ d, r (donorAt P hnext d) = p d) ∧
      CappedEq r q γ := by
  obtain ⟨r, hr, hread, hcap⟩ := GrowthPaddedStepDonorLift.restore P hk hnext hprev hp
    (hq.cap hγ) hγ hag (fun _ => min_le_right _ _) hinactive
  exact ⟨r, hr, hread, fun d => (hcap d).trans (by rw [min_assoc, min_self])⟩

/-- All permitted original caps, including bottom and top. The prescription
and ambient are arbitrary lawful inputs; every physical cap is retained. -/
theorem donor_lift (hsmall : n + 1 < X.req.N)
    (hprev : GrowthPaddedStepDonorLift.DonorLowerLift P)
    {p}
    {q}
    (hp : RespectsSemanticsBelow I.left.rows (Finset.univ, k + 1) p)
    (hq : RespectsSemanticsBelow₀ q)
    {γ} (hγ : SelfVis₀ γ)
    (hag : ∀ d, min (q (donorAt P hnext d)) γ = min (p d) γ) :
    ∃ r, RespectsSemanticsBelow₀ r ∧
      (∀ d, r (donorAt P hnext d) = p d) ∧
      CappedEq r q γ := by
  by_cases hi : ∀ d, I.left.scheme.grade d.1 = k + 1 → p d ≤ γ
  · grind [donor_inactive]
  obtain ⟨d, hd⟩ := not_forall.mp hi
  obtain ⟨hg, hv⟩ := not_imp.mp hd
  have hN  :=
    hg ▸ Growth.donor_grade_lt I.left hsmall d.1
  by_cases hz : γ = ⊥
  · obtain ⟨r, hr, hread⟩ := GrowthPaddedStepSupply.donor_bottom_supply P hk hnext hN hp
    exact ⟨r, hr, hread, fun _ => by simp only [hz, min_bot_right]⟩
  exact GrowthPaddedStepDonorLift.active_donor_lift P hk hnext hN hprev hp hq hγ
    (bot_lt_iff_ne_bot.mpr hz) ⟨d, hg, not_le.mp hv⟩ hag


