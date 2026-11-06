
import VaughtConjecture.Knight.PointwiseLabels
/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/

import Mathlib.Tactic

import VaughtConjecture.Knight.GrowthPaddedPrivateLift
import VaughtConjecture.Knight.GrowthPaddedDonorLift
import VaughtConjecture.Knight.GrowthPaddedSupply

/-! # Both all-cap original-face grade-two lifts on unchanged growth rows

Bottom supply is independent. Inactive prescriptions use the capped ambient
and the checked lower lift; active ones use their own asymmetric scalar fibre.
No pair ledger or higher successor is constructed here. The proof structure
follows LowOnlyPaddedOriginalLifts, consuming growth repairs on growth rows.
-/

namespace VaughtConjecture.Knight.GrowthPaddedOriginalLifts
open     Growth
open GrowthPaddedSuccessor GrowthPaddedDecode


variable {ι : Type*} [DecidableEq ι] {A B C : Finset ι}
  {R : VaughtConjecture.AmalgamationPlan.SupportFamily ι} {m n J : ℕ}
  (I : WholeDonorBoundary.Input A B C R m (n + 1) J)
  (X : I.GrowthData)
  (T : I.GrowthAttachment X)
  (hA : 2 ≤ A.card) (hB : B ⊂ A) (hC : C ⊂ A)

local notation "RespectsSemanticsBelow₀" => RespectsSemanticsBelow (rows I X T hA hB hC) (A, 2)

local notation "carrier₀" => carrier I X T hA hB hC

local notation "privateAt₀" => privateAt I X T hA hB hC

theorem private_inactive
    {p}
    {q}
    (hp : RespectsSemanticsBelow I.right.rows (Finset.univ, 2) p)
    (hq : RespectsSemanticsBelow₀ q)
    {γ} (hγ : SelfVis 2 γ)
    (hinactive : ∀ d, I.right.scheme.grade d.1 = 2 → p d ≤ γ)
    (hag : CappedEq (q ∘ privateAt₀) p γ) :
    ∃ r, RespectsSemanticsBelow₀ r ∧
      (PointwiseEq (r ∘ privateAt₀) p) ∧
      CappedEq r q γ := by
  obtain ⟨r, hr, hread, hcap⟩ := GrowthPaddedPrivateLift.restore I X T hA hB hC hp
    (hq.cap hγ) hγ hag (fun _ => min_le_right _ _) hinactive
  exact ⟨r, hr, hread, fun d => (hcap d).trans (by rw [min_assoc, min_self])⟩

/-- All permitted original caps, including bottom and top. The prescription
and ambient are arbitrary lawful inputs; every physical cap is retained. -/
theorem private_lift
    {p}
    {q}
    (hp : RespectsSemanticsBelow I.right.rows (Finset.univ, 2) p)
    (hq : RespectsSemanticsBelow₀ q)
    {γ} (hγ : SelfVis 2 γ)
    (hag : CappedEq (q ∘ privateAt₀) p γ) :
    ∃ r, RespectsSemanticsBelow₀ r ∧
      (PointwiseEq (r ∘ privateAt₀) p) ∧
      CappedEq r q γ := by
  by_cases hz : γ = ⊥
  · obtain ⟨r, hr, hread⟩ := GrowthPaddedSupply.private_bottom_supply I X T hA hB hC hp
    exact ⟨r, hr, hread, fun _ => by simp only [hz, min_bot_right]⟩
  by_cases ha : ∃ d, I.right.scheme.grade d.1 = 2 ∧ γ < p d
  · exact GrowthPaddedPrivateLift.active_private_lift I X T hA hB hC hp hq hγ
      (bot_lt_iff_ne_bot.mpr hz) ha hag
  · aesop (add safe apply [private_inactive])

local notation "donorAt₀" => donorAt I X T hA hB hC

theorem donor_inactive (hN : 1 < X.req.N)
    {p}
    {q}
    (hp : RespectsSemanticsBelow I.left.rows (Finset.univ, 2) p)
    (hq : RespectsSemanticsBelow₀ q)
    {γ} (hγ : SelfVis 2 γ)
    (hinactive : ∀ d, I.left.scheme.grade d.1 = 2 → p d ≤ γ)
    (hag : CappedEq (q ∘ donorAt₀) p γ) :
    ∃ r, RespectsSemanticsBelow₀ r ∧
      (PointwiseEq (r ∘ donorAt₀) p) ∧
      CappedEq r q γ := by
  obtain ⟨r, hr, hread, hcap⟩ := GrowthPaddedDonorLift.restore I X T hA hB hC hN hp
    (hq.cap hγ) hγ hag (fun _ => min_le_right _ _) hinactive
  exact ⟨r, hr, hread, fun d => (hcap d).trans (by rw [min_assoc, min_self])⟩

/-- All permitted original caps, including bottom and top. The prescription
and ambient are arbitrary lawful inputs; every physical cap is retained. -/
theorem donor_lift (hN : 2 < X.req.N)
    {p}
    {q}
    (hp : RespectsSemanticsBelow I.left.rows (Finset.univ, 2) p)
    (hq : RespectsSemanticsBelow₀ q)
    {γ} (hγ : SelfVis 2 γ)
    (hag : CappedEq (q ∘ donorAt₀) p γ) :
    ∃ r, RespectsSemanticsBelow₀ r ∧
      (PointwiseEq (r ∘ donorAt₀) p) ∧
      CappedEq r q γ := by
  by_cases hz : γ = ⊥
  · obtain ⟨r, hr, hread⟩ := GrowthPaddedSupply.donor_bottom_supply I X T hA hB hC hN hp
    exact ⟨r, hr, hread, fun _ => by simp only [hz, min_bot_right]⟩
  by_cases ha : ∃ d, I.left.scheme.grade d.1 = 2 ∧ γ < p d
  · exact GrowthPaddedDonorLift.active_donor_lift I X T hA hB hC hN hp hq hγ
      (bot_lt_iff_ne_bot.mpr hz) ha hag
  · grind only [donor_inactive]


