
import VaughtConjecture.Knight.PointwiseLabels
/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/

import VaughtConjecture.Knight.CanonicalRecursiveCutPrefix
import VaughtConjecture.Knight.CanonicalOwnerBoundary
import VaughtConjecture.Knight.RetunedCutDecoding
import VaughtConjecture.Knight.OwnerCap

/-! # Constructed active-owner capped lifting on the recursive successor

Owner alignment and old-face completion run on the current boundary cut.
The complete persistent field inventory is retained before recursive prefix
completion. Arbitrary target-local ambient caps survive at every coordinate.
Literal lower restoration is the next composition step.
-/

namespace VaughtConjecture.Knight.CanonicalRecursiveOwnerLift
open  Value ExtOrd  CoatomBoundaryExtension
open CanonicalRecursiveSuccessorRows CanonicalRecursiveCutPrefix

variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A}
variable (sem : Semantics D) (n : ℕ) (hA : n + 4 ≤ A.card)
variable (hproper : AvoidsValue D.scope A)
variable (P : CanonicalRecursiveContract.State sem n (Nat.le_of_succ_le hA))

local notation "cut₀" => cut (D := D) n

local notation "occurrence₀" => occurrence (D := D) n

local notation "oldTarget₀" => oldTarget sem n hA

local notation "source₀" => source sem n hA hproper P

theorem exists_owner_capped_lift
    (c : Cell (cut₀)) (hc : (cut₀).grade c = n + 4)
    {p : (cut₀).belowCell c → ExtOrd}
    (hp : RespectsSemanticsBelow (cutRows sem n) ((cut₀).cell c) p)
    {q}
    (hq : RespectsSemanticsBelow (rows sem n hA hproper P) (A, n + 4) q)
    {γ} (hγ : SelfVis (n + 4) γ) (hγb : γ ≠ ⊥)
    (hag : ∀ e, min (p e) γ = min (q (oldTarget₀ e.1)) γ)
    (hpc : γ < p ⟨c, GradedLe.refl _⟩)
    {U V O}
    (hcover : ∀ d ,
      GradedLe ((cut₀).cell d) U ∨ GradedLe ((cut₀).cell d) V)
    (hcU : GradedLe ((cut₀).cell c) U) (hOU : GradedLe O U) (hOV : GradedLe O V)
    (hinter : ∀ d , GradedLe ((cut₀).cell d) U →
      GradedLe ((cut₀).cell d) V → GradedLe ((cut₀).cell d) O)
    (hleft : CappedLift (cutRows sem n) hcU) (hright : CappedLift (cutRows sem n) hOV)
    (hU : U.2 ≤ n + 4) (hV : V.2 ≤ n + 4) :
    ∃ r ,
      RespectsSemanticsBelow (rows sem n hA hproper P) (A, n + 4) r ∧
      (∀ e, r (oldTarget₀ e.1) = min (p e) (p ⟨c, GradedLe.refl _⟩)) ∧
      CappedEq r q γ := by
  classical
  let _ := Fintype.ofFinite ((cut₀).belowCell c)
  let F := data sem n hA hproper P
  let M := p ⟨c, GradedLe.refl _⟩
  let pp := fun e => min (p e) M
  have hactive : γ ≤ q (oldTarget₀ c) :=
    (AmbientGradeCharts.cap_reaches_iff (hag ⟨c, GradedLe.refl _⟩)).mp hpc.le
  obtain ⟨a, τ, _, hτ, hbound, _, _, _, _, _, _, _, hambient, _⟩ :=
    CanonicalRecursiveAmbient.exists_capped_source sem n hA hproper P hq
      (oldTarget₀ c) ((congrArg Prod.snd (oldTarget_cell sem n hA c)).trans hc)
      hγ hγb hactive
  have hface (e : (cut₀).belowCell c) :
      τ (a.val (occurrence₀ e.1)) = min (p e) γ := by
    have he := hambient (oldTarget₀ e.1)
    change τ (source₀ a
      (boundary sem n hA (occurrence₀ e.1))) = _ at he
    rw [source_boundary] at he
    exact he.trans (hag e).symm
  have H := CanonicalOwnerBoundary.exists_completion (sem := cutRows sem n) (a := a.val)
    (by simpa only [hc] using a.property.2) a.property.1 hp
    hcover hOU hinter hleft hright
    (by simpa only [hc] using hU) (by simpa only [hc] using hV)
    (by simpa only [hc] using hτ) (by simpa only [hc] using hγ)
    (bot_lt_iff_ne_bot.mpr hγb) hbound hface hpc
  simp only [hc] at H
  obtain ⟨h, ρ, δ, u, _, _, ⟨B, hB, hBeq⟩, hρ, hγδ, hδM, hδvis,
      hρh, hu, hucap, huface, _, hread, hretune⟩ := H
  let tail := 2 * Fintype.card (Cell D) + 1
  have hroom : h < ofOrd (Ordinal.omega0 * tail) := by
    rw [hBeq]
    exact ofOrd_lt_ofOrd.mpr (code_add_lt_mul
      (Nat.cast_lt.mpr (by dsimp [tail]; omega)) _)
  obtain ⟨v, hv, hvt, hvcap, hvface⟩ :=
    exists_topFree_aligned_completion hroom hu
      (GradeCutBoundary.grade_bound) huface
  obtain ⟨w, hw, hwold, hwcap⟩ := CanonicalRecursiveCutPrefix.exists_section
    sem n hA hproper P a hv hvt (hB.trans (Nat.le_succ _))
    (fun d => by rw [← hBeq]; exact ((hvcap d).trans (hucap d)).symm)
  have hwcap' (d) : min (w d) h = min (source₀ a d) h := by
    rw [hBeq]
    exact hwcap d
  apply RetunedCutDecoding.decode_lift
    (F.profile_respects (controller sem n hA a))
    hw hq (fun d => d.2.2) hρ hδvis hγb hγδ hroom hρh.ge
    (fun d => hwcap' d.1)
  · intro d
    exact (hretune _ (source_short sem n hA hproper P a d.1)).trans
      ((min_eq_left (hbound _)).trans (hambient d))
  · intro e
    change min (pp e) δ = min (ρ (source₀ a
      (boundary sem n hA (occurrence₀ e.1)))) δ
    rw [source_boundary]
    dsimp only [pp]
    rw [min_assoc, min_eq_right hδM]
    exact hread e
  · intro e
    have hs : ((fun d => source₀ a d.1) ∘
        fun e : (cut₀).belowCell c => oldTarget₀ e.1) =
        fun e => a.val (occurrence₀ e.1) := by
      funext e
      exact source_boundary sem n hA hproper P a (occurrence₀ e.1)
    rw [hs]
    change w (oldTarget₀ e.1).1 = _
    rw [hwold, hvface e, huface]


