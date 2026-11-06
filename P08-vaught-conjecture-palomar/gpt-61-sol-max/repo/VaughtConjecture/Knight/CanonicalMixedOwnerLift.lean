
import VaughtConjecture.Knight.PointwiseLabels
/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/

import Mathlib.Tactic

import VaughtConjecture.Knight.CanonicalMixedAmbient
import VaughtConjecture.Knight.CanonicalMixedPrefix
import VaughtConjecture.Knight.CanonicalOwnerBoundary
import VaughtConjecture.Knight.RetunedCutDecoding
import VaughtConjecture.Knight.OwnerCap

/-! # An arbitrary-ambient active-owner lift on the canonical carrier

Availability constructs the ambient source; owner locality constructs alignment;
the two old faces construct a boundary completion. A finite clipping ceiling
makes that coded boundary proper without changing its prescription or source
caps. The canonical supported-prefix operator extends it over BOTH controller
layers, then retuned decoding preserves every original ambient cap.

The conclusion reads the prescribed face capped at its owner. Literal readback
therefore follows when that owner dominates the face. Larger prescribed lower-
grade values remain a separate restoration obligation.
-/

namespace VaughtConjecture.Knight.CanonicalMixedOwnerLift
open  Value ExtOrd  CanonicalMixedGradeLayers
open CoatomBoundaryExtension
noncomputable section

variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A}
variable (sem : Semantics D) (j : ℕ) (hj : 0 < j) (hjA : j ≤ A.card)
variable (hproper : AvoidsValue D.scope A)
variable (k : ℕ) (hg : BoundedBy D.grade k)
variable (hk : 0 < k) (hkA : k ≤ A.card) (hjk : j < k)

local notation "lowerOld₀" => lowerOld sem j hj hjA

local notation "oldCell₀" => oldCell sem j hj hjA

abbrev oldTarget (d : Cell D) : CanonicalMixedAmbient.target sem j hj hjA k hk hkA :=
  SourcePrefixAmbient.occurrence (data sem j hj hjA hproper k hg hk hkA hjk)
    (oldCell₀ k hk hkA (lowerOld₀ d))

local notation "oldTarget₀" => oldTarget sem j hj hjA hproper k hg hk hkA hjk

theorem oldTarget_grade d :
    (scheme sem j hj hjA k hk hkA).grade
      (oldTarget₀ d).1 = D.grade d := by
  change (SourceLayerCarrier.scheme _ _ _ _ _).grade
    (SourceLayerCarrier.toCell _ _ _ _ _ (.inl
      (SourceLayerCarrier.toCell _ _ _ _ _ (.inl d)))) = _
  simp only [CellScheme.grade, SourceLayerCarrier.cell_toCell, SourceLayerCarrier.index]

theorem exists_owner_capped_lift c (hc : D.grade c = k)
    {p}
    (hp : Semantics.RowLawful sem c p)
    {q}
    (hq : RespectsSemanticsBelow (rows sem j hj hjA hproper k hg hk hkA hjk) (A, k) q)
    {γ} (hγ : SelfVis k γ) (hγb : γ ≠ ⊥)
    (hag : ∀ e , min (p e) γ =
      min (q (oldTarget₀ e.1)) γ)
    (hpc : γ < p ⟨c, GradedLe.refl _⟩)
    {U V O}
    (hcover : ∀ d , GradedLe (D.cell d) U ∨ GradedLe (D.cell d) V)
    (hcU : GradedLe (D.cell c) U) (hOU : GradedLe O U) (hOV : GradedLe O V)
    (hinter : ∀ d , GradedLe (D.cell d) U → GradedLe (D.cell d) V →
      GradedLe (D.cell d) O)
    (hleft : CappedLift sem hcU) (hright : CappedLift sem hOV)
    (hU : U.2 ≤ k) (hV : V.2 ≤ k) :
    ∃ r ,
      RespectsSemanticsBelow (rows sem j hj hjA hproper k hg hk hkA hjk) (A, k) r ∧
      (∀ e ,
        r (oldTarget₀ e.1) =
          min (p e) (p ⟨c, GradedLe.refl _⟩)) ∧
      CappedEq r q γ := by 
  classical
  let _ := Fintype.ofFinite (D.belowCell c)
  subst k
  let F := data sem j hj hjA hproper (D.grade c) hg hk hkA hjk
  let M := p ⟨c, GradedLe.refl _⟩
  let pp : BelowLabels D (D.cell c) := fun e => min (p e) M
  have hactive  :=
    (AmbientGradeCharts.cap_reaches_iff (hag ⟨c, GradedLe.refl _⟩)).mp hpc.le
  let core2 := oldTarget sem j hj hjA hproper (D.grade c) hg hk hkA hjk
  obtain ⟨a, τ, _, hτ, hbound, _, _, _, _, _, _, _, hambient, _⟩ :=
    CanonicalMixedAmbient.exists_capped_source sem j hj hjA hproper (D.grade c) hg hk hkA
      hjk hq (core2 c)
      (oldTarget_grade sem j hj hjA hproper (D.grade c) hg hk hkA hjk c) hγ hγb hactive
  let core1 := source sem j hj hjA hproper (D.grade c) hg hk hkA hjk
  have hface (e : D.belowCell c) : τ (a.val e.1) = min (p e) γ := by
    have he := hambient (core2 e.1)
    change τ (core1 a
      (oldCell₀ (D.grade c) hk hkA (lowerOld₀ e.1))) = _ at he
    simp_rw [core1, source_boundary] at he
    exact he.trans (hag e).symm
  obtain ⟨h, ρ, δ, u, hhpos, hvis, ⟨B, hB, hBeq⟩, hρ, hγδ, hδM, hδvis,
      hρh, hu, hucap, huface, _, hread, hretune⟩ :=
    CanonicalOwnerBoundary.exists_completion a.property.2 a.property.1 hp
      hcover hOU hinter hleft hright hU hV hτ hγ
      (bot_lt_iff_ne_bot.mpr hγb) hbound hface hpc
  let tail := 2 * Fintype.card (Cell D) + 1
  have hroom : h < ofOrd (Ordinal.omega0 * tail) := by
    rw [hBeq]
    exact ofOrd_lt_ofOrd.mpr (code_add_lt_mul
      (Nat.cast_lt.mpr (by dsimp [tail]; omega)) _)
  obtain ⟨v, hv, hvt, hvcap, hvface⟩ :=
    exists_topFree_aligned_completion hroom hu
      hg huface
  obtain ⟨w, hw, hwold, hwcap⟩ := CanonicalMixedPrefix.exists_section sem j hj hjA hproper
    (D.grade c) hg hk hkA hjk a hv hvt (hB.trans (Nat.le_succ _))
    (fun d => by rw [← hBeq]; exact ((hvcap d).trans (hucap d)).symm)
  have hwcap' (d) : min (w d) h = min (core1 a d) h := by rw [hBeq]; exact hwcap d
  apply RetunedCutDecoding.decode_lift
    ((F.profile_respects (controller sem j hj hjA (D.grade c) hk hkA a)).toBelow _)
    (hw.toBelow _) hq (fun d => F.max_grade d.1) hρ hδvis hγb hγδ hroom hρh.ge
    (fun d => hwcap' d.1)
  · intro d
    exact (hretune _ (source_short sem j hj hjA hproper (D.grade c) hg hk hkA hjk a d.1)).trans
      ((min_eq_left (hbound _)).trans (hambient d))
  · intro e
    change min (pp e) δ = min (ρ (core1 a
      (oldCell₀ (D.grade c) hk hkA (lowerOld₀ e.1)))) δ
    simp_rw [core1, source_boundary]
    dsimp only [pp]
    rw [min_assoc, min_eq_right hδM]
    exact hread e
  · intro e
    have hs : ((fun d => core1 a d.1) ∘
        fun e : D.belowCell c => core2 e.1) = fun e => a.val e.1 := by
      funext e
      exact source_boundary sem j hj hjA hproper (D.grade c) hg hk hkA hjk a e.1
    rw [hs]
    change w (oldCell₀ (D.grade c) hk hkA (lowerOld₀ e.1)) = _
    rw [hwold, hvface e, huface]
    rfl

