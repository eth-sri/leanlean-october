
import VaughtConjecture.Knight.PointwiseLabels
/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/

import Mathlib.Tactic

import VaughtConjecture.Knight.CanonicalMixedGradeLayers

/-! # The actual lower domain of the canonical two-layer output

Adding the upper layer does not alter the lower-grade domain, its rows, or
availability. These are literal occurrence equivalences, not an assumption
that an arbitrary lower ambient extends to the whole output.
-/

namespace VaughtConjecture.Knight.CanonicalLowerDomain
open    CanonicalMixedGradeLayers
noncomputable section

variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A}
variable (sem : Semantics D) (j : ℕ) (hj : 0 < j) (hjA : j ≤ A.card)
variable (hproper : AvoidsValue D.scope A)
variable (k : ℕ) (hg : BoundedBy D.grade k)
variable (hk : 0 < k) (hkA : k ≤ A.card) (hjk : j < k)

local notation "lowerScheme₀" => lowerScheme sem j hj hjA

local notation "scheme₀" => scheme sem j hj hjA k hk hkA

def upperEquiv (BJ : GradedIndex ι) (hBJ : BJ.2 ≤ j) :
    (lowerScheme₀).below BJ ≃ (scheme₀).below BJ :=
  Equiv.ofBijective (fun d => ⟨oldCell sem j hj hjA k hk hkA d.1, by
    simpa only [oldCell, SourceLayerCarrier.cell_toCell, SourceLayerCarrier.index] using d.2⟩)
    ⟨by
      intro d e he
      exact Subtype.ext ((inherited_order sem j hj hjA k hk hkA).injective
        (congrArg Subtype.val he)), by
      intro d
      have hd : (scheme₀).cell d.1 ≠ (A, k) := by
        intro he
        have hg := d.2.2
        rw [he] at hg
        exact (not_le_of_gt hjk) (hg.trans hBJ)
      obtain ⟨e, he⟩ := SourceLayerCarrier.old_occurrence lowerScheme₀
        (CanonicalFieldLayer.Profile sem k (Cell D) id) k hk hkA d.1 hd
      have hem  := by
        have hm := d.2
        rw [he, SourceLayerCarrier.cell_toCell] at hm
        exact hm
      exact ⟨⟨e, hem⟩, Subtype.ext he.symm⟩⟩

local notation "upperEquiv₀" => upperEquiv sem j hj hjA k hk hkA hjk

theorem upperEquiv_cell (BJ : GradedIndex ι) (hBJ : BJ.2 ≤ j)
    d :
    (scheme₀).cell
      (upperEquiv₀ BJ hBJ d).1 =
      (lowerScheme₀).cell d.1 :=
  SourceLayerCarrier.cell_toCell _ _ _ _ _ (.inl d.1)

local notation "RespectsSemanticsBelow₀" => RespectsSemanticsBelow (rows sem j hj hjA hproper k hg hk hkA hjk)

theorem upper_respects_iff (BJ : GradedIndex ι) (hBJ : BJ.2 ≤ j)
    p :
    RespectsSemanticsBelow (lowerSem sem j hj hjA hproper) BJ p ↔
      RespectsSemanticsBelow₀ BJ
        (p ∘ (upperEquiv₀ BJ hBJ).symm) := by
  apply respects_iff_of_equiv (upperEquiv₀ BJ hBJ)
    (fun d => ?_) (fun d e => ?_) (fun b d _ => ?_) p
  · exact (congrArg Prod.snd (upperEquiv_cell sem j hj hjA k hk hkA hjk BJ hBJ d)).symm
  · simp_all only [CellScheme.scope, upperEquiv_cell]
  · exact (inherited_row sem j hj hjA hproper k hg hk hkA hjk b.1 d).symm

def equiv (BJ : GradedIndex ι) (hBJ : BJ.2 ≤ j) :
    (CanonicalGradeCutSections.lower sem j hj hjA).below BJ ≃
      (scheme₀).below BJ :=
  (GradeCutLayerCarrier.belowEquiv BJ hBJ).trans (upperEquiv₀ BJ hBJ)

theorem respects_iff (BJ : GradedIndex ι) (hBJ : BJ.2 ≤ j)
    p :
    RespectsSemanticsBelow (CanonicalGradeCutSections.lowerRows sem j hj hjA hproper) BJ p ↔
      RespectsSemanticsBelow₀ BJ
        (p ∘ (equiv sem j hj hjA k hk hkA hjk BJ hBJ).symm) := (GradeCutLayerRows.lower_respects_iff D (CanonicalGradeCutSections.Profiles sem j)
    j hj hjA hproper sem (CanonicalGradeCutSections.lowerRows sem j hj hjA hproper)
    (CanonicalGradeCutSections.overlap sem j hj hjA hproper) BJ hBJ p).trans
    (upper_respects_iff sem j hj hjA hproper k hg hk hkA hjk BJ hBJ _)

theorem pullback_respects {BJ : GradedIndex ι} (hBJ : BJ.2 ≤ j)
    {q}
    (hq : RespectsSemanticsBelow₀ BJ q) :
    RespectsSemanticsBelow (CanonicalGradeCutSections.lowerRows sem j hj hjA hproper) BJ
      (q ∘ equiv sem j hj hjA k hk hkA hjk BJ hBJ) := by
  apply (respects_iff sem j hj hjA hproper k hg hk hkA hjk BJ hBJ _).mpr
  simpa only [Function.comp_def, Equiv.apply_symm_apply] using hq

