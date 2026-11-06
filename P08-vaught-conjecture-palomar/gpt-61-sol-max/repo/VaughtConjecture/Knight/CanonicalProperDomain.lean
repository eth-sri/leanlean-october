
import VaughtConjecture.Knight.PointwiseLabels
/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/

import Mathlib.Tactic

import VaughtConjecture.Knight.CanonicalMixedOwnerLift

/-! # Exact proper-domain transport through both canonical layers

Neither new layer adds an occurrence to a proper scope. The equivalences below
transport all rows and lawful target-local ambients, not only chosen sections.
-/

namespace VaughtConjecture.Knight.CanonicalProperDomain
open    CanonicalMixedGradeLayers CoatomBoundaryExtension
noncomputable section

variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A}
variable (sem : Semantics D) (j : ℕ) (hj : 0 < j) (hjA : j ≤ A.card)
variable (hproper : AvoidsValue D.scope A)
variable (k : ℕ) (hg : BoundedBy D.grade k)
variable (hk : 0 < k) (hkA : k ≤ A.card) (hjk : j < k)

local notation "scheme₀" => scheme sem j hj hjA k hk hkA

def equiv (BJ : GradedIndex ι) (hB : ¬ A ⊆ BJ.1) :
    D.below BJ ≃ (scheme₀).below BJ :=
  (GradeCutLayerCarrier.properEquiv D (CanonicalGradeCutSections.Profiles sem j)
    j hj hjA BJ hB).trans
    (GradeCutLayerCarrier.properEquiv (lowerScheme sem j hj hjA)
      (CanonicalFieldLayer.Profile sem k (Cell D) id) k hk hkA BJ hB)

local notation "equiv₀" => equiv sem j hj hjA k hk hkA

theorem equiv_cell (BJ : GradedIndex ι) (hB : ¬ A ⊆ BJ.1) d :
    (scheme₀).cell (equiv₀ BJ hB d).1 =
      D.cell d.1 := by
  change (SourceLayerCarrier.scheme _ _ _ _ _).cell
    (SourceLayerCarrier.toCell _ _ _ _ _ (.inl
      (SourceLayerCarrier.toCell _ _ _ _ _ (.inl d.1)))) = _
  simp only [SourceLayerCarrier.cell_toCell, SourceLayerCarrier.index]

local notation "rows₀" => rows sem j hj hjA hproper k hg hk hkA hjk

theorem respects_iff (BJ : GradedIndex ι) (hB : ¬ A ⊆ BJ.1) p :
    RespectsSemanticsBelow sem BJ p ↔
      RespectsSemanticsBelow (rows₀) BJ
        (p ∘ (equiv₀ BJ hB).symm) := by
  apply respects_iff_of_equiv (equiv₀ BJ hB)
    (fun d => ?_) (fun d e => ?_) (fun b d _ => ?_) p
  · exact (congrArg Prod.snd (equiv_cell sem j hj hjA k hk hkA BJ hB d)).symm
  · grind [CellScheme.scope, equiv_cell]
  · exact (original_row sem j hj hjA hproper k hg hk hkA hjk b.1 d).symm

variable {sem j hj hjA hproper k hg hk hkA hjk} in
theorem pullback_respects {BJ : GradedIndex ι} (hB : ¬ A ⊆ BJ.1)
    {q}
    (hq : RespectsSemanticsBelow (rows₀) BJ q) :
    RespectsSemanticsBelow sem BJ (q ∘ equiv₀ BJ hB) := by
  apply (respects_iff sem j hj hjA hproper k hg hk hkA hjk BJ hB _).mpr
  simpa only [Function.comp_def, Equiv.apply_symm_apply] using hq

/-- Every proper-target lifting clause is exactly an old clause. -/
theorem lift {I J} (h : GradedLe I J) (hB : ¬ A ⊆ J.1)
    (hlift : CappedLift sem h) :
    CappedLift (rows₀) h := by
  intro p q γ hp hq hγ hag
  have hC : ¬ A ⊆ I.1 := fun hc => hB (hc.trans h.1)
  let eI := equiv₀ I hC
  let eJ := equiv₀ J hB
  have hm (d : D.below I) :
      eJ (CellScheme.below.mono h d) = CellScheme.below.mono h (eI d) := rfl
  obtain ⟨r, hr, hcap, hread⟩ := hlift (p ∘ eI) (q ∘ eJ) γ
    (pullback_respects hC hp)
    (pullback_respects hB hq) hγ
    (fun d => hag (eI d))
  refine ⟨r ∘ eJ.symm, (respects_iff sem j hj hjA hproper k hg hk hkA hjk J hB r).mp hr,
    fun d => ?_, fun d => ?_⟩
  · simp_all
  · have hd : eJ.symm (CellScheme.below.mono h d) =
        CellScheme.below.mono h (eI.symm d) := by
      grind
    rw [Function.comp_apply, hd, hread]
    exact congrArg p (eI.apply_symm_apply d)

