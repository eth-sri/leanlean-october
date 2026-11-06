/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.CanonicalMixedOwnerLift

/-! # Exact proper-domain transport through both canonical layers

Neither new layer adds an occurrence to a proper scope. The equivalences below
transport all rows and lawful target-local ambients, not only chosen sections.
-/

@[expose] public noncomputable section

namespace VaughtConjecture.Knight.CanonicalProperDomain
open Transform Value ExtOrd CanonicalMixedGradeLayers CoatomBoundaryExtension

variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A}
  (sem : Semantics D) (j : ℕ) (hj : 0 < j) (hjA : j ≤ A.card)
  (hproper : ∀ d : Cell D, D.scope d ≠ A)
  (k : ℕ) (hg : ∀ d : Cell D, D.grade d ≤ k)
  (hk : 0 < k) (hkA : k ≤ A.card) (hjk : j < k)

def equiv (BJ : Finset ι × ℕ) (hB : ¬ A ⊆ BJ.1) :
    D.below BJ ≃ (scheme sem j hj hjA k hk hkA).below BJ :=
  (GradeCutLayerCarrier.properEquiv D (CanonicalGradeCutSections.Profiles sem j)
    j hj hjA BJ hB).trans
    (GradeCutLayerCarrier.properEquiv (lowerScheme sem j hj hjA)
      (CanonicalFieldLayer.Profile sem k (Cell D) id) k hk hkA BJ hB)

theorem equiv_cell (BJ : Finset ι × ℕ) (hB : ¬ A ⊆ BJ.1) (d : D.below BJ) :
    (scheme sem j hj hjA k hk hkA).cell (equiv sem j hj hjA k hk hkA BJ hB d).1 =
      D.cell d.1 := by
  change (SourceLayerCarrier.scheme _ _ _ _ _).cell
    (SourceLayerCarrier.toCell _ _ _ _ _ (.inl
      (SourceLayerCarrier.toCell _ _ _ _ _ (.inl d.1)))) = _
  simp only [SourceLayerCarrier.cell_toCell, SourceLayerCarrier.index]

theorem respects_iff (BJ : Finset ι × ℕ) (hB : ¬ A ⊆ BJ.1) (p : D.below BJ → ExtOrd) :
    RespectsSemanticsBelow sem BJ p ↔
      RespectsSemanticsBelow (rows sem j hj hjA hproper k hg hk hkA hjk) BJ
        (p ∘ (equiv sem j hj hjA k hk hkA BJ hB).symm) := by
  apply respects_iff_of_equiv (equiv sem j hj hjA k hk hkA BJ hB)
    (fun d => ?_) (fun d e => ?_) (fun b d _ => ?_) p
  · exact (congrArg Prod.snd (equiv_cell sem j hj hjA k hk hkA BJ hB d)).symm
  · change (D.cell d.1).1 ⊆ (D.cell e.1).1 ↔ _
    simp only [CellScheme.scope, equiv_cell]
  · exact (original_row sem j hj hjA hproper k hg hk hkA hjk b.1 d).symm

theorem pullback_respects {BJ : Finset ι × ℕ} (hB : ¬ A ⊆ BJ.1)
    {q : (scheme sem j hj hjA k hk hkA).below BJ → ExtOrd}
    (hq : RespectsSemanticsBelow (rows sem j hj hjA hproper k hg hk hkA hjk) BJ q) :
    RespectsSemanticsBelow sem BJ (q ∘ equiv sem j hj hjA k hk hkA BJ hB) := by
  apply (respects_iff sem j hj hjA hproper k hg hk hkA hjk BJ hB _).mpr
  simpa only [Function.comp_def, Equiv.apply_symm_apply] using hq

/-- Every proper-target lifting clause is exactly an old clause. -/
theorem lift {I J : Finset ι × ℕ} (h : GradedLe I J) (hB : ¬ A ⊆ J.1)
    (hlift : CappedLift sem h) :
    CappedLift (rows sem j hj hjA hproper k hg hk hkA hjk) h :=
  have hC : ¬ A ⊆ I.1 := fun hc => hB (hc.trans h.1)
  hlift.of_respects_iff (equiv sem j hj hjA k hk hkA I hC) (equiv sem j hj hjA k hk hkA J hB)
    (fun _ => rfl) (respects_iff sem j hj hjA hproper k hg hk hkA hjk I hC)
    (respects_iff sem j hj hjA hproper k hg hk hkA hjk J hB)

