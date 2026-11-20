/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.CanonicalMixedOwnerLift

@[expose] public section

namespace VaughtConjecture.Knight.CanonicalProperDomain

open Transform Value ExtOrd CanonicalMixedGradeLayers CoatomBoundaryExtension

noncomputable section

variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A}

variable (M : Frame D)

local notation "sem" => M.sem
local notation "j" => M.lower
local notation "k" => M.upper
local notation "hj" => M.pos
local notation "hjA" => M.lower_card
local notation "hk" => M.upper_pos
local notation "hkA" => M.height
local notation "hjk" => M.strict
local notation "hg" => M.grade
local notation "hproper" => M.proper

def equiv (BJ : Finset ι × ℕ) (hB : ¬ A ⊆ BJ.1) :
    D.below BJ ≃ (scheme M).below BJ :=
  (GradeCutLayerCarrier.properEquiv D (CanonicalGradeCutSections.Profiles sem j)
    j hj hjA BJ hB).trans
    (GradeCutLayerCarrier.properEquiv (lowerScheme M)
      (CanonicalFieldLayer.Profile sem k (Cell D) id) k hk hkA BJ hB)

theorem equiv_cell (BJ : Finset ι × ℕ) (hB : ¬ A ⊆ BJ.1) (d : D.below BJ) :
    (scheme M).cell (equiv M BJ hB d).1 =
      D.cell d.1 := by
  change (SourceLayerCarrier.scheme _ _ _ _ _).cell
    (SourceLayerCarrier.toCell _ _ _ _ _ (.inl
      (SourceLayerCarrier.toCell _ _ _ _ _ (.inl d.1)))) = _
  simp only [SourceLayerCarrier.cell_toCell, SourceLayerCarrier.index]

theorem respects_iff (BJ : Finset ι × ℕ) (hB : ¬ A ⊆ BJ.1) (p : D.below BJ → ExtOrd) :
    RespectsSemanticsBelow sem BJ p ↔
      RespectsSemanticsBelow (rows M) BJ
        (p ∘ (equiv M BJ hB).symm) := 
  respects_iff_of_index_equiv (equiv M BJ hB)
    (equiv_cell M BJ hB)
    (fun b d _ => (original_row M b.1 d).symm) p

theorem pullback_respects {BJ : Finset ι × ℕ} (hB : ¬ A ⊆ BJ.1)
    {q : (scheme M).below BJ → ExtOrd}
    (hq : RespectsSemanticsBelow (rows M) BJ q) :
    RespectsSemanticsBelow sem BJ (q ∘ equiv M BJ hB) := by
  apply (respects_iff M BJ hB _).mpr
  simpa [Function.comp_def, Equiv.apply_symm_apply] using hq

/-- Every proper-target lifting clause is exactly an old clause. -/
theorem lift {I J : Finset ι × ℕ} (h : GradedLe I J) (hB : ¬ A ⊆ J.1)
    (hlift : CappedLift sem h) :
    CappedLift (rows M) h := by
  have hC : ¬ A ⊆ I.1 := fun hc => hB (hc.trans h.1)
  exact CappedLift.of_equiv (equiv M I hC) (equiv M J hB)
    (fun _ => rfl) le_rfl (respects_iff M I hC)
    (respects_iff M J hB) hlift

end

end VaughtConjecture.Knight.CanonicalProperDomain
