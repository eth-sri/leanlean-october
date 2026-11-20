/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.CanonicalMixedGradeLayers

@[expose] public section

namespace VaughtConjecture.Knight.CanonicalLowerDomain

open Transform Value ExtOrd CanonicalMixedGradeLayers

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

def upperEquiv (BJ : Finset ι × ℕ) (hBJ : BJ.2 ≤ j) :
    (lowerScheme M).below BJ ≃ (scheme M).below BJ :=
  SourceLayerCarrier.inheritedEquiv (lowerScheme M) _ k hk hkA BJ
    (fun h => Nat.not_le_of_lt hjk (h.2.trans hBJ))

theorem upperEquiv_cell (BJ : Finset ι × ℕ) (hBJ : BJ.2 ≤ j)
    (d : (lowerScheme M).below BJ) :
    (scheme M).cell
      (upperEquiv M BJ hBJ d).1 =
      (lowerScheme M).cell d.1 :=
  SourceLayerCarrier.cell_toCell _ _ _ _ _ (.inl d.1)

theorem upper_respects_iff (BJ : Finset ι × ℕ) (hBJ : BJ.2 ≤ j)
    (p : (lowerScheme M).below BJ → ExtOrd) :
    RespectsSemanticsBelow (lowerSem M) BJ p ↔
      RespectsSemanticsBelow (rows M) BJ
        (p ∘ (upperEquiv M BJ hBJ).symm) := 
  respects_iff_of_index_equiv (upperEquiv M BJ hBJ)
    (upperEquiv_cell M BJ hBJ)
    (fun b d _ => (inherited_row M b.1 d).symm) p

def equiv (BJ : Finset ι × ℕ) (hBJ : BJ.2 ≤ j) :
    (CanonicalGradeCutSections.lower sem j hj hjA).below BJ ≃
      (scheme M).below BJ :=
  (GradeCutLayerCarrier.belowEquiv D (CanonicalGradeCutSections.Profiles sem j)
    j hj hjA BJ hBJ).trans (upperEquiv M BJ hBJ)

theorem respects_iff (BJ : Finset ι × ℕ) (hBJ : BJ.2 ≤ j)
    (p : (CanonicalGradeCutSections.lower sem j hj hjA).below BJ → ExtOrd) :
    RespectsSemanticsBelow (CanonicalGradeCutSections.lowerRows sem j hj hjA hproper) BJ p ↔
      RespectsSemanticsBelow (rows M) BJ
        (p ∘ (equiv M BJ hBJ).symm) := by
  exact (GradeCutLayerRows.lower_respects_iff D (CanonicalGradeCutSections.Profiles sem j)
    j hj hjA hproper sem (CanonicalGradeCutSections.lowerRows sem j hj hjA hproper)
    (CanonicalGradeCutSections.overlap sem j hj hjA hproper) BJ hBJ p).trans
    (upper_respects_iff M BJ hBJ _)

theorem pullback_respects {BJ : Finset ι × ℕ} (hBJ : BJ.2 ≤ j)
    {q : (scheme M).below BJ → ExtOrd}
    (hq : RespectsSemanticsBelow (rows M) BJ q) :
    RespectsSemanticsBelow (CanonicalGradeCutSections.lowerRows sem j hj hjA hproper) BJ
      (q ∘ equiv M BJ hBJ) := by
  apply (respects_iff M BJ hBJ _).mpr
  simpa [Function.comp_def, Equiv.apply_symm_apply] using hq

end

end VaughtConjecture.Knight.CanonicalLowerDomain
