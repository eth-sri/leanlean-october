/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.Correspondence
public import VaughtConjecture.Knight.Rank
public import Mathlib.SetTheory.Cardinal.Regular
public import Mathlib.SetTheory.Cardinal.Arithmetic

@[expose] public section

namespace VaughtConjecture.Knight

open TypeTower Spectrum Cardinal

theorem blockStage_zero_le_omegaStage : blockStage 0 ≤ omegaStage := by
  rw [blockStage_zero]
  exact le_rfl

/-- The source-stage presentation used by `KnightNatModel`, recast at `blockStage 0`
(the stage of the rank layer, equal to `omegaStage` by `blockStage_zero`). -/
noncomputable def KnightNatModel.atBlockZero (R : KnightNatModel) :
    KnightRealization (blockStage 0) ℕ :=
  R.1.reduct blockStage_zero_le_omegaStage

/-- Rank transport across isomorphism, in the form the quotient descent needs:
isomorphic models have isomorphic block-zero recasts (`Iso.reduct`). -/
theorem KnightNatModel.iso_atBlockZero {R R' : KnightNatModel}
    (hi : Nonempty (R.1.Iso R'.1)) : Nonempty (R.atBlockZero.Iso R'.atBlockZero) := by
  obtain ⟨i⟩ := hi
  exact ⟨i.reduct blockStage_zero_le_omegaStage⟩

end VaughtConjecture.Knight
