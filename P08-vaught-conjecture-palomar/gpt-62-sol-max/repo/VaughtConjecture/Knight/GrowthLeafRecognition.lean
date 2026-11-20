/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.GrowthPaddedSuccessor
public import VaughtConjecture.Knight.GrowthNormalization
public import VaughtConjecture.Knight.SupportLadderBottomReflection
public import VaughtConjecture.Knight.AmbientGradeCharts
public import VaughtConjecture.Knight.SupportLadderBottomReflection

@[expose] public section

namespace VaughtConjecture.Knight.GrowthLeafRecognition

open Transform Value ExtOrd Growth GrowthHigherSources GrowthPaddedSuccessor

open SupportLadderRows LadderScalarRendering SharpWitnessComposition

noncomputable section

theorem card_pos {ι : Type*} {A : Finset ι} (h : 2 ≤ A.card) : 0 < A.card := by omega

variable {ι : Type*} [DecidableEq ι] {A B C : Finset ι}
  {R : Finset (Finset ι)} {m n J : ℕ}
  (I : WholeDonorBoundary.Input A B C R m (n + 1) J)
  (X : I.GrowthData)
  (T : I.GrowthAttachment X)
  (hA : 2 ≤ A.card) (hB : B ⊂ A) (hC : C ⊂ A)

local notation "Fld" => Field I.right.scheme I.left.scheme

local notation "ranks₁" => RelativeLadderLayer.ranks (fields X 1)

local notation "rungs" => RelativeLadderLayer.rungs (X := Fld)

theorem rungs_pos : 0 < rungs := Nat.succ_pos _

variable (p : CellScheme.below (carrier I X T hA hB hC) (A, 2) → ExtOrd)

/-- Finite maxima commute with capping. -/
theorem cap_sup {Y : Type*} [Fintype Y] (g : Y → ExtOrd) (h : ExtOrd) :
    min (Finset.univ.sup g) h = Finset.univ.sup fun y => min (g y) h :=
  Finset.apply_sup_eq_sup_comp_of_linearOrder (fun x => min x h)
    (fun _ _ hxy => min_le_min_right _ hxy) (min_bot_left _)

theorem rank_le_rungs (a : Catalogue X 1) (f : Fld) : ranks₁ a f ≤ rungs :=
  (RelativeLadderLayer.rank_bound (fields X 1) a f).le

/-- The birth anchor's own shadow of `f` is indexed by the rank of `f`. -/
theorem index_shadow_self (a : Catalogue X 1) (f : Fld) :
    SupportLadderRows.index (H := rungs) ranks₁ a (shadow a f) = ranks₁ a f := by
  change min (FiniteProfileControllers.cut rungs (ranks₁ a) (ranks₁ a)) (ranks₁ a f) = _
  rw [FiniteProfileControllers.cut_refl]
  exact min_eq_right (rank_le_rungs I X a f)

variable {p}

/-- The catalogue is nonempty: the zero state is admitted and canonical. -/
def zeroMember (j : ℕ) (hj : 1 ≤ j) : Catalogue X j :=
  Growth.zeroMember X j hj

end

end VaughtConjecture.Knight.GrowthLeafRecognition
