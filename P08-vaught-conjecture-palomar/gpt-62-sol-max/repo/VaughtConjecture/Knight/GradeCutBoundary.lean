/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.FilteredBoundary
public import VaughtConjecture.Knight.SeparatedSourceLayerCarrier
public import VaughtConjecture.Knight.PairedSlotComparison
public import VaughtConjecture.Knight.CoatomBoundaryExtension

@[expose] public section

namespace VaughtConjecture.Knight.GradeCutBoundary

open Transform Value ExtOrd

noncomputable section

variable {ι : Type*} [DecidableEq ι] {A : Finset ι}

variable (D : CellScheme A) (j : ℕ)

def filter : FilteredBoundary D A where
  keep J := J.2 ≤ j
  decideKeep _ := inferInstance
  down h hJ := h.2.trans hJ
  plan := D.plan
  valid := D.isPlan
  supports d _ := D.cell_mem d

local notation "F" => filter D j

def scheme : CellScheme A := (F).scheme

def toCell : Cell (scheme D j) ↪o Cell D := (F).toCell

theorem grade_bound (d : Cell (scheme D j)) : D.grade (toCell D j d) ≤ j := (F).retained d

theorem exhaustive {d : Cell D} (hd : D.grade d ≤ j) : ∃ c, toCell D j c = d := (F).exhaustive hd

def fromCell (d : Cell D) (hd : D.grade d ≤ j) : Cell (scheme D j) :=
  (exhaustive D j hd).choose

theorem to_from (d : Cell D) (hd : D.grade d ≤ j) :
    toCell D j (fromCell D j d hd) = d := (exhaustive D j hd).choose_spec

def belowEquiv (BJ : Finset ι × ℕ) (hBJ : BJ.2 ≤ j) :
    (scheme D j).below BJ ≃ D.below BJ := (F).belowEquiv BJ hBJ

variable (sem : Semantics D)

def rows : Semantics (scheme D j) := (F).rows sem

theorem respects_iff (BJ : Finset ι × ℕ) (hBJ : BJ.2 ≤ j) (p : (scheme D j).below BJ → ExtOrd) :
    RespectsSemanticsBelow (rows D j sem) BJ p ↔
      RespectsSemanticsBelow sem BJ (p ∘ (belowEquiv D j BJ hBJ).symm) := (F).respects_iff sem BJ hBJ p

theorem pullback_respects {BJ : Finset ι × ℕ} (hBJ : BJ.2 ≤ j)
    {p : D.below BJ → ExtOrd} (hp : RespectsSemanticsBelow sem BJ p) :
    RespectsSemanticsBelow (rows D j sem) BJ (p ∘ belowEquiv D j BJ hBJ) :=
  (F).pullback_respects sem hBJ hp

theorem restrict_respects {p : Cell D → ExtOrd} (hp : RespectsSemantics sem p) :
    RespectsSemantics (rows D j sem) (fun d => p (toCell D j d)) := by
  have hr := (F).pullback_respects sem (J := (A, j)) le_rfl (hp.toBelow (A, j))
  exact hr.toRespects (fun d => ⟨D.scope_subset _, grade_bound D j d⟩)

theorem consistent (hs : sem.IsConsistent) : (rows D j sem).IsConsistent := (F).consistent sem hs

theorem proper (hp : ∀ d : Cell D, D.scope d ≠ A) (d : Cell (scheme D j)) :
    (scheme D j).scope d ≠ A := hp (toCell D j d)

end

end VaughtConjecture.Knight.GradeCutBoundary
