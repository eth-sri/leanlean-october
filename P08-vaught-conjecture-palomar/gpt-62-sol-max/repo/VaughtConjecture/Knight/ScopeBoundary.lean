/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.GradeCutBoundary

@[expose] public section

namespace VaughtConjecture.Knight.ScopeBoundary

open AmalgamationPlan Transform Value ExtOrd

noncomputable section

variable {ι : Type*} [DecidableEq ι] {A : Finset ι}

variable (D : CellScheme A) (B : Finset ι) (hB : B ∈ D.plan)

def filter : FilteredBoundary D B where
  keep J := J.1 ⊆ B
  decideKeep _ := inferInstance
  down h hJ := h.1.trans hJ
  plan := Plan.restrictPlan D.plan B
  valid := Plan.restrict_isPlan D.isPlan hB
  supports d h := by
    obtain ⟨hs, hk, hc⟩ := Plan.mem_gradedPlan.mp (D.cell_mem d)
    exact Plan.mem_gradedPlan.mpr ⟨Finset.mem_inter.mpr ⟨hs, Finset.mem_powerset.mpr h⟩, hk, hc⟩

local notation "F" => filter D B hB

def scheme : CellScheme B := (F).scheme

def toCell : Cell (scheme D B hB) ↪o Cell D := (F).toCell

theorem scope_bound (d : Cell (scheme D B hB)) : D.scope (toCell D B hB d) ⊆ B := (F).retained d

theorem exhaustive {d : Cell D} (hd : D.scope d ⊆ B) : ∃ c, toCell D B hB c = d := (F).exhaustive hd

def belowEquiv (BJ : Finset ι × ℕ) (hBJ : BJ.1 ⊆ B) :
    (scheme D B hB).below BJ ≃ D.below BJ := (F).belowEquiv BJ hBJ

variable (sem : Semantics D)

def rows : Semantics (scheme D B hB) := (F).rows sem

theorem respects_iff (BJ : Finset ι × ℕ) (hBJ : BJ.1 ⊆ B)
    (p : (scheme D B hB).below BJ → ExtOrd) :
    RespectsSemanticsBelow (rows D B hB sem) BJ p ↔
      RespectsSemanticsBelow sem BJ (p ∘ (belowEquiv D B hB BJ hBJ).symm) :=
  (F).respects_iff sem BJ hBJ p

theorem consistent (hs : sem.IsConsistent) : (rows D B hB sem).IsConsistent := (F).consistent sem hs

theorem coded (hs : sem.IsCoded) : (rows D B hB sem).IsCoded := fun _ _ => hs _ _

end

end VaughtConjecture.Knight.ScopeBoundary
