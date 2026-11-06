
import VaughtConjecture.Knight.PointwiseLabels
/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/

import Mathlib.Tactic

import VaughtConjecture.Knight.PairedBoundarySections

/-! # Exact ordered grade cuts of the retained boundary

Grade restriction filters actual occurrences, not source values. Every lower
domain at a retained grade is unchanged, including all availability witnesses.
The point plan is retained; completeness at grades above the cut is not asserted.
-/

namespace VaughtConjecture.Knight.GradeCutBoundary


noncomputable section

variable {ι : Type*} [DecidableEq ι] {A : Finset ι}
variable (D : CellScheme A) (j : ℕ)

def inventory := Finset.univ.filter (fun d => D.grade d ≤ j)

def scheme : CellScheme A where
  plan := D.plan
  isPlan := D.isPlan
  card := (inventory D j).card
  cell c := D.cell ((inventory D j).orderEmbOfFin rfl c)
  cell_mem _c := D.cell_mem _

local notation "Cell₀" => Cell (scheme D j)

def toCell : Cell₀ ↪o Cell D := (inventory D j).orderEmbOfFin rfl

local notation "toCell₀" => toCell D j

theorem cell_eq d : (scheme D j).cell d = D.cell (toCell₀ d) := rfl

variable {D j} in
theorem grade_bound d : D.grade (toCell₀ d) ≤ j :=
  (Finset.mem_filter.mp ((inventory D j).orderEmbOfFin_mem rfl d)).2

theorem exhaustive {d} (hd : D.grade d ≤ j) : ∃ c, toCell₀ c = d := by
  have hm : d ∈ Set.range ((inventory D j).orderEmbOfFin  rfl) := by
    rw [Finset.range_orderEmbOfFin]
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hd⟩
  exact hm

def fromCell d (hd : D.grade d ≤ j) :=
  (exhaustive D j hd).choose

theorem to_from d (hd : D.grade d ≤ j) :
    toCell₀ (fromCell D j d hd) = d := (exhaustive D j hd).choose_spec

variable {j} in
def belowEquiv (BJ : GradedIndex ι) (hBJ : BJ.2 ≤ j) :
    (scheme D j).below BJ ≃ D.below BJ :=
  Equiv.ofBijective (fun d => ⟨toCell₀ d.1, d.2⟩) ⟨by
    intro a b hab
    have he  :=
      congrArg (fun z => z.1) hab
    exact Subtype.ext ((toCell₀).injective he), by
    intro d
    obtain ⟨c, hc⟩ := exhaustive D j (d.2.2.trans hBJ)
    refine ⟨⟨c, ?_⟩, Subtype.ext hc⟩
    simpa only [cell_eq, hc] using d.2⟩

variable (sem : Semantics D)

def rows : Semantics (scheme D j) where
  E c d := sem.E (toCell₀ c) (belowEquiv D ((scheme D j).cell c) (grade_bound c) d)
  orderly c _d := sem.orderly (toCell₀ c) _

variable {D j} in
theorem respects_iff (BJ : GradedIndex ι) (hBJ : BJ.2 ≤ j)
    p :
    RespectsSemanticsBelow (rows D j sem) BJ p ↔
      RespectsSemanticsBelow sem BJ (p ∘ (belowEquiv D BJ hBJ).symm) :=
  respects_iff_of_equiv (belowEquiv D BJ hBJ) (fun _ => rfl) (fun _ _ => Iff.rfl)
    (fun _ _ _ => rfl) p

variable {D j sem} in
theorem pullback_respects {BJ : GradedIndex ι} (hBJ : BJ.2 ≤ j)
    {p} (hp : RespectsSemanticsBelow sem BJ p) :
    RespectsSemanticsBelow (rows D j sem) BJ (p ∘ belowEquiv D BJ hBJ) := by
  apply (respects_iff sem BJ hBJ _).mpr
  simpa only [Function.comp_def, Equiv.apply_symm_apply] using hp

theorem restrict_respects {p} (hp : RespectsSemantics sem p) :
    RespectsSemantics (rows D j sem) (fun d => p (toCell₀ d)) := by
  have hr := pullback_respects le_rfl (hp.toBelow (A, j))
  exact hr.toRespects (fun d => ⟨D.scope_subset _, grade_bound d⟩)

theorem consistent (hs : sem.IsConsistent) : (rows D j sem).IsConsistent := by solve_by_elim [pullback_respects]

variable {D j} in
theorem proper (hp : AvoidsValue D.scope A) d :
    (scheme D j).scope d ≠ A := hp (toCell₀ d)

