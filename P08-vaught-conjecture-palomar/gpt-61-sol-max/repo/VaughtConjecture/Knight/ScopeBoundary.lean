/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/

import Mathlib.Tactic

import VaughtConjecture.Knight.GradeCutBoundary

/-! # Literal restriction to a point scope without changing point names

This restriction keeps the actual ordered occurrences whose supports lie in
`B`. Every retained owner's entire lower domain is preserved. It is used before
installing a full-scope source layer on a proper mixed scope of a larger carrier.
-/

namespace VaughtConjecture.Knight.ScopeBoundary
open AmalgamationPlan   
noncomputable section
variable {ι : Type*} [DecidableEq ι] {A : Finset ι}
variable (D : CellScheme A) (B : Finset ι) (hB : B ∈ D.plan)

def inventory := Finset.univ.filter (fun d => D.scope d ⊆ B)

local notation "inventory₀" => inventory D B

def scheme : CellScheme B where
  plan := Plan.restrictPlan D.plan B
  isPlan := Plan.restrict_isPlan D.isPlan hB
  card := (inventory₀).card
  cell c := D.cell ((inventory₀).orderEmbOfFin rfl c)
  cell_mem c := by
    obtain ⟨hs, hk, hc⟩ := Plan.mem_gradedPlan.mp
      (D.cell_mem ((inventory₀).orderEmbOfFin rfl c))
    exact Plan.mem_gradedPlan.mpr ⟨Finset.mem_inter.mpr
      ⟨hs, Finset.mem_powerset.mpr
        (Finset.mem_filter.mp ((inventory₀).orderEmbOfFin_mem rfl c)).2⟩, hk, hc⟩

local notation "scheme₀" => scheme D B hB

def toCell : Cell (scheme₀) ↪o Cell D := (inventory₀).orderEmbOfFin rfl

local notation "toCell₀" => toCell D B hB

theorem cell_eq d :
    (scheme₀).cell d = D.cell (toCell₀ d) := rfl

theorem scope_bound d : D.scope (toCell₀ d) ⊆ B :=
  (Finset.mem_filter.mp ((inventory₀).orderEmbOfFin_mem rfl d)).2

theorem exhaustive {d} (hd : D.scope d ⊆ B) : ∃ c, toCell₀ c = d := by
  have hm : d ∈ Set.range ((inventory₀).orderEmbOfFin  rfl) := by
    rw [Finset.range_orderEmbOfFin]
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hd⟩
  exact hm

def belowEquiv {BJ : GradedIndex ι} (hBJ : BJ.1 ⊆ B) :
    (scheme₀).below BJ ≃ D.below BJ :=
  Equiv.ofBijective (fun d => ⟨toCell₀ d.1, d.2⟩) ⟨by
    intro a b hab
    exact Subtype.ext ((toCell₀).injective
      (congrArg (fun z => z.1) hab)), by
    intro d
    obtain ⟨c, hc⟩ := exhaustive D B hB (d.2.1.trans hBJ)
    refine ⟨⟨c, ?_⟩, Subtype.ext hc⟩
    simpa only [cell_eq, hc] using d.2⟩

variable (sem : Semantics D)

def rows : Semantics (scheme₀) where
  E c d := sem.E (toCell₀ c)
    (belowEquiv D B hB (scope_bound D B hB c) d)
  orderly c _d := sem.orderly (toCell₀ c) _

local notation "rows₀" => rows D B hB sem

theorem respects_iff (BJ : GradedIndex ι) (hBJ : BJ.1 ⊆ B)
    p :
    RespectsSemanticsBelow (rows₀) BJ p ↔
      RespectsSemanticsBelow sem BJ (p ∘ (belowEquiv D B hB hBJ).symm) :=
  respects_iff_of_equiv (belowEquiv D B hB hBJ) (fun _ => rfl) (fun _ _ => Iff.rfl)
    (fun _ _ _ => rfl) p

theorem pullback_respects {BJ : GradedIndex ι} (hBJ : BJ.1 ⊆ B)
    {p} (hp : RespectsSemanticsBelow sem BJ p) :
    RespectsSemanticsBelow (rows₀) BJ (p ∘ belowEquiv D B hB hBJ) := by simp_all [respects_iff, Function.comp_def]

theorem consistent (hs : sem.IsConsistent) : (rows₀).IsConsistent := by solve_by_elim [pullback_respects]

theorem coded (hs : sem.IsCoded) : (rows₀).IsCoded := fun _ _ => hs _ _

