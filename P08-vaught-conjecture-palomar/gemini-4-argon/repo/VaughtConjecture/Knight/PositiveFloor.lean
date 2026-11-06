/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.SourceBlockLocalityTransport
public import VaughtConjecture.Knight.OrbitBlock
public import VaughtConjecture.Knight.CoupledGradeOne
public import VaughtConjecture.Knight.RelativeLiftData
public import VaughtConjecture.Knight.PositiveNormalization
public import VaughtConjecture.Knight.FullScopeZeroExtension
public import VaughtConjecture.Knight.RowReadback
public import VaughtConjecture.Knight.RowCorrectness
public import VaughtConjecture.Knight.Semantics
public import VaughtConjecture.Knight.CappedLocalityRecoding
public import VaughtConjecture.Knight.Reduction
public import VaughtConjecture.Knight.VisibilityAlgebra
public import VaughtConjecture.Knight.CountedRecoding

/-! # The common visible positive floor, and bottom-reflecting transport on long rows

The reviewer's notes5 (`plan13.md` §2, 2026-09-18).  For a nonbottom `K`-visible `w`, the
**positive floor** `F_w x = ⊥` if `x = ⊥`, `max x w` otherwise, is a bottom-reflecting
normalized grade-`K` witness (`witness_positiveFloor`): replacement at any grade at most `K`
commutes with it (`positiveFloor_evr`), because replacement is monotone and fixes `w`.  The
visibility of `w` at `K` is what makes one common floor respect every active grade below `K`;
a floor visible only at a lower grade would not.

**Transport on unchanged long rows** (`map_respects_of_bottom_reflecting`,
`positiveFloor_respects`): a bounded replacement-commuting, bottom-reflecting scalar image of a
lawful section is lawful — from the ported source-block theorem
`map_respects_iff_rowBlockBottom`, since a bottom-reflecting map preserves the row-block bottom
law.  No source-shortness is assumed.  Also `flat_section`: replacing every positive value of a
lawful section by one `K`-visible `w` is lawful (a cap at a visible value).

Construction-private (not root-exported). -/

@[expose] public section

namespace VaughtConjecture.Knight

open AmalgamationPlan Transform Value ExtOrd SharpWitnessComposition

/-! ## The floor -/

/-! ## Transport on unchanged long rows -/

variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A} {sem : Semantics D}

/-- **Bottom-reflecting transport**: a bounded replacement-commuting, bottom-reflecting scalar
image of a lawful section is lawful on the unchanged rows. -/
theorem map_respects_of_bottom_reflecting {BJ : Finset ι × ℕ} {r : D.below BJ → ExtOrd}
    (hr : RespectsSemanticsBelow sem BJ r) {K : ℕ} (hK : ∀ d : D.below BJ, D.grade d.1 ≤ K)
    {ν : ExtOrd → ExtOrd} (hν : BoundedMap K ν) (hrefl : ∀ x, ν x = ⊥ → x = ⊥) :
    RespectsSemanticsBelow sem BJ (fun d => ν (r d)) := by
  refine (map_respects_iff_rowBlockBottom hr hK hν).mpr ?_
  intro c d e hb hz
  have h0 := rowBlockBottom_of_respects hr c d e hb
  change min (ν (r (CellScheme.below.incl c d))) (ν (r c)) = ⊥ at hz
  change min (ν (r (CellScheme.below.incl c e))) (ν (r c)) = ⊥
  rw [← hν.mono.map_min] at hz ⊢
  rw [h0 (hrefl _ hz), hν.bot]
