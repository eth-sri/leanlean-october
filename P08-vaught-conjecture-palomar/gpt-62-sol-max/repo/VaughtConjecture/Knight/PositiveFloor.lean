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
public import VaughtConjecture.Knight.CountedRecoding
public import VaughtConjecture.Knight.CappedLocalityRecoding
public import VaughtConjecture.Knight.Semantics
public import VaughtConjecture.Knight.Reduction
public import VaughtConjecture.Knight.VisibilityAlgebra
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import VaughtConjecture.Knight.FullScopeZeroExtension
public import VaughtConjecture.Knight.RowCorrectness
public import VaughtConjecture.Knight.RowReadback
public import VaughtConjecture.Knight.PositiveNormalization

@[expose] public section

namespace VaughtConjecture.Knight

open AmalgamationPlan Transform Value ExtOrd SharpWitnessComposition

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
  grind [← hν.mono.map_min]

end VaughtConjecture.Knight
