/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.FullScopeBountiful
public import VaughtConjecture.Knight.ReferenceContext
public import VaughtConjecture.Knight.FreeDiagonal
public import VaughtConjecture.Knight.MixedGradeInterpolation
public import VaughtConjecture.Knight.RequestAttachment
public import VaughtConjecture.Knight.CoupledGradeOne
public import VaughtConjecture.Knight.MixedRows
public import VaughtConjecture.Knight.ReferenceContext
public import VaughtConjecture.Knight.CountedRecoding
public import VaughtConjecture.Knight.RowCorrectness
public import VaughtConjecture.Knight.RowReadback
public import VaughtConjecture.Knight.PositiveNormalization
public import VaughtConjecture.Knight.RestrictedComposition

@[expose] public section

namespace VaughtConjecture.Knight

open Transform Value ExtOrd

theorem evr_eq_bot_iff {a : ExtOrd} (k i : ℕ) : extVisibilityReplace a k i = ⊥ ↔ a = ⊥ := by
  constructor
  · intro h; by_contra ha; exact extVisibilityReplace_ne_bot ha k i h
  simp_all

end VaughtConjecture.Knight
