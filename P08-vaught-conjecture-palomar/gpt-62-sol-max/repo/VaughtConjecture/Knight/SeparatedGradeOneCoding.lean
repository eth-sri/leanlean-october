/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import Mathlib.Data.Finset.Sort
public import VaughtConjecture.Knight.VisibleOrderInterpolation
public import VaughtConjecture.Knight.SourceBlockLocalityTransport
public import Mathlib.Data.Fintype.Lattice
public import Mathlib.Logic.Relation
public import VaughtConjecture.Knight.SourceCode

@[expose] public section

namespace VaughtConjecture.Knight.SeparatedGradeOne

open AmalgamationPlan Transform Value ExtOrd FullRowLifting

/-- The fixed offset-one source form. -/
noncomputable def band (n : ℕ) : ExtOrd := ofOrd (Ordinal.omega0 * n + (1 : ℕ))

theorem band_visible (n : ℕ) : SelfVis 1 (band n) := by
  rw [band, selfVis_ofOrd_iff]
  exact (finitePart_mul_add n 1).ge

theorem band_coded (n k : ℕ) : IsCodedLabel k (band n) :=
  Or.inr ⟨n, 1, by omega, rfl⟩

theorem band_mono {m n : ℕ} (h : m ≤ n) : band m ≤ band n := by
  apply ofOrd_le_ofOrd.mpr
  gcongr

theorem band_floor (n : ℕ) : blockFloor (band n) = ofOrd (Ordinal.omega0 * n) := by
  rw [band, blockFloor_ofOrd, limitPart_mul_add n 1]

end VaughtConjecture.Knight.SeparatedGradeOne
