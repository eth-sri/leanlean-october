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

/-! # Producing separated source profiles by one common codebook

Grade-one coding of visible labels has exactly offset one at every nonbottom
value. Thus equality of block floors is equality of codes. This supplies the
separation hypothesis of the actual bountiful row construction, including
inputs with literal top. The selected uncoded labels themselves respect the
new rows by direct outgoing witnesses, not by faithful composition.

This is not a replacement for arbitrary inherited rows. The source profile
is shared by all grade-one rows, and every higher-grade row remains mute.
-/

@[expose] public section

namespace VaughtConjecture.Knight.SeparatedGradeOne

open AmalgamationPlan Transform Value ExtOrd FullRowLifting

section
variable (n : ℕ)

/-- The fixed offset-one source form. -/
noncomputable def band  : ExtOrd := ofOrd (Ordinal.omega0 * n + (1 : ℕ))

theorem band_visible  : SelfVis 1 (band n) := by
  rw [band, selfVis_ofOrd_iff]
  exact (finitePart_mul_add n 1).ge

end

theorem band_coded n k : IsCodedLabel k (band n) :=
  Or.inr ⟨n, 1, by omega, rfl⟩

theorem band_mono {m n} (h : m ≤ n) : band m ≤ band n := by
  apply ofOrd_le_ofOrd.mpr
  gcongr

theorem band_floor n : blockFloor (band n) = ofOrd (Ordinal.omega0 * n) := by
  rw [band, blockFloor_ofOrd, limitPart_mul_add n 1]

end VaughtConjecture.Knight.SeparatedGradeOne
