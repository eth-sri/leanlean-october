/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/

import Mathlib.Data.Finset.Sort
import VaughtConjecture.Knight.VisibleOrderInterpolation
import VaughtConjecture.Knight.SourceBlockLocalityTransport
import Mathlib.Data.Fintype.Lattice
import Mathlib.Logic.Relation
import VaughtConjecture.Knight.SourceCode

/-! # Producing separated source profiles by one common codebook

Grade-one coding of visible labels has exactly offset one at every nonbottom
value. Thus equality of block floors is equality of codes. This supplies the
separation hypothesis of the actual bountiful row construction, including
inputs with literal top. The selected uncoded labels themselves respect the
new rows by direct outgoing witnesses, not by faithful composition.

This is not a replacement for arbitrary inherited rows. The source profile
is shared by all grade-one rows, and every higher-grade row remains mute.
-/

namespace VaughtConjecture.Knight.SeparatedGradeOne

open    ExtOrd 

/-- The fixed offset-one source form. -/
noncomputable def band (n : ℕ) : ExtOrd := ofOrd (Ordinal.omega0 * n + (1 : ℕ))

theorem band_visible (n : ℕ) : SelfVis 1 (band n) := by
  rw [band, selfVis_ofOrd_iff]
  exact (finitePart_mul_add n 1).ge

theorem band_coded (n k : ℕ) : IsCodedLabel k (band n) :=
  Or.inr ⟨n, 1, by omega, rfl⟩

theorem band_floor (n : ℕ) : blockFloor (band n) = ofOrd (Ordinal.omega0 * n) := by
  rw [band, blockFloor_ofOrd, limitPart_mul_add n 1]

variable {ι : Type*} [DecidableEq ι]  

