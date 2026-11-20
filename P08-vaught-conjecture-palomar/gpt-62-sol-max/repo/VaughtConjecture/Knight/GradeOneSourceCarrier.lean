/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.GradeOneBoundaryFamily
public import VaughtConjecture.Knight.SourcePrefixLayer
public import VaughtConjecture.Knight.AmalgamatedBoundaryRows
public import VaughtConjecture.Knight.FiniteOffset

/-! # Actual occurrences for the first supported controller layer

Append exactly the constructed normalized family to the proper grade-one
boundary. The old cells keep their enumeration and complete lower domains.
There are no lower positive full-scope grades and no mute higher placeholders.
-/

@[expose] public section

set_option autoImplicit false

namespace VaughtConjecture.Knight.GradeOneSourceCarrier

open AmalgamationPlan Transform Value ExtOrd GradeOneBoundaryFamily

variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A}
variable (sem : Semantics D) (hA : 0 < A.card)

noncomputable def scheme : CellScheme A where
  plan := D.plan
  isPlan := D.isPlan
  card := D.card + Fintype.card (Profile sem)
  cell := Fin.addCases D.cell (fun _ => (A, 1))
  cell_mem c := by
    refine Fin.addCases ?_ ?_ c
    · intro d; simpa only [Fin.addCases_left] using D.cell_mem d
    · intro q
      simp only [Fin.addCases_right]
      exact Plan.mem_gradedPlan.mpr ⟨D.isPlan.domain_mem, Nat.one_pos, hA⟩

abbrev Occ := Cell D ⊕ Profile sem

noncomputable def enumeration : Occ sem ≃ Cell (scheme sem hA) :=
  (Equiv.sumCongr (Equiv.refl _) (Fintype.equivFin (Profile sem))).trans finSumFinEquiv

noncomputable def toCell (d : Occ sem) : Cell (scheme sem hA) := enumeration sem hA d
noncomputable def toOcc (d : Cell (scheme sem hA)) : Occ sem := (enumeration sem hA).symm d

@[simp] theorem toOcc_toCell (d : Occ sem) : toOcc sem hA (toCell sem hA d) = d :=
  (enumeration sem hA).symm_apply_apply d

@[simp] theorem toCell_toOcc (d : Cell (scheme sem hA)) : toCell sem hA (toOcc sem hA d) = d :=
  (enumeration sem hA).apply_symm_apply d

variable (hproper : ∀ d : Cell D, D.scope d ≠ A)

end VaughtConjecture.Knight.GradeOneSourceCarrier
