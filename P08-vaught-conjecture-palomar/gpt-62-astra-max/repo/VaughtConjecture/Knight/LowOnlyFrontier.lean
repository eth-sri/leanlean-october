/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.LowOnlyFaceRestoration
public import VaughtConjecture.Knight.CappedDonorRelease

/-! # Private source gaps independently of receiving reference records

This is precisely the original-row data needed for LOW-only frontier release. There is
no upper threshold, reference-block inventory, or inequality between the two facet arities.
-/

@[expose] public section

namespace VaughtConjecture.Knight.LowOnly

open Transform Value ExtOrd SharpWitnessComposition AmalgamationPlan CappedDonor

/-- A private owner and a strictly lower rounded source on its actual row. -/
structure SourceGap {n} (C : SemScheme n) (K : ℕ) where
  c : Cell C.scheme
  c_grade : C.scheme.grade c = K
  r : C.scheme.RowDomain c
  gap_c : extVisibilityReplace (C.rows.E c r) K K <
    C.rows.E c ⟨c, GradedLe.refl _⟩

namespace SourceGap

variable {n K : ℕ} {C : SemScheme n} (L : SourceGap C K)

abbrev Dom := C.scheme.RowDomain L.c

def cL : L.Dom := ⟨L.c, GradedLe.refl _⟩

include L in
theorem K_pos : 0 < K := (C.scheme.grade_pos L.c).trans_eq L.c_grade

include L in
theorem K_le : K ≤ n := L.c_grade.symm.trans_le (gradeC_le L.c)

noncomputable def h : ExtOrd := extVisibilityReplace (C.rows.E L.c L.r) K K

theorem h_lt_c : L.h < C.rows.E L.c L.cL := L.gap_c

theorem srcE_r_le_h : C.rows.E L.c L.r ≤ L.h := TopSupport.le_evr_self _ K

noncomputable def e (v : L.Dom → ExtOrd) : ExtOrd :=
  min (v L.cL) (extVisibilityReplace (v L.r) K K)

theorem e_min {γ} (hγ : SelfVis K γ) v :
    L.e (fun d => min (v d) γ) = min (L.e v) γ := by
  unfold e
  rw [evr_min_of_selfVis hγ le_rfl le_rfl, min_min_min_comm, min_self]

theorem c_selfVis {v}
    (hv : C.rows.Lawful v) :
    SelfVis K (v L.cL) := by
  have h := (hv.orderly L.cL).symm
  change SelfVis (C.scheme.grade L.c) (v L.cL) at h
  rwa [L.c_grade] at h

theorem exists_witness {v}
    (hv : C.rows.Lawful v) :
    ∃ τ, Witness (gTop K) τ ∧ (∀ x, τ x ≤ v L.cL) ∧
      ∀ d : L.Dom, τ (C.rows.E L.c d) = min (v d) (v L.cL) := by
  have h := exists_bounded_exact_capped_witness (grade := fun d : L.Dom => C.scheme.grade d.1)
    (c := L.cL) (p := v) (fun d => d.2.2) (hv.orderly L.cL).symm (hv.locality L.cL)
  have hg : C.scheme.grade L.cL.1 = K := L.c_grade
  rwa [hg] at h

/-- The original strict gap, not the numerical top flag, supplies this bound. -/
theorem e_le_of_gap {v}
    (hv : C.rows.Lawful v)
    d (hd : L.h < C.rows.E L.c d) : L.e v ≤ v d := by
  obtain ⟨τ, hτ, -, hread⟩ := L.exists_witness hv
  rw [show L.e v = τ L.h from by
        unfold e h
        rw [hτ.comm_gTop _ le_rfl, hread, evr_min_of_selfVis (L.c_selfVis hv) le_rfl le_rfl, min_comm]]
  exact (hτ.mono hd.le).trans ((hread d).le.trans (min_le_left _ _))

theorem domLe {j} (hj : K ≤ j) : GradedLe (C.scheme.cell L.c) (effC n j) :=
  ⟨Finset.subset_univ _, L.c_grade.trans_le (le_min hj L.K_le)⟩

def lowD {j} (hj : K ≤ j) (v : C.ClippedCells j → ExtOrd)
    (d : L.Dom) : ExtOrd := v (CellScheme.below.mono (L.domLe hj) d)

theorem lowD_respects {j} (hj : K ≤ j) {v}
    (hv : C.rows.Lawful v) :
    C.rows.Lawful (L.lowD hj v) := hv.mono (L.domLe hj)

def cC {j} (hj : K ≤ j) : C.ClippedCells j :=
  CellScheme.below.mono (L.domLe hj) L.cL

def rC {j} (hj : K ≤ j) : C.ClippedCells j :=
  CellScheme.below.mono (L.domLe hj) L.r

noncomputable def eC {j} (hj : K ≤ j) (v : C.ClippedCells j → ExtOrd) : ExtOrd :=
  L.e (L.lowD hj v)

end SourceGap

end VaughtConjecture.Knight.LowOnly
