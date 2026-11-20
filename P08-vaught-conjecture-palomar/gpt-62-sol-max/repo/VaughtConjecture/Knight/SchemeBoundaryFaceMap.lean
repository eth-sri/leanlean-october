/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.PointImageBountiful
public import VaughtConjecture.Knight.OrderedFaceBoundaryRows

@[expose] public section

namespace VaughtConjecture.Knight.SemSchemeBoundaryInput

open Transform Value ExtOrd

noncomputable section

section Face

variable {m n : ℕ} (D : SemScheme n) (F : SemScheme m) (f : Fin m ↪ Fin n)
  (hv : Finset.univ.image f ∈ D.scheme.plan) (hf : D.restrictFace f hv = F)

/-- The original ordered occurrence map, transported through literal face equality. -/
def faceMap : Cell F.scheme ↪o Cell D.scheme := by
  subst F
  exact CellScheme.restrictFace.toCell D.scheme f hv

theorem faceMap_index (d : Cell F.scheme) :
    D.scheme.cell (faceMap D F f hv hf d) =
      ((F.scheme.scope d).image f, F.scheme.grade d) := by
  subst F
  exact (CellScheme.restrictFace.pushGraded_cell D.scheme f hv d).symm

theorem faceMap_exhaustive (d : Cell D.scheme)
    (hd : D.scheme.scope d ⊆ Finset.univ.image f) :
    ∃ i, faceMap D F f hv hf i = d := by
  subst F
  exact CellScheme.restrictFace.exists_toCell_eq D.scheme f hv hd

/-- Equality includes every actual shared row argument, and bottom outside its lower set. -/
theorem faceMap_total (c d : Cell F.scheme) :
    AmalgamatedBoundaryRows.total D.rows (faceMap D F f hv hf c)
      (faceMap D F f hv hf d) = AmalgamatedBoundaryRows.total F.rows c d := by
  subst F
  classical
  change AmalgamatedBoundaryRows.total D.rows
      (CellScheme.restrictFace.toCell D.scheme f hv c)
      (CellScheme.restrictFace.toCell D.scheme f hv d) = _
  by_cases h : GradedLe ((D.restrictFace f hv).scheme.cell d)
      ((D.restrictFace f hv).scheme.cell c)
  · have h' := CellScheme.restrictFace.gradedLe_of_restrictFace D.scheme f hv h
    rw [AmalgamatedBoundaryRows.total_below _ _ ⟨_, h'⟩,
      AmalgamatedBoundaryRows.total_below _ _ ⟨_, h⟩]
    rfl
  · rw [AmalgamatedBoundaryRows.total_outside _ _ _ h,
      AmalgamatedBoundaryRows.total_outside _ _ _ (fun h' =>
        h ((CellScheme.restrictFace.gradedLe_restrictFace_iff D.scheme f hv).mpr h'))]

end Face

end

end VaughtConjecture.Knight.SemSchemeBoundaryInput
