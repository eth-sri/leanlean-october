/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.ReferenceContext
public import VaughtConjecture.Knight.FreeDiagonal
public import VaughtConjecture.Knight.MixedGradeInterpolation

/-! # Completing finite reference orbits with the existing witness

An actual `ReferenceContext` supplies a coded old row whose cap dominates all finite requests.
The source for a new requested offset is the replacement of the old representative's source.
One normalized witness of the old row reads every such new source correctly. No inverse,
composition of faithful transformations, or independently chosen new source order is used.

Requests are indexed by their positions in the list, so repeated requests remain distinct
occurrences. Old row entries stay literal; their target values are capped at the controller,
not asserted to stay literal above that cap. The new sources have the requested finite parts,
are coded in existing source blocks, and lie strictly below the old diagonal source.

This is a source-row construction and faithful readback, not an enlarged cell scheme.
Candidate-side and mixed-scope localities, availability outside the row, bountifulness, and the
infinite-label branch are not supplied here. In particular it is not terminal comparison.
-/

@[expose] public section

namespace VaughtConjecture.Knight

open TypeTower StageType Transform Value ExtOrd VaughtConjecture.AmalgamationPlan

universe w

namespace ReferenceContext

variable {M : Type w} {α : LimitStage} {R : KnightRealization α M}
  {n : ℕ} {t : Fin n ↪ M} {reqs : List BlockRequest}
  (C : ReferenceContext R t reqs)

/-- A full-scope controller of the reference grade, dominating the reference cap. -/
structure FullController where
  cell : Cell C.p₀.scheme.scheme
  index : C.p₀.scheme.scheme.cell cell = (Finset.univ, C.N)
  dominates : C.p₀.label C.capBase ≤ C.p₀.label cell

/-- Completeness and actual availability choose the controller; no new row is postulated. -/
theorem exists_fullController : Nonempty C.FullController := by
  have hmem : ((Finset.univ : Finset (Fin C.m)), C.N) ∈
      Plan.gradedPlan C.p₀.scheme.scheme.plan := by
    refine Plan.mem_gradedPlan.mpr
      ⟨C.p₀.scheme.scheme.isPlan.domain_mem, ?_, ?_⟩
    · rw [← C.cap_grade]
      exact C.p₀.scheme.scheme.grade_pos C.capBase
    · rw [← C.cap_grade]
      exact (C.p₀.scheme.scheme.grade_le_card_scope C.capBase).trans
        (Finset.card_le_card (Finset.subset_univ _))
  obtain ⟨d, hd⟩ := C.p₀.scheme.complete _ hmem
  obtain ⟨c, hc, hle⟩ := C.p₀.respects.availability C.capBase d
    (by rw [show C.p₀.scheme.scheme.scope d = Finset.univ from congrArg Prod.fst hd]
        exact Finset.subset_univ _)
    (C.cap_grade.trans (congrArg Prod.snd hd).symm)
  exact ⟨⟨c, hc.trans hd, hle⟩⟩

end ReferenceContext

end VaughtConjecture.Knight
