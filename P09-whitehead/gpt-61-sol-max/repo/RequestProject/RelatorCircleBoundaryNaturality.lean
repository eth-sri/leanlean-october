import Mathlib.Tactic

import RequestProject.PresRelatorCircleEmbedding
import RequestProject.FinitePosetCycleNaturality

/-! Literal presentation inclusions preserve the actual boundary-circle
parametrization exactly. No independent choice of circle coordinates is
made on the larger presentation. Pending Lean verification. -/

noncomputable section
namespace FiniteChains.PresModel.PresWordEmbedding
open Comb

variable {A B J K : Type} {w : J → List (A × Bool)} {v : K → List (B × Bool)}
  (h : PresWordEmbedding w v)

variable (j : J)
theorem relatorCircleSize_eq  :
    relatorCircleSize w j = relatorCircleSize v (h.cell j) := by
  simp [relatorCircleSize, h.word_length]

variable (hw : 0 < (w j).length)
theorem relatorCircleEnumeration_natural 
     (hv : 0 < (v (h.cell j)).length)
    (i : Fin (relatorCircleSize w j + 2)) :
    h.relatorCircleMap j (relatorCircleEnumeration w j hw i) =
      relatorCircleEnumeration v (h.cell j) hv
        (Fin.cast (congrArg (fun n => n + 2) (h.relatorCircleSize_eq j)) i) := rfl

/-- The actual boundary coordinates of every retained cell commute with
the literal presentation inclusion. -/
theorem relatorCircleBoundaryHomeomorph_natural 
     (hv : 0 < (v (h.cell j)).length)
    (x : orderNerveRealization (RelatorCircle w j)) :
    relatorCircleBoundaryHomeomorph v (h.cell j) hv
      (h.relatorCircleRealizationMap j x) =
        relatorCircleBoundaryHomeomorph w j hw x := by
  classical solve_by_elim (transparency := .default) (maxDepth := 10) [FiniteChains.Comb.FinitePosetCycle.boundaryHomeomorph_natural_cast, FiniteChains.PresModel.PresWordEmbedding.relatorCircleSize_eq, FiniteChains.PresModel.PresWordEmbedding.relatorCircleEnumeration_natural, relatorCircleCycle]

theorem relatorCircleBoundaryHomeomorph_symm_natural 
     (hv : 0 < (v (h.cell j)).length)
    (z : FiniteChains.RelativeAttachment.UnitBoundary (Fin 2 → ℝ)) :
    h.relatorCircleRealizationMap j ((relatorCircleBoundaryHomeomorph w j hw).symm z) =
      (relatorCircleBoundaryHomeomorph v (h.cell j) hv).symm z := by
  apply (relatorCircleBoundaryHomeomorph v (h.cell j) hv).injective
  rw [h.relatorCircleBoundaryHomeomorph_natural j hw hv, Homeomorph.apply_symm_apply,
    Homeomorph.apply_symm_apply]

end FiniteChains.PresModel.PresWordEmbedding
