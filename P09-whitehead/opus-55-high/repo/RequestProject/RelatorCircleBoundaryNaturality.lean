import RequestProject.PresRelatorCircleEmbedding
import RequestProject.FinitePosetCycleNaturality


/-! Literal presentation inclusions preserve the actual boundary-circle
parametrization exactly. No independent choice of circle coordinates is
made on the larger presentation. Pending Lean verification. -/

namespace FiniteChains.PresModel.PresWordEmbedding
open Comb

variable {A B J K : Type} {w : J → List (A × Bool)} {v : K → List (B × Bool)}
  (h : PresWordEmbedding w v)

theorem relatorCircleSize_eq j :
    relatorCircleSize w j = relatorCircleSize v (h.cell j) := by
  simp [relatorCircleSize, h.word_length]

theorem relatorCircleEnumeration_natural j
    hw hv
    i :
    h.relatorCircleMap j (relatorCircleEnumeration w j hw i) =
      relatorCircleEnumeration v (h.cell j) hv
        (Fin.cast (congrArg (· + 2) (h.relatorCircleSize_eq j)) i) := by
  rfl

/-- The actual boundary coordinates of every retained cell commute with
the literal presentation inclusion. -/
theorem relatorCircleBoundaryHomeomorph_natural j
    hw hv
    x :
    relatorCircleBoundaryHomeomorph v (h.cell j) hv
      (h.relatorCircleRealizationMap j x) =
        relatorCircleBoundaryHomeomorph w j hw x := (relatorCircleCycle w j hw).boundaryHomeomorph_natural_cast
    _ (h.relatorCircleSize_eq j)
    _ _
    (h.relatorCircleEnumeration_natural j hw hv) x

theorem relatorCircleBoundaryHomeomorph_symm_natural j
    hw hv
    z :
    h.relatorCircleRealizationMap j ((relatorCircleBoundaryHomeomorph w j hw).symm z) =
      (relatorCircleBoundaryHomeomorph v (h.cell j) hv).symm z := by
  apply (relatorCircleBoundaryHomeomorph v _ hv).injective
  grind [h.relatorCircleBoundaryHomeomorph_natural j hw hv, Homeomorph.apply_symm_apply]
