import Mathlib.Tactic

/- Adapted from the local 2026-09-11 Lean audit; see PROVENANCE.json. -/

import RequestProject.TopologicalSingular.SmallChainHomology
import RequestProject.TopologicalSingular.SingularHomologySequence

/-! # The small singular subcomplex and its quotient

All complexes are defined from the actual singular differential. The
short exact sequence is valid for an arbitrary family of subsets; no
openness or covering assumption is used in this file.
-/

set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.SingularSubdivision

open CategoryTheory CategoryTheory.Limits TopologicalSingular Set

variable {X : Type u} [TopologicalSpace X] {ι : Type v}

noncomputable def smallBoundary (U : ι → Set X) (n : ℕ)  :=
  ((boundary n).comp (smallChains U (n + 1)).subtype).codRestrict _
    (fun c => boundary_mem_small U n c.property)

theorem smallBoundary_squared (U : ι → Set X) (n : ℕ) :
    (smallBoundary U n).comp (smallBoundary U (n + 1)) = 0 := by
  apply LinearMap.ext
  intro c
  apply Subtype.ext
  exact boundary_boundary n c.val

end FiniteChains.SingularSubdivision
