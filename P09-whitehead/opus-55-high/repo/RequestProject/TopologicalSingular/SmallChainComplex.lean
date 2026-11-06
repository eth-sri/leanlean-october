/- Adapted from the local 2026-09-11 Lean audit; see PROVENANCE.json. -/

import RequestProject.TopologicalSingular.SmallChainHomology
import RequestProject.TopologicalSingular.SingularHomologySequence
import RequestProject.Tac


/-! # The small singular subcomplex and its quotient

All complexes are defined from the actual singular differential. The
short exact sequence is valid for an arbitrary family of subsets; no
openness or covering assumption is used in this file.
-/

bwd

namespace FiniteChains.SingularSubdivision

open CategoryTheory CategoryTheory.Limits TopologicalSingular Set

universe u v
variable {X : Type u} [TopologicalSpace X] {ι : Type v}

noncomputable def smallBoundary (U : ι → Set X) n :
    smallChains U (n + 1) →ₗ[ℤ] smallChains U n :=
  ((boundary n).comp (smallChains U _).subtype).codRestrict _
    (boundary_mem_small U n ·.property)

theorem smallBoundary_squared (U : ι → Set X) n :
    (smallBoundary U n).comp (smallBoundary U (n + 1)) = 0 := by
  apply LinearMap.ext
  intro c
  apply Subtype.ext
  exact boundary_boundary n c.val
