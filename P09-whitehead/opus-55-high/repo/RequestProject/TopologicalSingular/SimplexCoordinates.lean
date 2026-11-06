import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Topology.Homeomorph.Lemmas
import RequestProject.Tac


namespace FiniteChains.TopologicalSingular

bwd

/-- The finite-support simplex and the barycentric-coordinate simplex have the same topology. -/
noncomputable def simplexCoordinates n :
    Convexity.StdSimplex ℝ (Fin (n + 1)) ≃ₜ stdSimplex ℝ (Fin (n + 1)) :=
  (Convexity.StdSimplex.isEmbedding_toFun_comp_weights ℝ _).toHomeomorph.trans
    (Homeomorph.setCongr (by
      rw [Convexity.StdSimplex.range_toFun_comp_weights]
      aesop))

@[simp] theorem simplexCoordinates_apply n
    z :
    (simplexCoordinates n z).val = z.weights := rfl

/-- Barycentric coordinates commute with maps of vertex sets. -/
theorem simplexCoordinates_map f
    (z : Convexity.StdSimplex ℝ (Fin (n + 1))) :
    simplexCoordinates m (Convexity.StdSimplex.map f z) =
      stdSimplex.map f (simplexCoordinates n z) := by
  apply Subtype.ext
  funext i
  change (Finsupp.mapDomain f z.weights) i = (FunOnFinite.linearMap ℝ ℝ f z.weights) i
  simp [FunOnFinite.linearMap_apply_apply, Finsupp.mapDomain_apply,
    Finsupp.sum_fintype, Finsupp.single_apply, Finset.sum_filter, eq_comm]

@[simp] theorem simplexCoordinates_symm_weights_apply n
    z i :
    ((simplexCoordinates n).symm z).weights i = z.val i := congrArg (·.val i)
    ((simplexCoordinates n).apply_symm_apply z)
