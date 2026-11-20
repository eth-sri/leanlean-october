module

public import Mathlib.Analysis.Convex.StdSimplex
public import Mathlib.Topology.Homeomorph.Lemmas

@[expose] public section

namespace FiniteChains.TopologicalSingular

variable (n : ℕ)

/-- The finite-support simplex and the barycentric-coordinate simplex have the same topology. -/
noncomputable def simplexCoordinates :
    Convexity.StdSimplex ℝ (Fin (n + 1)) ≃ₜ stdSimplex ℝ (Fin (n + 1)) :=
  (Convexity.StdSimplex.isEmbedding_toFun_comp_weights ℝ (Fin _)).toHomeomorph.trans
    (Homeomorph.setCongr (by
      ext <;> simp_all [Convexity.StdSimplex.range_toFun_comp_weights, stdSimplex]))

@[simp] theorem simplexCoordinates_apply
    (z : Convexity.StdSimplex ℝ _) :
    (simplexCoordinates n z).val = z.weights := rfl

/-- Barycentric coordinates commute with maps of vertex sets. -/
theorem simplexCoordinates_map {n m : ℕ} (f : Fin _ → Fin _)
    (z : Convexity.StdSimplex ℝ _) :
    simplexCoordinates m (Convexity.StdSimplex.map f z) =
      stdSimplex.map f (simplexCoordinates n z) := by
  apply Subtype.ext
  funext i
  change (Finsupp.mapDomain f z.weights) i = (FunOnFinite.linearMap ℝ ℝ f z.weights) i
  simp [FunOnFinite.linearMap_apply_apply, Finsupp.mapDomain_apply,
    Finsupp.sum_fintype, Finsupp.single_apply, Finset.sum_filter, eq_comm]

@[simp] theorem simplexCoordinates_symm_weights_apply (n : ℕ)
    (z : stdSimplex ℝ (Fin _)) (i : Fin _) :
    ((simplexCoordinates n).symm z).weights i = z.val i := congrArg (fun w : stdSimplex ℝ (Fin _) => w.val i)
    ((simplexCoordinates n).apply_symm_apply z)

end FiniteChains.TopologicalSingular
