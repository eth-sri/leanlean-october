module

public import Mathlib.Analysis.Convex.StdSimplex
public import Mathlib.Topology.Homeomorph.Lemmas

@[expose] public section

namespace FiniteChains.TopologicalSingular


/-- The finite-support simplex and the barycentric-coordinate simplex have the same topology. -/
noncomputable def simplexCoordinates (n : ℕ) :
    Convexity.StdSimplex ℝ (Fin (n + 1)) ≃ₜ stdSimplex ℝ (Fin (n + 1)) :=
  (Convexity.StdSimplex.isEmbedding_toFun_comp_weights ℝ (Fin (n + 1))).toHomeomorph.trans
    (Homeomorph.setCongr (by
      rw [Convexity.StdSimplex.range_toFun_comp_weights]
      ext x
      simp [stdSimplex]))

@[simp] theorem simplexCoordinates_apply (n : ℕ)
    (z : Convexity.StdSimplex ℝ (Fin (n + 1))) :
    (simplexCoordinates n z).val = z.weights := rfl

/-- Barycentric coordinates commute with maps of vertex sets. -/
theorem simplexCoordinates_map {n m : ℕ} (f : Fin (n + 1) → Fin (m + 1))
    (z : Convexity.StdSimplex ℝ (Fin (n + 1))) :
    simplexCoordinates m (Convexity.StdSimplex.map f z) =
      stdSimplex.map f (simplexCoordinates n z) := by
  apply Subtype.ext
  funext i
  change (Finsupp.mapDomain f z.weights) i = (FunOnFinite.linearMap ℝ ℝ f z.weights) i
  simp [FunOnFinite.linearMap_apply_apply, Finsupp.mapDomain_apply,
    Finsupp.sum_fintype, Finsupp.single_apply, Finset.sum_filter, eq_comm]

@[simp] theorem simplexCoordinates_symm_weights_apply (n : ℕ)
    (z : stdSimplex ℝ (Fin (n + 1))) (i : Fin (n + 1)) :
    ((simplexCoordinates n).symm z).weights i = z.val i := congrArg (fun w  => w.val i)
    ((simplexCoordinates n).apply_symm_apply z)

/-- In barycentric coordinates a face inclusion inserts one zero coordinate. -/
theorem simplex_map_succAbove {n : ℕ} (i : Fin (n + 2)) (z : stdSimplex ℝ (Fin (n + 1))) :
    (stdSimplex.map i.succAbove z).val = i.insertNth (0 : ℝ) z.val := by
  funext j
  change (FunOnFinite.linearMap ℝ ℝ i.succAbove z.val) j = _
  rw [FunOnFinite.linearMap_apply_apply]
  exact Fin.succAboveCases i (by simp) (fun k => by simp [Finset.sum_filter]) j

theorem exists_simplex_map_succAbove {n : ℕ} (z : stdSimplex ℝ (Fin (n + 2)))
    (i : Fin (n + 2)) (hi : z.val i = 0) :
    ∃ w : stdSimplex ℝ (Fin (n + 1)), stdSimplex.map i.succAbove w = z := by
  refine ⟨⟨Fin.removeNth i z.val, fun j => z.2.1 _, ?_⟩, Subtype.ext ?_⟩
  · have h := z.2.2
    rwa [Fin.sum_univ_succAbove z.val i, hi, zero_add] at h
  · rw [simplex_map_succAbove]
    simpa only [hi] using Fin.insertNth_self_removeNth i z.val

end FiniteChains.TopologicalSingular
