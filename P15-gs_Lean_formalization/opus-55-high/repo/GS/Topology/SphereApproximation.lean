module

public import GS.Topology.SphereApproximationHomotopy
public import Mathlib.Analysis.Calculus.BumpFunction.SmoothApprox
public import Mathlib.Topology.MetricSpace.HausdorffDimension
public import Mathlib.Topology.TietzeExtension
public import Mathlib.Analysis.Convex.Contractible

@[expose] public section


/-!
# Nullhomotopy of maps between spheres of increasing dimension

The proof extends a sphere map continuously to the ambient vector space,
approximates the extension by a smooth map near the compact source sphere,
and subtracts a sufficiently small point outside the smooth map's range.
The resulting map never vanishes and hence normalizes to a sphere-valued
map on the entire, contractible ambient vector space.

All approximation and dimension facts are theorems of the pinned mathlib;
no homology or homotopy computation is assumed.
-/

noncomputable section

open Set Metric Function
open scoped Topology ContDiff unitInterval

namespace GS.Topology

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F]

/-- Every map between unit spheres is nullhomotopic if the source ambient
vector space has strictly smaller real dimension than the target.

For spheres `S^k` and `S^m`, the hypothesis is precisely `k < m`.
The assertion concerns arbitrary continuous maps and the usual subspace
topology on the spheres. -/
theorem sphereMap_nullhomotopic_of_finrank_lt
    (hdim : Module.finrank ℝ E < Module.finrank ℝ F)
    (f : C(sphere (0 : E) 1, sphere (0 : F) 1)) : f.Nullhomotopic := by
  let e : F ≃L[ℝ] (Fin (Module.finrank ℝ F) → ℝ) :=
    ContinuousLinearEquiv.ofFinrankEq (by simp)
  letI : TietzeExtension F := TietzeExtension.of_homeo e.toHomeomorph
  obtain ⟨f₀, hf₀⟩ := (⟨fun x => f x, by fun_prop⟩ : C(sphere (0 : E) 1, F)).exists_restrict_eq isClosed_sphere
  rcases Metric.uniformContinuousOn_iff.mp ((isCompact_sphere (0 : E) 1).cthickening (r := 1) |>.uniformContinuousOn_of_continuous
    (map_continuous f₀).continuousOn) (1 / 2) (by norm_num) with ⟨δ, hδ, hfδ⟩
  rcases (map_continuous f₀).exists_contDiff_dist_le_of_forall_mem_ball_dist_le
    (lt_min one_pos hδ) with ⟨g, hgc, hg⟩
  obtain ⟨y, hy, hyε⟩ := ((hgc.differentiable (by simp)).dense_compl_range_of_finrank_lt_finrank hdim).exists_dist_lt 0
    (by norm_num : (0 : ℝ) < 1 / 2)
  let gC : C(E, F) := ⟨fun x => g x - y, by fun_prop⟩
  have hg0 : ∀ x, gC x ≠ 0 := fun x h => hy ⟨x, sub_eq_zero.1 h⟩
  have hclose : ∀ x : sphere (0 : E) 1, dist (gC.restrict _ x) (f x : F) < 1 := by
    intro x
    have := hg x _ fun y hy => by
      rw [mem_ball, lt_min_iff] at hy
      exact hfδ _ (mem_cthickening_of_dist_le _ x.1 _ _ x.2 hy.1.le) _ (self_subset_cthickening _ x.2) hy.2 |>.le
    have heq : f₀ x = (f x : F) := congrArg (fun h : C(sphere (0 : E) 1, F) => h x) hf₀
    simp only [ContinuousMap.restrict_apply, gC, ContinuousMap.coe_mk, ← heq]
    linarith [dist_triangle (g x - y) (g x) (f₀ x), show dist (g x - y) (g x) < 1/2 by simpa using hyε]
  have hfg := homotopic_sphereNormalize_of_dist_lt_one f (gC.restrict _) (by aesop) hclose
  have hn : (sphereNormalize gC hg0).Nullhomotopic := by
    simpa using (id_nullhomotopic E).comp_right (sphereNormalize gC hg0)
  obtain ⟨c, hc⟩ := hn.comp_left (⟨Subtype.val, continuous_subtype_val⟩ :
    C(sphere (0 : E) 1, E))
  exact ⟨c, hfg.trans hc⟩

end GS.Topology
