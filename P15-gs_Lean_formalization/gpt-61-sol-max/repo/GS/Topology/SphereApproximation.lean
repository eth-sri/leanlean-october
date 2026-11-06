import Mathlib.Tactic

import GS.Topology.SphereApproximationHomotopy
import Mathlib.Analysis.Calculus.BumpFunction.SmoothApprox
import Mathlib.Topology.MetricSpace.HausdorffDimension
import Mathlib.Topology.TietzeExtension
import Mathlib.Analysis.Convex.Contractible



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

open Metric
open scoped ContDiff

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
    ContinuousLinearEquiv.ofFinrankEq (Module.finrank_fin_fun ℝ).symm
  letI := TietzeExtension.of_homeo e.toHomeomorph
  let fF : C(sphere (0 : E) 1, F) :=
    ⟨fun x => f x, continuous_subtype_val.comp f.continuous⟩
  obtain ⟨f₀, hf₀⟩ := fF.exists_restrict_eq isClosed_sphere
  obtain ⟨g,hgc,hg⟩ := (mem_closure_iff_nhds_basis
    (nhds_basis_uniformity uniformity_basis_dist.compactConvergenceUniformity)).mp
      (ContinuousMap.dense_setOfPred_contDiff   f₀)
        (sphere (0 : E) 1, (1/2 : ℝ)) ⟨isCompact_sphere _ _, by norm_num⟩
  change ContDiff ℝ ∞ (g : E → F) at hgc
  change ∀ x ∈ sphere (0 : E) 1, dist (g x) (f₀ x) < 1/2 at hg
  have hdense := (hgc.differentiable (by simp)).dense_compl_range_of_finrank_lt_finrank hdim
  obtain ⟨y,hy,hyε⟩ := hdense.exists_dist_lt 0 (by norm_num : (0 : ℝ) < 1/2)
  let gC : C(E, F) := ⟨fun x => g x-y, g.continuous.sub continuous_const⟩
  have hg0 (x : E) : gC x ≠ 0 := fun hx => hy ⟨x,sub_eq_zero.mp hx⟩
  have hclose : ∀ x : sphere (0 : E) 1, dist (gC.restrict _ x) (f x : F) < 1 := by
    intro x
    have heq : f₀ x = (f x : F) := congrArg (fun h : C(sphere (0 : E) 1, F) => h x) hf₀
    calc
      _ ≤ dist (gC x) (g x) + dist (g x) (f x : F) := dist_triangle _ _ _
      _ < 1/2+1/2 := add_lt_add (by aesop)
        (by grind)
      _ = 1 := by norm_num
  let a : C(unitInterval × sphere (0 : E) 1,F) :=
    ⟨fun z => (1-(z.1 : ℝ)) • (f z.2 : F)+(z.1 : ℝ) • gC z.2,by fun_prop⟩
  have ha : ∀ z, a z ≠ 0 := by
    intro z hz
    have hf := mem_sphere_zero_iff_norm.mp (f z.2).property
    have hd : dist (a z) (f z.2 : F) < 1 :=
      (convex_ball (f z.2 : F) 1) (by simp) (hclose z.2)
        (sub_nonneg.mpr z.1.property.2) z.1.property.1 (sub_add_cancel 1 (z.1 : ℝ))
    simpa [hz,hf] using hd
  have hfg : f.Homotopic ((sphereNormalize gC hg0).comp
      (⟨Subtype.val,continuous_subtype_val⟩ : C(sphere (0 : E) 1,E))) := by
    refine ⟨{ toContinuousMap := sphereNormalize a ha
              map_zero_left := ?_
              map_one_left := ?_ }⟩
    · aesop (add norm [sphereNormalize,Subtype.ext,mem_sphere_zero_iff_norm])
    · intro x
      apply Subtype.ext
      simp [sphereNormalize,a]
  have hn  := by
    simpa using (id_nullhomotopic E).comp_right (sphereNormalize gC hg0)
  obtain ⟨c, hc⟩ := hn.comp_left (⟨Subtype.val, continuous_subtype_val⟩ :
    C(sphere (0 : E) 1, E))
  exact ⟨c, hfg.trans hc⟩

end GS.Topology
