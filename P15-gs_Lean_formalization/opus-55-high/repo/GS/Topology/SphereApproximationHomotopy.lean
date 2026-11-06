module

public import Mathlib.Analysis.Normed.Module.Convex
public import Mathlib.Topology.Homotopy.Contractible
public import Mathlib.Tactic.FunProp

@[expose] public section


noncomputable section
open Set Metric Function
namespace GS.Topology
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Normalize a continuous, nowhere-zero map to the unit sphere. -/
def sphereNormalize {X : Type*} [TopologicalSpace X] (g : C(X, F))
    (hg : ∀ x, g x ≠ 0) : C(X, sphere (0 : F) 1) := by
  refine ⟨fun x => ⟨‖g x‖⁻¹ • g x, ?_⟩, ?_⟩
  · rw [mem_sphere_zero_iff_norm, norm_smul, Real.norm_eq_abs,
      abs_of_pos (by simp_all),
      inv_mul_cancel₀ (by simp_all)]
  · exact ((g.continuous.norm.inv₀ fun x => norm_ne_zero_iff.mpr (hg x)).smul
      g.continuous).subtype_mk _

/-- A continuous approximation within distance one of a sphere map becomes
homotopic to that map after normalization. -/
theorem homotopic_sphereNormalize_of_dist_lt_one {X : Type*} [TopologicalSpace X]
    (f : C(X, sphere (0 : F) 1)) (g : C(X, F)) (hg : ∀ x, g x ≠ 0)
    (hclose : ∀ x, dist (g x) (f x : F) < 1) :
    f.Homotopic (sphereNormalize g hg) := by
  let a : C(unitInterval × X, F) :=
    ⟨fun z => (1 - (z.1 : ℝ)) • (f z.2 : F) + (z.1 : ℝ) • g z.2, by
      fun_prop⟩
  have ha (z) : a z ≠ 0 := by
    have := (convex_ball (f z.2 : F) 1) (mem_ball_self one_pos) (hclose z.2) (sub_nonneg.mpr z.1.2.2) z.1.2.1 (by simp)
    have := (f z.2).2
    aesop
  exact ⟨{ toContinuousMap := sphereNormalize a ha
           map_zero_left x := by simp [sphereNormalize, a, mem_sphere_zero_iff_norm.mp (f x).2]
           map_one_left := by simp [sphereNormalize, a] }⟩

end GS.Topology
