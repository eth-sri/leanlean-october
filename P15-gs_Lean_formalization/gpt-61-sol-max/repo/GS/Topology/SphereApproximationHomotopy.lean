import Mathlib.Tactic

import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Topology.Homotopy.Contractible
import Mathlib.Tactic.FunProp



noncomputable section
open Metric
namespace GS.Topology
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Normalize a continuous, nowhere-zero map to the unit sphere. -/
def sphereNormalize {X : Type*} [TopologicalSpace X] (g : C(X, F))
    (hg : ∀ x, g x ≠ 0) : C(X, sphere (0 : F) 1) := by
  refine ⟨fun x => ⟨‖g x‖⁻¹ • g x, ?_⟩, ?_⟩
  · simp_all [inv_mul_cancel₀,norm_smul]
  · exact ((g.continuous.norm.inv₀ fun x => norm_ne_zero_iff.mpr (hg x)).smul
      g.continuous).subtype_mk _

end GS.Topology
