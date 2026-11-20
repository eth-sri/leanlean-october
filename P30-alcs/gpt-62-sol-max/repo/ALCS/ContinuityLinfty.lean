module

public import ALCS.ZeroClass
public import Mathlib.Topology.UniformSpace.UniformApproximation

public section

open MeasureTheory Filter Topology Set
open scoped ENNReal

namespace ALCS

variable {𝕜 X U : Type*} [RCLike 𝕜]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X]
  [NormedAddCommGroup U] [NormedSpace 𝕜 U]

/-- **Corollary 1.6**: `t ↦ Φ t u` is continuous. On a short time window it is
uniformly approximated by the free orbit from the start of the window. -/
theorem continuousOn_Phi (S : ALCS 𝕜 X U ∞) (u : Lp U ∞ muPlus) :
    ContinuousOn (fun t => S.Φ t u) (Ici 0) := by
  refine continuousOn_of_locally_uniform_approx_of_continuousWithinAt fun t ht w hw => ?_
  obtain ⟨ε, hε, hsub⟩ := Metric.uniformity_basis_dist.mem_iff.1 hw
  have hz : Tendsto (fun s => ‖S.Φ s‖ * ‖u‖) (𝓝[≥] 0) (𝓝 0) := by
    simpa using S.zero_class.mul_const ‖u‖
  obtain ⟨δ, hδ, hb⟩ := (nhdsGE_basis_Ico (0 : ℝ)).mem_iff.1 (hz.eventually_lt_const hε)
  obtain ⟨a, ha, hwin⟩ := C0Semigroup.exists_window (t := t) hδ
  obtain ⟨v, hv, hcat⟩ := exists_shift a u
  let F (s : ℝ) := S.T (max 0 (s - a)) (S.Φ a u)
  have hf : Continuous F := (S.toC0Semigroup.continuousOn_orbit _).comp_continuous
    (by fun_prop) (fun s => le_max_left _ _)
  refine ⟨_, hwin, F, hf.continuousWithinAt, fun s hs => hsub ?_⟩
  have he := S.composition a (s - a) ha hs.1 u v u hcat
  rw [add_sub_cancel] at he
  simpa [he, F, max_eq_right hs.1, dist_eq_norm] using
    ((S.Φ _).le_opNorm_of_le hv).trans_lt (hb hs)

end ALCS
