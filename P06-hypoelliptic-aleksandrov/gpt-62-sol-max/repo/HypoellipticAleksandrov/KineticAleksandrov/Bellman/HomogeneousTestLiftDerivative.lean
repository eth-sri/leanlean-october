module

public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.HomogeneousTestLiftFirstIntegral
public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.HomogeneousTestLiftIntegrandDerivative
import Mathlib.Analysis.Calculus.FDeriv.Congr
import Mathlib.Analysis.Calculus.FDeriv.Const
import Mathlib.Tactic

/-! # First derivatives pass through the actual radial lift integral -/

@[expose] public section
noncomputable section
open Set MeasureTheory Filter Topology
namespace HypoellipticAleksandrov.KineticAleksandrov

/-- The first derivative is the integral of the actual dilated test derivative. -/
theorem bellman_lift_fderiv (alpha : ℝ) (zeta : (ℝ × ℝ) → ℝ)
    (hz : ContDiffOn ℝ 1 zeta bellmanPuncturedSet) (hc : HasCompactSupport zeta)
    (hs : tsupport zeta ⊆ bellmanPuncturedSet)
    (q : ℝ × ℝ) (hq : q ∈ bellmanPuncturedSet) (e : ℝ × ℝ) :
    fderiv ℝ (lift alpha zeta) q e =
      ∫ r : BellmanPositiveTime, r.val ^ (-1 - alpha) *
        fderiv ℝ zeta (bellmanPlaneDilation r.val q) (bellmanDilationLinear r.val e)
        ∂bellmanPositiveTimeVolume := by
  have hzglobal := bellman_compact_test_contDiff_order 1 zeta hz hs
  have hf := bellmanLiftIntegrand_contDiffOn_order 1 alpha zeta hzglobal
  obtain ⟨U, hU, hqU, K, hK, hwindow, he⟩ :=
    bellman_lift_locally_eq_subtype alpha zeta hc hs q hq
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let mu : Measure K := Measure.comap Subtype.val bellmanPositiveTimeVolume
  let : IsFiniteMeasure mu := bellman_radius_window_volume_finite K hK
  let radius : K → ℝ := fun r => r.val.val
  have hr : Continuous radius := continuous_subtype_val.comp continuous_subtype_val
  have hrp : ∀ r : K, 0 < radius r := fun r => r.val.property
  rw [he.fderiv_eq]
  change fderiv ℝ (fun x => ∫ r : K, bellmanLiftIntegrand alpha zeta (x, radius r) ∂mu) q e = _
  rw [bellman_joint_integral_fderiv mu hU radius hr hrp
    (bellmanLiftIntegrand alpha zeta) (hf.mono (prod_mono (subset_univ U) Subset.rfl))
    q hqU e]
  simp_rw [bellmanLiftIntegrand_spatial_fderiv alpha zeta hzglobal _ _ (hrp _)]
  symm
  apply bellman_integral_compact_radius_subtype K hK
  intro r hrK
  have hn : bellmanPlaneDilation r.val q ∉ tsupport zeta :=
    fun ht => hrK (hwindow r ht)
  rw [fderiv_of_notMem_tsupport ℝ hn]
  simp only [zero_apply, mul_zero]

end HypoellipticAleksandrov.KineticAleksandrov
