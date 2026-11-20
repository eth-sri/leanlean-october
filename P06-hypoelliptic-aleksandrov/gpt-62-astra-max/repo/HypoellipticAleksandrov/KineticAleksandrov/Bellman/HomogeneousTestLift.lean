module

public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.BarrierFunctionSpace
public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.FundamentalMeasure
public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.HomogeneousTestLiftCalculus
import Mathlib.Tactic

/-! # The literal radial integral lifting compact tests to homogeneous functions -/

@[expose] public section
noncomputable section
open MeasureTheory Set Filter Topology
namespace HypoellipticAleksandrov.KineticAleksandrov

variable (n : WithTop ℕ∞) (alpha : ℝ) (zeta : (ℝ × ℝ) → ℝ)

include alpha zeta in
/-- The test lift is the actual positive-radius integral with degree minus one minus alpha. -/
def lift (q : ℝ × ℝ) : ℝ :=
  ∫ r : BellmanPositiveTime, r.val ^ (-1 - alpha) *
    zeta (bellmanPlaneDilation r.val q) ∂bellmanPositiveTimeVolume

/-- Regularity extends across the zero neighborhood of any test supported away from zero. -/
theorem bellman_compact_test_contDiff_order
    (hz : ContDiffOn ℝ n zeta bellmanPuncturedSet)
    (hs : tsupport zeta ⊆ bellmanPuncturedSet) : ContDiff ℝ n zeta := by
  apply contDiff_iff_contDiffAt.mpr
  intro q
  by_cases hq : q ∈ bellmanPuncturedSet
  · exact (hz q hq).contDiffAt (bellmanPuncturedSet_isOpen.mem_nhds hq)
  · have he : zeta =ᶠ[𝓝 q] fun _ => 0 := by
      filter_upwards [(isClosed_tsupport zeta).isOpen_compl.mem_nhds (fun ht => hq (hs ht))] with x hx
      exact image_eq_zero_of_notMem_tsupport hx
    exact contDiffAt_const.congr_of_eventuallyEq he

/-- A compact test supported away from zero is globally C², including its zero neighborhood. -/
theorem bellman_compact_test_contDiff
    (hz : ContDiffOn ℝ 2 zeta bellmanPuncturedSet)
    (hs : tsupport zeta ⊆ bellmanPuncturedSet) : ContDiff ℝ 2 zeta :=
  bellman_compact_test_contDiff_order 2 zeta hz hs

end HypoellipticAleksandrov.KineticAleksandrov
