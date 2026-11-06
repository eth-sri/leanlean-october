module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.BarrierModulusLocal

/-! # Reference position and velocity increments from the actual homogeneous jets -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous.BarrierRegularization
open HypoellipticAleksandrov Set MeasureTheory Filter
open scoped Topology

/- Off the origin the extension has the original local germ. -/
theorem barrierExtension_eventuallyEq (phi : (ℝ × ℝ) → ℝ) {q }
    (hq : q ≠ (0, 0)) : bellmanOriginExtension phi =ᶠ[𝓝 q] phi := by
  filter_upwards [bellmanPuncturedSet_isOpen.mem_nhds hq] with z hz
  exact bellmanOriginExtension_eqOn phi hz

/- A gauge at least one excludes the origin. -/
theorem barrier_gauge_one_ne_zero {q } (hq : 1 ≤ bellmanGauge q) : q ≠ (0, 0) := by
  intro he
  subst q
  norm_num [bellmanGauge, bellmanGaugePower] at hq

/- The continuous extension satisfies the same homogeneity including at the origin. -/
theorem barrierExtension_scaling {alpha phi}
    (h : IsBellmanHomogeneous alpha phi) (r : ℝ) (hr : 0 < r) (q : ℝ × ℝ) :
    bellmanOriginExtension phi (bellmanPlaneDilation r q) =
      r ^ alpha * bellmanOriginExtension phi q := by
  by_cases hq : q = (0, 0)
  · subst q
    simp only [bellmanPlaneDilation, mul_zero, bellmanOriginExtension_zero]
  · rw [bellmanOriginExtension_eqOn phi (bellmanPlaneDilation_ne_zero r hr q hq),
      bellmanOriginExtension_eqOn phi hq]
    exact h.2 r hr q hq

/- One constant controls every reference-scale increment in either coordinate. -/
end HypoellipticAleksandrov.KineticAleksandrov.Autonomous.BarrierRegularization
