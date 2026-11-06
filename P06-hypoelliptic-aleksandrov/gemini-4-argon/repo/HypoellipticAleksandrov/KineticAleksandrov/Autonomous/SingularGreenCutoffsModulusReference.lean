module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.SingularGreenCutoffsModulusLocal

/-! # Reference position and velocity increments from the actual homogeneous jets -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open HypoellipticAleksandrov Set MeasureTheory Filter
open scoped Topology

/-- Off the origin the extension has the original local germ. -/
theorem barrierExtension_eventuallyEq (phi : (ℝ × ℝ) → ℝ) {q }
    (hq : q ≠ (0, 0)) : bellmanOriginExtension phi =ᶠ[𝓝 q] phi := by
  filter_upwards [bellmanPuncturedSet_isOpen.mem_nhds hq] with z hz
  exact bellmanOriginExtension_eqOn phi hz

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
