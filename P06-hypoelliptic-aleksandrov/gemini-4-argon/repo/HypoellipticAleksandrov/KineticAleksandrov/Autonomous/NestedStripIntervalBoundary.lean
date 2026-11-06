module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.NestedStripIntervalRestart

/-! # Exact terminal, outer-lateral and internal-lateral interval exit splitting -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov

/- The literal interval exit boundary is Borel in physical coordinates. -/
theorem measurableSet_nestedIntervalExit (H : Interval) (sMinus T : ℝ) :
    MeasurableSet (reconstructionExit H sMinus T) := by
  have hv : Measurable (fun p : Point => p.velocity 0) :=
    ((continuous_apply 0).comp continuous_velocity).measurable
  exact ((measurableSet_eq_fun continuous_time.measurable measurable_const).inter
    (measurableSet_Icc.preimage hv)).union
    ((measurableSet_lt measurable_const continuous_time.measurable).inter
      ((measurableSet_lt continuous_time.measurable measurable_const).inter
        ((measurableSet_eq_fun hv measurable_const).union
          (measurableSet_eq_fun hv measurable_const))))

/- On a smaller interval exit, being outside the larger exit is exactly being internal. -/
end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
