module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.CoreDominationRemainder
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.VisitRecursionUnconditionalKernels
import Mathlib.Topology.Instances.ENNReal.Lemmas

/-! # Actual finite-strip Green mixtures have vanishing remainder mass -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory ProbabilityTheory HypoellipticAleksandrov Filter
open scoped Topology

section
variable {lam Lam : ℝ} (A : SmoothAutonomous lam Lam) (H : FiniteIntervalUnion) (s T : ℝ)

/-- The actual physical Green mixture is bounded by time length times starting mass. -/
theorem visitUnionGreenKernel_comp_mass_le (mu : Measure Point) :
    (visitUnionGreenKernel A H s T ∘ₘ mu) univ ≤
      ENNReal.ofReal (T - s) * mu univ := by
  rw [Measure.bind_apply MeasurableSet.univ (Kernel.aemeasurable _)]
  exact Trans.trans (lintegral_mono (visitUnionGreenKernel_mass_le A H s T)) (lintegral_const (ENNReal.ofReal (T - s)))

/-- A finite counting measure makes the actual outer Green continuation masses vanish. -/
theorem visit_green_mixture_remainder_tendsto_zero
    (mu : ℕ → Measure Point) [IsFiniteMeasure (Measure.sum mu)] :
    Tendsto (fun n => (visitUnionGreenKernel A H s T ∘ₘ mu n) univ)
      atTop (𝓝 0) := by
  have hm := ENNReal.Tendsto.const_mul (a := ENNReal.ofReal (T - s)) (visit_measure_mass_tendsto_zero mu)
    (Or.inr ENNReal.ofReal_ne_top)
  simp only [mul_zero] at hm
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hm
    (fun _ => zero_le) (fun n => visitUnionGreenKernel_comp_mass_le
      A H s T (mu n))

end

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
