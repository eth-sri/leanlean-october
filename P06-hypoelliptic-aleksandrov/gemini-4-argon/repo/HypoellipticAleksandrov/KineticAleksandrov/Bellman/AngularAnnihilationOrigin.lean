module

public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.AngularPositiveTailGrowth
public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.AngularAnnihilationMoments
import Mathlib.Tactic

/-! # Vanishing angular value and flux at the origin -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov
open MeasureTheory Set Filter
open scoped Topology

/- A nonnegative angular density bounded below by its value at zero must vanish there. -/
theorem bellmanAngularFirstMoment_tendsto_zero (f : ℝ → ℝ)
    (hf : LocallyIntegrable f volume) :
    Tendsto (bellmanAngularFirstMoment f) (𝓝 (0 : ℝ)) (𝓝 0) := by
  have hi : LocallyIntegrable (fun z => z * f z) volume := by
    simpa only [pow_one] using bellman_polynomial_locallyIntegrable f hf 1
  have hc := bellman_lebesguePrimitive_continuous _ hi
  change Tendsto (fun y => ∫ z in 0..y, z * f z) (𝓝 (0 : ℝ)) (𝓝 0)
  simpa only [intervalIntegral.integral_same] using hc.tendsto (0 : ℝ)

/- The normalized second moment tends to zero at the origin without pointwise regularity of
f. -/
end HypoellipticAleksandrov.KineticAleksandrov
