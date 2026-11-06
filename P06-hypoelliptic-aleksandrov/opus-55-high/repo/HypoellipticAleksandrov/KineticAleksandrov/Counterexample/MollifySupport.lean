module

public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.MollifyNativeMeasure
public import Mathlib.Topology.MetricSpace.Thickening

/-! # Support control by the actual mollifier radius -/

@[expose] public section
namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample
open MeasureTheory Set Metric
variable {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
  [MeasureSpace G] [BorelSpace G] [FiniteDimensional ℝ G]
  [Measure.IsAddHaarMeasure (volume : Measure G)]

/-- A mollified value vanishes outside the open thickening of the original support. -/
theorem spatialMollify_eq_zero_outside_thickening (phi : ContDiffBump (0 : G))
    (f : G → ℝ) (K : Set G) (hf : Function.support f ⊆ K) (q : G)
    (hq : q ∉ thickening phi.rOut K) : spatialMollify phi f q = 0 := by
  apply integral_eq_zero_of_ae
  filter_upwards [] with w
  change phi.normed volume w * f _ = 0
  by_cases hk : phi.normed volume w = 0
  · simp_all
  · have hw : ‖w‖ < phi.rOut := by
      have he : w ∈ ball (0) phi.rOut := by
        rw [← phi.support_normed_eq (μ := volume)]
        exact hk
      simp_all
    have hz : f (q - w) = 0 := by
      by_contra hn
      apply hq
      apply mem_thickening_iff.mpr
      refine ⟨q - w, hf hn, ?_⟩
      simp_all
    simp_all

end HypoellipticAleksandrov.KineticAleksandrov.Counterexample
