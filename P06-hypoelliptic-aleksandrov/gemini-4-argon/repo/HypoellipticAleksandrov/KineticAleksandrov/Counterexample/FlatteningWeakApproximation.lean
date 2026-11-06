module

public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.MollifyWeakJets
public import Mathlib.Topology.MetricSpace.Thickening
public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.ProfileBounds

/-! # Local bounds for the normalized convolutions used in the weak chain rule

The mollification API is the independently written generic M-lane API. All uses here
are of proved normalized-convolution lemmas, with their ordinary analytic hypotheses.
-/

@[expose] public section

namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample

open MeasureTheory Filter Set Metric
open scoped Convolution

/-- A local bound on the kernel sampling ball suffices for the normalized convolution bound. -/
theorem spatialMollify_norm_le_on_ball {d } (phi : ContDiffBump (0 : XV d))
    (g : XV d → ℝ) (hg : AEStronglyMeasurable g volume) (C ) (hC : 0 ≤ C)
    (q : XV d) (hb : ∀ y ∈ ball q phi.rOut, ‖g y‖ ≤ C) :
    ‖spatialMollify phi g q‖ ≤ C := by
  have h := dist_convolution_le (μ := volume) (x₀ := q) (z₀ := (0 : ℝ)) hC
    phi.support_normed_eq.subset phi.nonneg_normed phi.integral_normed hg
    (fun y hy => by simpa only [dist_zero_right] using hb y hy)
  simpa only [spatialMollify, dist_zero_right] using h

/-- The standard normalized convolution converges almost everywhere for every locally
integrable scalar function, without a global boundedness assumption. -/
theorem spatialMollify_ae_tendsto {d } (g : XV d → ℝ) (hg : LocallyIntegrable g volume) :
    ∀ᵐ q ∂volume,
      Tendsto (fun n => spatialMollify (standardMollifierSequence n) g q) atTop (nhds (g q)) := by
  exact (ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable (standardMollifierSequence_rOut_tendsto (G := XV d)) (Eventually.of_forall (standardMollifierSequence_radius_ratio (G := XV d))) hg)

end HypoellipticAleksandrov.KineticAleksandrov.Counterexample
