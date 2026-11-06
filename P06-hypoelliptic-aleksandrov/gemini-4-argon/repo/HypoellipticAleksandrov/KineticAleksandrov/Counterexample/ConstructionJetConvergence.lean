module

public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.ConstructionMollifiedJets

/-! # Almost-everywhere convergence of the selected spatial jets -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample
open Filter MeasureTheory
open scoped Topology Convolution

/- The concrete normalized kernels recover every locally integrable native scalar field. -/
theorem construction_spatialMollify_tendsto_ae {d } (f : XV d → ℝ)
    (hf : LocallyIntegrable f volume) :
    ∀ᵐ q ∂volume, Tendsto
      (fun n => spatialMollify (standardMollifierSequence n) f q) atTop (𝓝 (f q)) := by
  exact ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable
    standardMollifierSequence_rOut_tendsto
    (Eventually.of_forall standardMollifierSequence_radius_ratio) hf

/- At each time the selected first and second representatives are recovered simultaneously. -/
end HypoellipticAleksandrov.KineticAleksandrov.Counterexample
