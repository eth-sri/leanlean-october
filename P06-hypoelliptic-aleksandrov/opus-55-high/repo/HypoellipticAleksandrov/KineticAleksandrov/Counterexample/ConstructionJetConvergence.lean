module

public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.ConstructionMollifiedJets

/-! # Almost-everywhere convergence of the selected spatial jets -/

@[expose] public section
namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample
open Filter MeasureTheory
open scoped Topology Convolution

variable {d : ℕ}

/-- The concrete normalized kernels recover every locally integrable native scalar field. -/
theorem construction_spatialMollify_tendsto_ae  (f : XV d → ℝ)
    (hf : LocallyIntegrable f volume) :
    ∀ᵐ q ∂volume, Tendsto
      (fun n => spatialMollify (standardMollifierSequence n) f q) atTop (𝓝 (f q)) := ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable
    standardMollifierSequence_rOut_tendsto
    (Eventually.of_forall standardMollifierSequence_radius_ratio) hf

/-- At each time the selected first and second representatives are recovered simultaneously. -/
theorem construction_selected_jets_tendsto_ae  {alpha : ℝ}
    (h : CounterProfileStatement d alpha) (r : ℝ) (hr : 0 < r) (mu R m t : ℝ) :
    ∀ᵐ q ∂volume,
      (∀ i : Fin (d + d), Tendsto
        (fun n => spatialMollify (standardMollifierSequence n)
          (fun y => constructionExtendedNativeGradient h r mu R m t y i) q)
        atTop (𝓝 (constructionExtendedNativeGradient h r mu R m t q i))) ∧
      (∀ i k : Fin d, Tendsto
        (fun n => spatialMollify (standardMollifierSequence n)
          (fun y => constructionExtendedNativeHessian h r mu R m t y i k) q)
        atTop (𝓝 (constructionExtendedNativeHessian h r mu R m t q i k))) := by
  have hg (i : Fin _) := construction_spatialMollify_tendsto_ae
    (fun y => constructionExtendedNativeGradient h r mu R m t y i)
    (construction_locallyIntegrable_native _
      (construction_extendedGradient_locallyIntegrable h r hr mu R m t i))
  have hh (i k : Fin d) := construction_spatialMollify_tendsto_ae
    (fun y => constructionExtendedNativeHessian h r mu R m t y i k)
    (construction_locallyIntegrable_native _
      (construction_extendedHessian_locallyIntegrable h r hr mu R m t i k))
  simp_all

end HypoellipticAleksandrov.KineticAleksandrov.Counterexample
