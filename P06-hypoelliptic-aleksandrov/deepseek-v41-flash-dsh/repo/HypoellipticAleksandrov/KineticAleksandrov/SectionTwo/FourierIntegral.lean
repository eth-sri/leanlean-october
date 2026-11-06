module

public import HypoellipticAleksandrov.KineticAleksandrov.SectionTwo.FourierBounds
public import HypoellipticAleksandrov.KineticAleksandrov.SectionTwo.DensityIntegral

/-! # Fourier integral bridges on real and complex bounded Borel data -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.SectionTwo
open MeasureTheory Set
open scoped ENNReal

/-- Complex bounded Borel integration uses the explicit complex multiplication pairing. -/
theorem fourierProjection_integral_complex {d : ℕ} {Ω : Set (PDE.Vec d)}
    {γ : ℝ → PDE.Vec d} (K : MovingFiberKernel Ω γ) (q : EvolutionQuery Ω γ)
    (ξ : PDE.Vec d) (ν : ComplexMeasure (PDE.Vec d)) (hν : IsFourierProjection K q ξ ν)
    (f : PDE.Vec d → ℂ) (hf : Measurable f) (hbounded : ∃ C : ℝ, ∀ v, ‖f v‖ ≤ C) :
    (∫ᵛ v, f v ∂[ContinuousLinearMap.mul ℝ ℂ; ν]) =
      ∫ w, f w.1 * fourierPhase ξ q.1.2.2.2 w ∂K.master q := by
  rw [fourierProjection_eq_densityMap K q ξ ν hν]
  let g := fourierPhase ξ q.1.2.2.2
  have hv : ((K.master q).withDensityᵥ g).variation = K.master q :=
    variation_density_one _ g (continuous_fourierPhase ξ _).measurable
      (norm_fourierPhase ξ _)
  have hi : Integrable (fun w : EvolutionAmbientState d => f w.1) (K.master q) := by
    obtain ⟨C, hC⟩ := hbounded
    exact Integrable.mono' (integrable_const C)
      (hf.comp measurable_fst).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun w => hC w.1))
  have hiv : ((K.master q).withDensityᵥ g).Integrable (f ∘ Prod.fst) := by
    simpa only [VectorMeasure.Integrable, hv, Function.comp_def] using hi
  rw [VectorMeasure.integral_map measurable_fst hf.aestronglyMeasurable hiv]
  exact integral_density_one _ g (continuous_fourierPhase ξ _).measurable
    (norm_fourierPhase ξ _) _ hi

end HypoellipticAleksandrov.KineticAleksandrov.SectionTwo
