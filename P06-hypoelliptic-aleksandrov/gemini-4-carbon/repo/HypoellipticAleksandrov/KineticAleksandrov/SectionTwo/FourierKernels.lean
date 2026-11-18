module

public import HypoellipticAleksandrov.KineticAleksandrov.SectionTwo.FourierBounds
public import HypoellipticAleksandrov.KineticAleksandrov.SectionTwo.DensityIntegral
public import HypoellipticAleksandrov.KineticAleksandrov.SectionTwo.Green
import Mathlib.Probability.Kernel.MeasurableIntegral

@[expose] public noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.SectionTwo
open MeasureTheory Set
open scoped ENNReal ProbabilityTheory

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
  have hi : Integrable (fun w => f w.1) (K.master q) := by
    obtain ⟨C, hC⟩ := hbounded
    exact Integrable.mono' (integrable_const C)
      (hf.comp measurable_fst).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun w => hC w.1))
  have hiv : ((K.master q).withDensityᵥ g).Integrable (f ∘ Prod.fst) := by
    simpa only [VectorMeasure.Integrable, hv, Function.comp_def] using hi
  rw [VectorMeasure.integral_map measurable_fst hf.aestronglyMeasurable hiv]
  exact integral_density_one _ g (continuous_fourierPhase ξ _).measurable
    (norm_fourierPhase ξ _) _ hi


/-- The Fourier measure of a Borel set depends measurably on the complete query. -/
theorem measurable_fourierProjection_apply {d : ℕ} {Ω : Set (PDE.Vec d)}
    {γ : ℝ → PDE.Vec d} (K : MovingFiberKernel Ω γ) (ξ : PDE.Vec d)
    (E : Set (PDE.Vec d)) (hE : MeasurableSet E) :
    Measurable (fun q : EvolutionQuery Ω γ => fourierProjection K q ξ E) := by
  have hm : Measurable (fun p : EvolutionQuery Ω γ × EvolutionAmbientState d =>
      fourierPhase ξ p.1.1.2.2.2 p.2) := by
    unfold fourierPhase PDE.vecDot
    fun_prop
  convert ((hm.indicator (measurable_snd (hE.prod MeasurableSet.univ))).stronglyMeasurable).integral_kernel_prod_right' (κ := K.master).measurable using 1
  funext q
  rw [fourierProjection_spec K q ξ E hE, ← integral_indicator (hE.prod MeasurableSet.univ)]
  rfl

/-- Whole-space Fourier kernels use starting position zero, removed later by covariance. -/
def fourierKernel {d : ℕ} (K : MovingFiberKernel (wholeSpace d) (fun _ => 0))
    (σ τ : ℝ) (hστ : σ ≤ τ) (ξ v : PDE.Vec d) : ComplexMeasure (PDE.Vec d) :=
  fourierProjection K (wholeSpaceQuery σ τ hστ v 0) ξ

/-- The whole-space Fourier kernel satisfies the displacement integral characterization. -/
theorem fourierKernel_spec {d : ℕ}
    (K : MovingFiberKernel (wholeSpace d) (fun _ => 0))
    (σ τ : ℝ) (hστ : σ ≤ τ) (ξ v : PDE.Vec d) :
    IsFourierProjection K (wholeSpaceQuery σ τ hστ v 0) ξ
      (fourierKernel K σ τ hστ ξ v) :=
  fourierProjection_spec K _ ξ

/-- Whole-space Fourier kernels are Borel in their starting velocity. -/
theorem measurable_fourierKernel_apply {d : ℕ}
    (K : MovingFiberKernel (wholeSpace d) (fun _ => 0))
    (σ τ : ℝ) (hστ : σ ≤ τ) (ξ : PDE.Vec d)
    (E : Set (PDE.Vec d)) (hE : MeasurableSet E) :
    Measurable (fun v => fourierKernel K σ τ hστ ξ v E) := by
  exact (measurable_fourierProjection_apply K ξ E hE).comp
    ((measurable_const.prodMk (measurable_const.prodMk
      (measurable_id.prodMk measurable_const))).subtype_mk)

/-- Total variation is dominated by the positive velocity marginal as a measure. -/
theorem fourierKernel_variation_le {d : ℕ}
    (K : MovingFiberKernel (wholeSpace d) (fun _ => 0))
    (σ τ : ℝ) (hστ : σ ≤ τ) (ξ v : PDE.Vec d) :
    (fourierKernel K σ τ hστ ξ v).variation ≤
      K.firstMarginal (wholeSpaceQuery σ τ hστ v 0) :=
  fourierProjection_variation_le K _ ξ _ (fourierKernel_spec K σ τ hστ ξ v)

/-- Sub-Markov contraction bounds the Fourier kernel's total variation by one. -/
theorem fourierKernel_totalVariation_le_one {d : ℕ}
    (K : MovingFiberKernel (wholeSpace d) (fun _ => 0))
    (σ τ : ℝ) (hστ : σ ≤ τ) (ξ v : PDE.Vec d) :
    totalVariationNorm (fourierKernel K σ τ hστ ξ v) ≤ 1 :=
  fourierProjection_totalVariation_le_one K _ ξ _ (fourierKernel_spec K σ τ hστ ξ v)

end HypoellipticAleksandrov.KineticAleksandrov.SectionTwo

