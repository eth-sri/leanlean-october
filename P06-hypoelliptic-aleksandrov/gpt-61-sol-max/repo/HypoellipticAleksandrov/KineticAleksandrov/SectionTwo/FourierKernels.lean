module

public import HypoellipticAleksandrov.KineticAleksandrov.SectionTwo.FourierIntegral
public import HypoellipticAleksandrov.KineticAleksandrov.SectionTwo.Green
import Mathlib.Probability.Kernel.MeasurableIntegral

/-! # Borel Fourier kernels and their marginal bounds -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.SectionTwo
open MeasureTheory Set
open scoped ENNReal ProbabilityTheory

variable {d : ℕ}

/-- The Fourier measure of a Borel set depends measurably on the complete query. -/
theorem measurable_fourierProjection_apply  {Ω : PDE.VelocityRegion d}
    {γ : ℝ → PDE.Vec d} (K : MovingFiberKernel Ω γ) (ξ : PDE.Vec d)
    (E : PDE.VelocityRegion d) (hE : MeasurableSet E) :
    Measurable (fun q  => fourierProjection K q ξ E) := by
  have hm : Measurable (fun p : EvolutionQuery Ω γ × EvolutionAmbientState d =>
      fourierPhase ξ p.1.1.2.2.2 p.2) := by
    unfold fourierPhase PDE.vecDot
    fun_prop


  convert (((hm.indicator (measurable_snd (hE.prod MeasurableSet.univ))).stronglyMeasurable).integral_kernel_prod_right' (κ := K.master)).measurable using 1
  funext q
  rw [fourierProjection_spec K q ξ E hE, ← integral_indicator (hE.prod MeasurableSet.univ)]
  rfl

variable (K : MovingFiberKernel (wholeSpace d) (fun _ => 0)) (σ τ : ℝ) (hστ : σ ≤ τ)

variable (ξ v : PDE.Vec d)

/-- Whole-space Fourier kernels use starting position zero, removed later by covariance. -/
def fourierKernel    : ComplexMeasure (PDE.Vec d) :=
  fourierProjection K (wholeSpaceQuery σ τ hστ v 0) ξ

/-- The whole-space Fourier kernel satisfies the displacement integral characterization. -/
theorem fourierKernel_spec
      :
    IsFourierProjection K (wholeSpaceQuery σ τ hστ v 0) ξ
      (fourierKernel K σ τ hστ ξ v) :=
  fourierProjection_spec K _ ξ

/-- Whole-space Fourier kernels are Borel in their starting velocity. -/
theorem measurable_fourierKernel_apply
     (ξ : PDE.Vec d)
    (E : PDE.VelocityRegion d) (hE : MeasurableSet E) :
    Measurable (fun v => fourierKernel K σ τ hστ ξ v E) := (measurable_fourierProjection_apply K ξ E hE).comp
    ((measurable_const.prodMk (measurable_const.prodMk
      (measurable_id.prodMk measurable_const))).subtype_mk)

variable (ξ v : PDE.Vec d)

/-- Total variation is dominated by the positive velocity marginal as a measure. -/
theorem fourierKernel_variation_le
      :
    (fourierKernel K σ τ hστ ξ v).variation ≤
      K.firstMarginal (wholeSpaceQuery σ τ hστ v 0) :=
  fourierProjection_variation_le K _ ξ _ (fourierKernel_spec K σ τ hστ ξ v)

/-- Sub-Markov contraction bounds the Fourier kernel's total variation by one. -/
theorem fourierKernel_totalVariation_le_one
      :
    totalVariationNorm (fourierKernel K σ τ hστ ξ v) ≤ 1 :=
  fourierProjection_totalVariation_le_one K _ ξ _ (fourierKernel_spec K σ τ hστ ξ v)

end HypoellipticAleksandrov.KineticAleksandrov.SectionTwo
