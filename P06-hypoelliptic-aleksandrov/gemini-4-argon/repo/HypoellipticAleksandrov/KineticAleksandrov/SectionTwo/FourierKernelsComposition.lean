module

public import HypoellipticAleksandrov.KineticAleksandrov.SectionTwo.FourierKernelsTranslation
import Mathlib.Probability.Kernel.Composition.IntegralCompProd

/-! # Fourier phase factorization and Chapman--Kolmogorov integration -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.SectionTwo
open MeasureTheory Set
open scoped ENNReal ProbabilityTheory

/- A derived fiber kernel is finite uniformly, by its sub-Markov mass bound. -/
instance fiberKernel_isFiniteKernel {d : ℕ} {Ω : Set (PDE.Vec d)}
    {γ : ℝ → PDE.Vec d} (K : MovingFiberKernel Ω γ) (hΩ : MeasurableSet Ω)
    (σ τ : ℝ) (hστ : σ ≤ τ) : ProbabilityTheory.IsFiniteKernel (K.fiberKernel hΩ σ τ hστ) :=
  ⟨1, ENNReal.one_lt_top, K.fiberKernel_mass_le_one hΩ σ τ hστ⟩

/- Integrals against the ambient master measure equal integrals against the derived fiber. -/
theorem master_integral_eq_fiber {d Ω γ} (K : MovingFiberKernel Ω γ) (hΩ : MeasurableSet Ω)
    (σ τ : ℝ) (hστ : σ ≤ τ) (p : EvolutionState Ω γ σ)
    (f : EvolutionAmbientState d → ℂ) (hf : Measurable f) :
    (∫ w, f w ∂K.master (evolutionQueryOfState Ω γ σ τ hστ p)) =
      ∫ w, f w.1 ∂K.fiberKernel hΩ σ τ hστ p := by
  rw [← K.map_fiberKernel_eq_master hΩ σ τ hστ p]
  exact integral_map measurable_subtype_coe.aemeasurable hf.aestronglyMeasurable

/- Fourier phases factor at the intermediate position, with the source sign convention. -/
theorem fourierPhase_factor {d } (ξ z : PDE.Vec d)
    (w w' : EvolutionAmbientState d) :
    fourierPhase ξ z w' = fourierPhase ξ z w * fourierPhase ξ w.2 w' := by
  have hd : PDE.vecDot ξ (w'.2 - z) =
      PDE.vecDot ξ (w.2 - z) + PDE.vecDot ξ (w'.2 - w.2) := by
    unfold PDE.vecDot
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    simp only [Pi.sub_apply]
    ring
  unfold fourierPhase
  rw [hd, Complex.ofReal_add, mul_add, Complex.exp_add]

/- Chapman--Kolmogorov gives iterated integration of every bounded Borel complex datum. -/
theorem master_integral_composition {d Ω γ} (K : MovingFiberKernel Ω γ) (hΩ : MeasurableSet Ω)
    (hcomp : K.HasComposition hΩ) (σ r τ : ℝ) (hσr : σ ≤ r) (hrτ : r ≤ τ)
    (p : EvolutionState Ω γ σ) (f : EvolutionAmbientState d → ℂ)
    (hf : Measurable f) (hbound : ∃ C : ℝ, ∀ w, ‖f w‖ ≤ C) :
    (∫ w, f w ∂K.master (evolutionQueryOfState Ω γ σ τ (hσr.trans hrτ) p)) =
      ∫ w, (∫ w', f w' ∂K.master (evolutionQueryOfState Ω γ r τ hrτ w))
        ∂K.fiberKernel hΩ σ r hσr p := by
  rw [master_integral_eq_fiber K hΩ σ τ (hσr.trans hrτ) p f hf,
    hcomp σ r τ hσr hrτ]
  have hi : Integrable (fun w : EvolutionState Ω γ τ => f w.1)
      ((K.fiberKernel hΩ r τ hrτ ∘ₖ K.fiberKernel hΩ σ r hσr) p) := by
    obtain ⟨C, hC⟩ := hbound
    exact Integrable.mono' (integrable_const C)
      (hf.comp measurable_subtype_coe).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun w => hC w.1))
  rw [ProbabilityTheory.Kernel.integral_comp hi]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun w =>
    (master_integral_eq_fiber K hΩ r τ hrτ w f hf).symm

/- Every Fourier kernel value has norm at most one, uniformly in the Borel set. -/
theorem fourierKernel_apply_norm_le_one {d }
    (K : MovingFiberKernel (wholeSpace d) (fun _ => 0))
    (σ τ : ℝ) (hστ : σ ≤ τ) (ξ v : PDE.Vec d) (E : Set (PDE.Vec d)) :
    ‖fourierKernel K σ τ hστ ξ v E‖ ≤ 1 := by
  have he :=
    (measure_mono (subset_univ E)).trans
      (fourierKernel_totalVariation_le_one K σ τ hστ ξ v)
  have hn := VectorMeasure.norm_measure_le_variation
    (μ := fourierKernel K σ τ hστ ξ v) (ne_of_lt (he.trans_lt ENNReal.one_lt_top))
  exact hn.trans (by simpa only [Measure.real, ENNReal.toReal_one] using
    ENNReal.toReal_mono ENNReal.one_ne_top he)

/- The Fourier kernel obeys temporal composition with complex multiplication pairing. -/
end HypoellipticAleksandrov.KineticAleksandrov.SectionTwo
