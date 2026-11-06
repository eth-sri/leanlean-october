module

public import HypoellipticAleksandrov.KineticAleksandrov.Interval.FourierKernels
public import HypoellipticAleksandrov.KineticAleksandrov.SectionTwo.FourierKernelsComposition
import HypoellipticAleksandrov.KineticAleksandrov.Decay.MinorantScaling
import HypoellipticAleksandrov.KineticAleksandrov.Interval.FourierKernelsEvolution
import HypoellipticAleksandrov.KineticAleksandrov.SectionTwo.FourierKernelsTranslation

/-! # Composition of interval Fourier kernels with their zero extension -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Interval
open MeasureTheory Set HypoellipticAleksandrov
open HypoellipticAleksandrov.KineticAleksandrov.SectionTwo
open HypoellipticAleksandrov.KineticAleksandrov.Decay
variable {a c : ℝ}

/- Evaluations of the killed zero extension are measurable on ambient velocity space. -/
theorem measurable_intervalFourierKernelZero_apply
    (K : MovingFiberKernel (PDE.oneDimensionalAxisBox a c) stationary)
    (hJ : MeasurableSet (PDE.oneDimensionalAxisBox a c))
    (σ τ : ℝ) (hστ : σ ≤ τ) (ξ : PDE.Vec 1)
    (E ) (hE : MeasurableSet E) :
    Measurable (fun v => intervalFourierKernelZero K σ τ hστ ξ v E) := by
  have _h_xinl_0 : Measurable (fun v => intervalFourierKernel K σ τ hστ ξ v E) := by
    exact (measurable_fourierProjection_apply K ξ E hE).comp
      ((measurable_const.prodMk (measurable_const.prodMk
        (measurable_subtype_coe.prodMk measurable_const))).subtype_mk)
  convert ((MeasurableEmbedding.subtype_coe hJ).measurable_extend _h_xinl_0 (measurable_const (a := (0 : ℂ)))) using 1
  funext v
  by_cases hv : v ∈ PDE.oneDimensionalAxisBox a c
  · have he := Subtype.val_injective.extend_apply
      (fun w => intervalFourierKernel K σ τ hστ ξ w E) (fun _ => (0 : ℂ)) ⟨v, hv⟩
    exact (congrArg (fun ν : ComplexMeasure (PDE.Vec 1) => ν E)
      (intervalFourierKernelZero_coe K σ τ hστ ξ ⟨v, hv⟩)).trans he.symm
  · rw [intervalFourierKernelZero_of_notMem K σ τ hστ ξ v hv]
    exact (Function.extend_apply'
      (f := (Subtype.val : PDE.oneDimensionalAxisBox a c → PDE.Vec 1))
      (fun w => intervalFourierKernel K σ τ hστ ξ w E) (fun _ => (0 : ℂ)) v
      (by rintro ⟨w, rfl⟩; exact hv w.2)).symm

/- Every interval Fourier kernel evaluation has norm at most one. -/
theorem intervalFourierKernel_apply_norm_le_one
    (K : MovingFiberKernel (PDE.oneDimensionalAxisBox a c) stationary)
    (σ τ : ℝ) (hστ : σ ≤ τ) (ξ : PDE.Vec 1)
    (v : PDE.oneDimensionalAxisBox a c) (E : Set (PDE.Vec 1)) :
    ‖intervalFourierKernel K σ τ hστ ξ v E‖ ≤ 1 := by
  have he :=
    (measure_mono (subset_univ E)).trans
      (intervalFourierKernel_totalVariation_le_one K σ τ hστ ξ v)
  have hn := VectorMeasure.norm_measure_le_variation
    (μ := intervalFourierKernel K σ τ hστ ξ v) (ne_of_lt (he.trans_lt ENNReal.one_lt_top))
  exact hn.trans (by simpa only [Measure.real, ENNReal.toReal_one] using
    ENNReal.toReal_mono ENNReal.one_ne_top he)

/- The zero extension retains the uniform evaluation bound. -/
theorem intervalFourierKernelZero_apply_norm_le_one
    (K : MovingFiberKernel (PDE.oneDimensionalAxisBox a c) stationary)
    (σ τ : ℝ) (hστ : σ ≤ τ) (ξ v : PDE.Vec 1) (E : Set (PDE.Vec 1)) :
    ‖intervalFourierKernelZero K σ τ hστ ξ v E‖ ≤ 1 := by
  by_cases hv : v ∈ PDE.oneDimensionalAxisBox a c
  · exact (intervalFourierKernelZero_coe K σ τ hστ ξ ⟨v, hv⟩ ▸
      intervalFourierKernel_apply_norm_le_one K σ τ hστ ξ ⟨v, hv⟩ E)
  · rw [intervalFourierKernelZero_of_notMem K σ τ hστ ξ v hv]
    simp

/- Chapman--Kolmogorov on an interval, integrating the killed zero extension. -/
end HypoellipticAleksandrov.KineticAleksandrov.Interval
