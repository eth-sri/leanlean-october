module

public import HypoellipticAleksandrov.KineticAleksandrov.Interval.FourierKernelsEvolution
public import HypoellipticAleksandrov.KineticAleksandrov.SectionTwo.FourierKernelsTranslation
public import HypoellipticAleksandrov.KineticAleksandrov.Decay.MinorantScaling

/-! # Fourier kernels on the actual interval velocity fiber

Starting velocities belong to the interval. The ambient extension is literally zero
outside the interval, as required for killed-kernel composition.
-/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Interval
open Set MeasureTheory HypoellipticAleksandrov
open HypoellipticAleksandrov.KineticAleksandrov.SectionTwo
open HypoellipticAleksandrov.KineticAleksandrov.Decay

variable {a c : ℝ}

/- The displacement Fourier measure, with initial position zero and velocity in `J`. -/
def intervalFourierKernel
    (K : MovingFiberKernel (PDE.oneDimensionalAxisBox a c) stationary)
    (σ τ : ℝ) (hστ : σ ≤ τ) (ξ : PDE.Vec 1)
    (v : PDE.oneDimensionalAxisBox a c) : ComplexMeasure (PDE.Vec 1) :=
  fourierProjection K (movingQuery σ τ hστ v.1 0
    (by simpa only [movingDomain_stationary] using v.2)) ξ

/- Characterization by the same ambient master measure and Fourier phase. -/
theorem intervalFourierKernel_spec
    (K : MovingFiberKernel (PDE.oneDimensionalAxisBox a c) stationary)
    (σ τ : ℝ) (hστ : σ ≤ τ) (ξ : PDE.Vec 1)
    (v : PDE.oneDimensionalAxisBox a c) :
    IsFourierProjection K (movingQuery σ τ hστ v.1 0
      (by simpa only [movingDomain_stationary] using v.2)) ξ
      (intervalFourierKernel K σ τ hστ ξ v) :=
  fourierProjection_spec K _ ξ

/- The interval kernel is Borel in its starting velocity. -/
def intervalFourierKernelZero
    (K : MovingFiberKernel (PDE.oneDimensionalAxisBox a c) stationary)
    (σ τ : ℝ) (hστ : σ ≤ τ) (ξ : PDE.Vec 1) :
    PDE.Vec 1 → ComplexMeasure (PDE.Vec 1) :=
  Function.extend Subtype.val (intervalFourierKernel K σ τ hστ ξ) (fun _ => 0)

/- The zero extension agrees with the actual kernel at every interval velocity. -/
theorem intervalFourierKernelZero_coe
    (K : MovingFiberKernel (PDE.oneDimensionalAxisBox a c) stationary)
    (σ τ : ℝ) (hστ : σ ≤ τ) (ξ : PDE.Vec 1)
    (v : PDE.oneDimensionalAxisBox a c) :
    intervalFourierKernelZero K σ τ hστ ξ v.1 =
      intervalFourierKernel K σ τ hστ ξ v :=
  Subtype.val_injective.extend_apply _ _ v

/- Outside the interval the extension is the zero measure. -/
theorem intervalFourierKernelZero_of_notMem
    (K : MovingFiberKernel (PDE.oneDimensionalAxisBox a c) stationary)
    (σ τ : ℝ) (hστ : σ ≤ τ) (ξ v : PDE.Vec 1)
    (hv : v ∉ PDE.oneDimensionalAxisBox a c) :
    intervalFourierKernelZero K σ τ hστ ξ v = 0 := by
  exact Function.extend_apply' _ _ v (by
    rintro ⟨w, rfl⟩
    exact hv w.2)

/- The killed Fourier kernel is a contraction. -/
theorem intervalFourierKernel_totalVariation_le_one
    (K : MovingFiberKernel (PDE.oneDimensionalAxisBox a c) stationary)
    (σ τ : ℝ) (hστ : σ ≤ τ) (ξ : PDE.Vec 1)
    (v : PDE.oneDimensionalAxisBox a c) :
    totalVariationNorm (intervalFourierKernel K σ τ hστ ξ v) ≤ 1 :=
  fourierProjection_totalVariation_le_one K _ ξ _
    (intervalFourierKernel_spec K σ τ hστ ξ v)

/- At zero frequency the kernel is exactly its positive velocity marginal. -/
theorem intervalFourierKernel_zero
    (K : MovingFiberKernel (PDE.oneDimensionalAxisBox a c) stationary)
    (σ τ : ℝ) (hστ : σ ≤ τ) (v : PDE.oneDimensionalAxisBox a c) :
    intervalFourierKernel K σ τ hστ 0 v =
      (K.firstMarginal (movingQuery σ τ hστ v.1 0
        (by simpa only [movingDomain_stationary] using v.2))).withDensityᵥ
          (fun _ => (1 : ℂ)) :=
  fourierProjection_zero_measure K _ _ (intervalFourierKernel_spec K σ τ hστ 0 v)

/- Covariance removes the initial position on the interval, without changing its geometry. -/
end HypoellipticAleksandrov.KineticAleksandrov.Interval
