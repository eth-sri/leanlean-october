module

public import HypoellipticAleksandrov.KineticAleksandrov.Interval.SlabFourierExtensionCovariance

/-! # First marginals of the zero extension

The adapter agrees at interior starts and vanishes at exterior starts.
-/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Interval
open Set MeasureTheory HypoellipticAleksandrov
open HypoellipticAleksandrov.KineticAleksandrov.SectionTwo
open HypoellipticAleksandrov.KineticAleksandrov.Decay

/- Whole-space scalar queries inside the interval recover the original first marginal. -/
theorem intervalExtension_first_outside {a c }
    (hJ : MeasurableSet (PDE.oneDimensionalAxisBox a c))
    (K : MovingFiberKernel (PDE.oneDimensionalAxisBox a c) stationary)
    (σ τ : ℝ) (hστ : σ ≤ τ) (v : PDE.Vec 1)
    (hv : v ∉ PDE.oneDimensionalAxisBox a c) :
    (intervalExtension hJ K).firstMarginal (wholeSpaceQuery σ τ hστ v 0) = 0 := by
  unfold MovingFiberKernel.firstMarginal
  rw [ProbabilityTheory.Kernel.fst_apply]
  change Measure.map Prod.fst (intervalExtensionMaster hJ K
    (wholeSpaceQuery σ τ hστ v 0)) = 0
  rw [intervalExtensionMaster_outside hJ K _ hv, Measure.map_zero]

/- Pulling an ambient finite measure back to the actual interval cannot increase mass. -/
end HypoellipticAleksandrov.KineticAleksandrov.Interval
