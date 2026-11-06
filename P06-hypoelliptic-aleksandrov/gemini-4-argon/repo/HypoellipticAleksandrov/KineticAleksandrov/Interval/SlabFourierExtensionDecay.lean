module

public import HypoellipticAleksandrov.KineticAleksandrov.Interval.SlabFourierExtensionOccupation
import HypoellipticAleksandrov.KineticAleksandrov.Interval.BlockScaling
import HypoellipticAleksandrov.KineticAleksandrov.Interval.DecayBlocks
import HypoellipticAleksandrov.KineticAleksandrov.Interval.DecayFrequency
import HypoellipticAleksandrov.KineticAleksandrov.Interval.DecayMass

/-! # Fourier decay on the zero-extension carrier

Interior Fourier measures are unchanged. Exterior ones vanish. Thus the proved
interval killing and frequency decay apply on the full ambient starting carrier.
-/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Interval
open Set MeasureTheory HypoellipticAleksandrov
open HypoellipticAleksandrov.KineticAleksandrov.SectionTwo
open HypoellipticAleksandrov.KineticAleksandrov.Decay
open scoped ENNReal

/- Interior Fourier measures of the carrier adapter are exactly the interval Fourier measures. -/
theorem intervalExtension_fourier_inside {a c }
    (hJ : MeasurableSet (PDE.oneDimensionalAxisBox a c))
    (K : MovingFiberKernel (PDE.oneDimensionalAxisBox a c) stationary)
    (σ τ : ℝ) (hστ : σ ≤ τ) (ξ : PDE.Vec 1) (v : PDE.oneDimensionalAxisBox a c) :
    fourierKernel (intervalExtension hJ K) σ τ hστ ξ v.1 =
      intervalFourierKernel K σ τ hστ ξ v := by
  have he : (intervalExtension hJ K).master (wholeSpaceQuery σ τ hστ v.1 0) =
      K.master (movingQuery σ τ hστ v.1 0
        (by simpa only [movingDomain_stationary] using v.2)) := by
    change intervalExtensionMaster hJ K (intervalQueryInclusion
      (movingQuery σ τ hστ v.1 0
        (by simpa only [movingDomain_stationary] using v.2))) = _
    exact intervalExtensionMaster_inside hJ K _
  apply VectorMeasure.ext
  intro E hE
  rw [fourierKernel_spec _ _ _ _ _ _ E hE,
    intervalFourierKernel_spec _ _ _ _ _ _ E hE, he]
  rfl

/- Exterior Fourier measures of the carrier adapter vanish. -/
end HypoellipticAleksandrov.KineticAleksandrov.Interval
