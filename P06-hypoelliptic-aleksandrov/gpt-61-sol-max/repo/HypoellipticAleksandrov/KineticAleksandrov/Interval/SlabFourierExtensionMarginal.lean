module

public import HypoellipticAleksandrov.KineticAleksandrov.Interval.SlabFourierExtensionCovariance

/-! # First marginals of the zero extension

The adapter agrees at interior starts and vanishes at exterior starts.
-/

 public section

namespace HypoellipticAleksandrov.KineticAleksandrov.Interval
open Set MeasureTheory
open HypoellipticAleksandrov.KineticAleksandrov.SectionTwo
open HypoellipticAleksandrov.KineticAleksandrov.Decay

variable {a c : ℝ} (hJ : MeasurableSet (PDE.oneDimensionalAxisBox a c))

variable (K : MovingFiberKernel (PDE.oneDimensionalAxisBox a c) stationary) (σ τ : ℝ) (hστ : σ ≤ τ)

/-- Whole-space scalar queries inside the interval recover the original first marginal. -/
theorem intervalExtension_first_inside
     (v : PDE.oneDimensionalAxisBox a c) :
    (intervalExtension hJ K).firstMarginal (wholeSpaceQuery σ τ hστ v.1 0) =
      K.firstMarginal (movingQuery σ τ hστ v.1 0
        (by simpa only [movingDomain_stationary] using v.2)) := by
  unfold MovingFiberKernel.firstMarginal
  rw [ProbabilityTheory.Kernel.fst_apply, ProbabilityTheory.Kernel.fst_apply]
  congr 1
  change intervalExtensionMaster hJ K (intervalQueryInclusion
    (movingQuery σ τ hστ v.1 0
      (by simpa only [movingDomain_stationary] using v.2))) = _
  exact intervalExtensionMaster_inside hJ K _

/-- Whole-space first marginals vanish when the starting velocity is exterior. -/
theorem intervalExtension_first_outside
     (v : PDE.Vec 1)
    (hv : v ∉ PDE.oneDimensionalAxisBox a c) :
    (intervalExtension hJ K).firstMarginal (wholeSpaceQuery σ τ hστ v 0) = 0 := by
  unfold MovingFiberKernel.firstMarginal
  rw [ProbabilityTheory.Kernel.fst_apply]
  change Measure.map Prod.fst (intervalExtensionMaster hJ K
    (wholeSpaceQuery σ τ hστ v 0)) = 0
  rw [intervalExtensionMaster_outside hJ K _ hv, Measure.map_zero]

include hJ in
/-- Pulling an ambient finite measure back to the actual interval cannot increase mass. -/
theorem intervalInitial_comap_mass_le  (ρ : Measure (PDE.Vec 1)) :
    (Measure.comap (Subtype.val : PDE.oneDimensionalAxisBox a c → PDE.Vec 1) ρ) univ ≤
      ρ univ := by
  rw [(MeasurableEmbedding.subtype_coe hJ).comap_apply ρ univ]
  exact measure_mono (subset_univ _)

end HypoellipticAleksandrov.KineticAleksandrov.Interval
