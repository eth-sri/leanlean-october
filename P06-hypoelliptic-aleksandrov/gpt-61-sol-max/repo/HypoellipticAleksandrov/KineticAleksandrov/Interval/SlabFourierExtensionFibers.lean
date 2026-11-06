module

public import HypoellipticAleksandrov.KineticAleksandrov.Interval.SlabFourierExtension

/-! # Fixed-time fibers of the zero extension

Interior fibers are the exact pushforwards under inclusion of interval states.
Exterior starting fibers vanish.
-/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Interval
open MeasureTheory
open HypoellipticAleksandrov.KineticAleksandrov.SectionTwo
open HypoellipticAleksandrov.KineticAleksandrov.Decay

variable {a c : ℝ}

variable (σ : ℝ)

/-- Include an interval state in the whole-space fiber at the same time. -/
def intervalStateInclusion   :
    EvolutionState (PDE.oneDimensionalAxisBox a c) stationary σ →
      EvolutionState (wholeSpace 1) (fun _ => (0 )) σ :=
  fun p => ⟨p.1, by rw [evolutionStateSet, movingDomain_wholeSpace]; trivial⟩

/-- The fixed-time state inclusion is measurable. -/
theorem measurable_intervalStateInclusion   :
    Measurable (intervalStateInclusion (a := a) (c := c) σ) :=
  measurable_subtype_coe.subtype_mk

variable (hJ : MeasurableSet (PDE.oneDimensionalAxisBox a c)) (K : MovingFiberKernel (PDE.oneDimensionalAxisBox a c) stationary)

/-- Exterior queries have zero master measure under the extension. -/
theorem intervalExtensionMaster_outside

    (q : EvolutionQuery (wholeSpace 1) (fun _ => (0 )))
    (hq : q.1.2.2.1 ∉ PDE.oneDimensionalAxisBox a c) :
    intervalExtensionMaster hJ K q = 0 := by
  change Function.extend intervalQueryInclusion K.master (fun _ => 0) q = 0
  apply Function.extend_apply'
  rintro ⟨p, hp⟩
  have he : p.1 = q.1 := congrArg Subtype.val hp
  apply hq
  rw [← he]
  simpa only [movingDomain_stationary] using p.2.2.1

variable (σ τ : ℝ) (hστ : σ ≤ τ)

/-- Interior extended fibers are literal pushforwards of the original interval fibers. -/
theorem intervalExtension_fiber_inside


    (p : EvolutionState (PDE.oneDimensionalAxisBox a c) stationary σ) :
    (intervalExtension hJ K).fiberKernel intervalWholeSpace_measurable σ τ hστ
      (intervalStateInclusion σ p) =
      (K.fiberKernel hJ σ τ hστ p).map (intervalStateInclusion τ) := by
  apply (MeasurableEmbedding.subtype_coe
    (measurableSet_evolutionStateSet intervalWholeSpace_measurable τ)).map_injective
  rw [(intervalExtension hJ K).map_fiberKernel_eq_master intervalWholeSpace_measurable,
    Measure.map_map measurable_subtype_coe (measurable_intervalStateInclusion τ)]
  change intervalExtensionMaster hJ K
    (intervalQueryInclusion (evolutionQueryOfState _
      stationary σ τ hστ p)) =
    (K.fiberKernel hJ σ τ hστ p).map Subtype.val
  rw [intervalExtensionMaster_inside, K.map_fiberKernel_eq_master]

/-- Starting outside the interval gives the zero fixed-time fiber. -/
theorem intervalExtension_fiber_outside


    (p : EvolutionState (wholeSpace 1) (fun _ => (0 )) σ)
    (hp : p.1.1 ∉ PDE.oneDimensionalAxisBox a c) :
    (intervalExtension hJ K).fiberKernel intervalWholeSpace_measurable σ τ hστ p = 0 := by
  rw [MovingFiberKernel.fiberKernel_apply]
  change Measure.comap Subtype.val (intervalExtensionMaster hJ K
    (evolutionQueryOfState (wholeSpace 1) _ σ τ hστ p)) = 0
  rw [intervalExtensionMaster_outside hJ K _ hp, Measure.comap_zero]

end HypoellipticAleksandrov.KineticAleksandrov.Interval
