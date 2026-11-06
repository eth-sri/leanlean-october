module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.VisitRecursionUnconditionalKernels

/-! # No-loss conversion from physical measures to subtype pole mixtures -/

 public section

namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory ProbabilityTheory
open scoped Classical

/-- Pulling a supported physical measure to its pole subtype and mapping it back loses no mass. -/
theorem visitPoleMeasure_map_comap (D : Set Point) (hD : MeasurableSet D)
    (mu : Measure Point) (hmu : ∀ᵐ p ∂mu, p ∈ D) :
    (mu.comap (Subtype.val : D → Point)).map Subtype.val = mu := by
  rw [map_comap_subtype_coe hD, Measure.restrict_eq_self_of_ae_mem hmu]

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
