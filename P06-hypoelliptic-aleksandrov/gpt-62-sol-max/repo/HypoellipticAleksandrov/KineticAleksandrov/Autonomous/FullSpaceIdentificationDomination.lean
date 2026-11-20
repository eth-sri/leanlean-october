module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.FullSpaceIdentification

/-! # Zero-extension domination of every supplied velocity-strip kernel -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open HypoellipticAleksandrov Set MeasureTheory
open HypoellipticAleksandrov.KineticAleksandrov.SectionTwo

/-- Every stationary velocity interval is contained in the full velocity domain. -/
theorem strip_subset_fullspace (H : Interval) (t : ℝ) :
    movingDomain (intervalDomain H) (fun _ => 0) t ⊆
      movingDomain autonomousWholeDomain (fun _ => 0) t := by
  change _ ⊆ movingDomain (wholeSpace 1) (fun _ => 0) t
  rw [movingDomain_wholeSpace]
  exact subset_univ _

section
variable {lam Lam : ℝ} (A : SmoothAutonomous lam Lam) (E : FullSpaceEvolution)
  (hE : IsFullSpaceEvolution A E)
include hE

/-- Every realizing full-space kernel inherits domain domination from the evolution theorem. -/
theorem fullspace_domainMonotone :
    IsDomainMonotoneEvolution autonomousWholeDomain (fun _ => 0)
      (evolutionCoefficient A.a) (identityDrift 1) E.2 := 
  ((autonomous_terminalEvolution A autonomousWholeDomain_admissible).clauses hE).2.1

/-- Every supplied strip realization is measure dominated by the supplied full-space one. -/
theorem strip_kernel_le_fullspace
    (H : Interval) (G : StripEvolution H) (hG : IsStripEvolution A H G) :
    MovingFiberKernel.IsZeroExtensionDominatedBy G.2 E.2 (strip_subset_fullspace H) :=
  domainMonotone_of_realizes (evolutionCoefficient A.a) (identityDrift 1) E.2
    (fullspace_domainMonotone A E hE)
    (intervalDomain H) (fun _ => 0) (intervalDomain_admissible H)
    (zeroCurve_piecewiseC1 1) (strip_subset_fullspace H) G.1 G.2 hG

end

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
