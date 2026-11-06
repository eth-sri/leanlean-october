module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.EvolutionInstance
public import HypoellipticAleksandrov.KineticAleksandrov.LocalA.BoundedSourceWeak

/-! # Autonomous strip specialization of the shared bounded-source weak theorem

The shared signed Borel-source identity supplies the forcing equation. No smoothness or
separation from the velocity faces is imposed on the source.
-/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open HypoellipticAleksandrov MeasureTheory
open SectionTwo Evolution

/-- Every bounded Borel source has the actual weak Duhamel forcing equation on the strip. -/
theorem strip_duhamel_weak {lam Lam : ℝ} (A : SmoothAutonomous lam Lam)
    (H : Interval) (E : StripEvolution H) (hE : IsStripEvolution A H E)
    (T : ℝ) (g : BoundedBorel Point) :
    IsKineticWeakTransportedSolution (evolutionCoefficient A.a) (identityDrift 1)
      (evolutionPastOpenCylinder (intervalDomain H) (fun _ => 0) T)
      (duhamelPotential E.2 T g) (fun p => -g p) := by
  obtain ⟨C, hC, hg⟩ := g.exists_bound
  exact duhamel_bounded_isKineticWeakTransportedSolution (intervalDomain_admissible H)
    (intervalDomain_measurable H) continuous_const (evolutionCoefficient A.a)
    (identityDrift 1) E.1 E.2 hE (evolutionCoefficient_smooth A)
    (evolutionCoefficient_symmetric A.a) (identityDrift_smooth 1)
    g g.measurable C hC hg T

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
