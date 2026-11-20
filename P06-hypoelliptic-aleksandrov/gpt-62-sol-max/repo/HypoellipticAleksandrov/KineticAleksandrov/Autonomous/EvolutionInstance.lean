module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.FullCoefficientAdapters
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.Assembly
public import HypoellipticAleksandrov.KineticAleksandrov.SectionTwo.Uniqueness

/-! # The unique autonomous killed evolution on a velocity interval

The diffused coordinate is physical velocity; the transported coordinate is physical position.
Only the Lieberman ellipsoid and Hörmander inputs are used.
-/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov
open HypoellipticAleksandrov.KineticAleksandrov.SectionTwo

/-- All stationary autonomous domains use the same identity-drift specialization. -/
theorem autonomous_terminalEvolution {lam Lam : ℝ} (A : SmoothAutonomous lam Lam)
    {Ω : Set (PDE.Vec 1)} (hΩ : IsAdmissibleEvolutionDomain Ω) :
    TerminalEvolutionResult Ω (fun _ => 0) (evolutionCoefficient A.a) (identityDrift 1) hΩ :=
  exists_terminalEvolution_of_classical.stationary le_rfl A.positive A.ordered hΩ
    (evolutionCoefficient_smooth A) (evolutionCoefficient_symmetric A.a) (evolutionCoefficient_bounds A)

section
variable (H : Interval)
include H

/-- The literal interval in the one-dimensional diffused coordinate. -/
def intervalDomain : Set (PDE.Vec 1) :=
  PDE.oneDimensionalAxisBox H.lo H.hi

/-- A nonempty bounded velocity interval is an admissible evolution domain. -/
theorem intervalDomain_admissible :
    IsAdmissibleEvolutionDomain (intervalDomain H) :=
  Or.inr (Or.inr ⟨rfl, H.lo, H.hi, H.ordered, rfl⟩)

/-- The literal interval domain is Borel. -/
theorem intervalDomain_measurable : MeasurableSet (intervalDomain H) :=
  measurableSet_of_isAdmissibleEvolutionDomain (intervalDomain_admissible H)

/-- A pair of operator and kernel families on the stationary interval. -/
abbrev StripEvolution :=
  TerminalOperatorFamily (intervalDomain H) (fun _ => 0) ×
    MovingFiberKernel (intervalDomain H) (fun _ => 0)

end

section
variable {lam Lam : ℝ} (A : SmoothAutonomous lam Lam) (H : Interval)
include lam Lam A

/-- The autonomous realization, with the physical position and velocity correctly exchanged. -/
def IsStripEvolution
    (E : StripEvolution H) : Prop :=
  RealizesTerminalEvolution (intervalDomain H) (fun _ => 0) (intervalDomain_measurable H)
    (evolutionCoefficient A.a) (identityDrift 1) E.1 E.2

/-- Existence and uniqueness precede the definition of a canonical killed family. -/
theorem existsUnique_stripEvolution :
    ∃! E : StripEvolution H, IsStripEvolution A H E := 
  (autonomous_terminalEvolution A (intervalDomain_admissible H)).existsUnique_realization

/-- The canonical pair is chosen solely from its proved unique characterization. -/
def stripEvolution : StripEvolution H :=
  (existsUnique_stripEvolution A H).exists.choose

/-- The canonical pair realizes precisely the autonomous operator on the interval. -/
theorem stripEvolution_spec :
    IsStripEvolution A H (stripEvolution A H) :=
  (existsUnique_stripEvolution A H).exists.choose_spec

end

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
