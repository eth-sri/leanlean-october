module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.StripMassInfinite
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.Assembly
public import HypoellipticAleksandrov.KineticAleksandrov.SectionTwo.Uniqueness

/-! # Canonical full-space autonomous evolution

The full-coefficient existence theorem is applied to physical position dependence.
The diffused coordinate is velocity and the transported coordinate is position.
-/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov
open HypoellipticAleksandrov.KineticAleksandrov.SectionTwo

/-- The literal full velocity domain. -/
def autonomousWholeDomain : Set (PDE.Vec 1) := univ

/-- The full velocity domain is an admissible evolution domain. -/
theorem autonomousWholeDomain_admissible : IsAdmissibleEvolutionDomain autonomousWholeDomain :=
  Or.inl rfl

/-- The full velocity domain is Borel. -/
theorem autonomousWholeDomain_measurable : MeasurableSet autonomousWholeDomain :=
  measurableSet_of_isAdmissibleEvolutionDomain autonomousWholeDomain_admissible

/-- A pair of operator and kernel families on the stationary full domain. -/
abbrev FullSpaceEvolution :=
  TerminalOperatorFamily autonomousWholeDomain (fun _ => 0) ×
    MovingFiberKernel autonomousWholeDomain (fun _ => 0)

section
variable {lam Lam : ℝ} (A : SmoothAutonomous lam Lam)
include lam Lam A

/-- The autonomous realization, with the physical position and velocity correctly exchanged. -/
def IsFullSpaceEvolution
    (E : FullSpaceEvolution) : Prop :=
  RealizesTerminalEvolution autonomousWholeDomain (fun _ => 0) autonomousWholeDomain_measurable
    (evolutionCoefficient A.a) (identityDrift 1) E.1 E.2

/-- Existence and uniqueness precede the definition of a canonical full-space family. -/
theorem existsUnique_fullSpaceEvolution :
    ∃! E : FullSpaceEvolution, IsFullSpaceEvolution A E := 
  (autonomous_terminalEvolution A autonomousWholeDomain_admissible).existsUnique_realization

/-- The canonical pair is chosen solely from its proved unique characterization. -/
def fullSpaceEvolution : FullSpaceEvolution :=
  (existsUnique_fullSpaceEvolution A).exists.choose

/-- The canonical pair realizes precisely the autonomous operator on the whole space. -/
theorem fullSpaceEvolution_spec :
    IsFullSpaceEvolution A (fullSpaceEvolution A) :=
  (existsUnique_fullSpaceEvolution A).exists.choose_spec

end

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
