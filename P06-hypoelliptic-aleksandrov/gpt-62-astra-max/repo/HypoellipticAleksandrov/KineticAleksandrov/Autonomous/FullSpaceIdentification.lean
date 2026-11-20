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

variable {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam) (A : SmoothAutonomous lam Lam)

include A in
/-- The autonomous realization, with the physical position and velocity correctly exchanged. -/
def IsFullSpaceEvolution
    (E : FullSpaceEvolution) : Prop :=
  RealizesTerminalEvolution autonomousWholeDomain (fun _ => 0) autonomousWholeDomain_measurable
    (evolutionCoefficient A.a) (identityDrift 1) E.1 E.2

include hlam hLam in
/-- The autonomous full-space evolution is supplied by the full-coefficient existence theorem. -/
theorem autonomous_fullspace_instance :
    ∃ E : FullSpaceEvolution, IsFullSpaceEvolution A E := by
  obtain ⟨S, K, hc, -, -, -, -, hi, -, -, -, -, he, hcomp, -, -, -⟩ :=
    exists_terminalEvolution_of_classical 1 (by omega) lam Lam 1 1
      hlam hLam one_pos le_rfl autonomousWholeDomain (fun _ => 0)
      (evolutionCoefficient A.a) (identityDrift 1) autonomousWholeDomain_admissible
      (zeroCurve_piecewiseC1 1) (evolutionCoefficient_smooth A)
      (evolutionCoefficient_symmetric A.a) (evolutionCoefficient_bounds A)
      (identityDrift_smooth 1) (identityDrift_bounds 1).1 (identityDrift_bounds 1).2
  exact ⟨(S, K), hc, hi, he, hcomp⟩

/-- Uniqueness holds for every realizing pair, rather than for a selected construction. -/
theorem fullSpaceEvolution_unique
    (E E' : FullSpaceEvolution)
    (hE : IsFullSpaceEvolution A E) (hE' : IsFullSpaceEvolution A E') : E = E' := by
  obtain ⟨hS, hK⟩ := terminalEvolution_unique autonomousWholeDomain (fun _ => 0)
    autonomousWholeDomain_admissible (evolutionCoefficient A.a) (identityDrift 1)
    E.1 E'.1 E.2 E'.2 hE hE'
  exact Prod.ext hS hK

include hlam hLam in
/-- Existence and uniqueness precede the definition of a canonical full-space family. -/
theorem existsUnique_fullSpaceEvolution :
    ∃! E : FullSpaceEvolution, IsFullSpaceEvolution A E := by
  obtain ⟨E, hE⟩ := autonomous_fullspace_instance hlam hLam A
  exact ⟨E, hE, fun E' hE' => fullSpaceEvolution_unique A E' E hE' hE⟩

include hlam hLam A in
/-- The canonical pair is chosen solely from its proved unique characterization. -/
def fullSpaceEvolution : FullSpaceEvolution :=
  (existsUnique_fullSpaceEvolution hlam hLam A).exists.choose

/-- The canonical pair realizes precisely the autonomous operator on the whole space. -/
theorem fullSpaceEvolution_spec :
    IsFullSpaceEvolution A (fullSpaceEvolution hlam hLam A) :=
  (existsUnique_fullSpaceEvolution hlam hLam A).exists.choose_spec

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
