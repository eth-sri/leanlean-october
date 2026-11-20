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

variable {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam) (A : SmoothAutonomous lam Lam)
    (H : Interval)

include H in
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

include H in
/-- A pair of operator and kernel families on the stationary interval. -/
abbrev StripEvolution :=
  TerminalOperatorFamily (intervalDomain H) (fun _ => 0) ×
    MovingFiberKernel (intervalDomain H) (fun _ => 0)

include A in
/-- The autonomous realization, with the physical position and velocity correctly exchanged. -/
def IsStripEvolution
    (E : StripEvolution H) : Prop :=
  RealizesTerminalEvolution (intervalDomain H) (fun _ => 0) (intervalDomain_measurable H)
    (evolutionCoefficient A.a) (identityDrift 1) E.1 E.2

include hlam hLam in
/-- The autonomous killed evolution is supplied by the full-coefficient existence theorem. -/
theorem autonomous_evolution_instance :
    ∃ E : StripEvolution H, IsStripEvolution A H E := by
  obtain ⟨S, K, hc, -, -, -, -, hi, -, -, -, -, he, hcomp, -, -, -⟩ :=
    exists_terminalEvolution_of_classical 1 (by omega) lam Lam 1 1
      hlam hLam one_pos le_rfl (intervalDomain H) (fun _ => 0)
      (evolutionCoefficient A.a) (identityDrift 1) (intervalDomain_admissible H)
      (zeroCurve_piecewiseC1 1) (evolutionCoefficient_smooth A)
      (evolutionCoefficient_symmetric A.a) (evolutionCoefficient_bounds A)
      (identityDrift_smooth 1) (identityDrift_bounds 1).1 (identityDrift_bounds 1).2
  exact ⟨(S, K), hc, hi, he, hcomp⟩

/-- Uniqueness holds for every realizing pair, rather than for a selected construction. -/
theorem stripEvolution_unique (E E' : StripEvolution H)
    (hE : IsStripEvolution A H E) (hE' : IsStripEvolution A H E') : E = E' := by
  obtain ⟨hS, hK⟩ := terminalEvolution_unique (intervalDomain H) (fun _ => 0)
    (intervalDomain_admissible H) (evolutionCoefficient A.a) (identityDrift 1)
    E.1 E'.1 E.2 E'.2 hE hE'
  exact Prod.ext hS hK

include hlam hLam in
/-- Existence and uniqueness precede the definition of a canonical killed family. -/
theorem existsUnique_stripEvolution :
    ∃! E : StripEvolution H, IsStripEvolution A H E := by
  obtain ⟨E, hE⟩ := autonomous_evolution_instance hlam hLam A H
  exact ⟨E, hE, fun E' hE' => stripEvolution_unique A H E' E hE' hE⟩

include hlam hLam A in
/-- The canonical pair is chosen solely from its proved unique characterization. -/
def stripEvolution : StripEvolution H :=
  (existsUnique_stripEvolution hlam hLam A H).exists.choose

/-- The canonical pair realizes precisely the autonomous operator on the interval. -/
theorem stripEvolution_spec :
    IsStripEvolution A H (stripEvolution hlam hLam A H) :=
  (existsUnique_stripEvolution hlam hLam A H).exists.choose_spec

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
