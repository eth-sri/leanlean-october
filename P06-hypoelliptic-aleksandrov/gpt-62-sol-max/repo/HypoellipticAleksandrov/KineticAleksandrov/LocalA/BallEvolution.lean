module

public import HypoellipticAleksandrov.KineticAleksandrov.ClassicalInputs
public import HypoellipticAleksandrov.KineticAleksandrov.LocalA.Geometry
public import HypoellipticAleksandrov.KineticAleksandrov.SectionTwo.Realization
import HypoellipticAleksandrov.KineticAleksandrov.SectionTwo.Uniqueness
import HypoellipticAleksandrov.KineticAleksandrov.Evolution.Assembly

/-! # Unique velocity-ball terminal evolution

The terminal evolution theorem supplies existence; uniqueness fixes both the
operator family and its master kernel. The existence and uniqueness statements are proved before
any choice-based boundary construction.
-/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.LocalA
open Set MeasureTheory SectionTwo Parabolic

section
variable {d : ℕ}

/-- Operator family and kernel on the stationary Euclidean velocity ball. -/
abbrev LocalBallEvolution (v₀ : PDE.Vec d) (R : ℝ) :=
  TerminalOperatorFamily (PDE.euclideanBall v₀ R) (fun _ => 0) ×
    MovingFiberKernel (PDE.euclideanBall v₀ R) (fun _ => 0)

/-- Positive-radius Euclidean balls satisfy the source domain admissibility criterion. -/
theorem localBall_admissible (v₀ : PDE.Vec d) {R : ℝ} (hR : 0 < R) :
    IsAdmissibleEvolutionDomain (PDE.euclideanBall v₀ R) :=
  Or.inr (Or.inl ⟨v₀, R, hR, rfl⟩)

/-- Ball terminal evolution is unique, relative only to the two analytic hypotheses. -/
theorem existsUnique_localBallEvolution (hd : 1 ≤ d) {lam Lam : ℝ}
    (B : CoefficientField d) (hB : IsSectionTwoCoefficient lam Lam B)
    (v₀ : PDE.Vec d) {R : ℝ} (hR : 0 < R) :
    ∃! E : LocalBallEvolution v₀ R,
      RealizesTerminalEvolution (PDE.euclideanBall v₀ R) (fun _ => 0)
        (PDE.isOpen_euclideanBall v₀ R).measurableSet
        (zIndependentCoefficient B) (identityDrift d) E.1 E.2 := 
  (exists_terminalEvolution_of_classical.timeVelocity hd (localBall_admissible v₀ hR) B hB).existsUnique_realization

end

end HypoellipticAleksandrov.KineticAleksandrov.LocalA
