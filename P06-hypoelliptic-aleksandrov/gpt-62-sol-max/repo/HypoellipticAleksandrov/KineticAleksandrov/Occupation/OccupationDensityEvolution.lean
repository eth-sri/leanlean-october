module

public import HypoellipticAleksandrov.KineticAleksandrov.SectionTwo.Uniqueness

/-!
# The exact evolution premise and transfer to an arbitrary realization

The premise is the terminal evolution statement (companion paper, Proposition 2.1),
spelled out with the clause predicates of `SectionTwo`.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Occupation

open Set MeasureTheory
open HypoellipticAleksandrov HypoellipticAleksandrov.Parabolic
open HypoellipticAleksandrov.KineticAleksandrov.SectionTwo
open scoped MatrixOrder ProbabilityTheory

/-- The terminal evolution conclusion (companion paper, Proposition 2.1). -/
def TerminalEvolutionStatement : Prop := TerminalEvolutionConclusion

/-- The full evolution premise supplies the marginal bundle for every whole-space realization. -/
theorem wholeSpace_marginalBundle_of_evolution
    (hEvol : TerminalEvolutionStatement) {d : ℕ} (hd : 0 < d)
    {lam Lam : ℝ} {B : CoefficientField d} (hB : IsSectionTwoCoefficient lam Lam B)
    (S : TerminalOperatorFamily (wholeSpace d) (fun _ => (0 : PDE.Vec d)))
    (K : MovingFiberKernel (wholeSpace d) (fun _ => (0 : PDE.Vec d)))
    (hreal : RealizesTerminalEvolution (wholeSpace d) (fun _ => (0 : PDE.Vec d))
      MeasurableSet.univ (zIndependentCoefficient B) (identityDrift d) S K) :
    HasParabolicMarginalBundle (wholeSpace d) (fun _ => (0 : PDE.Vec d))
      MeasurableSet.univ (zIndependentCoefficient B) K := 
  (TerminalEvolutionResult.clauses
    (TerminalEvolutionConclusion.timeVelocity hEvol hd (wholeSpace_admissible d) B hB) hreal).2.2

end HypoellipticAleksandrov.KineticAleksandrov.Occupation
