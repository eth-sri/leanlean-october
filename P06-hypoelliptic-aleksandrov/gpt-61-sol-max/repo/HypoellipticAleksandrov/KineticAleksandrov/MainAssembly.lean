module

public import HypoellipticAleksandrov.Statements.HormanderHypoellipticity
public import HypoellipticAleksandrov.Statements.LiebermanDirichlet
public import HypoellipticAleksandrov.KineticAleksandrov.ClassicalInputs
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.Assembly
public import HypoellipticAleksandrov.KineticAleksandrov.TheoremA.Final
public import HypoellipticAleksandrov.KineticAleksandrov.TheoremA.LocalisedFinal
public import HypoellipticAleksandrov.KineticAleksandrov.LocalA.FinalA
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.FinalAutonomous

/-!
# Unconditional proofs of the main statements

The two classical inputs are discharged from the theorems in `Statements`, and the seven final
statements are proved from the existing internal theorems with no extra hypotheses.
-/

 public section

-- The statement types are verbatim copies of the statements in `Statements`, which name binders
-- that occur only inside nested types.
set_option linter.unusedVariables false
namespace HypoellipticAleksandrov.KineticAleksandrov
open MeasureTheory Set Autonomous Holder LocalA
open HypoellipticAleksandrov.Parabolic
open scoped MatrixOrder ProbabilityTheory

/-- Hörmander hypoellipticity, from the statement in `Statements`. -/
theorem hormanderHypoellipticityStatement_holds : HormanderHypoellipticityStatement :=
  exists_smooth_aeRepresentative_of_hormander

/-- Lieberman ellipsoid Dirichlet solvability, from the statement in `Statements`. -/
theorem liebermanEllipsoidDirichletStatement_holds : LiebermanEllipsoidDirichletStatement :=
  exists_isClassicalBackwardDirichletSolution_openEllipsoid_uniqueOn_of_lieberman

variable (d : ℕ) (hd : 1 ≤ d)

section
variable (lam Lam p : ℝ) (hlam : 0 < lam) (hLam : lam ≤ Lam) (hp : 2 * (d : ℝ) + 1 < p)

include hd hlam hLam hp
/-- Companion paper, Theorem 1.1 (time-velocity coefficients), with no extra hypotheses. -/
theorem kinetic_aleksandrov_timeVelocity_proof
      : type_of% (kinetic_aleksandrov_timeVelocity_of_terminalEvolution d hd lam Lam p hlam hLam hp
    (exists_terminalEvolution_of_classical liebermanEllipsoidDirichletStatement_holds
      hormanderHypoellipticityStatement_holds)
    hormanderHypoellipticityStatement_holds) := kinetic_aleksandrov_timeVelocity_of_terminalEvolution d hd lam Lam p hlam hLam hp
    (exists_terminalEvolution_of_classical liebermanEllipsoidDirichletStatement_holds
      hormanderHypoellipticityStatement_holds)
    hormanderHypoellipticityStatement_holds

/-- Companion paper, Corollary 1.3 for time-velocity coefficients, with no extra hypotheses. -/
theorem kinetic_aleksandrov_timeVelocity_localised_proof
      : type_of% (kinetic_aleksandrov_timeVelocity_localised_of_terminalEvolution
    d hd lam Lam p hlam hLam hp
    (exists_terminalEvolution_of_classical liebermanEllipsoidDirichletStatement_holds
      hormanderHypoellipticityStatement_holds)
    hormanderHypoellipticityStatement_holds) := kinetic_aleksandrov_timeVelocity_localised_of_terminalEvolution
    d hd lam Lam p hlam hLam hp
    (exists_terminalEvolution_of_classical liebermanEllipsoidDirichletStatement_holds
      hormanderHypoellipticityStatement_holds)
    hormanderHypoellipticityStatement_holds
end


include hd in
/-- Companion paper, Corollary 9.9, with no extra hypotheses. -/
theorem kinetic_holder_timeVelocity_proof
     (lam Lam : ℝ) (hlam : 0 < lam) (hLam : lam ≤ Lam) : type_of% (kinetic_holder_timeVelocity_relative_of_smooth
    smoothLocalRegularityStatement_holds hormanderHypoellipticityStatement_holds
    liebermanEllipsoidDirichletStatement_holds d hd lam Lam hlam hLam) := kinetic_holder_timeVelocity_relative_of_smooth
    smoothLocalRegularityStatement_holds hormanderHypoellipticityStatement_holds
    liebermanEllipsoidDirichletStatement_holds d hd lam Lam hlam hLam

/-- Companion paper, Theorem 1.2 (autonomous coefficients), with no extra hypotheses. -/
theorem kinetic_aleksandrov_autonomous_proof
    (lam Lam p : ℝ) (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (hp : 1 + bellmanAdjointExponent (Lam / lam)
      ((le_div_iff₀ hlam).2 (by simpa)) < p) : type_of% (kinetic_aleksandrov_autonomous_relative_of_frontier
    autonomousRemainingFrontier_holds hormanderHypoellipticityStatement_holds
    liebermanEllipsoidDirichletStatement_holds lam Lam p hlam hLam hp) := kinetic_aleksandrov_autonomous_relative_of_frontier
    autonomousRemainingFrontier_holds hormanderHypoellipticityStatement_holds
    liebermanEllipsoidDirichletStatement_holds lam Lam p hlam hLam hp

/-- Companion paper, Corollary 1.3 for autonomous coefficients, with no extra hypotheses. -/
theorem kinetic_aleksandrov_autonomous_localised_proof
    (lam Lam p : ℝ) (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (hp : 1 + bellmanAdjointExponent (Lam / lam)
      ((le_div_iff₀ hlam).2 (by simpa)) < p) : type_of% (kinetic_aleksandrov_autonomous_localised_relative_of_frontier
    autonomousRemainingFrontier_holds hormanderHypoellipticityStatement_holds
    liebermanEllipsoidDirichletStatement_holds lam Lam p hlam hLam hp) := kinetic_aleksandrov_autonomous_localised_relative_of_frontier
    autonomousRemainingFrontier_holds hormanderHypoellipticityStatement_holds
    liebermanEllipsoidDirichletStatement_holds lam Lam p hlam hLam hp

/-- Companion paper, Corollary 9.10, with no extra hypotheses. -/
theorem kinetic_holder_autonomous_proof
    (lam Lam : ℝ) (hlam : 0 < lam) (hLam : lam ≤ Lam) : type_of% (kinetic_holder_autonomous_relative_of_frontier
    autonomousRemainingFrontier_holds hormanderHypoellipticityStatement_holds
    liebermanEllipsoidDirichletStatement_holds lam Lam hlam hLam) := kinetic_holder_autonomous_relative_of_frontier
    autonomousRemainingFrontier_holds hormanderHypoellipticityStatement_holds
    liebermanEllipsoidDirichletStatement_holds lam Lam hlam hLam

end HypoellipticAleksandrov.KineticAleksandrov
