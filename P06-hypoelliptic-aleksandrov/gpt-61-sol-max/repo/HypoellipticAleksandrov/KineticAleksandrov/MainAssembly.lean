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

@[expose] public section
noncomputable section
-- The statement types are verbatim copies of the statements in `Statements`, which name binders
-- that occur only inside nested types.
set_option linter.unusedVariables false
namespace HypoellipticAleksandrov.KineticAleksandrov
open HypoellipticAleksandrov MeasureTheory Set Autonomous Holder LocalA
open HypoellipticAleksandrov.Parabolic
open scoped ENNReal MatrixOrder ProbabilityTheory

/-- Hörmander hypoellipticity, from the statement in `Statements`. -/
theorem hormanderHypoellipticityStatement_holds : HormanderHypoellipticityStatement :=
  fun hΩ X c g u hX hspan hc hEq =>
    exists_smooth_aeRepresentative_of_hormander hΩ X c g u hX hspan hc hEq

/-- Lieberman ellipsoid Dirichlet solvability, from the statement in `Statements`. -/
theorem liebermanEllipsoidDirichletStatement_holds : LiebermanEllipsoidDirichletStatement :=
  fun hQ hr lam Lam hlam hlamLam a b haSymm haSmooth haLower haUpper hbSmooth φ hφSmooth
      hφCompact hφSupport =>
    exists_isClassicalBackwardDirichletSolution_openEllipsoid_uniqueOn_of_lieberman
      hQ hr lam Lam hlam hlamLam a b haSymm haSmooth haLower haUpper hbSmooth φ hφSmooth
      hφCompact hφSupport

/-- Companion paper, Theorem 1.1 (time-velocity coefficients), with no extra hypotheses. -/
theorem kinetic_aleksandrov_timeVelocity_proof
    (d : ℕ) (hd : 1 ≤ d) (lam Lam p : ℝ)
    (hlam : 0 < lam) (hLam : lam ≤ Lam) (hp : 2 * (d : ℝ) + 1 < p) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (P₀ : KineticPoint d) (R : ℝ), 0 < R →
      ∀ (A : CoefficientField d),
        IsBorelCoefficient A → IsSymmetricCoefficient A →
        HasLowerEllipticityAE lam A → HasUpperEllipticityAE Lam A →
      ∀ (f u : KineticPoint d → ℝ),
        Measurable (fun P : backwardCylinder P₀ R => f P) →
        ContinuousOn u (closure (backwardCylinder P₀ R)) →
        Parabolic.IsKineticC112On u (backwardCylinder P₀ R) →
        (∀ᵐ P ∂(volume.restrict (backwardCylinder P₀ R)),
          backwardOperatorOfTimeVelocityCoefficient A u P ≤ f P) →
        MemLp (fun P => max (f P) 0) (ENNReal.ofReal p)
          (volume.restrict (backwardCylinder P₀ R)) →
        ∀ P ∈ closure (backwardCylinder P₀ R),
          u P ≤ sSup ((fun P => max (u P) 0) '' kineticBoundary P₀ R) +
            C * R ^ (2 - (4 * (d : ℝ) + 2) / p) *
              (eLpNorm (fun P => max (f P) 0) (ENNReal.ofReal p)
                (volume.restrict (backwardCylinder P₀ R))).toReal := by
  exact kinetic_aleksandrov_timeVelocity_of_terminalEvolution d hd lam Lam p hlam hLam hp
    (exists_terminalEvolution_of_classical liebermanEllipsoidDirichletStatement_holds
      hormanderHypoellipticityStatement_holds)
    hormanderHypoellipticityStatement_holds

/-- Companion paper, Corollary 1.3 for time-velocity coefficients, with no extra hypotheses. -/
theorem kinetic_aleksandrov_timeVelocity_localised_proof
    (d : ℕ) (hd : 1 ≤ d) (lam Lam p : ℝ)
    (hlam : 0 < lam) (hLam : lam ≤ Lam) (hp : 2 * (d : ℝ) + 1 < p) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (P₀ : KineticPoint d) (R : ℝ), 0 < R →
      ∀ (A : CoefficientField d),
        IsBorelCoefficient A → IsSymmetricCoefficient A →
        HasLowerEllipticityAE lam A → HasUpperEllipticityAE Lam A →
      ∀ (f u : KineticPoint d → ℝ),
        Measurable (fun P : backwardCylinder P₀ R => f P) →
        ContinuousOn u (closure (backwardCylinder P₀ R)) →
        Parabolic.IsKineticC112On u (backwardCylinder P₀ R) →
        (∀ᵐ P ∂(volume.restrict (backwardCylinder P₀ R)),
          backwardOperatorOfTimeVelocityCoefficient A u P ≤ f P) →
        MemLp (fun P => max (f P) 0) (ENNReal.ofReal p)
          (volume.restrict (backwardCylinder P₀ R)) →
        ∀ P ∈ closure (backwardCylinder P₀ R),
          u P ≤ sSup ((fun P => max (u P) 0) '' kineticBoundary P₀ R) +
            C * R ^ (2 - (4 * (d : ℝ) + 2) / p) *
              (eLpNorm ({P | 0 < u P}.indicator (fun P => max (f P) 0)) (ENNReal.ofReal p)
                (volume.restrict (backwardCylinder P₀ R))).toReal := by
  exact kinetic_aleksandrov_timeVelocity_localised_of_terminalEvolution
    d hd lam Lam p hlam hLam hp
    (exists_terminalEvolution_of_classical liebermanEllipsoidDirichletStatement_holds
      hormanderHypoellipticityStatement_holds)
    hormanderHypoellipticityStatement_holds

/-- Companion paper, Corollary 9.9, with no extra hypotheses. -/
theorem kinetic_holder_timeVelocity_proof
    (d : ℕ) (hd : 1 ≤ d) (lam Lam : ℝ) (hlam : 0 < lam) (hLam : lam ≤ Lam) :
    ∃ alpha C : ℝ, 0 < alpha ∧ alpha ≤ 1 ∧
      ∀ A : CoefficientField d,
        IsBorelCoefficient A → IsSymmetricCoefficient A →
        HasLowerEllipticityAE lam A → HasUpperEllipticityAE Lam A →
      ∀ (Omega : Set (KineticPoint d)), IsOpen Omega →
      ∀ (u : KineticPoint d → ℝ),
        (∃ M : ℝ, ∀ P ∈ Omega, |u P| ≤ M) →
        Parabolic.IsKineticC112On u Omega →
        (∀ᵐ P ∂(volume.restrict Omega),
          backwardOperatorOfTimeVelocityCoefficient A u P = 0) →
      ∀ (K : Set (KineticPoint d)), K ⊆ Omega → IsCompact K →
      ∀ (R₀ : ℝ), 0 < R₀ →
        (∀ P ∈ K, closure (backwardCylinder P (2 * R₀)) ⊆ Omega) →
      ∀ P ∈ K, ∀ P' ∈ K,
        |u P - u P'| ≤ C * oscillationOn u (holderNeighbourhood R₀ K) *
          (quasiDistance P P' / R₀) ^ alpha := by
  exact kinetic_holder_timeVelocity_relative_of_smooth
    smoothLocalRegularityStatement_holds hormanderHypoellipticityStatement_holds
    liebermanEllipsoidDirichletStatement_holds d hd lam Lam hlam hLam

/-- Companion paper, Theorem 1.2 (autonomous coefficients), with no extra hypotheses. -/
theorem kinetic_aleksandrov_autonomous_proof
    (lam Lam p : ℝ) (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (hp : 1 + bellmanAdjointExponent (Lam / lam)
      ((le_div_iff₀ hlam).2 (by simpa only [one_mul] using hLam)) < p) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (P₀ : KineticPoint 1) (R : ℝ), 0 < R →
      ∀ (a : ℝ → ℝ → ℝ),
        Measurable (Function.uncurry a) →
        (∀ x v : ℝ, lam ≤ a x v ∧ a x v ≤ Lam) →
      ∀ (f u : KineticPoint 1 → ℝ),
        Measurable (fun P : backwardCylinder P₀ R => f P) →
        ContinuousOn u (closure (backwardCylinder P₀ R)) →
        Parabolic.IsKineticC112On u (backwardCylinder P₀ R) →
        (∀ᵐ P ∂(volume.restrict (backwardCylinder P₀ R)),
          autonomousScalarOperator a u P ≤ f P) →
        MemLp (fun P => max (f P) 0) (ENNReal.ofReal p)
          (volume.restrict (backwardCylinder P₀ R)) →
        ∀ P ∈ closure (backwardCylinder P₀ R),
          u P ≤ sSup ((fun P => max (u P) 0) '' kineticBoundary P₀ R) +
            C * R ^ (2 - 6 / p) *
              (eLpNorm (fun P => max (f P) 0) (ENNReal.ofReal p)
                (volume.restrict (backwardCylinder P₀ R))).toReal := by
  exact kinetic_aleksandrov_autonomous_relative_of_frontier
    autonomousRemainingFrontier_holds hormanderHypoellipticityStatement_holds
    liebermanEllipsoidDirichletStatement_holds lam Lam p hlam hLam hp

/-- Companion paper, Corollary 1.3 for autonomous coefficients, with no extra hypotheses. -/
theorem kinetic_aleksandrov_autonomous_localised_proof
    (lam Lam p : ℝ) (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (hp : 1 + bellmanAdjointExponent (Lam / lam)
      ((le_div_iff₀ hlam).2 (by simpa only [one_mul] using hLam)) < p) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (P₀ : KineticPoint 1) (R : ℝ), 0 < R →
      ∀ (a : ℝ → ℝ → ℝ),
        Measurable (Function.uncurry a) →
        (∀ x v : ℝ, lam ≤ a x v ∧ a x v ≤ Lam) →
      ∀ (f u : KineticPoint 1 → ℝ),
        Measurable (fun P : backwardCylinder P₀ R => f P) →
        ContinuousOn u (closure (backwardCylinder P₀ R)) →
        Parabolic.IsKineticC112On u (backwardCylinder P₀ R) →
        (∀ᵐ P ∂(volume.restrict (backwardCylinder P₀ R)),
          autonomousScalarOperator a u P ≤ f P) →
        MemLp (fun P => max (f P) 0) (ENNReal.ofReal p)
          (volume.restrict (backwardCylinder P₀ R)) →
        ∀ P ∈ closure (backwardCylinder P₀ R),
          u P ≤ sSup ((fun P => max (u P) 0) '' kineticBoundary P₀ R) +
            C * R ^ (2 - 6 / p) *
              (eLpNorm ({P | 0 < u P}.indicator (fun P => max (f P) 0)) (ENNReal.ofReal p)
                (volume.restrict (backwardCylinder P₀ R))).toReal := by
  exact kinetic_aleksandrov_autonomous_localised_relative_of_frontier
    autonomousRemainingFrontier_holds hormanderHypoellipticityStatement_holds
    liebermanEllipsoidDirichletStatement_holds lam Lam p hlam hLam hp

/-- Companion paper, Corollary 9.10, with no extra hypotheses. -/
theorem kinetic_holder_autonomous_proof
    (lam Lam : ℝ) (hlam : 0 < lam) (hLam : lam ≤ Lam) :
    ∃ alpha C : ℝ, 0 < alpha ∧ alpha ≤ 1 ∧
      ∀ a : ℝ → ℝ → ℝ,
        Measurable (Function.uncurry a) →
        (∀ x v : ℝ, lam ≤ a x v ∧ a x v ≤ Lam) →
      ∀ (Omega : Set (KineticPoint 1)), IsOpen Omega →
      ∀ (u : KineticPoint 1 → ℝ),
        (∃ M : ℝ, ∀ P ∈ Omega, |u P| ≤ M) →
        Parabolic.IsKineticC112On u Omega →
        (∀ᵐ P ∂(volume.restrict Omega), autonomousScalarOperator a u P = 0) →
      ∀ (K : Set (KineticPoint 1)), K ⊆ Omega → IsCompact K →
      ∀ (R₀ : ℝ), 0 < R₀ →
        (∀ P ∈ K, closure (backwardCylinder P (2 * R₀)) ⊆ Omega) →
      ∀ P ∈ K, ∀ P' ∈ K,
        |u P - u P'| ≤ C * oscillationOn u (holderNeighbourhood R₀ K) *
          (quasiDistance P P' / R₀) ^ alpha := by
  exact kinetic_holder_autonomous_relative_of_frontier
    autonomousRemainingFrontier_holds hormanderHypoellipticityStatement_holds
    liebermanEllipsoidDirichletStatement_holds lam Lam hlam hLam

end HypoellipticAleksandrov.KineticAleksandrov
