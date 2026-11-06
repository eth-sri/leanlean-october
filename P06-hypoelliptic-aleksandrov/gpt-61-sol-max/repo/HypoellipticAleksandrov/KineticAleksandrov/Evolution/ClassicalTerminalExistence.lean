module

public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ClassicalTerminal
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.TerminalPointValue
import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ExhaustionLimit

/-! # Existence of the classical terminal solution and its downstream premise

Viscous existence is discharged by the exhaustion argument. Only classical Dirichlet
solvability on ellipsoids (Lieberman, Theorem 5.14) and Hörmander's hypoellipticity theorem
remain explicit hypotheses.
-/

 public section

namespace HypoellipticAleksandrov.KineticAleksandrov
open Set
open scoped MatrixOrder

variable (n : ℕ) (hn : 1 ≤ n) (lam Lam m L_b : ℝ) (hlam : 0 < lam) (hlamLam : lam ≤ Lam) (hm : 0 < m) (hmLb : m ≤ L_b) (Ω : PDE.VelocityRegion n) (γ : ℝ → PDE.Vec n) (B : FullKineticCoefficient n) (b : PDE.VectorField n) (hΩ : IsAdmissibleEvolutionDomain Ω) (hγ : IsContinuousPiecewiseC1 γ) (hB_smooth : IsSmoothFullKineticCoefficient B) (hB_symm : IsSymmetricFullKineticCoefficient B) (hB_ell : HasEverywhereLoewnerBounds lam Lam B) (hb_smooth : IsSmoothDrift b) (hb_lipschitz : HasEuclideanLipschitzDrift L_b b) (hb_coercive : HasUnitDirectionDriftCoercivity m b) (hLE : LiebermanEllipsoidDirichletStatement) (hH : HormanderHypoellipticityStatement)

include hn hlam hlamLam hm hmLb hΩ hγ hB_smooth hB_symm hB_ell hb_smooth hb_lipschitz hb_coercive hLE hH
/-- Bounded classical terminal solutions exist and are unique on the closed past
cylinder, relative only to the Lieberman ellipsoid and Hörmander inputs. -/
theorem exists_classical_terminalSolution

    (τ : ℝ) (F : BoundedBorel (EvolutionAmbientState n))
    (hF : IsSmoothCompactTerminalDatum Ω γ τ F) :
    ∃ u : HypoellipticAleksandrov.KineticScalarField n,
      IsClassicalTerminalSolution Ω γ B b τ F u ∧
      (∀ C : ℝ, 0 ≤ C → (∀ q, |F q| ≤ C) →
        ∀ p ∈ evolutionPastClosedCylinder Ω γ τ, |u p| ≤ C) ∧
      (∀ v : HypoellipticAleksandrov.KineticScalarField n,
        IsClassicalTerminalSolution Ω γ B b τ F v →
          EqOn v u (evolutionPastClosedCylinder Ω γ τ)) := (exists_classical_terminalSolution_of_viscous (fun {k N} {Ω} => hH) n hn lam Lam m L_b hlam hlamLam hm hmLb Ω γ B b hΩ hγ
  hB_smooth hB_symm hB_ell hb_smooth hb_lipschitz hb_coercive
  (fun τ F hF ε hε hε1 C hC hFC =>
    exists_viscous_terminalSolution n hn lam Lam m L_b hlam hlamLam hm hmLb Ω γ B b hΩ hγ hB_smooth hB_symm hB_ell
      hb_smooth hb_lipschitz hb_coercive (fun {N} {r₀ r₁} {Q} => hLE) (fun {k N} {Ω} => hH) τ F hF ε hε hε1 C hC hFC)
  τ F hF)

/-- The existence premise used for the terminal point value and its consumers is discharged
by the existence theorem above, with only the same two hypotheses. -/
theorem classicalTerminalExistence_holds

    : ClassicalTerminalExistence Ω γ B b := exists_classical_terminalSolution n hn lam Lam m L_b hlam hlamLam hm hmLb
    Ω γ B b hΩ hγ hB_smooth hB_symm hB_ell hb_smooth hb_lipschitz hb_coercive hLE hH

end HypoellipticAleksandrov.KineticAleksandrov
