module

public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.TerminalPointValue
import HypoellipticAleksandrov.Parabolic.Transposition.KineticTerminal

/-! # Existence of the classical terminal solution and its downstream premise

We solve the sum-of-squares problem directly on finite moving slabs and glue by comparison.
-/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov
open HypoellipticAleksandrov Set
open scoped MatrixOrder

variable (n : ℕ) (hn : 1 ≤ n) (lam Lam m L_b : ℝ) (hlam : 0 < lam) (hlamLam : lam ≤ Lam)
    (hm : 0 < m) (hmLb : m ≤ L_b) (Ω : Set (PDE.Vec n)) (γ : ℝ → PDE.Vec n)
    (B : FullKineticCoefficient n) (b : PDE.Vec n → PDE.Vec n)
    (hΩ : IsAdmissibleEvolutionDomain Ω) (hγ : IsContinuousPiecewiseC1 γ)
    (hB_smooth : IsSmoothFullKineticCoefficient B) (hB_symm : IsSymmetricFullKineticCoefficient B)
    (hB_ell : HasEverywhereLoewnerBounds lam Lam B) (hb_smooth : IsSmoothDrift b)
    (hb_lipschitz : HasEuclideanLipschitzDrift L_b b)
    (hb_coercive : HasUnitDirectionDriftCoercivity m b)
include hn hlam hlamLam hm hmLb hΩ hγ hB_smooth hB_symm hB_ell hb_smooth hb_lipschitz hb_coercive

/-- Bounded classical terminal solutions exist and are unique on the closed past
cylinder. -/
theorem exists_classical_terminalSolution
    (τ : ℝ) (F : BoundedBorel (EvolutionAmbientState n))
    (hF : IsSmoothCompactTerminalDatum Ω γ τ F) :
    ∃ u : KineticPoint n → ℝ,
      IsClassicalTerminalSolution Ω γ B b τ F u ∧
      (∀ C : ℝ, 0 ≤ C → (∀ q, |F q| ≤ C) →
        ∀ p ∈ evolutionPastClosedCylinder Ω γ τ, |u p| ≤ C) ∧
      (∀ v : KineticPoint n → ℝ,
        IsClassicalTerminalSolution Ω γ B b τ F v →
          EqOn v u (evolutionPastClosedCylinder Ω γ τ)) :=
  Parabolic.Transposition.solve_kinetic_terminal hn hΩ hγ hlam hB_ell hB_smooth hb_smooth hm hb_coercive hb_lipschitz hF

/-- The existence premise used for the terminal point value and its consumers is discharged
by the existence theorem above, with only the same two hypotheses. -/
theorem classicalTerminalExistence_holds
    : ClassicalTerminalExistence Ω γ B b := exists_classical_terminalSolution n hn lam Lam m L_b hlam hlamLam hm hmLb
    Ω γ B b hΩ hγ hB_smooth hB_symm hB_ell hb_smooth hb_lipschitz hb_coercive

end HypoellipticAleksandrov.KineticAleksandrov
