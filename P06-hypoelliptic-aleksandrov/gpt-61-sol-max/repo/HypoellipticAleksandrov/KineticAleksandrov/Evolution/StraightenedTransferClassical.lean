module

public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ComparisonEvolution
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.StraightenedTransferOperator
public import HypoellipticAleksandrov.KineticAleksandrov.EvolutionProblem
public import HypoellipticAleksandrov.Parabolic.ScalarDirichletData
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
public import PDEFoundation.Calculus.RegularityOrder


/-!
# Classical solutions: straightened variables versus absolute variables

Chain-rule transfer.  A classical solution
`ũ` of the straightened problem, with drift `-g'(σ) · ∇_Y`, pulls back along
`Y = y - g(σ)` to a classical solution `u(σ, y, z) = ũ(σ, (y - g(σ), z))` of the absolute
problem in the sense of the comparison theorems and of `IsClassicalViscousTerminalSolution`.

* `isClassicalViscousTerminalSolution_straightenedPullback`: the straightened problem on the
  whole past cylinder `{σ ≤ τ, Y ∈ closure Ω}` (all `z`) gives `IsClassicalViscousTerminalSolution`
  for the moving domain `g + Ω`; at `ε = 0` this is `IsClassicalTerminalSolution`.
* `straightenedPullback_of_dirichlet`: the finite-slab Dirichlet problem on an arbitrary open
  spatial base `D` of `(Y, z)` (for instance the truncation ellipsoid) gives, in absolute
  variables, continuity, slice regularity, joint smoothness, `L_ε u = 0` and the terminal and
  lateral values on the corresponding absolute cylinder, which are the hypotheses of
  `bounded_comparison` and `two_barriers`.

Interior smoothness of `ũ` is a hypothesis of the transfer; it is what the weak formulation and
the Hörmander theorem supply for the Dirichlet solution, and it is exactly the regularity
demanded by the classical-solution predicates.
-/

 public section


set_option autoImplicit false

open HypoellipticAleksandrov HypoellipticAleksandrov.Parabolic Set
open scoped ContDiff

namespace HypoellipticAleksandrov.KineticAleksandrov

variable {n : ℕ}

/-- Membership of a point in the frontier of the moving domain. -/
theorem mem_frontier_movingDomain_iff {Ω : PDE.VelocityRegion n} {γ : ℝ → PDE.Vec n} {σ : ℝ}
    {y : PDE.Vec n} : y ∈ frontier (movingDomain Ω γ σ) ↔ y - γ σ ∈ frontier Ω := by
  have h : movingDomain Ω γ σ = (Homeomorph.subRight (γ σ)) ⁻¹' Ω := by
    rw [movingDomain, ← PDE.preimage_subRight_eq_translateSet]
    rfl
  rw [h, ← Homeomorph.preimage_frontier]
  rfl





/-- A smooth curve is continuous and piecewise `C¹` (with a single piece). -/
theorem isContinuousPiecewiseC1_of_contDiff {g : ℝ → PDE.Vec n}
    (hg : ContDiff ℝ PDE.smoothOrder g) : IsContinuousPiecewiseC1 g := by
  refine ⟨hg.continuous, fun a b hab => ⟨0, ![a, b], ?_, rfl, rfl, fun i => ?_⟩⟩
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all
  · exact (hg.contDiffOn (s := Set.Icc _ _)).of_le
      (WithTop.coe_le_coe.mpr (le_top ))

end HypoellipticAleksandrov.KineticAleksandrov
