module

public import HypoellipticAleksandrov.Parabolic.ScalarClassical
public import PDEFoundation.Ambient.EuclideanNorm

/-!
# Geometry for the scalar parabolic Dirichlet problem

This module fixes the literal uniform exterior-cone hypothesis and the
initial and terminal-corner faces used by the bounded scalar Dirichlet
problem.  It contains no barrier, regularity, or solvability result.
-/

@[expose] public section

namespace HypoellipticAleksandrov.Parabolic

/-- `Ω` has a uniform exterior cone with strictly positive angular opening. -/
def HasUniformNondegenerateExteriorCone {n : ℕ}
    (Ω : PDE.VelocityRegion n) : Prop :=
  ∃ ρ θ : ℝ, 0 < ρ ∧ 0 < θ ∧ θ < 1 ∧
    ∀ y ∈ frontier Ω, ∃ ν : PDE.Vec n,
      PDE.vecEuclideanNorm ν = 1 ∧
        ∀ z : PDE.Vec n,
          0 < PDE.vecEuclideanNorm z →
          PDE.vecEuclideanNorm z < ρ →
          θ * PDE.vecEuclideanNorm z ≤ PDE.vecDot z ν →
          y + z ∉ Ω

variable {n : ℕ}









end HypoellipticAleksandrov.Parabolic
