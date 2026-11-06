module

public import HypoellipticAleksandrov.Parabolic.ScalarClassical
public import PDEFoundation.Ambient.EuclideanNorm
public import HypoellipticAleksandrov.Ambient.TypeAbbrev
public import HypoellipticAleksandrov.Parabolic.TypeAbbrev

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
    (Ω : HypoellipticAleksandrov.VecSet n) : Prop :=
  ∃ ρ θ : ℝ, 0 < ρ ∧ 0 < θ ∧ θ < 1 ∧
    ∀ y ∈ frontier Ω, ∃ ν : PDE.Vec n,
      PDE.vecEuclideanNorm ν = 1 ∧
        ∀ z : PDE.Vec n,
          0 < PDE.vecEuclideanNorm z →
          PDE.vecEuclideanNorm z < ρ →
          θ * PDE.vecEuclideanNorm z ≤ PDE.vecDot z ν →
          y + z ∉ Ω

/-- The initial face `{r₀} × closure Ω` of a scalar parabolic cylinder. -/
def scalarParabolicInitialFace {n : ℕ} (r₀ : ℝ) (Ω : HypoellipticAleksandrov.VecSet n) :
    HypoellipticAleksandrov.Parabolic.TVSet n :=
  ({r₀} : Set ℝ) ×ˢ closure Ω

/-- Membership in the initial face of a scalar parabolic cylinder. -/
@[simp] theorem mem_scalarParabolicInitialFace_iff {n : ℕ} {r₀ r : ℝ}
    {Ω : HypoellipticAleksandrov.VecSet n} {y : PDE.Vec n} :
    (r, y) ∈ scalarParabolicInitialFace r₀ Ω ↔ r = r₀ ∧ y ∈ closure Ω := by
  simp [scalarParabolicInitialFace]

/-- The terminal corner `{r₁} × frontier Ω` of a scalar parabolic cylinder. -/
def scalarParabolicTerminalCorner {n : ℕ} (r₁ : ℝ) (Ω : HypoellipticAleksandrov.VecSet n) :
    HypoellipticAleksandrov.Parabolic.TVSet n :=
  ({r₁} : Set ℝ) ×ˢ frontier Ω

/-- Membership in the terminal corner of a scalar parabolic cylinder. -/
@[simp] theorem mem_scalarParabolicTerminalCorner_iff {n : ℕ} {r₁ r : ℝ}
    {Ω : HypoellipticAleksandrov.VecSet n} {y : PDE.Vec n} :
    (r, y) ∈ scalarParabolicTerminalCorner r₁ Ω ↔ r = r₁ ∧ y ∈ frontier Ω := by
  simp [scalarParabolicTerminalCorner]

end HypoellipticAleksandrov.Parabolic
