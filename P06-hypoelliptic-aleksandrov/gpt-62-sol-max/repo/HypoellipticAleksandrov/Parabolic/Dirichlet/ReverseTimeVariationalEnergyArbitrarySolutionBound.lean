module

public import HypoellipticAleksandrov.Parabolic.Dirichlet.ReverseTimeVariationalEnergyExistenceBound

/-!
# Uniform radius bound for arbitrary reverse-time variational solutions

This module transports the constructed Galerkin radius bound to every supplied
reverse-time variational energy solution with the same data.
-/

@[expose] public section

open Topology
open scoped ENNReal Matrix.Norms.Elementwise MatrixOrder

noncomputable section

namespace HypoellipticAleksandrov.Parabolic.Dirichlet

/-- Every supplied reverse-time variational energy solution is bounded by the
constructed Galerkin primal radius. -/
theorem IsReverseTimeVariationalEnergySolution.norm_le_reverseTimeGalerkinPrimalRadius
    {d : ℕ} {Ω : Set (PDE.Vec d)}
    (r₀ r₁ lam Lam : ℝ) (h₀₁ : r₀ < r₁)
    (hlam : 0 < lam) (hlamLam : lam ≤ Lam)
    (hΩ : IsOpen Ω) (hΩbounded : Bornology.IsBounded Ω)
    (a : CoefficientField d)
    (b : ℝ → PDE.Vec d → PDE.Vec d)
    (c F : ℝ → PDE.Vec d → ℝ)
    (haSmooth : IsSmoothOnClosedCylinder r₀ r₁ Ω a)
    (hbSmooth : IsSmoothOnClosedCylinder r₀ r₁ Ω b)
    (hcSmooth : IsSmoothOnClosedCylinder r₀ r₁ Ω c)
    (hFSmooth : IsSmoothOnClosedCylinder r₀ r₁ Ω F)
    (hLower : HasLowerEllipticityOn lam a (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hUpper : HasUpperEllipticityOn Lam a (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hcNonpos : ∀ z : TimeVelocity d,
      z ∈ scalarParabolicClosedCylinder r₀ r₁ Ω → c z.1 z.2 ≤ 0)
    (initial : PDE.ScalarLp Ω (2 : ℝ≥0∞))
    (u : ReverseTimeL2V hΩ (r₁ - r₀))
    (g : ReverseTimeL2VStar hΩ (r₁ - r₀))
    (hdu : HasGelfandWeakTimeDerivative hΩ (r₁ - r₀)
      (sub_pos.mpr h₀₁) u g)
    (hu : IsReverseTimeVariationalEnergySolution r₀ r₁ h₀₁ hΩ hΩbounded
      a b c F hFSmooth initial u g hdu) :
    ‖u‖ ≤
      reverseTimeGalerkinPrimalRadius
        ⟨h₀₁, hlam, hΩ, hΩbounded, a, b, c, F, haSmooth, hbSmooth, hcSmooth, hFSmooth, hLower, hcNonpos⟩ initial := by
  obtain ⟨U, G, hU, hSolU, hNorm⟩ :=
    exists_reverseTime_variational_energy_solution_norm_le_radius
      r₀ r₁ lam Lam h₀₁ hlam hlamLam hΩ hΩbounded a b c F
      haSmooth hbSmooth hcSmooth hFSmooth hLower hUpper hcNonpos initial
  obtain ⟨hUeq, _⟩ :=
    reverseTimeVariationalEnergySolution_unique
      r₀ r₁ lam h₀₁ hlam hΩ hΩbounded a b c F
      haSmooth hbSmooth hcSmooth hFSmooth hLower hcNonpos initial
      U G hU hSolU u g hdu hu
  simpa only [hUeq] using hNorm

end HypoellipticAleksandrov.Parabolic.Dirichlet
