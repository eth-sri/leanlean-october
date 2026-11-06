module

public import HypoellipticAleksandrov.Parabolic.Dirichlet.ReverseTimeVariationalEnergyExistenceBound
import HypoellipticAleksandrov.Parabolic.Dirichlet.ReverseTimeGalerkinPrimalInitialTraceNorm
import HypoellipticAleksandrov.Parabolic.Dirichlet.VariationalEnergy
import HypoellipticAleksandrov.Parabolic.Dirichlet.ReverseTimeGalerkinPrimalInitialTrace
import HypoellipticAleksandrov.Parabolic.Dirichlet.ReverseTimeGalerkinPrimalResidualDerivative
import HypoellipticAleksandrov.Parabolic.Dirichlet.ReverseTimeGalerkinPrimalResidualDerivativeNorm
import HypoellipticAleksandrov.Topology.WeakLimitNorm

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
open Set
open scoped RealInnerProductSpace
open Filter
open scoped Topology

/- Every supplied reverse-time variational energy solution is bounded by the
constructed Galerkin primal radius. -/
theorem IsReverseTimeVariationalEnergySolution.norm_le_reverseTimeGalerkinPrimalRadius
    {d Ω}
    (r₀ r₁ lam Lam : ℝ) (h₀₁ : r₀ < r₁)
    (hlam : 0 < lam) (hlamLam : lam ≤ Lam)
    (hΩ : IsOpen Ω) (hΩbounded : Bornology.IsBounded Ω)
    (a : CoefficientField d)
    (b : ℝ → PDE.Vec d → PDE.Vec d)
    (c F : ℝ → PDE.Vec d → ℝ)
    (haSmooth : IsSmoothOnNeighborhood
      (fun z : TimeVelocity d => a z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hbSmooth : IsSmoothOnNeighborhood
      (fun z : TimeVelocity d => b z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hcSmooth : IsSmoothOnNeighborhood
      (fun z : TimeVelocity d => c z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hFSmooth : IsSmoothOnNeighborhood
      (fun z : TimeVelocity d => F z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hLower : ∀ z : TimeVelocity d,
      z ∈ scalarParabolicClosedCylinder r₀ r₁ Ω →
        lam • (1 : PDE.Mat d) ≤ a z.1 z.2)
    (hUpper : ∀ z : TimeVelocity d,
      z ∈ scalarParabolicClosedCylinder r₀ r₁ Ω →
        a z.1 z.2 ≤ Lam • (1 : PDE.Mat d))
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
      reverseTimeGalerkinPrimalRadius r₀ r₁ lam h₀₁ hlam hΩ hΩbounded a b c F
        haSmooth hbSmooth hcSmooth hFSmooth hLower hcNonpos initial := by
  obtain ⟨U, G, hU, hSolU, hNorm⟩ : ∃ (u : ReverseTimeL2V hΩ (r₁ - r₀)),
      ∃ (g : ReverseTimeL2VStar hΩ (r₁ - r₀)),
        ∃ hdu : HasGelfandWeakTimeDerivative hΩ (r₁ - r₀)
          (sub_pos.mpr h₀₁) u g,
          IsReverseTimeVariationalEnergySolution
              r₀ r₁ h₀₁ hΩ hΩbounded a b c F hFSmooth initial u g hdu ∧
            ‖u‖ ≤
              reverseTimeGalerkinPrimalRadius r₀ r₁ lam h₀₁ hlam hΩ hΩbounded
                a b c F haSmooth hbSmooth hcSmooth hFSmooth hLower hcNonpos initial := by
    obtain ⟨U, hdu, htrace, hNorm⟩ : ∃ (U : ReverseTimeL2V hΩ (r₁ - r₀)),
      ∃ hdu : HasGelfandWeakTimeDerivative hΩ (r₁ - r₀) (sub_pos.mpr h₀₁) U
        (reverseTimeFormResidual r₀ r₁ h₀₁ hΩ hΩbounded a b c
          haSmooth hbSmooth hcSmooth F hFSmooth U),
        reverseTimeInitialTrace hΩ (r₁ - r₀) (sub_pos.mpr h₀₁) U
          (reverseTimeFormResidual r₀ r₁ h₀₁ hΩ hΩbounded a b c
            haSmooth hbSmooth hcSmooth F hFSmooth U) hdu = initial ∧
          ‖U‖ ≤
            reverseTimeGalerkinPrimalRadius r₀ r₁ lam h₀₁ hlam hΩ hΩbounded a b c F
              haSmooth hbSmooth hcSmooth hFSmooth hLower hcNonpos initial := by
      obtain ⟨U, phi, hphi, hclm, hdu, hNorm⟩ : ∃ (U : ReverseTimeL2V hΩ (r₁ - r₀)) (φ : ℕ → ℕ),
          StrictMono φ ∧
          (∀ ell : ReverseTimeL2V hΩ (r₁ - r₀) →L[ℝ] ℝ,
            Tendsto
              (fun n => ell
                (reverseTimeGalerkinPrimal r₀ r₁ lam h₀₁ hlam hΩ hΩbounded
                  a b c F haSmooth hbSmooth hcSmooth hFSmooth hLower hcNonpos
                  (φ n) initial))
              atTop (𝓝 (ell U))) ∧
          HasGelfandWeakTimeDerivative hΩ (r₁ - r₀) (sub_pos.mpr h₀₁) U
            (reverseTimeFormResidual r₀ r₁ h₀₁ hΩ hΩbounded a b c
              haSmooth hbSmooth hcSmooth F hFSmooth U) ∧
          ‖U‖ ≤
            reverseTimeGalerkinPrimalRadius r₀ r₁ lam h₀₁ hlam hΩ hΩbounded a b c F
              haSmooth hbSmooth hcSmooth hFSmooth hLower hcNonpos initial := by
        obtain ⟨U, φ, hφ, hclm, hdu⟩ :=
          exists_strictMono_tendsto_clm_reverseTimeGalerkinPrimal_residual_derivative
            r₀ r₁ lam h₀₁ hlam hΩ hΩbounded a b c F
            haSmooth hbSmooth hcSmooth hFSmooth hLower hcNonpos initial
        refine ⟨U, φ, hφ, hclm, hdu, ?_⟩
        exact HypoellipticAleksandrov.norm_le_of_tendsto_clm_of_norm_le
          (fun n => reverseTimeGalerkinPrimal r₀ r₁ lam h₀₁ hlam hΩ hΩbounded a b c F
            haSmooth hbSmooth hcSmooth hFSmooth hLower hcNonpos (φ n) initial)
          U
          (reverseTimeGalerkinPrimalRadius r₀ r₁ lam h₀₁ hlam hΩ hΩbounded a b c F
            haSmooth hbSmooth hcSmooth hFSmooth hLower hcNonpos initial)
          (fun n => norm_reverseTimeGalerkinPrimal_le_radius
            r₀ r₁ lam h₀₁ hlam hΩ hΩbounded a b c F
            haSmooth hbSmooth hcSmooth hFSmooth hLower hcNonpos initial (φ n))
          hclm
      exact ⟨U, hdu, (reverseTimeGalerkinPrimal_initialTrace_of_strictMono_tendsto_clm r₀ r₁ lam h₀₁ hlam hΩ hΩbounded a b c F haSmooth hbSmooth hcSmooth hFSmooth hLower hcNonpos initial U phi hphi hclm hdu), hNorm⟩
    refine ⟨U,
      reverseTimeFormResidual r₀ r₁ h₀₁ hΩ hΩbounded a b c
        haSmooth hbSmooth hcSmooth F hFSmooth U,
      hdu, ?_, hNorm⟩
    exact ⟨htrace,
      ae_reverseTimeFormResidual_apply r₀ r₁ h₀₁ hΩ hΩbounded a b c
        haSmooth hbSmooth hcSmooth F hFSmooth U⟩
  obtain ⟨hUeq, _⟩ :=
    reverseTimeVariationalEnergySolution_unique
      r₀ r₁ lam h₀₁ hlam hΩ hΩbounded a b c F
      haSmooth hbSmooth hcSmooth hFSmooth hLower hcNonpos initial
      U G hU hSolU u g hdu hu
  simpa only [hUeq] using hNorm

end HypoellipticAleksandrov.Parabolic.Dirichlet
