module

public import HypoellipticAleksandrov.Parabolic.Dirichlet.ReverseTimeGalerkinPrimalInitialTrace
import HypoellipticAleksandrov.Topology.WeakLimitNorm

/-!
# Initial trace and radius for the residual Galerkin limit

This module combines the same residual Galerkin-limit witness with its
canonical initial trace and inherited uniform Bochner radius.
-/

@[expose] public section

open scoped ENNReal Matrix.Norms.Elementwise MatrixOrder

noncomputable section

namespace HypoellipticAleksandrov.Parabolic.Dirichlet

/-- There is a common residual Galerkin limit with the prescribed initial
trace and explicit uniform Bochner radius. -/
theorem exists_reverseTimeGalerkinPrimal_initialTrace_norm_le_radius
    {d : ℕ} {Ω : Set (PDE.Vec d)}
    {r₀ r₁ lam : ℝ} (P : ReverseTimeGalerkinProblem Ω r₀ r₁ lam)
    (initial : PDE.ScalarLp Ω (2 : ℝ≥0∞)) :
    ∃ (U : ReverseTimeL2V P.hΩ (r₁ - r₀)),
      ∃ hdu : HasGelfandWeakTimeDerivative P.hΩ (r₁ - r₀) (sub_pos.mpr P.h₀₁) U
        (P.residual U),
        reverseTimeInitialTrace P.hΩ (r₁ - r₀) (sub_pos.mpr P.h₀₁) U
          (P.residual U) hdu = initial ∧
          ‖U‖ ≤
            reverseTimeGalerkinPrimalRadius P initial
    := by
  obtain ⟨U, phi, hphi, hclm, hdu⟩ :=
    exists_strictMono_tendsto_clm_reverseTimeGalerkinPrimal_residual_derivative
      P initial
  have hTrace :=
    reverseTimeGalerkinPrimal_initialTrace_of_strictMono_tendsto_clm
      P
      initial U phi hphi hclm hdu
  exact ⟨U, hdu, hTrace, HypoellipticAleksandrov.norm_le_of_tendsto_clm_of_norm_le
    (fun n => reverseTimeGalerkinPrimal P (phi n) initial) U (reverseTimeGalerkinPrimalRadius P initial)
    (fun n => norm_reverseTimeGalerkinPrimal_le_radius P initial (phi n)) hclm⟩

end HypoellipticAleksandrov.Parabolic.Dirichlet
