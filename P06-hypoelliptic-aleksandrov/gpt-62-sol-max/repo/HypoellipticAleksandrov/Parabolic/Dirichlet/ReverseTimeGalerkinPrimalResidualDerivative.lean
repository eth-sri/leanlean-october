module

public import HypoellipticAleksandrov.Parabolic.Dirichlet.ReverseTimeFormResidual
public import HypoellipticAleksandrov.Parabolic.Dirichlet.ReverseTimeGelfandPairing
public import HypoellipticAleksandrov.Parabolic.Dirichlet.WeakTimeDerivative
public import HypoellipticAleksandrov.Parabolic.Dirichlet.ReverseTimeGalerkinPrimalArbitraryTestLimit

/-!
# Residual weak derivative of the reverse-time Galerkin limit

This module identifies the concrete Bochner residual as the Gelfand weak time
derivative of the common reverse-time Galerkin limit.
-/

@[expose] public section

open Filter MeasureTheory Set Topology
open scoped ENNReal Matrix Matrix.Norms.Elementwise MatrixOrder RealInnerProductSpace

noncomputable section

namespace HypoellipticAleksandrov.Parabolic.Dirichlet

local instance instResidualDerivativeReverseTimeL2VStarModule
    {d : ℕ} {Ω : Set (PDE.Vec d)} (hΩ : IsOpen Ω) (T : ℝ) :
    Module ℝ (ReverseTimeL2VStar hΩ T) :=
  MeasureTheory.Lp.instModule

section
variable {d : ℕ} {Ω : Set (PDE.Vec d)}

end

variable {d : ℕ} {Ω : Set (PDE.Vec d)}
variable
  {r₀ r₁ lam : ℝ} (P : ReverseTimeGalerkinProblem Ω r₀ r₁ lam)

/-- A common weak Galerkin subsequence converges to a curve whose Gelfand weak
time derivative is the concrete reverse-time form residual. -/
theorem exists_strictMono_tendsto_clm_reverseTimeGalerkinPrimal_residual_derivative
    (initial : PDE.ScalarLp Ω (2 : ℝ≥0∞)) :
    ∃ (U : ReverseTimeL2V P.hΩ (r₁ - r₀)) (φ : ℕ → ℕ),
      StrictMono φ ∧
      P.WeakLimit initial U φ ∧
      HasGelfandWeakTimeDerivative P.hΩ (r₁ - r₀) (sub_pos.mpr P.h₀₁) U
        (P.residual U) := by
  obtain ⟨U, φ, hφ, hclm, hidentity⟩ :=
    exists_strictMono_tendsto_clm_reverseTimeGalerkinPrimal_arbitraryTests
      P initial
  let T := r₁ - r₀
  refine ⟨U, φ, hφ, hclm, ?_⟩
  intro v eta
  let g := P.residual U
  refine ⟨integrable_reverseTimeWeakDerivative_left P.hΩ T U v eta,
    integrable_reverseTimeWeakDerivative_right P.hΩ T g v eta, ?_⟩
  have hleft :
      (∫ tau, inner ℝ (valueCLM P.hΩ v)
        (reverseTimeValueCLM P.hΩ T U tau) * eta.deriv tau
        ∂reverseTimeVolume T) =
      (∫ tau, inner ℝ (valueCLM P.hΩ v) (valueCLM P.hΩ (U tau)) * eta.deriv tau
        ∂reverseTimeVolume T) := by
    apply integral_congr_ae
    filter_upwards [coeFn_reverseTimeValueCLM P.hΩ T U] with tau hU
    rw [hU]
  have hm := reverseTimeGelfand_pairing_multiplier_eq_integral P.hΩ U eta.deriv (eta.memLp_deriv _) v
  have hg := reverseTimeDualPairing_multiplier_eq_integral P.hΩ g eta (eta.memLp _) v
    (ae_of_all _ fun _ => rfl)
  have h := hidentity v eta
  unfold ReverseTimeGalerkinProblem.TestEquation at h
  rw [hm] at h
  exact hleft.trans (h.trans (congrArg Neg.neg hg))

end HypoellipticAleksandrov.Parabolic.Dirichlet
