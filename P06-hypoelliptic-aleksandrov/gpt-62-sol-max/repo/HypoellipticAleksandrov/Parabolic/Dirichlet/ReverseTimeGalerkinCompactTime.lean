module

public import HypoellipticAleksandrov.Parabolic.Dirichlet.ReverseTimeGalerkinWeakForm
public import HypoellipticAleksandrov.Parabolic.Dirichlet.TimeTests
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-!
# Compactly supported time tests for finite reverse-time Galerkin curves

This module turns the finite Galerkin row equation into its scalar
compact-time identity.  It remains entirely finite dimensional in the spatial
test and does not construct a weak time derivative or a limiting solution.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.Parabolic.Dirichlet

open MeasureTheory Set
open scoped ENNReal Matrix Matrix.Norms.Elementwise MatrixOrder RealInnerProductSpace

/-- The value pairing with a fixed test vector on Galerkin coordinates. -/
private noncomputable def galerkinPairingCLM {d : ℕ} {Ω : Set (PDE.Vec d)}
    (hΩ : IsOpen Ω) (N : ℕ) (v : galerkinSpace hΩ N) : GalerkinCoordinates hΩ N →L[ℝ] ℝ :=
  (innerSL ℝ (valueCLM hΩ (v : H10HilbertGraph hΩ))).comp
    ((valueCLM hΩ).comp (galerkinReconstructCLM hΩ N))

section
variable {d : ℕ} {Ω : Set (PDE.Vec d)} (hΩ : IsOpen Ω) (N : ℕ) (x : ℝ → GalerkinCoordinates hΩ N)

theorem hasDerivWithinAt_galerkinPairing
    (xdot : GalerkinCoordinates hΩ N)
    (v : galerkinSpace hΩ N) {s : Set ℝ} {τ : ℝ}
    (hx : HasDerivWithinAt x xdot s τ) :
    HasDerivWithinAt
      (fun t =>
        inner ℝ (valueCLM hΩ (v : H10HilbertGraph hΩ))
          (valueCLM hΩ
            (galerkinReconstruct hΩ N (x t) : H10HilbertGraph hΩ)))
      (inner ℝ (valueCLM hΩ (v : H10HilbertGraph hΩ))
        (valueCLM hΩ (galerkinReconstruct hΩ N xdot : H10HilbertGraph hΩ))) s τ := by
  simpa [galerkinPairingCLM, Function.comp_def] using
    (galerkinPairingCLM hΩ N v).hasFDerivAt.comp_hasDerivWithinAt τ hx

theorem continuousOn_galerkinPairing
    (v : galerkinSpace hΩ N) (s : Set ℝ) (hx : ContinuousOn x s) :
    ContinuousOn
      (fun t =>
        inner ℝ (valueCLM hΩ (v : H10HilbertGraph hΩ))
          (valueCLM hΩ
            (galerkinReconstruct hΩ N (x t) : H10HilbertGraph hΩ))) s := (galerkinPairingCLM hΩ N v).continuous.comp_continuousOn hx

end

private theorem boundaryTime_scalar_identity
    (T : ℝ) (hT : 0 < T) (pairing residual eta etaDeriv : ℝ → ℝ)
    (hpairing : ContinuousOn pairing (Icc 0 T))
    (hresidual : IntegrableOn residual (Icc 0 T) volume)
    (hderivPairing : ∀ τ ∈ Icc 0 T,
      HasDerivWithinAt pairing (residual τ) (Icc 0 T) τ)
    (hEta : ∀ τ ∈ Icc 0 T,
      HasDerivWithinAt eta (etaDeriv τ) (Icc 0 T) τ)
    (hDerivCont : ContinuousOn etaDeriv (Icc 0 T))
    (hEtaT : eta T = 0) :
    Integrable (fun τ => pairing τ * etaDeriv τ) (reverseTimeVolume T) ∧
    Integrable (fun τ => residual τ * eta τ) (reverseTimeVolume T) ∧
    (∫ τ, pairing τ * etaDeriv τ ∂reverseTimeVolume T) =
      -(∫ τ, residual τ * eta τ ∂reverseTimeVolume T) - pairing 0 * eta 0 := by
  have hcont : ContinuousOn eta (Icc 0 T) := fun τ hτ => (hEta τ hτ).continuousWithinAt
  have hi := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivWithinAt
    (u := pairing) (u' := residual) (v := eta) (v' := etaDeriv)
    (by simpa only [uIcc_of_le hT.le] using hderivPairing)
    (by simpa only [uIcc_of_le hT.le] using hEta)
    ((intervalIntegrable_iff_integrableOn_Icc_of_le hT.le).mpr hresidual)
    (hDerivCont.intervalIntegrable_of_Icc hT.le)
  simp only [reverseTimeVolume, reverseTimeOpenInterval, restrict_Ioo_eq_restrict_Icc]
  refine ⟨(hpairing.mul hDerivCont).integrableOn_Icc,
    hresidual.mul_continuousOn hcont isCompact_Icc, ?_⟩
  rw [hEtaT, mul_zero] at hi
  simp only [intervalIntegral.integral_of_le hT.le, restrict_Ioc_eq_restrict_Icc] at hi
  rw [hi]
  ring

/-- Integration by parts for the finite Galerkin row equation, with the initial pairing. -/
theorem IsGalerkinTrajectory.boundaryTime
    {d : ℕ} {Ω : Set (PDE.Vec d)}
    {r₀ r₁ lam : ℝ} (P : ReverseTimeGalerkinProblem Ω r₀ r₁ lam)
    {N : ℕ}
    {initial : PDE.ScalarLp Ω 2} {x : ℝ → GalerkinCoordinates P.hΩ N}
    (hspec : IsGalerkinTrajectory P N initial x)
    (v : galerkinSpace P.hΩ N) (eta etaDeriv : ℝ → ℝ)
    (hEta : ∀ τ ∈ Icc 0 (r₁ - r₀), HasDerivWithinAt eta (etaDeriv τ) (Icc 0 (r₁ - r₀)) τ)
    (hDerivCont : ContinuousOn etaDeriv (Icc 0 (r₁ - r₀)))
    (hEtaT : eta (r₁ - r₀) = 0) :
    let T := r₁ - r₀
    let pairing : ℝ → ℝ := fun τ =>
      inner ℝ (valueCLM P.hΩ (v : H10HilbertGraph P.hΩ))
        (valueCLM P.hΩ (galerkinReconstruct P.hΩ N (x τ) : H10HilbertGraph P.hΩ))
    let residual : ℝ → ℝ := fun τ =>
      P.sourceRaw τ
        (v : H10HilbertGraph P.hΩ) -
      P.form τ
        (galerkinReconstruct P.hΩ N (x τ) : H10HilbertGraph P.hΩ)
        (v : H10HilbertGraph P.hΩ)
    Integrable (fun τ => pairing τ * etaDeriv τ) (reverseTimeVolume T) ∧
    Integrable (fun τ => residual τ * eta τ) (reverseTimeVolume T) ∧
    (∫ τ, pairing τ * etaDeriv τ ∂reverseTimeVolume T) =
      -(∫ τ, residual τ * eta τ ∂reverseTimeVolume T) - pairing 0 * eta 0 := by
  dsimp only
  have hsource := (continuous_reverseTimeNegativeSourceRaw r₀ r₁ P.h₀₁ P.hΩ P.hΩbounded P.F P.hFSmooth).clm_apply
    (continuous_const (y := (v : H10HilbertGraph P.hΩ)))
  have hclamp := ((continuous_reverseTimeSpatialFormOperatorClamp r₀ r₁ P.h₀₁ P.hΩ P.hΩbounded P.a P.b P.c
    P.haSmooth P.hbSmooth P.hcSmooth).continuousOn.clm_apply (continuousOn_galerkinReconstruct hspec.continuousOn)).clm_apply
    (continuousOn_const (c := (v : H10HilbertGraph P.hΩ)))
  have hae := ae_reverseTimeSpatialFormOperatorClamp_apply r₀ r₁ P.h₀₁ P.hΩ P.hΩbounded P.a P.b P.c
    P.haSmooth P.hbSmooth P.hcSmooth
  rw [reverseTimeVolume, reverseTimeOpenInterval, restrict_Ioo_eq_restrict_Icc] at hae
  refine boundaryTime_scalar_identity _ (sub_pos.mpr P.h₀₁) _ _ _ _
    (continuousOn_galerkinPairing P.hΩ N x v _ hspec.continuousOn)
    ((hsource.continuousOn.sub hclamp).integrableOn_Icc.congr ?_) ?_ hEta hDerivCont hEtaT
  · filter_upwards [hae] with τ hτ
    rw [Pi.sub_apply, hτ]
  · intro τ hτ
    let t : Set.Icc 0 (r₁ - r₀) := ⟨τ, hτ⟩
    have hrow := galerkinRate_weak P N t (x t) v
    convert hasDerivWithinAt_galerkinPairing P.hΩ N x _ v (hspec.deriv t) using 1
    rw [real_inner_comm]
    exact (eq_sub_of_add_eq hrow).symm

end HypoellipticAleksandrov.Parabolic.Dirichlet
