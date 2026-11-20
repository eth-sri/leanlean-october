module

public import HypoellipticAleksandrov.Parabolic.Dirichlet.ReverseTimeGelfandPairing
public import HypoellipticAleksandrov.Parabolic.Dirichlet.ReverseTimeDualPairingRight
public import HypoellipticAleksandrov.Parabolic.Dirichlet.ReverseTimeSourceBochner
public import HypoellipticAleksandrov.Parabolic.Dirichlet.ReverseTimeSpatialFormBochner
public import HypoellipticAleksandrov.Parabolic.Dirichlet.ReverseTimeGalerkinPrimalBochner

public import HypoellipticAleksandrov.Parabolic.Dirichlet.ReverseTimeGalerkinPrimalBase

public import HypoellipticAleksandrov.Parabolic.Dirichlet.ReverseTimeFormResidual

/-!
# Finite reverse-time Galerkin pairing identity

This module transports the selected finite Galerkin compact-time identity to
canonical Bochner quotient representatives using the
almost-everywhere representatives.
-/

@[expose] public section

open Filter MeasureTheory Set Topology
open scoped ENNReal Matrix Matrix.Norms.Elementwise MatrixOrder RealInnerProductSpace
noncomputable section
namespace HypoellipticAleksandrov.Parabolic.Dirichlet

variable {d : ℕ} {Ω : Set (PDE.Vec d)}

/-- A fixed lower Galerkin test pairs the higher initial projection exactly as
it pairs the original spatial initial datum. -/
private theorem inner_value_galerkinInitialProjection_eq
    (hΩ : IsOpen Ω) {M N : ℕ} (hMN : M ≤ N)
    (initial : PDE.ScalarLp Ω (2 : ℝ≥0∞))
    (v : galerkinSpace hΩ M) :
    inner ℝ (valueCLM hΩ (v : H10HilbertGraph hΩ))
      (valueCLM hΩ (galerkinInitialProjection hΩ N initial :
        H10HilbertGraph hΩ)) =
      inner ℝ (valueCLM hΩ (v : H10HilbertGraph hΩ)) initial := by
  let K := galerkinValueSpace hΩ N
  have hvN : (v : H10HilbertGraph hΩ) ∈ galerkinSpace hΩ N :=
    galerkinSpace_mono hΩ hMN v.property
  let u : K := ⟨valueCLM hΩ (v : H10HilbertGraph hΩ), ⟨v, hvN, rfl⟩⟩
  rw [value_galerkinInitialProjection]
  change inner ℝ (u : PDE.ScalarLp Ω (2 : ℝ≥0∞)) (K.orthogonalProjection initial) =
    inner ℝ (u : PDE.ScalarLp Ω (2 : ℝ≥0∞)) initial
  exact Submodule.inner_orthogonalProjection_eq_of_mem_left u initial

variable {r₀ r₁ lam : ℝ} (P : ReverseTimeGalerkinProblem Ω r₀ r₁ lam)

/-- The source minus the spatial form, as a Bochner dual value. -/
noncomputable abbrev ReverseTimeGalerkinProblem.residual (U : ReverseTimeL2V P.hΩ (r₁ - r₀)) :=
  reverseTimeFormResidual r₀ r₁ P.h₀₁ P.hΩ P.hΩbounded P.a P.b P.c
    P.haSmooth P.hbSmooth P.hcSmooth P.F P.hFSmooth U

/-- The reflected equation tested against a separated time and space test. -/
def ReverseTimeGalerkinProblem.TestEquation
    (U : ReverseTimeL2V P.hΩ (r₁ - r₀))
    (v : H10HilbertGraph P.hΩ)
    (eta : ReverseTimeScalarTest (r₁ - r₀)) : Prop :=
  reverseTimeDualPairingRightCLM P.hΩ (r₁ - r₀)
      (reverseTimeSeparatedVTestOfMemLp P.hΩ eta.deriv
        (eta.memLp_deriv ∞) v)
      (reverseTimeGelfandCLM P.hΩ (r₁ - r₀) U) =
    -reverseTimeDualPairingRightCLM P.hΩ (r₁ - r₀)
      (reverseTimeSeparatedVTest P.hΩ eta v) (P.residual U)

local notation "primalCurve" => reverseTimeGalerkinPrimal P

section
variable (N : ℕ)

/-- The boundary identity in the Bochner quotients, for a bounded time multiplier
that vanishes only at the terminal endpoint. -/
theorem reverseTimeGalerkinPrimal_boundaryPairing (initial : PDE.ScalarLp Ω 2) (v : galerkinSpace P.hΩ N)
    (q dq : ℝ → ℝ) (hq : MemLp q ∞ (reverseTimeVolume (r₁ - r₀)))
    (hdq : MemLp dq ∞ (reverseTimeVolume (r₁ - r₀)))
    (hderiv : ∀ t ∈ Icc 0 (r₁ - r₀), HasDerivWithinAt q (dq t) (Icc 0 (r₁ - r₀)) t)
    (hcont : ContinuousOn dq (Icc 0 (r₁ - r₀))) (hT : q (r₁ - r₀) = 0) :
    let T := r₁ - r₀
    let U := primalCurve N initial
    let w : H10HilbertGraph P.hΩ := v
    let z := reverseTimeSeparatedVTestOfMemLp P.hΩ q hq w
    let dz := reverseTimeSeparatedVTestOfMemLp P.hΩ dq hdq w
    reverseTimeDualPairingRightCLM P.hΩ T dz (reverseTimeGelfandCLM P.hΩ T U) =
      -reverseTimeDualPairingRightCLM P.hΩ T z (P.residual U) -
        inner ℝ (valueCLM P.hΩ w) initial * q 0 := by
  let T := r₁ - r₀
  let U := primalCurve N initial
  let w : H10HilbertGraph P.hΩ := v
  let raw := reverseTimeGalerkinPrimalRaw P N initial
  let g := P.residual U
  have hraw := ae_reverseTimeGalerkinPrimal_eq_raw P N initial
  have hmass := reverseTimeGelfand_pairing_multiplier_eq_integral P.hΩ U dq hdq w
  have hboundary := ((reverseTimeGalerkinPrimal_trajectory P N initial).boundaryTime P v q dq hderiv hcont hT).2.2
  change (∫ t, inner ℝ (valueCLM P.hΩ w) (valueCLM P.hΩ (raw t)) * dq t ∂reverseTimeVolume T) =
    -(∫ t, (P.sourceRaw t w - P.form t (raw t) w) * q t ∂reverseTimeVolume T) -
      inner ℝ (valueCLM P.hΩ w) (valueCLM P.hΩ (reverseTimeGalerkinPrimalRaw P N initial 0)) * q 0 at hboundary
  rw [reverseTimeGalerkinPrimalRaw_zero P N initial, inner_value_galerkinInitialProjection_eq P.hΩ le_rfl initial v] at hboundary
  have hres := ae_reverseTimeFormResidual_eq_raw r₀ r₁ P.h₀₁ P.hΩ P.hΩbounded P.a P.b P.c
    P.haSmooth P.hbSmooth P.hcSmooth P.F P.hFSmooth U
  have hpair := reverseTimeDualPairing_multiplier_eq_integral P.hΩ g q hq w
    (ae_of_all _ (fun _ => rfl))
  have hmassRaw : (∫ t, inner ℝ (valueCLM P.hΩ w) (valueCLM P.hΩ (U t)) * dq t ∂reverseTimeVolume T) =
      ∫ t, inner ℝ (valueCLM P.hΩ w) (valueCLM P.hΩ (raw t)) * dq t ∂reverseTimeVolume T := by
    refine integral_congr_ae ?_
    filter_upwards [hraw] with t ht
    exact congrArg (fun u => inner ℝ (valueCLM P.hΩ w) (valueCLM P.hΩ u) * dq t) ht
  have hresRaw : (∫ t, g t w * q t ∂reverseTimeVolume T) =
      ∫ t, (P.sourceRaw t w - P.form t (raw t) w) * q t ∂reverseTimeVolume T := by
    refine integral_congr_ae ?_
    filter_upwards [hres, hraw] with t hg ht
    rw [hg w]
    exact congrArg (fun u => (P.sourceRaw t w - P.form t u w) * q t) ht
  have h := hmass.trans (hmassRaw.trans hboundary)
  rw [← hresRaw, ← hpair] at h
  exact h

end

end HypoellipticAleksandrov.Parabolic.Dirichlet
