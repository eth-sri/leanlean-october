module

public import HypoellipticAleksandrov.Parabolic.Dirichlet.ReverseTimeGalerkinPrimalPairingIdentity
public import HypoellipticAleksandrov.Parabolic.Dirichlet.ReverseTimeGalerkinPrimalWeakSeqCLM

/-!
# Fixed actual-test reverse-time Galerkin limit identity

This module passes the common weak subsequence to every fixed actual
Galerkin vector and scalar time test.
-/

@[expose] public section

open Filter MeasureTheory Set Topology
open scoped ENNReal Matrix Matrix.Norms.Elementwise MatrixOrder RealInnerProductSpace
noncomputable section
namespace HypoellipticAleksandrov.Parabolic.Dirichlet

variable {d : ℕ} {Ω : Set (PDE.Vec d)}
variable
  {r₀ r₁ lam : ℝ} (P : ReverseTimeGalerkinProblem Ω r₀ r₁ lam)

local notation "primalCurve" => reverseTimeGalerkinPrimal P

/-- A separated multiplier vanishing at the terminal endpoint passes to the weak limit,
including its initial endpoint term. -/
theorem ReverseTimeGalerkinProblem.WeakLimit.boundaryPairing
    {initial : PDE.ScalarLp Ω 2} {U : ReverseTimeL2V P.hΩ (r₁ - r₀)} {φ : ℕ → ℕ}
    (hclm : P.WeakLimit initial U φ) (hφ : StrictMono φ) (k : ℕ)
    (q dq : ℝ → ℝ) (hq : MemLp q ∞ (reverseTimeVolume (r₁ - r₀)))
    (hdq : MemLp dq ∞ (reverseTimeVolume (r₁ - r₀)))
    (hderiv : ∀ t ∈ Icc 0 (r₁ - r₀), HasDerivWithinAt q (dq t) (Icc 0 (r₁ - r₀)) t)
    (hcont : ContinuousOn dq (Icc 0 (r₁ - r₀))) (hT : q (r₁ - r₀) = 0) :
    let T := r₁ - r₀
    let v := galerkinVector P.hΩ k
    reverseTimeDualPairingRightCLM P.hΩ T (reverseTimeSeparatedVTestOfMemLp P.hΩ dq hdq v)
        (reverseTimeGelfandCLM P.hΩ T U) =
      -reverseTimeDualPairingRightCLM P.hΩ T (reverseTimeSeparatedVTestOfMemLp P.hΩ q hq v)
        (P.residual U) - inner ℝ (valueCLM P.hΩ v) initial * q 0 := by
  let T := r₁ - r₀
  let v := galerkinVector P.hΩ k
  let mass := (reverseTimeDualPairingRightCLM P.hΩ T
    (reverseTimeSeparatedVTestOfMemLp P.hΩ dq hdq v)).comp (reverseTimeGelfandCLM P.hΩ T)
  let pair := reverseTimeDualPairingRightCLM P.hΩ T (reverseTimeSeparatedVTestOfMemLp P.hΩ q hq v)
  let A := reverseTimeSpatialFormBochnerAction r₀ r₁ P.h₀₁ P.hΩ P.hΩbounded
    P.a P.b P.c P.haSmooth P.hbSmooth P.hcSmooth
  let S := reverseTimeNegativeSource r₀ r₁ P.h₀₁ P.hΩ P.hΩbounded P.F P.hFSmooth
  let form := pair.comp A
  let start := inner ℝ (valueCLM P.hΩ v) initial * q 0
  have hneg (W : ReverseTimeL2V P.hΩ T) : -pair (P.residual W) = form W - pair S := by
    change -pair (S - A W) = pair (A W) - pair S
    rw [map_sub, neg_sub]
  have hFinite : (fun n => mass (primalCurve (φ n) initial)) =ᶠ[atTop]
      fun n => form (primalCurve (φ n) initial) - pair S - start := by
    filter_upwards [eventually_ge_atTop (k + 1)] with n hn
    let w : galerkinSpace P.hΩ (φ n) := ⟨v,
      Submodule.subset_span ⟨⟨k, hn.trans (hφ.id_le n)⟩, rfl⟩⟩
    have h := reverseTimeGalerkinPrimal_boundaryPairing P (φ n) initial w q dq hq hdq hderiv hcont hT
    change mass (primalCurve (φ n) initial) = -pair (P.residual (primalCurve (φ n) initial)) - start at h
    rwa [hneg] at h
  change mass U = -pair (P.residual U) - start
  rw [hneg]
  exact tendsto_nhds_unique_of_eventuallyEq (hclm mass)
    (((hclm form).sub tendsto_const_nhds).sub tendsto_const_nhds) hFinite

/-- One common weakly convergent Galerkin subsequence satisfies the identity for every
fixed actual Galerkin vector and scalar time test. -/
theorem exists_strictMono_tendsto_clm_reverseTimeGalerkinPrimal_fixedTests
    (initial : PDE.ScalarLp Ω (2 : ℝ≥0∞)) :
    ∃ (U : ReverseTimeL2V P.hΩ (r₁ - r₀)) (φ : ℕ → ℕ),
      StrictMono φ ∧ P.WeakLimit initial U φ ∧
      ∀ (k : ℕ) (eta : ReverseTimeScalarTest (r₁ - r₀)),
        P.TestEquation U (galerkinVector P.hΩ k) eta := by
  obtain ⟨U, φ, hφ, hclm⟩ := exists_strictMono_tendsto_clm_reverseTimeGalerkinPrimal P initial
  refine ⟨U, φ, hφ, hclm, fun k eta => ?_⟩
  have hzero (t : ℝ) (ht : t ∉ Ioo 0 (r₁ - r₀)) : eta t = 0 :=
    image_eq_zero_of_notMem_tsupport (fun h => ht (eta.tsupport_subset h))
  have hd (t : ℝ) (_ : t ∈ Icc 0 (r₁ - r₀)) :
      HasDerivWithinAt eta (eta.deriv t) (Icc 0 (r₁ - r₀)) t := by
    rw [ReverseTimeScalarTest.deriv_apply]
    exact ((eta.contDiff.differentiable (by simp)).differentiableAt.hasDerivAt).hasDerivWithinAt
  simpa only [ReverseTimeGalerkinProblem.TestEquation, reverseTimeSeparatedVTest,
    hzero 0 (by simp), mul_zero, sub_zero] using
    ReverseTimeGalerkinProblem.WeakLimit.boundaryPairing P hclm hφ k eta eta.deriv
      (eta.memLp ∞) (eta.memLp_deriv ∞) hd eta.contDiff_deriv.continuous.continuousOn (hzero _ (by simp))

end HypoellipticAleksandrov.Parabolic.Dirichlet
