module

public import HypoellipticAleksandrov.Parabolic.Dirichlet.ReverseTimeGalerkinPrimalFixedTestLimit

/-!
# Arbitrary-test reverse-time Galerkin limit identity

This module extends the common-subsequence identity from the dense
range of actual Galerkin vectors to every spatial `H¹₀` Hilbert test.
-/

@[expose] public section

open Filter MeasureTheory Set Topology
open scoped ENNReal Matrix Matrix.Norms.Elementwise MatrixOrder RealInnerProductSpace
noncomputable section
namespace HypoellipticAleksandrov.Parabolic.Dirichlet

variable {d : ℕ} {Ω : Set (PDE.Vec d)}
variable
  {r₀ r₁ lam : ℝ} (P : ReverseTimeGalerkinProblem Ω r₀ r₁ lam)

/-- One common weakly convergent Galerkin subsequence satisfies the identity
for every spatial test and every scalar time test. -/
theorem exists_strictMono_tendsto_clm_reverseTimeGalerkinPrimal_arbitraryTests
    (initial : PDE.ScalarLp Ω (2 : ℝ≥0∞)) :
    ∃ (U : ReverseTimeL2V P.hΩ (r₁ - r₀)) (φ : ℕ → ℕ),
      StrictMono φ ∧
      P.WeakLimit initial U φ ∧
      ∀ (v : H10HilbertGraph P.hΩ)
        (eta : ReverseTimeScalarTest (r₁ - r₀)),
        P.TestEquation U v eta := by
  obtain ⟨U, φ, hφ, hclm, hfixed⟩ :=
    exists_strictMono_tendsto_clm_reverseTimeGalerkinPrimal_fixedTests
      P initial
  refine ⟨U, φ, hφ, hclm, ?_⟩
  intro v eta
  have hcont (q : ℝ → ℝ) (hq : MemLp q ∞ (reverseTimeVolume (r₁ - r₀)))
      (g : ReverseTimeL2VStar P.hΩ (r₁ - r₀)) :
      Continuous (fun w => reverseTimeDualPairingRightCLM P.hΩ (r₁ - r₀)
        (reverseTimeSeparatedVTestOfMemLp P.hΩ q hq w) g) :=
    (reverseTimeDualPairingCLM P.hΩ (r₁ - r₀) g).continuous.comp
      (reverseTimeSeparatedVTestCLM P.hΩ q hq).continuous
  apply congrFun (Continuous.ext_on (denseRange_galerkinVector P.hΩ) (hcont _ _ _)
    (hcont eta (eta.memLp ∞) (P.residual U)).neg ?_) v
  rintro _ ⟨k, rfl⟩
  exact hfixed k eta

end HypoellipticAleksandrov.Parabolic.Dirichlet
