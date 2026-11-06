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

variable {d : ℕ} {Ω : PDE.VelocityRegion d}
variable
  (r₀ r₁ lam : ℝ) (h₀₁ : r₀ < r₁) (hlam : 0 < lam)
  (hΩ : IsOpen Ω) (hΩbounded : Bornology.IsBounded Ω)
  (a : CoefficientField d)
  (b : PDE.TimeVectorField d) (c F : PDE.TimeScalarField d)
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
  (hcNonpos : ∀ z : TimeVelocity d,
    z ∈ scalarParabolicClosedCylinder r₀ r₁ Ω → c z.1 z.2 ≤ 0)

/-- The quotient-level reverse-time identity against a fixed actual Galerkin test. -/
def reverseTimeGalerkinPrimal_fixed_test_identity_prop
    {d : ℕ} {Ω : PDE.VelocityRegion d}
    (r₀ r₁ : ℝ) (h₀₁ : r₀ < r₁)
    (hΩ : IsOpen Ω) (hΩbounded : Bornology.IsBounded Ω)
    (a : CoefficientField d)
    (b : PDE.TimeVectorField d)
    (c F : PDE.TimeScalarField d)
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
    (U : ReverseTimeL2V hΩ (r₁ - r₀))
    (k : ℕ) (eta : ReverseTimeScalarTest (r₁ - r₀)) : Prop :=
  reverseTimeDualPairingRightCLM hΩ (r₁ - r₀)
      (reverseTimeSeparatedVTestOfMemLp hΩ eta.deriv
        (eta.memLp_deriv ∞) (galerkinVector hΩ k))
      (reverseTimeGelfandCLM hΩ (r₁ - r₀) U) =
    -reverseTimeDualPairingRightCLM hΩ (r₁ - r₀)
        (reverseTimeSeparatedVTest hΩ eta (galerkinVector hΩ k))
        (reverseTimeNegativeSource r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth) +
      reverseTimeDualPairingRightCLM hΩ (r₁ - r₀)
        (reverseTimeSeparatedVTest hΩ eta (galerkinVector hΩ k))
        (reverseTimeSpatialFormBochnerAction r₀ r₁ h₀₁ hΩ hΩbounded
          a b c haSmooth hbSmooth hcSmooth U)

/-- One common weakly convergent Galerkin subsequence satisfies the identity for every
fixed actual Galerkin vector and scalar time test. -/
theorem exists_strictMono_tendsto_clm_reverseTimeGalerkinPrimal_fixedTests
    (initial : PDE.ScalarLp Ω (2 )) :
    ∃ (U : ReverseTimeL2V hΩ (r₁ - r₀)) (φ : ℕ → ℕ),
      StrictMono φ ∧
      (∀ ell : ReverseTimeL2V hΩ (r₁ - r₀) →L[ℝ] ℝ,
        Tendsto
          (fun n => ell
            (reverseTimeGalerkinPrimal r₀ r₁ lam h₀₁ hlam hΩ hΩbounded
              a b c F haSmooth hbSmooth hcSmooth hFSmooth hLower hcNonpos
              (φ n) initial))
          atTop (𝓝 (ell U))) ∧
      ∀ (k : ℕ) (eta : ReverseTimeScalarTest (r₁ - r₀)),
        reverseTimeGalerkinPrimal_fixed_test_identity_prop
          r₀ r₁ h₀₁ hΩ hΩbounded a b c F
          haSmooth hbSmooth hcSmooth hFSmooth U k eta := (Exists.casesOn
  (exists_strictMono_tendsto_clm_reverseTimeGalerkinPrimal r₀ r₁ lam h₀₁ hlam hΩ hΩbounded a b c F haSmooth hbSmooth
    hcSmooth hFSmooth hLower hcNonpos initial)
  fun U h =>
  Exists.casesOn h fun φ h =>
    And.casesOn h fun hφ hclm =>
      Exists.intro U
        (Exists.intro φ
          ⟨hφ,
            ⟨hclm, fun k eta =>
              id
                (tendsto_nhds_unique_of_eventuallyEq
                  (hclm
                    (reverseTimeDualPairingRightCLM hΩ (r₁ - r₀)
                        (reverseTimeSeparatedVTestOfMemLp hΩ eta.deriv (ReverseTimeScalarTest.memLp_deriv eta ∞)
                          (galerkinVector hΩ k)) ∘SL
                      reverseTimeGelfandCLM hΩ (r₁ - r₀)))
                  (Tendsto.add (Tendsto.neg tendsto_const_nhds)
                    (hclm
                      (reverseTimeDualPairingRightCLM hΩ (r₁ - r₀)
                          (reverseTimeSeparatedVTest hΩ eta (galerkinVector hΩ k)) ∘SL
                        reverseTimeSpatialFormBochnerAction r₀ r₁ h₀₁ hΩ hΩbounded a b c haSmooth hbSmooth hcSmooth)))
                  (mp_mem
                    (mp_mem (eventually_ge_atTop (k + 1))
                      (univ_mem' (id fun n hn => LE.le.trans hn (StrictMono.id_le hφ n))))
                    (univ_mem'
                      (id fun n hn =>
                        id
                          (reverseTimeGalerkinPrimal_pairing_identity r₀ r₁ lam h₀₁ hlam hΩ hΩbounded a b c F haSmooth
                            hbSmooth hcSmooth hFSmooth hLower hcNonpos (φ n) initial
                            ⟨galerkinVector hΩ k,
                              galerkinSpace_mono hΩ hn
                                (id (Submodule.subset_span (Exists.intro ⟨k, Nat.lt_succ_self k⟩ rfl)))⟩
                            eta)))))⟩⟩))

end HypoellipticAleksandrov.Parabolic.Dirichlet
