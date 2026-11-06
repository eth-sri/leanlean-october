module

public import HypoellipticAleksandrov.Parabolic.Dirichlet.ReverseTimeGelfandPairing
public import HypoellipticAleksandrov.Parabolic.Dirichlet.ReverseTimeSourcePairing
public import HypoellipticAleksandrov.Parabolic.Dirichlet.ReverseTimeSpatialFormPairing
public import HypoellipticAleksandrov.Parabolic.Dirichlet.ReverseTimeGalerkinPrimalBochner

/-!
# Finite reverse-time Galerkin pairing identity

This module transports the selected finite Galerkin compact-time identity to
canonical Bochner quotient representatives using the
almost-everywhere representatives.
-/

@[expose] public section

open Filter MeasureTheory Set
open scoped ENNReal Matrix Matrix.Norms.Elementwise MatrixOrder
noncomputable section
namespace HypoellipticAleksandrov.Parabolic.Dirichlet

private theorem integrable_reverseTimeNegativeSourceRaw_mul_test
    {d : ℕ} {Ω : PDE.VelocityRegion d} (r₀ r₁ : ℝ) (h₀₁ : r₀ < r₁)
    (hΩ : IsOpen Ω) (hΩbounded : Bornology.IsBounded Ω)
    (F : PDE.TimeScalarField d)
    (hFSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => F z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (eta : ReverseTimeScalarTest (r₁ - r₀)) (v : H10HilbertGraph hΩ) :
    Integrable (fun τ => reverseTimeNegativeSourceRaw r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth τ v * eta τ)
      (reverseTimeVolume (r₁ - r₀)) := by
  let S := reverseTimeNegativeSource r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth
  let z := reverseTimeSeparatedVTest hΩ eta v

  refine (integrable_reverseTimeDualPairing hΩ (r₁ - r₀) z S).congr ?_
  filter_upwards [(memLp_reverseTimeNegativeSourceRaw r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth).coeFn_toLp,
    ae_reverseTimeSeparatedVTest hΩ eta v] with τ hS hz
  dsimp only [S, z]
  calc
    reverseTimeNegativeSource r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth τ
        (reverseTimeSeparatedVTest hΩ eta v τ) =
        reverseTimeNegativeSource r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth τ (eta τ • v) :=
      congrArg _ hz
    _ = eta τ * reverseTimeNegativeSource r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth τ v := by
      rw [ContinuousLinearMap.map_smul]
      rfl
    _ = eta τ * reverseTimeNegativeSourceRaw r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth τ v :=
      congrArg (fun g => eta τ * g v) hS
    _ = reverseTimeNegativeSourceRaw r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth τ v * eta τ := mul_comm _ _

variable {α : Type*}

private theorem raw_integral_transport
     [MeasurableSpace α] (μ : Measure α)
    (mass source form : ℝ) (s f : α → ℝ)
    (hs : Integrable s μ) (hsf : Integrable (fun x => s x - f x) μ)
    (hmass : mass = -(∫ x, (s x - f x) ∂μ))
    (hsource : source = ∫ x, s x ∂μ) (hform : form = ∫ x, f x ∂μ) :
    mass = -source + form := by

  calc
    mass = -(∫ x, (s x - f x) ∂μ) := hmass
    _ = -((∫ x, s x ∂μ) - ∫ x, f x ∂μ) := by rw [integral_sub hs (by
        refine (hs.sub hsf).congr (Eventually.of_forall fun x => ?_)
        change s x - (s x - f x) = f x
        ring)]
    _ = -(∫ x, s x ∂μ) + ∫ x, f x ∂μ := by ring
    _ = -source + form := by rw [← hsource, ← hform]


private theorem integral_eq_of_ae_of_integrable
     [MeasurableSpace α] (μ : Measure α) (f g : α → ℝ)
    (hf : Integrable f μ) (hg : Integrable g μ) (hfg : f =ᵐ[μ] g) :
    (∫ x, f x ∂μ) = ∫ x, g x ∂μ := by

  calc
    (∫ x, f x ∂μ) = ∫ x, (hf.toL1 f) x ∂μ := (L1.integral_of_fun_eq_integral hf).symm
    _ = ∫ x, (hg.toL1 g) x ∂μ := congrArg (fun w : α →₁[μ] ℝ => ∫ x, w x ∂μ) ((Integrable.toL1_eq_toL1_iff f g hf hg).2 hfg)
    _ = ∫ x, g x ∂μ := L1.integral_of_fun_eq_integral hg

variable {d : ℕ} {Ω : PDE.VelocityRegion d}
variable (r₀ r₁ lam : ℝ) (h₀₁ : r₀ < r₁) (hlam : 0 < lam)
  (hΩ : IsOpen Ω) (hΩbounded : Bornology.IsBounded Ω) (a : CoefficientField d)
  (b : PDE.TimeVectorField d) (c F : PDE.TimeScalarField d)
  (haSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => a z.1 z.2)
    (scalarParabolicClosedCylinder r₀ r₁ Ω))
  (hbSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => b z.1 z.2)
    (scalarParabolicClosedCylinder r₀ r₁ Ω))
  (hcSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => c z.1 z.2)
    (scalarParabolicClosedCylinder r₀ r₁ Ω))
  (hFSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => F z.1 z.2)
    (scalarParabolicClosedCylinder r₀ r₁ Ω))
  (hLower : ∀ z : TimeVelocity d, z ∈ scalarParabolicClosedCylinder r₀ r₁ Ω → lam • (1 : PDE.Mat
    d) ≤ a z.1 z.2)
  (hcNonpos : ∀ z : TimeVelocity d, z ∈ scalarParabolicClosedCylinder r₀ r₁ Ω → c z.1 z.2 ≤ 0)

/-- The literal finite Galerkin mass/source/form pairing identity. -/
def reverseTimeGalerkinPrimal_pairing_identity_prop {d : ℕ} {Ω : PDE.VelocityRegion d}
    (r₀ r₁ lam : ℝ) (h₀₁ : r₀ < r₁) (hlam : 0 < lam) (hΩ : IsOpen Ω) (hΩbounded :
      Bornology.IsBounded Ω)
    (a : CoefficientField d) (b : PDE.TimeVectorField d) (c F : PDE.TimeScalarField d)
    (haSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => a z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hbSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => b z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hcSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => c z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hFSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => F z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hLower : ∀ z : TimeVelocity d, z ∈ scalarParabolicClosedCylinder r₀ r₁ Ω → lam • (1 : PDE.Mat
      d) ≤ a z.1 z.2)
    (hcNonpos : ∀ z : TimeVelocity d, z ∈ scalarParabolicClosedCylinder r₀ r₁ Ω → c z.1 z.2 ≤ 0)
    (N : ℕ) (initial : PDE.ScalarLp Ω (2 )) (v : galerkinSpace hΩ N) (eta :
      ReverseTimeScalarTest (r₁-r₀)) : Prop :=
  reverseTimeDualPairingRightCLM hΩ (r₁-r₀) (reverseTimeSeparatedVTestOfMemLp hΩ eta.deriv
    (eta.memLp_deriv ∞) (v : H10HilbertGraph hΩ))
      (reverseTimeGelfandCLM hΩ (r₁-r₀) (reverseTimeGalerkinPrimal r₀ r₁ lam h₀₁ hlam hΩ hΩbounded
        a b c F haSmooth hbSmooth hcSmooth hFSmooth hLower hcNonpos N initial)) =
    -reverseTimeDualPairingRightCLM hΩ (r₁-r₀) (reverseTimeSeparatedVTest hΩ eta (v :
      H10HilbertGraph hΩ)) (reverseTimeNegativeSource r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth) +
    reverseTimeDualPairingRightCLM hΩ (r₁-r₀) (reverseTimeSeparatedVTest hΩ eta (v :
      H10HilbertGraph hΩ))
      (reverseTimeSpatialFormBochnerAction r₀ r₁ h₀₁ hΩ hΩbounded a b c haSmooth hbSmooth hcSmooth
        (reverseTimeGalerkinPrimal r₀ r₁ lam h₀₁ hlam hΩ hΩbounded a b c F haSmooth hbSmooth
          hcSmooth hFSmooth hLower hcNonpos N initial))

variable (N : ℕ) (initial : PDE.ScalarLp Ω (2 )) (v : galerkinSpace hΩ N) (eta : ReverseTimeScalarTest (r₁ - r₀))



/-- The finite Galerkin pairing identity for canonical quotient representatives. -/
theorem reverseTimeGalerkinPrimal_pairing_identity
     :
    reverseTimeGalerkinPrimal_pairing_identity_prop r₀ r₁ lam h₀₁ hlam hΩ hΩbounded a b c F
      haSmooth hbSmooth hcSmooth hFSmooth hLower hcNonpos N initial v eta := by
  let sharedTerm_084132931c := ((valueCLM hΩ (v : H10HilbertGraph hΩ)))
  let sharedTerm_17d78133b4 := ((reverseTimeVolume (r₁ - r₀)))
  let U := reverseTimeGalerkinPrimal r₀ r₁ lam h₀₁ hlam hΩ hΩbounded a b c F haSmooth hbSmooth
    hcSmooth hFSmooth hLower hcNonpos N initial
  let raw := reverseTimeGalerkinPrimalRaw r₀ r₁ lam h₀₁ hlam hΩ hΩbounded a b c F haSmooth
    hbSmooth hcSmooth hFSmooth hLower hcNonpos N initial
  have hUraw : U =ᵐ[reverseTimeVolume (r₁ - r₀)] raw := by
    exact ae_reverseTimeGalerkinPrimal_eq_raw r₀ r₁ lam h₀₁ hlam hΩ hΩbounded
      a b c F haSmooth hbSmooth hcSmooth hFSmooth hLower hcNonpos N initial
  obtain ⟨hMassRaw, hResidualRaw, hRawIdentity⟩ :=
    reverseTimeGalerkinPrimal_compactTime r₀ r₁ lam h₀₁ hlam hΩ hΩbounded a b c F haSmooth
      hbSmooth hcSmooth hFSmooth hLower hcNonpos N initial v eta
  have hMassRaw' : Integrable (fun τ => inner ℝ sharedTerm_084132931c
      (valueCLM hΩ (raw τ)) * eta.deriv τ) sharedTerm_17d78133b4 := by
    simpa only [raw] using hMassRaw

  let massRaw : ℝ := ∫ τ, inner ℝ sharedTerm_084132931c (valueCLM hΩ (raw τ)) *
    eta.deriv τ ∂reverseTimeVolume (r₁ - r₀)

  have hSourceRaw := integrable_reverseTimeNegativeSourceRaw_mul_test r₀ r₁ h₀₁ hΩ hΩbounded F
    hFSmooth eta (v : H10HilbertGraph hΩ)
  have hSourcePair := reverseTimeNegativeSource_pairing_eq_integral_raw r₀ r₁ h₀₁ hΩ hΩbounded F
    hFSmooth eta (v : H10HilbertGraph hΩ)
  have hFormPair := reverseTimeSpatialForm_pairing_eq_integral r₀ r₁ h₀₁ hΩ hΩbounded a b c
    haSmooth hbSmooth hcSmooth U eta (v : H10HilbertGraph hΩ)

  have hResidualRaw' : Integrable (fun τ =>
      (reverseTimeNegativeSourceRaw r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth τ (v : H10HilbertGraph hΩ) -
        reverseTimeSpatialForm hΩ r₁ τ a b c (raw τ) (v : H10HilbertGraph hΩ)) * eta τ)
          sharedTerm_17d78133b4 := by
    exact hResidualRaw
  have hDiffRaw : Integrable (fun τ =>
      reverseTimeNegativeSourceRaw r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth τ (v : H10HilbertGraph hΩ) *
        eta τ -
      reverseTimeSpatialForm hΩ r₁ τ a b c (raw τ) (v : H10HilbertGraph hΩ) * eta τ)
        sharedTerm_17d78133b4 := by
    refine hResidualRaw'.congr (Eventually.of_forall fun τ => ?_)
    change (reverseTimeNegativeSourceRaw r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth τ (v : H10HilbertGraph
      hΩ) -
      reverseTimeSpatialForm hΩ r₁ τ a b c (raw τ) (v : H10HilbertGraph hΩ)) * eta τ =
      reverseTimeNegativeSourceRaw r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth τ (v : H10HilbertGraph hΩ) *
        eta τ -
      reverseTimeSpatialForm hΩ r₁ τ a b c (raw τ) (v : H10HilbertGraph hΩ) * eta τ
    exact sub_mul _ _ _

  have hConcrete := raw_integral_transport sharedTerm_17d78133b4 _ _ _
    (fun τ => reverseTimeNegativeSourceRaw r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth τ (v :
      H10HilbertGraph hΩ) * eta τ)
    (fun τ => reverseTimeSpatialForm hΩ r₁ τ a b c (raw τ) (v : H10HilbertGraph hΩ) * eta τ)
    hSourceRaw hDiffRaw ((show reverseTimeDualPairingRightCLM hΩ (r₁ - r₀)
      (reverseTimeSeparatedVTestOfMemLp hΩ eta.deriv (eta.memLp_deriv ∞) (v : H10HilbertGraph hΩ))
      (reverseTimeGelfandCLM hΩ (r₁ - r₀) U) = massRaw by
        calc
          _ = ∫ τ, inner ℝ sharedTerm_084132931c (valueCLM hΩ (U τ)) * eta.deriv τ
            ∂reverseTimeVolume (r₁ - r₀) :=
            reverseTimeGelfand_pairing_multiplier_eq_integral hΩ U eta.deriv (eta.memLp_deriv ∞) _
          _ = massRaw := by
            dsimp only [massRaw]
            apply integral_eq_of_ae_of_integrable sharedTerm_17d78133b4
              (fun τ => inner ℝ sharedTerm_084132931c (valueCLM hΩ (U τ)) * eta.deriv
                τ)
              (fun τ => inner ℝ sharedTerm_084132931c (valueCLM hΩ (raw τ)) *
                eta.deriv τ)
              (by
                  refine hMassRaw'.congr ?_
                  filter_upwards [hUraw] with τ hτ
                  rw [hτ]) hMassRaw'
            filter_upwards [hUraw] with τ hτ
            rw [hτ]).trans (by
        have hRawIdentity0 : massRaw = -∫ τ,
            (reverseTimeNegativeSourceRaw r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth τ (v : H10HilbertGraph hΩ) -
            reverseTimeSpatialForm hΩ r₁ τ a b c (raw τ) (v : H10HilbertGraph hΩ)) * eta τ
              ∂reverseTimeVolume (r₁-r₀) := by
          simpa only [massRaw, raw] using hRawIdentity
        rw [hRawIdentity0]
        congr 1
        apply integral_eq_of_ae_of_integrable sharedTerm_17d78133b4 _ _ hResidualRaw' hDiffRaw
        filter_upwards with τ
        change (reverseTimeNegativeSourceRaw r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth τ (v : H10HilbertGraph
          hΩ) -
          reverseTimeSpatialForm hΩ r₁ τ a b c (raw τ) (v : H10HilbertGraph hΩ)) * eta τ =
          reverseTimeNegativeSourceRaw r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth τ (v : H10HilbertGraph hΩ) *
            eta τ -
          reverseTimeSpatialForm hΩ r₁ τ a b c (raw τ) (v : H10HilbertGraph hΩ) * eta τ
        exact sub_mul _ _ _)) hSourcePair (by
        calc
          _ = ∫ τ, reverseTimeSpatialForm hΩ r₁ τ a b c (U τ) (v : H10HilbertGraph hΩ) * eta τ
            ∂reverseTimeVolume (r₁ - r₀) := hFormPair
          _ = _ := by
            apply integral_congr_ae
            filter_upwards [hUraw] with τ hτ
            rw [hτ])
  assumption

end HypoellipticAleksandrov.Parabolic.Dirichlet
