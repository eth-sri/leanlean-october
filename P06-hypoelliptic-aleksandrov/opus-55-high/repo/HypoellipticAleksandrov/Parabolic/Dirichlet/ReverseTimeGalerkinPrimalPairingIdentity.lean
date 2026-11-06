module

public import HypoellipticAleksandrov.Parabolic.Dirichlet.ReverseTimeGelfandPairing
public import HypoellipticAleksandrov.Parabolic.Dirichlet.ReverseTimeSourcePairing
public import HypoellipticAleksandrov.Parabolic.Dirichlet.ReverseTimeSpatialFormPairing
public import HypoellipticAleksandrov.Parabolic.Dirichlet.ReverseTimeGalerkinPrimalBochner
public import HypoellipticAleksandrov.Parabolic.Dirichlet.ReverseTimeSeparatedResidual

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


private theorem raw_integral_transport
    {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (mass source form : ℝ) (s f : α → ℝ)
    (hs : Integrable s μ) (hsf : Integrable (fun x => s x - f x) μ)
    (hmass : mass = -(∫ x, (s x - f x) ∂μ))
    (hsource : source = ∫ x, s x ∂μ) (hform : form = ∫ x, f x ∂μ) :
    mass = -source + form := by
  have hf : Integrable f μ := by
    refine (hs.sub hsf).congr (Eventually.of_forall fun x => ?_)
    change s x - (s x - f x) = f x
    ring
  calc
    mass = -(∫ x, (s x - f x) ∂μ) := hmass
    _ = -((∫ x, s x ∂μ) - ∫ x, f x ∂μ) := by rw [integral_sub hs hf]
    _ = -(∫ x, s x ∂μ) + ∫ x, f x ∂μ := by ring
    _ = -source + form := by rw [← hsource, ← hform]


private theorem integral_eq_of_ae_of_integrable
    {α : Type*} [MeasurableSpace α] (μ : Measure α) (f g : α → ℝ)
    (hf : Integrable f μ) (hg : Integrable g μ) (hfg : f =ᵐ[μ] g) :
    (∫ x, f x ∂μ) = ∫ x, g x ∂μ := by
  have hL1 : hf.toL1 f = hg.toL1 g :=
    (Integrable.toL1_eq_toL1_iff f g hf hg).2 hfg
  calc
    (∫ x, f x ∂μ) = ∫ x, (hf.toL1 f) x ∂μ := (L1.integral_of_fun_eq_integral hf).symm
    _ = ∫ x, (hg.toL1 g) x ∂μ := congrArg (fun w : α →₁[μ] ℝ => ∫ x, w x ∂μ) hL1
    _ = ∫ x, g x ∂μ := L1.integral_of_fun_eq_integral hg

variable {d : ℕ} {Ω : Set (PDE.Vec d)}
variable (r₀ r₁ lam : ℝ) (h₀₁ : r₀ < r₁) (hlam : 0 < lam)
  (hΩ : IsOpen Ω) (hΩbounded : Bornology.IsBounded Ω) (a : CoefficientField d)
  (b : ℝ → PDE.Vec d → PDE.Vec d) (c F : ℝ → PDE.Vec d → ℝ)
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
def reverseTimeGalerkinPrimal_pairing_identity_prop {d : ℕ} {Ω : Set (PDE.Vec d)}
    (r₀ r₁ lam : ℝ) (h₀₁ : r₀ < r₁) (hlam : 0 < lam) (hΩ : IsOpen Ω) (hΩbounded :
      Bornology.IsBounded Ω)
    (a : CoefficientField d) (b : ℝ → PDE.Vec d → PDE.Vec d) (c F : ℝ → PDE.Vec d → ℝ)
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
    (N : ℕ) (initial : PDE.ScalarLp Ω (2 : ℝ≥0∞)) (v : galerkinSpace hΩ N) (eta :
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

variable (N : ℕ) (initial : PDE.ScalarLp Ω (2 : ℝ≥0∞)) (v : galerkinSpace hΩ N) (eta : ReverseTimeScalarTest (r₁ - r₀))

private theorem reverseTimeGalerkinPrimal_pairing_identity_prop_intro
     (U : ReverseTimeL2V hΩ (r₁ - r₀))
    (hU : U = reverseTimeGalerkinPrimal r₀ r₁ lam h₀₁ hlam hΩ hΩbounded a b c F
      haSmooth hbSmooth hcSmooth hFSmooth hLower hcNonpos N initial)
    (h : reverseTimeDualPairingRightCLM hΩ (r₁-r₀)
        (reverseTimeSeparatedVTestOfMemLp hΩ eta.deriv (eta.memLp_deriv ∞)
          (v : H10HilbertGraph hΩ))
        (reverseTimeGelfandCLM hΩ (r₁-r₀) U) =
      -reverseTimeDualPairingRightCLM hΩ (r₁-r₀)
          (reverseTimeSeparatedVTest hΩ eta (v : H10HilbertGraph hΩ))
          (reverseTimeNegativeSource r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth) +
        reverseTimeDualPairingRightCLM hΩ (r₁-r₀)
          (reverseTimeSeparatedVTest hΩ eta (v : H10HilbertGraph hΩ))
          (reverseTimeSpatialFormBochnerAction r₀ r₁ h₀₁ hΩ hΩbounded a b c
            haSmooth hbSmooth hcSmooth U)) :
    reverseTimeGalerkinPrimal_pairing_identity_prop r₀ r₁ lam h₀₁ hlam hΩ hΩbounded a b c F
      haSmooth hbSmooth hcSmooth hFSmooth hLower hcNonpos N initial v eta := by
  subst U
  simpa only [reverseTimeGalerkinPrimal_pairing_identity_prop] using h

/-- The finite Galerkin pairing identity for canonical quotient representatives. -/
theorem reverseTimeGalerkinPrimal_pairing_identity
     :
    reverseTimeGalerkinPrimal_pairing_identity_prop r₀ r₁ lam h₀₁ hlam hΩ hΩbounded a b c F
      haSmooth hbSmooth hcSmooth hFSmooth hLower hcNonpos N initial v eta := by
  let U := reverseTimeGalerkinPrimal r₀ r₁ lam h₀₁ hlam hΩ hΩbounded a b c F haSmooth hbSmooth
    hcSmooth hFSmooth hLower hcNonpos N initial
  let raw := reverseTimeGalerkinPrimalRaw r₀ r₁ lam h₀₁ hlam hΩ hΩbounded a b c F haSmooth
    hbSmooth hcSmooth hFSmooth hLower hcNonpos N initial
  have hUraw : U =ᵐ[reverseTimeVolume (r₁ - r₀)] raw := by
    simpa using ae_reverseTimeGalerkinPrimal_eq_raw r₀ r₁ lam h₀₁ hlam hΩ hΩbounded
      a b c F haSmooth hbSmooth hcSmooth hFSmooth hLower hcNonpos N initial
  obtain ⟨hMassRaw, hResidualRaw, hRawIdentity⟩ :=
    reverseTimeGalerkinPrimal_compactTime r₀ r₁ lam h₀₁ hlam hΩ hΩbounded a b c F haSmooth
      hbSmooth hcSmooth hFSmooth hLower hcNonpos N initial v eta
  have hMassRaw' : Integrable (fun τ => inner ℝ (valueCLM hΩ v)
      (valueCLM hΩ (raw τ)) * eta.deriv τ) (reverseTimeVolume (r₁-r₀)) := by
    simpa using hMassRaw
  have hMassCanonical : Integrable (fun τ => inner ℝ (valueCLM hΩ v)
      (valueCLM hΩ (U τ)) * eta.deriv τ) (reverseTimeVolume (r₁-r₀)) := by
    refine hMassRaw'.congr ?_
    filter_upwards [hUraw] with τ hτ
    rw [hτ]
  let massRaw  := ∫ τ, inner ℝ (valueCLM hΩ v) (valueCLM hΩ (raw τ)) *
    eta.deriv τ ∂reverseTimeVolume (r₁ - r₀)
  have hMassPair : reverseTimeDualPairingRightCLM hΩ _
      (reverseTimeSeparatedVTestOfMemLp hΩ eta.deriv (eta.memLp_deriv ∞) v)
      (reverseTimeGelfandCLM hΩ _ U) = massRaw := by
    calc
      _ = ∫ τ, inner ℝ _ _ * eta.deriv τ
        ∂reverseTimeVolume _ :=
        reverseTimeGelfand_pairing_multiplier_eq_integral hΩ U eta.deriv _ _
      _ = massRaw := by
        apply integral_eq_of_ae_of_integrable _
          _
          _
          hMassCanonical hMassRaw'
        filter_upwards [hUraw] with τ hτ
        rw [hτ]
  have hSourceRaw := integrable_reverseTimeNegativeSourceRaw_mul_test r₀ r₁ h₀₁ hΩ hΩbounded F
    hFSmooth eta v
  have hSourcePair := reverseTimeNegativeSource_pairing_eq_integral_raw r₀ r₁ h₀₁ hΩ hΩbounded F
    hFSmooth eta v
  have hFormPair := reverseTimeSpatialForm_pairing_eq_integral r₀ r₁ h₀₁ hΩ hΩbounded a b c
    haSmooth hbSmooth hcSmooth U eta v
  have hFormPairRaw : reverseTimeDualPairingRightCLM hΩ _
      (reverseTimeSeparatedVTest hΩ eta v)
      (reverseTimeSpatialFormBochnerAction r₀ r₁ h₀₁ hΩ hΩbounded a b c haSmooth hbSmooth hcSmooth
        U) =
      ∫ τ, reverseTimeSpatialForm hΩ r₁ τ a b c (raw τ) v * eta τ
        ∂reverseTimeVolume (r₁ - r₀) := by
    calc
      _ = ∫ τ, reverseTimeSpatialForm hΩ r₁ τ a b c _ _ * eta τ
        ∂reverseTimeVolume _ := hFormPair
      _ = _ := by
        apply integral_congr_ae
        filter_upwards [hUraw] with τ hτ
        rw [hτ]
  have hResidualRaw' : Integrable (fun τ =>
      (reverseTimeNegativeSourceRaw r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth τ v -
        reverseTimeSpatialForm hΩ r₁ τ a b c (raw τ) v) * eta τ)
          (reverseTimeVolume (r₁-r₀)) := by
    simpa using hResidualRaw
  have hDiffRaw : Integrable (fun τ =>
      reverseTimeNegativeSourceRaw r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth τ v *
        eta τ -
      reverseTimeSpatialForm hΩ r₁ τ a b c (raw τ) v * eta τ)
        (reverseTimeVolume (r₁-r₀)) := by
    refine hResidualRaw'.congr (Eventually.of_forall fun τ => ?_)
    exact sub_mul _ _ _
  have hRawIdentity' : massRaw = -∫ τ,
      (reverseTimeNegativeSourceRaw r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth τ v *
        eta τ -
      reverseTimeSpatialForm hΩ r₁ τ a b c (raw τ) v * eta τ)
        ∂reverseTimeVolume (r₁-r₀) := by
    have hRawIdentity0 : massRaw = -∫ τ,
        (reverseTimeNegativeSourceRaw r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth τ v -
        reverseTimeSpatialForm hΩ r₁ τ a b c (raw τ) v) * eta τ
          ∂reverseTimeVolume (r₁-r₀) := by
      simpa only [massRaw, raw] using hRawIdentity
    rw [hRawIdentity0]
    congr 1
    apply integral_eq_of_ae_of_integrable _ _ _ hResidualRaw' hDiffRaw
    filter_upwards with τ
    exact sub_mul _ _ _
  have hConcrete := raw_integral_transport _ _ _ _
    _
    _
    hSourceRaw hDiffRaw (hMassPair.trans hRawIdentity') hSourcePair hFormPairRaw
  have hU : U = reverseTimeGalerkinPrimal r₀ r₁ lam h₀₁ hlam hΩ hΩbounded a b c F
      haSmooth hbSmooth hcSmooth hFSmooth hLower hcNonpos N initial := rfl
  exact reverseTimeGalerkinPrimal_pairing_identity_prop_intro r₀ r₁ lam h₀₁ hlam hΩ hΩbounded a b
    c F
    haSmooth hbSmooth hcSmooth hFSmooth hLower hcNonpos N initial v eta U hU hConcrete

end HypoellipticAleksandrov.Parabolic.Dirichlet
