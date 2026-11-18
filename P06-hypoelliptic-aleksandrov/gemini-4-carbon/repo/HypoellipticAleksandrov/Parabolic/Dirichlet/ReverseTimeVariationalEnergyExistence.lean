module

public import HypoellipticAleksandrov.Parabolic.Dirichlet.ReverseTimeGalerkinPrimalBase
public import HypoellipticAleksandrov.Parabolic.Dirichlet.TimeHilbertTraces
public import HypoellipticAleksandrov.Parabolic.Dirichlet.TimeGelfandAffine
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
public import Mathlib.Topology.ContinuousMap.Interval
public import HypoellipticAleksandrov.Parabolic.Dirichlet.ReverseTimeGalerkinPrimalResidualDerivative
public import HypoellipticAleksandrov.Parabolic.Dirichlet.ReverseTimeGalerkinPrimalBochner
public import HypoellipticAleksandrov.Parabolic.Dirichlet.ReverseTimeGelfandPairing
public import HypoellipticAleksandrov.Parabolic.Dirichlet.ReverseTimeSeparatedMultiplier
public import HypoellipticAleksandrov.Parabolic.Dirichlet.VariationalEnergy

@[expose] public noncomputable section

namespace HypoellipticAleksandrov.Parabolic.Dirichlet
open MeasureTheory Set Filter Function Topology
open scoped ENNReal Matrix Matrix.Norms.Elementwise MatrixOrder RealInnerProductSpace





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
  have hEtaCont : ContinuousOn eta (Icc 0 T) := fun τ hτ =>
    (hEta τ hτ).continuousWithinAt
  have hderivInterval : IntervalIntegrable etaDeriv volume 0 T :=
    hDerivCont.intervalIntegrable_of_Icc hT.le
  have hinterval := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivWithinAt
    (a := 0)
    (by rw [uIcc_of_le hT.le]; exact hderivPairing)
    (by rw [uIcc_of_le hT.le]; exact hEta) ((intervalIntegrable_iff_integrableOn_Icc_of_le hT.le).mpr hresidual) hderivInterval
  have hintervalBoundary : (∫ τ in 0..T, pairing τ * etaDeriv τ) =
      -(∫ τ in 0..T, residual τ * eta τ) - pairing 0 * eta 0 := by
    calc
      (∫ τ in 0..T, pairing τ * etaDeriv τ) =
          pairing T * eta T - pairing 0 * eta 0 - ∫ τ in 0..T, residual τ * eta τ :=
        hinterval
      _ = -(∫ τ in 0..T, residual τ * eta τ) - pairing 0 * eta 0 := by
        rw [hEtaT]
        ring
  have hleftIcc : IntegrableOn (fun τ => pairing τ * etaDeriv τ) (Icc 0 T) volume :=
    (hpairing.mul hDerivCont).integrableOn_Icc
  obtain ⟨C, hC⟩ := ((isCompact_Icc.image_of_continuousOn hEtaCont).isBounded).exists_norm_le
  have hrightIcc : IntegrableOn (fun τ => residual τ * eta τ) (Icc 0 T) volume := by
    apply hresidual.mul_bdd (hEtaCont.aestronglyMeasurable measurableSet_Icc)
    filter_upwards [ae_restrict_mem measurableSet_Icc] with τ hτ
    exact hC (eta τ) ⟨τ, hτ, rfl⟩
  have hleft : Integrable (fun τ => pairing τ * etaDeriv τ) (reverseTimeVolume T) := by
    simpa only [reverseTimeVolume, reverseTimeOpenInterval, restrict_Ioo_eq_restrict_Icc,
      IntegrableOn]
      using hleftIcc
  have hright : Integrable (fun τ => residual τ * eta τ) (reverseTimeVolume T) := by
    simpa only [reverseTimeVolume, reverseTimeOpenInterval, restrict_Ioo_eq_restrict_Icc,
      IntegrableOn]
      using hrightIcc
  have hboundary : (∫ τ, pairing τ * etaDeriv τ ∂reverseTimeVolume T) =
      -(∫ τ, residual τ * eta τ ∂reverseTimeVolume T) - pairing 0 * eta 0 := by
    simpa only [reverseTimeVolume, reverseTimeOpenInterval, restrict_Ioo_eq_restrict_Icc,
      restrict_Ioc_eq_restrict_Icc, intervalIntegral.integral_of_le hT.le]
      using hintervalBoundary
  exact ⟨hleft, hright, hboundary⟩

/-- The selected finite reverse-time Galerkin raw curve obeys the terminal-zero
boundary-time identity, including its initial projected datum. -/
theorem reverseTimeGalerkinPrimal_boundaryTime
    {d : ℕ} {Ω : Set (PDE.Vec d)}
    (r₀ r₁ lam : ℝ) (h₀₁ : r₀ < r₁) (hlam : 0 < lam)
    (hΩ : IsOpen Ω) (hΩbounded : Bornology.IsBounded Ω)
    (a : CoefficientField d)
    (b : ℝ → PDE.Vec d → PDE.Vec d) (c F : ℝ → PDE.Vec d → ℝ)
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
    (N : ℕ) (initial : PDE.ScalarLp Ω (2 : ℝ≥0∞))
    (v : galerkinSpace hΩ N)
    (eta etaDeriv : ℝ → ℝ)
    (hEta : ∀ tau ∈ Set.Icc 0 (r₁ - r₀),
      HasDerivWithinAt eta (etaDeriv tau) (Set.Icc 0 (r₁ - r₀)) tau)
    (hDerivCont : ContinuousOn etaDeriv (Set.Icc 0 (r₁ - r₀)))
    (hEtaT : eta (r₁ - r₀) = 0) :
    MeasureTheory.Integrable
      (fun tau =>
        inner ℝ (valueCLM hΩ (v : H10HilbertGraph hΩ))
          (valueCLM hΩ
            (reverseTimeGalerkinPrimalRaw r₀ r₁ lam h₀₁ hlam hΩ hΩbounded a b c F
              haSmooth hbSmooth hcSmooth hFSmooth hLower hcNonpos N initial tau)) *
          etaDeriv tau)
      (reverseTimeVolume (r₁ - r₀)) ∧
    MeasureTheory.Integrable
      (fun tau =>
        (reverseTimeNegativeSourceRaw r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth tau
            (v : H10HilbertGraph hΩ) -
          reverseTimeSpatialForm hΩ r₁ tau a b c
            (reverseTimeGalerkinPrimalRaw r₀ r₁ lam h₀₁ hlam hΩ hΩbounded a b c F
              haSmooth hbSmooth hcSmooth hFSmooth hLower hcNonpos N initial tau)
            (v : H10HilbertGraph hΩ)) * eta tau)
      (reverseTimeVolume (r₁ - r₀)) ∧
    (∫ tau,
      inner ℝ (valueCLM hΩ (v : H10HilbertGraph hΩ))
        (valueCLM hΩ
          (reverseTimeGalerkinPrimalRaw r₀ r₁ lam h₀₁ hlam hΩ hΩbounded a b c F
            haSmooth hbSmooth hcSmooth hFSmooth hLower hcNonpos N initial tau)) *
        etaDeriv tau ∂reverseTimeVolume (r₁ - r₀)) =
      -(∫ tau,
        (reverseTimeNegativeSourceRaw r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth tau
            (v : H10HilbertGraph hΩ) -
          reverseTimeSpatialForm hΩ r₁ tau a b c
            (reverseTimeGalerkinPrimalRaw r₀ r₁ lam h₀₁ hlam hΩ hΩbounded a b c F
              haSmooth hbSmooth hcSmooth hFSmooth hLower hcNonpos N initial tau)
            (v : H10HilbertGraph hΩ)) * eta tau
        ∂reverseTimeVolume (r₁ - r₀)) -
      inner ℝ (valueCLM hΩ (v : H10HilbertGraph hΩ))
        (valueCLM hΩ (galerkinInitialProjection hΩ N initial :
          H10HilbertGraph hΩ)) * eta 0    := by
  have continuousOn_boundary_reconstruct {Ω : Set (PDE.Vec d)} (hΩ : IsOpen Ω) (N : ℕ) (x : ℝ → Fin (Module.finrank ℝ (galerkinSpace hΩ N)) → ℝ) (s : Set ℝ) (hx : ContinuousOn x s) :
      ContinuousOn
      (fun t => (galerkinReconstruct hΩ N (x t) : H10HilbertGraph hΩ)) s := by
    let R :=
      (galerkinSpace hΩ N).subtypeL.comp
        (LinearMap.toContinuousLinearMap (galerkinReconstruct hΩ N))
    have hR : ContinuousOn (fun t => R (x t)) s :=
      R.continuous.continuousOn.comp hx fun _ _ => Set.mem_univ _
    simpa [R, ContinuousLinearMap.coe_coe, Submodule.subtypeL_apply, LinearMap.coe_toContinuousLinearMap'] using hR
  have continuousOn_boundary_pairing {Ω : Set (PDE.Vec d)} (hΩ : IsOpen Ω) (N : ℕ) (x : ℝ → Fin (Module.finrank ℝ (galerkinSpace hΩ N)) → ℝ) (v : galerkinSpace hΩ N) (s : Set ℝ) (hx : ContinuousOn x s) :
      ContinuousOn
      (fun t =>
        inner ℝ (valueCLM hΩ (v : H10HilbertGraph hΩ))
          (valueCLM hΩ
            (galerkinReconstruct hΩ N (x t) : H10HilbertGraph hΩ))) s := by
    let R :=
      (galerkinSpace hΩ N).subtypeL.comp
        (LinearMap.toContinuousLinearMap (galerkinReconstruct hΩ N))
    let V :=
      (valueCLM hΩ).comp R
    let I :=
      innerSL ℝ (valueCLM hΩ (v : H10HilbertGraph hΩ))
    have hV :=
      V.continuous.continuousOn.comp hx fun _ _ => Set.mem_univ _
    simpa [I, V, R, ContinuousLinearMap.coe_coe, Submodule.subtypeL_apply, innerSL_apply_apply, Function.comp_def, LinearMap.coe_toContinuousLinearMap'] using
      I.continuous.continuousOn.comp hV fun _ _ => Set.mem_univ _
  have hasDerivWithinAt_boundary_pairing {Ω : Set (PDE.Vec d)} (hΩ : IsOpen Ω) (N : ℕ) (x : ℝ → Fin (Module.finrank ℝ (galerkinSpace hΩ N)) → ℝ) (xdot : Fin (Module.finrank ℝ (galerkinSpace hΩ N)) → ℝ) (v : galerkinSpace hΩ N) {s : Set ℝ} {τ : ℝ} (hx : HasDerivWithinAt x xdot s τ) :
      HasDerivWithinAt
      (fun t =>
        inner ℝ (valueCLM hΩ (v : H10HilbertGraph hΩ))
          (valueCLM hΩ
            (galerkinReconstruct hΩ N (x t) : H10HilbertGraph hΩ)))
      (inner ℝ (valueCLM hΩ (v : H10HilbertGraph hΩ))
        (valueCLM hΩ
          (galerkinReconstruct hΩ N xdot : H10HilbertGraph hΩ))) s τ := by
    let R :=
      (galerkinSpace hΩ N).subtypeL.comp
        (LinearMap.toContinuousLinearMap (galerkinReconstruct hΩ N))
    let V :=
      (valueCLM hΩ).comp R
    let I :=
      innerSL ℝ (valueCLM hΩ (v : H10HilbertGraph hΩ))
    have hI := (I.hasFDerivAt).comp_hasDerivWithinAt τ ((V.hasFDerivAt).comp_hasDerivWithinAt τ hx)
    simpa [I, V, R, ContinuousLinearMap.coe_coe, Submodule.subtypeL_apply, innerSL_apply_apply, Function.comp_def, LinearMap.coe_toContinuousLinearMap'] using hI
  let curveSpec := (((exists_reverseTimeGalerkin_uniform_energy_solution r₀ r₁ lam h₀₁ hlam hΩ hΩbounded a b c F haSmooth hbSmooth hcSmooth hFSmooth hLower hcNonpos).choose_spec.2).choose_spec.2 N initial).choose_spec
  have hspec := curveSpec.choose_spec
  let x := reverseTimeGalerkinPrimalCoordinate r₀ r₁ lam h₀₁ hlam hΩ hΩbounded
    a b c F haSmooth hbSmooth hcSmooth hFSmooth hLower hcNonpos N initial
  let T : ℝ := r₁ - r₀
  have hT := sub_nonneg.mpr h₀₁.le
  let A : ℝ → (Fin (Module.finrank ℝ (galerkinSpace hΩ N)) → ℝ) →L[ℝ]
      (Fin (Module.finrank ℝ (galerkinSpace hΩ N)) → ℝ) := fun τ =>
    reverseTimeGalerkinLinearPart r₀ r₁ h₀₁ hΩ hΩbounded a b c
      haSmooth hbSmooth hcSmooth N (Set.projIcc 0 T hT τ)
  let f : ℝ → Fin (Module.finrank ℝ (galerkinSpace hΩ N)) → ℝ := fun τ =>
    reverseTimeGalerkinForcing r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth N
      (Set.projIcc 0 T hT τ)
  let xdot : ℝ → Fin (Module.finrank ℝ (galerkinSpace hΩ N)) → ℝ := fun τ =>
    A τ (x τ) + f τ
  have hx : ContinuousOn x (Icc 0 T) := by
    simpa only [x, T, reverseTimeGalerkinPrimalCoordinate] using hspec.2.2.1
  have hxdot : ContinuousOn xdot (Icc 0 T) := by
    have hA : Continuous A :=
      (continuous_reverseTimeGalerkinLinearPart r₀ r₁ h₀₁ hΩ hΩbounded a b c
        haSmooth hbSmooth hcSmooth N).comp continuous_projIcc
    have hf : Continuous f :=
      (continuous_reverseTimeGalerkinForcing r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth N).comp
        continuous_projIcc
    exact (hA.continuousOn.clm_apply hx).add hf.continuousOn
  have hderiv : ∀ τ ∈ Icc 0 T,
      HasDerivWithinAt x (xdot τ) (Icc 0 T) τ := by
    intro τ hτ
    let τ' : Icc 0 (r₁ - r₀) := ⟨τ, by simpa using hτ⟩
    have hproj := Set.projIcc_of_mem hT hτ
    simpa only [x, xdot, A, f, T, hproj, reverseTimeGalerkinPrimalCoordinate] using
      (hspec.2.2.2.2.1 τ').1
  have hrows : ∀ τ : Icc 0 T,
      ∀ i : Fin (Module.finrank ℝ (galerkinSpace hΩ N)),
        inner ℝ
            (valueCLM hΩ (galerkinReconstruct hΩ N (xdot τ.1) :
              H10HilbertGraph hΩ))
            (valueCLM hΩ (galerkinSpaceBasis hΩ N i : H10HilbertGraph hΩ)) +
          reverseTimeSpatialForm hΩ r₁ τ.1 a b c
            (galerkinReconstruct hΩ N (x τ.1) : H10HilbertGraph hΩ)
            (galerkinSpaceBasis hΩ N i : H10HilbertGraph hΩ) =
          reverseTimeGalerkinSource r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth N
            ⟨τ.1, by simpa using τ.2⟩ i := by
    intro τ i
    let τ' : Icc 0 (r₁ - r₀) := ⟨τ.1, by simpa only [T] using τ.2⟩
    simpa only [x, xdot, A, f, T, (Set.projIcc_of_mem hT τ.2), reverseTimeGalerkinPrimalCoordinate, hspec.2.1] using
      (hspec.2.2.2.2.1 τ').2 i
  let pairing : ℝ → ℝ := fun τ =>
    inner ℝ (valueCLM hΩ (v : H10HilbertGraph hΩ))
      (valueCLM hΩ (galerkinReconstruct hΩ N (x τ) : H10HilbertGraph hΩ))
  let residual : ℝ → ℝ := fun τ =>
    reverseTimeNegativeSourceRaw r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth τ
      (v : H10HilbertGraph hΩ) -
    reverseTimeSpatialForm hΩ r₁ τ a b c
      (galerkinReconstruct hΩ N (x τ) : H10HilbertGraph hΩ)
      (v : H10HilbertGraph hΩ)
  let clampedResidual : ℝ → ℝ := fun τ =>
    reverseTimeNegativeSourceRaw r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth τ
      (v : H10HilbertGraph hΩ) -
    reverseTimeSpatialFormOperatorClamp r₀ r₁ h₀₁ hΩ hΩbounded a b c
      haSmooth hbSmooth hcSmooth τ
      (galerkinReconstruct hΩ N (x τ) : H10HilbertGraph hΩ)
      (v : H10HilbertGraph hΩ)
  have hTpos : 0 < T := by dsimp only [T]; linarith
  have hpairing : ContinuousOn pairing (Icc 0 T) := by
    simpa only [pairing] using continuousOn_boundary_pairing hΩ N x v (Icc 0 T) hx
  have hsource : Continuous
      (fun τ => reverseTimeNegativeSourceRaw r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth τ
        (v : H10HilbertGraph hΩ)) :=
    (continuous_reverseTimeNegativeSourceRaw r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth).clm_apply
      continuous_const
  have hclampedForm : ContinuousOn
      (fun τ => reverseTimeSpatialFormOperatorClamp r₀ r₁ h₀₁ hΩ hΩbounded a b c
        haSmooth hbSmooth hcSmooth τ
        (galerkinReconstruct hΩ N (x τ) : H10HilbertGraph hΩ)
        (v : H10HilbertGraph hΩ)) (Icc 0 T) :=
    ((continuous_reverseTimeSpatialFormOperatorClamp r₀ r₁ h₀₁ hΩ hΩbounded a b c
      haSmooth hbSmooth hcSmooth).continuousOn.clm_apply (continuousOn_boundary_reconstruct hΩ N x (Icc 0 T) hx)).clm_apply
      continuous_const.continuousOn
  have hclampedResidual : ContinuousOn clampedResidual (Icc 0 T) := by
    simpa only [clampedResidual, Pi.sub_def] using hsource.continuousOn.sub hclampedForm
  have hformAE : ∀ᵐ τ ∂volume.restrict (Icc 0 T),
      reverseTimeSpatialFormOperatorClamp r₀ r₁ h₀₁ hΩ hΩbounded a b c
        haSmooth hbSmooth hcSmooth τ
        (galerkinReconstruct hΩ N (x τ) : H10HilbertGraph hΩ)
        (v : H10HilbertGraph hΩ) =
      reverseTimeSpatialForm hΩ r₁ τ a b c
        (galerkinReconstruct hΩ N (x τ) : H10HilbertGraph hΩ)
        (v : H10HilbertGraph hΩ) := by
    have hformAEall : ∀ᵐ τ ∂volume.restrict (Icc 0 T), ∀ u v : H10HilbertGraph hΩ,
        reverseTimeSpatialFormOperatorClamp r₀ r₁ h₀₁ hΩ hΩbounded a b c
          haSmooth hbSmooth hcSmooth τ u v =
        reverseTimeSpatialForm hΩ r₁ τ a b c u v := by
      simpa only [T, reverseTimeVolume, reverseTimeOpenInterval, restrict_Ioo_eq_restrict_Icc]
        using ae_reverseTimeSpatialFormOperatorClamp_apply r₀ r₁ h₀₁ hΩ hΩbounded a b c
          haSmooth hbSmooth hcSmooth
    filter_upwards [hformAEall] with τ hτ
    exact hτ _ _
  have hresidualIcc : IntegrableOn residual (Icc 0 T) volume := by
    apply Integrable.congr hclampedResidual.integrableOn_Icc
    filter_upwards [hformAE] with τ hτ
    dsimp only [residual, clampedResidual]
    exact congrArg
      (fun z => reverseTimeNegativeSourceRaw r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth τ
        (v : H10HilbertGraph hΩ) - z) hτ
  have hderivPairing : ∀ τ ∈ Icc 0 T,
      HasDerivWithinAt pairing (residual τ) (Icc 0 T) τ := by
    intro τ hτ
    let τT : Icc 0 T := ⟨τ, hτ⟩
    let τ' : Icc 0 (r₁ - r₀) := ⟨τ, by simpa only [T] using hτ⟩
    have hrow := reverseTimeGalerkin_basisRows_forall r₀ r₁ h₀₁ hΩ hΩbounded a b c F
      haSmooth hbSmooth hcSmooth hFSmooth N τ' (x τ) (xdot τ) (hrows τT) v
    have hrate :
        inner ℝ (valueCLM hΩ (v : H10HilbertGraph hΩ))
          (valueCLM hΩ (galerkinReconstruct hΩ N (xdot τ) : H10HilbertGraph hΩ)) =
        residual τ := by
      rw [real_inner_comm]
      dsimp only [residual]
      linarith
    rw [← hrate]
    simpa only [pairing] using (hasDerivWithinAt_boundary_pairing hΩ N x (xdot τ) v (hderiv τ hτ))
  have hscalar := boundaryTime_scalar_identity T hTpos pairing residual eta etaDeriv hpairing
    hresidualIcc hderivPairing (by simpa only [T] using hEta)
    (by simpa only [T] using hDerivCont) (by simpa only [T] using hEtaT)
  have hpairingZero : pairing 0 =
      inner ℝ (valueCLM hΩ (v : H10HilbertGraph hΩ))
        (valueCLM hΩ (galerkinInitialProjection hΩ N initial : H10HilbertGraph hΩ)) := by
    simpa only [pairing, reverseTimeGalerkinPrimalRaw, x] using congrArg
      (fun w =>
        inner ℝ (valueCLM hΩ (v : H10HilbertGraph hΩ)) (valueCLM hΩ w))
      (reverseTimeGalerkinPrimalRaw_zero r₀ r₁ lam h₀₁ hlam hΩ hΩbounded a b c F
        haSmooth hbSmooth hcSmooth hFSmooth hLower hcNonpos N initial)
  rw [hpairingZero] at hscalar
  simpa only [reverseTimeGalerkinPrimalRaw, x, pairing, residual, T] using hscalar



private theorem intervalPrimitive_boundary_pairing
    {T : ℝ} (_hT : 0 < T) {f eta etaDeriv : ℝ → ℝ}
    (hf : IntegrableOn f (Set.Icc 0 T) volume)
    (hEta : ∀ tau ∈ Set.Icc 0 T,
      HasDerivWithinAt eta (etaDeriv tau) (Set.Icc 0 T) tau)
    (hEtaDerivCont : ContinuousOn etaDeriv (Set.Icc 0 T))
    (hEtaT : eta T = 0) :
    (∫ tau, PDE.intervalPrimitive 0 f tau * etaDeriv tau
      ∂reverseTimeVolume T) =
      -(∫ tau, f tau * eta tau ∂reverseTimeVolume T) := by
  have hEtaCont : ContinuousOn eta (Icc 0 T) := HasDerivWithinAt.continuousOn hEta
  have hleft :
      (∫ tau, PDE.intervalPrimitive 0 f tau * etaDeriv tau
        ∂reverseTimeVolume T) =
        ∫ tau in Icc 0 T, PDE.intervalPrimitive 0 f tau * etaDeriv tau := by
    simp only [reverseTimeVolume, reverseTimeOpenInterval,
      restrict_Ioo_eq_restrict_Icc]
  have hright :
      (∫ tau, f tau * eta tau ∂reverseTimeVolume T) =
        ∫ tau in Icc 0 T, f tau * eta tau := by
    simp only [reverseTimeVolume, reverseTimeOpenInterval,
      restrict_Ioo_eq_restrict_Icc]
  rw [hleft, hright]
  calc
    (∫ tau in Icc 0 T, PDE.intervalPrimitive 0 f tau * etaDeriv tau) =
        ∫ tau in Icc 0 T, ∫ s in Icc 0 tau, f s * etaDeriv tau := by
          apply setIntegral_congr_fun measurableSet_Icc
          intro tau htau
          change PDE.intervalPrimitive 0 f tau * etaDeriv tau = _
          rw [PDE.intervalPrimitive_eq_setIntegral_Icc htau.1, ← integral_mul_const]
    _ = ∫ s in Icc 0 T, ∫ tau in Icc s T, f s * etaDeriv tau :=
      PDE.setIntegral_setIntegral_Icc_swap hf hEtaDerivCont
    _ = ∫ s in Icc 0 T, -(f s * eta s) := by
      apply setIntegral_congr_fun measurableSet_Icc
      intro s hs
      change (∫ tau in Icc s T, f s * etaDeriv tau) = -(f s * eta s)
      rw [integral_const_mul]
      have hFTC : ∫ tau in s..T, etaDeriv tau = eta T - eta s := by
        exact intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le hs.2
          (hEtaCont.mono (Icc_subset_Icc hs.1 le_rfl)) (fun tau ht =>
            (hEta tau ⟨le_trans hs.1 ht.1.le, ht.2.le⟩).hasDerivAt
              (Icc_mem_nhds (lt_of_le_of_lt hs.1 ht.1) ht.2)
              |>.hasDerivWithinAt)
          ((hEtaDerivCont.mono (Icc_subset_Icc hs.1 le_rfl)).intervalIntegrable_of_Icc hs.2)
      rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hs.2,
        hFTC, hEtaT]
      ring
    _ = -(∫ s in Icc 0 T, f s * eta s) := by rw [integral_neg]


private theorem reverseTimeVolume_affine_constant_integral
    {T a : ℝ} (hT : 0 < T) :
    (∫ _ : ℝ, a * (-(T⁻¹)) ∂reverseTimeVolume T) = -a := by
  have hMeasure : (reverseTimeVolume T).real univ = T := by
    change (volume.restrict (Ioo 0 T)).real univ = T
    rw [MeasureTheory.measureReal_restrict_apply_univ,
      Real.volume_real_Ioo_of_le hT.le]
    norm_num
  calc
    (∫ _ : ℝ, a * (-(T⁻¹)) ∂reverseTimeVolume T) =
        ∫ _ : ℝ, a * (-(T⁻¹)) ∂reverseTimeVolume T := rfl
    _ = (reverseTimeVolume T).real univ * (a * (-(T⁻¹))) :=
      MeasureTheory.integral_const (a * (-(T⁻¹)))
    _ = -a := by
      rw [hMeasure]
      field_simp [hT.ne']





/-- Pairing the canonical continuous Hilbert representative with the affine
terminal-zero cutoff recovers the reverse-time source pairing and the canonical
initial trace. -/
theorem reverseTimeHilbertRepresentative_affine_initial_pairing
    {d : ℕ} {Ω : Set (PDE.Vec d)}
    (hΩ : IsOpen Ω) (T : ℝ) (hT : 0 < T)
    (u : ReverseTimeL2V hΩ T) (g : ReverseTimeL2VStar hΩ T)
    (hderiv : HasGelfandWeakTimeDerivative hΩ T hT u g)
    (v : H10HilbertGraph hΩ) :
    (∫ tau,
      inner ℝ (valueCLM hΩ v)
        (Set.IccExtend hT.le
          (reverseTimeHilbertRepresentative hΩ T hT u g hderiv) tau) *
          (-(T⁻¹))
        ∂reverseTimeVolume T) =
      -(∫ tau, (g tau) v * (1 - tau / T) ∂reverseTimeVolume T) -
        inner ℝ (valueCLM hΩ v)
          (reverseTimeInitialTrace hΩ T hT u g hderiv)     := by
  have reverseTimeHilbertRepresentative_affine_pairing_eqOn {Ω : Set (PDE.Vec d)} (hΩ : IsOpen Ω) (T : ℝ) (hT : 0 < T) (u : ReverseTimeL2V hΩ T) (g : ReverseTimeL2VStar hΩ T) (hderiv : HasGelfandWeakTimeDerivative hΩ T hT u g) (v : H10HilbertGraph hΩ) :
      EqOn
      (fun tau => inner ℝ (valueCLM hΩ v)
        (Set.IccExtend hT.le
          (reverseTimeHilbertRepresentative hΩ T hT u g hderiv) tau))
      (fun tau => reverseTimeVStarPrimitive hΩ T g tau v +
        reverseTimeGelfandAffineConstant hΩ T hT u g v)
      (Icc 0 T) := by
    let Ubar := reverseTimeHilbertRepresentative hΩ T hT u g hderiv
    let Uext : ℝ → PDE.ScalarLp Ω 2 := Set.IccExtend hT.le Ubar
    let P := reverseTimeVStarPrimitive hΩ T g
    let c := reverseTimeGelfandAffineConstant hΩ T hT u g
    have hUAE : ∀ᵐ tau ∂volume.restrict (Icc 0 T),
        ∀ ht : tau ∈ Ioo 0 T,
          Ubar ⟨tau, ⟨le_of_lt ht.1, le_of_lt ht.2⟩⟩ = valueCLM hΩ (u tau) := by
      simpa only [Ubar, ReverseTimeHilbertRepresentativeAgrees, reverseTimeVolume,
        reverseTimeOpenInterval, restrict_Ioo_eq_restrict_Icc] using
        (reverseTimeHilbertRepresentative_spec hΩ T hT u g hderiv).1
    have hGelfandAE : ∀ᵐ tau ∂volume.restrict (Icc 0 T),
        reverseTimeGelfandCLM hΩ T u tau =
          scalarLpToH10HilbertGraphDual hΩ (valueCLM hΩ (u tau)) := by
      have h := coeFn_reverseTimeGelfandCLM hΩ T u
      simp only [reverseTimeVolume, reverseTimeOpenInterval,
        restrict_Ioo_eq_restrict_Icc] at h
      filter_upwards [h] with tau ht
      exact ht
    have hAffineAE : ∀ᵐ tau ∂volume.restrict (Icc 0 T),
        reverseTimeGelfandCLM hΩ T u tau = P tau + c := by
      have h := reverseTimeGelfandCLM_ae_eq_reverseTimeVStarPrimitive_add_affineConstant
        hΩ T hT u g hderiv
      simp only [reverseTimeVolume, reverseTimeOpenInterval,
        restrict_Ioo_eq_restrict_Icc] at h
      filter_upwards [h] with tau ht
      exact ht
    have hIoo : ∀ᵐ tau ∂volume.restrict (Icc 0 T), tau ∈ Ioo 0 T := by
      rw [← restrict_Ioo_eq_restrict_Icc]
      exact ae_restrict_mem measurableSet_Ioo
    have hPairAE : (fun tau => inner ℝ (valueCLM hΩ v) (Uext tau)) =ᵐ[
        volume.restrict (Icc 0 T)] fun tau => P tau v + c v := by
      filter_upwards [hIoo, hUAE, hGelfandAE, hAffineAE]
        with tau ht hU hG hA
      have htIcc : tau ∈ Icc 0 T := ⟨le_of_lt ht.1, le_of_lt ht.2⟩
      calc
        inner ℝ (valueCLM hΩ v) (Uext tau) =
            inner ℝ (valueCLM hΩ v) (Ubar ⟨tau, htIcc⟩) := by
              change inner ℝ (valueCLM hΩ v) (Set.IccExtend hT.le Ubar tau) = _
              rw [Set.IccExtend_of_mem hT.le Ubar htIcc]
        _ = inner ℝ (valueCLM hΩ v) (valueCLM hΩ (u tau)) := by rw [hU ht]
        _ = scalarLpToH10HilbertGraphDual hΩ (valueCLM hΩ (u tau)) v := by
              rw [scalarLpToH10HilbertGraphDual_apply]
        _ = reverseTimeGelfandCLM hΩ T u tau v := by
              exact congrArg (fun ell => ell v) hG.symm
        _ = (P tau + c) v := congrArg (fun ell => ell v) hA
        _ = P tau v + c v := by rw [ContinuousLinearMap.add_apply]
    have hUCont : ContinuousOn (fun tau => inner ℝ (valueCLM hΩ v) (Uext tau)) (Icc 0 T) := by
      exact (innerSL ℝ (valueCLM hΩ v)).continuous.comp_continuousOn
        Ubar.continuous.Icc_extend'.continuousOn
    have hPCont : ContinuousOn (fun tau => P tau v + c v) (Icc 0 T) := by
      exact ((ContinuousLinearMap.apply ℝ ℝ v).continuous.comp_continuousOn
        (continuousOn_reverseTimeVStarPrimitive hΩ T g)).add continuousOn_const
    have hPairEqOn : EqOn (fun tau => inner ℝ (valueCLM hΩ v) (Uext tau))
        (fun tau => P tau v + c v) (Icc 0 T) :=
      Measure.eqOn_Icc_of_ae_eq volume hT.ne hPairAE hUCont hPCont
    exact hPairEqOn
  have reverseTimeGelfandAffineConstant_apply_eq_initial_trace {Ω : Set (PDE.Vec d)} (hΩ : IsOpen Ω) (T : ℝ) (hT : 0 < T) (u : ReverseTimeL2V hΩ T) (g : ReverseTimeL2VStar hΩ T) (hderiv : HasGelfandWeakTimeDerivative hΩ T hT u g) (v : H10HilbertGraph hΩ) :
      reverseTimeGelfandAffineConstant hΩ T hT u g v = inner ℝ (valueCLM hΩ v)
      (reverseTimeInitialTrace hΩ T hT u g hderiv) := by
    have hPairEqOn := reverseTimeHilbertRepresentative_affine_pairing_eqOn
      hΩ T hT u g hderiv v
    have hzero := hPairEqOn (left_mem_Icc.mpr hT.le)
    change inner ℝ (valueCLM hΩ v)
      (Set.IccExtend hT.le (reverseTimeHilbertRepresentative hΩ T hT u g hderiv) 0) =
        reverseTimeVStarPrimitive hΩ T g 0 v +
          reverseTimeGelfandAffineConstant hΩ T hT u g v at hzero
    rw [Set.IccExtend_left, reverseTimeVStarPrimitive_zero, ContinuousLinearMap.zero_apply,
      zero_add] at hzero
    change reverseTimeGelfandAffineConstant hΩ T hT u g v =
      inner ℝ (valueCLM hΩ v)
        (reverseTimeHilbertRepresentative hΩ T hT u g hderiv
          ⟨0, ⟨le_rfl, hT.le⟩⟩)
    exact hzero.symm
  have reverseTimeVStarPrimitive_affine_initial_source_pairing {Ω : Set (PDE.Vec d)} (hΩ : IsOpen Ω) (T : ℝ) (hT : 0 < T) (g : ReverseTimeL2VStar hΩ T) (v : H10HilbertGraph hΩ) :
      (∫ tau, reverseTimeVStarPrimitive hΩ T g tau v * (-(T⁻¹))
      ∂reverseTimeVolume T) =
      -(∫ tau, (g tau) v * (1 - tau / T) ∂reverseTimeVolume T) := by
    have reverseTimeVStarPrimitive_apply_eq_intervalPrimitive_on_Ioo {Ω : Set (PDE.Vec d)} (hΩ : IsOpen Ω) (T : ℝ) (g : ReverseTimeL2VStar hΩ T) (v : H10HilbertGraph hΩ) {tau : ℝ} (ht : tau ∈ Ioo 0 T) :
        reverseTimeVStarPrimitive hΩ T g tau v =
        PDE.intervalPrimitive 0 (fun s => (g s) v) tau := by
      rw [reverseTimeVStarPrimitive_apply hΩ T g v tau]
      change (∫ s in Ioc 0 tau, (g s) v ∂reverseTimeVolume T) = _
      rw [show (∫ s in Ioc 0 tau, (g s) v ∂reverseTimeVolume T) =
          ∫ s in Ioc 0 tau, (g s) v ∂volume by
            simp only [reverseTimeVolume, reverseTimeOpenInterval,
              Measure.restrict_restrict measurableSet_Ioc]
            rw [inter_eq_left.mpr]
            intro s hs
            exact ⟨hs.1, lt_of_le_of_lt hs.2 ht.2⟩]
      exact (intervalIntegral.integral_of_le (le_of_lt ht.1)).symm
    have hgIcc : IntegrableOn (fun tau => (g tau) v) (Icc 0 T) volume := by
      letI : IsFiniteMeasure (reverseTimeVolume T) := by
        change IsFiniteMeasure (volume.restrict (Ioo 0 T))
        infer_instance
      change Integrable (fun tau => (g tau) v) (volume.restrict (Icc 0 T))
      simpa only [reverseTimeVolume, reverseTimeOpenInterval,
        restrict_Ioo_eq_restrict_Icc, ContinuousLinearMap.apply_apply] using
        ((MeasureTheory.Lp.memLp g).continuousLinearMap_comp
          (ContinuousLinearMap.apply ℝ ℝ v)).integrable (by norm_num)
    have hAffineDeriv : ∀ tau ∈ Icc 0 T,
        HasDerivWithinAt (fun tau => 1 - tau / T) (-(T⁻¹)) (Icc 0 T) tau := by
      intro tau _
      simpa [div_eq_mul_inv, Pi.sub_def] using
        (hasDerivAt_const (x := tau) 1).sub
          ((hasDerivAt_id (x := tau)).mul_const T⁻¹) |>.hasDerivWithinAt
    have hAffineTerminal : 1 - T / T = 0 := by
      rw [div_self hT.ne']
      ring
    have hPrimitiveAE :
        (fun tau => reverseTimeVStarPrimitive hΩ T g tau v * (-(T⁻¹))) =ᵐ[
          reverseTimeVolume T] fun tau =>
            PDE.intervalPrimitive 0 (fun s => (g s) v) tau * (-(T⁻¹)) := by
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with tau ht
      exact congrArg (fun z => z * (-(T⁻¹)))
        (reverseTimeVStarPrimitive_apply_eq_intervalPrimitive_on_Ioo hΩ T g v ht)
    calc
      (∫ tau, reverseTimeVStarPrimitive hΩ T g tau v * (-(T⁻¹))
        ∂reverseTimeVolume T) =
          ∫ tau, PDE.intervalPrimitive 0 (fun s => (g s) v) tau * (-(T⁻¹))
            ∂reverseTimeVolume T := integral_congr_ae hPrimitiveAE
      _ = -(∫ tau, (g tau) v * (1 - tau / T) ∂reverseTimeVolume T) := (intervalPrimitive_boundary_pairing hT hgIcc hAffineDeriv continuousOn_const hAffineTerminal)
  have reverseTimeHilbertRepresentative_affine_pairing_integral {Ω : Set (PDE.Vec d)} (hΩ : IsOpen Ω) (T : ℝ) (hT : 0 < T) (u : ReverseTimeL2V hΩ T) (g : ReverseTimeL2VStar hΩ T) (hderiv : HasGelfandWeakTimeDerivative hΩ T hT u g) (v : H10HilbertGraph hΩ) :
      (∫ tau, inner ℝ (valueCLM hΩ v)
      (Set.IccExtend hT.le
        (reverseTimeHilbertRepresentative hΩ T hT u g hderiv) tau) * (-(T⁻¹))
      ∂reverseTimeVolume T) =
      ∫ tau, (reverseTimeVStarPrimitive hΩ T g tau v +
        reverseTimeGelfandAffineConstant hΩ T hT u g v) * (-(T⁻¹))
        ∂reverseTimeVolume T := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with tau ht
    exact congrArg (fun z => z * (-(T⁻¹)))
      ((reverseTimeHilbertRepresentative_affine_pairing_eqOn hΩ T hT u g hderiv v) ⟨le_of_lt ht.1, le_of_lt ht.2⟩)
  have hConstant :
      (∫ tau, reverseTimeGelfandAffineConstant hΩ T hT u g v * (-(T⁻¹))
        ∂reverseTimeVolume T) =
        -(reverseTimeGelfandAffineConstant hΩ T hT u g v) := by
    exact reverseTimeVolume_affine_constant_integral
      (a := reverseTimeGelfandAffineConstant hΩ T hT u g v) hT
  rw [(reverseTimeHilbertRepresentative_affine_pairing_integral hΩ T hT u g hderiv v)]
  calc
    (∫ tau, (reverseTimeVStarPrimitive hΩ T g tau v +
      reverseTimeGelfandAffineConstant hΩ T hT u g v) * (-(T⁻¹))
      ∂reverseTimeVolume T) =
        (∫ tau, reverseTimeVStarPrimitive hΩ T g tau v * (-(T⁻¹))
          ∂reverseTimeVolume T) +
          ∫ tau, reverseTimeGelfandAffineConstant hΩ T hT u g v * (-(T⁻¹))
            ∂reverseTimeVolume T := by
              rw [← integral_add]
              · apply integral_congr_ae
                filter_upwards with tau
                ring
              · exact (integrable_reverseTimeVStarPrimitive_apply hΩ T g v).mul_const _
              · letI : IsFiniteMeasure (reverseTimeVolume T) := by
                  change IsFiniteMeasure (volume.restrict (Ioo 0 T))
                  infer_instance
                exact integrable_const _
    _ = -(∫ tau, (g tau) v * (1 - tau / T) ∂reverseTimeVolume T) -
        reverseTimeGelfandAffineConstant hΩ T hT u g v := by
          rw [(reverseTimeVStarPrimitive_affine_initial_source_pairing hΩ T hT g v), hConstant]
          ring
    _ = -(∫ tau, (g tau) v * (1 - tau / T) ∂reverseTimeVolume T) -
        inner ℝ (valueCLM hΩ v)
          (reverseTimeInitialTrace hΩ T hT u g hderiv) := by rw [(reverseTimeGelfandAffineConstant_apply_eq_initial_trace hΩ T hT u g hderiv v)]

section
open Filter MeasureTheory Set Topology
open scoped ENNReal Matrix Matrix.Norms.Elementwise MatrixOrder RealInnerProductSpace

private def affineReverseTimeMultiplier (T : ℝ) : ℝ → ℝ := fun tau => 1 - tau / T

private def affineReverseTimeDerivative (T : ℝ) : ℝ → ℝ := fun _tau => -(T⁻¹)

private theorem memLp_affine_reverseTime_multiplier {T : ℝ} (hT : 0 < T) :
    MemLp (affineReverseTimeMultiplier T) (∞ : ℝ≥0∞) (reverseTimeVolume T) := by
  letI : IsFiniteMeasure (reverseTimeVolume T) := by
    change IsFiniteMeasure (volume.restrict (Ioo 0 T))
    infer_instance
  apply memLp_of_bounded (a := 0) (b := 1) ?_ ?_ _
  · filter_upwards [ae_restrict_mem measurableSet_Ioo] with tau ht
    change 1 - tau / T ∈ Icc 0 1
    have hquotient_nonneg : 0 ≤ tau / T := le_of_lt (div_pos ht.1 hT)
    have hquotient_le_one : tau / T ≤ 1 := (div_le_one₀ hT).2 ht.2.le
    constructor <;> linarith
  · exact (continuous_const.sub (continuous_id.div_const T)).aestronglyMeasurable

private theorem memLp_affine_reverseTime_deriv {T : ℝ} (_hT : 0 < T) :
    MemLp (affineReverseTimeDerivative T) (∞ : ℝ≥0∞) (reverseTimeVolume T) := by
  letI : IsFiniteMeasure (reverseTimeVolume T) := by
    change IsFiniteMeasure (volume.restrict (Ioo 0 T))
    infer_instance
  exact memLp_const _

private noncomputable def affineReverseTimeVTest
    {d : ℕ} {Ω : Set (PDE.Vec d)} (hΩ : IsOpen Ω) (T : ℝ)
    (hT : 0 < T) (v : H10HilbertGraph hΩ) : ReverseTimeL2V hΩ T :=
  reverseTimeSeparatedVTestOfMemLp hΩ (affineReverseTimeMultiplier T)
    (memLp_affine_reverseTime_multiplier hT) v

private noncomputable def affineReverseTimeDerivativeVTest
    {d : ℕ} {Ω : Set (PDE.Vec d)} (hΩ : IsOpen Ω) (T : ℝ)
    (hT : 0 < T) (v : H10HilbertGraph hΩ) : ReverseTimeL2V hΩ T :=
  reverseTimeSeparatedVTestOfMemLp hΩ (affineReverseTimeDerivative T)
    (memLp_affine_reverseTime_deriv hT) v

private theorem reverseTimeDualPairingRightCLM_ofMemLp_eq_integral
    {d : ℕ} {Ω : Set (PDE.Vec d)} {T : ℝ}
    (hΩ : IsOpen Ω) (g : ReverseTimeL2VStar hΩ T)
    (q : ℝ → ℝ) (hq : MemLp q (∞ : ℝ≥0∞) (reverseTimeVolume T))
    (v : H10HilbertGraph hΩ) :
    reverseTimeDualPairingRightCLM hΩ T
        (reverseTimeSeparatedVTestOfMemLp hΩ q hq v) g =
      ∫ tau, (g tau) v * q tau ∂reverseTimeVolume T := by
  calc
    reverseTimeDualPairingRightCLM hΩ T
        (reverseTimeSeparatedVTestOfMemLp hΩ q hq v) g =
        reverseTimeDualPairingCLM hΩ T g
          (reverseTimeSeparatedVTestOfMemLp hΩ q hq v) :=
      reverseTimeDualPairingRightCLM_apply hΩ T _ g
    _ = ∫ tau, g tau (reverseTimeSeparatedVTestOfMemLp hΩ q hq v tau)
        ∂reverseTimeVolume T := reverseTimeDualPairingCLM_apply hΩ T g _
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [ae_reverseTimeSeparatedVTestOfMemLp hΩ q hq v] with tau hz
      rw [hz, ContinuousLinearMap.map_smul]
      exact mul_comm _ _






private noncomputable def affineReverseTimeMassPairing
    {d : ℕ} {Ω : Set (PDE.Vec d)}
    (hΩ : IsOpen Ω) (T : ℝ) (hT : 0 < T)
    (u : ReverseTimeL2V hΩ T) (v : H10HilbertGraph hΩ) : ℝ :=
  reverseTimeDualPairingRightCLM hΩ T
    (affineReverseTimeDerivativeVTest hΩ T hT v)
    (reverseTimeGelfandCLM hΩ T u)

private noncomputable def affineReverseTimeSourcePairing
    {d : ℕ} {Ω : Set (PDE.Vec d)}
    (hΩ : IsOpen Ω) (T : ℝ) (hT : 0 < T)
    (S : ReverseTimeL2VStar hΩ T) (v : H10HilbertGraph hΩ) : ℝ :=
  reverseTimeDualPairingRightCLM hΩ T
    (affineReverseTimeVTest hΩ T hT v) S

private noncomputable def affineReverseTimeFormPairing
    {d : ℕ} {Ω : Set (PDE.Vec d)}
    (hΩ : IsOpen Ω) (T : ℝ) (hT : 0 < T)
    (A : ReverseTimeL2V hΩ T →L[ℝ] ReverseTimeL2VStar hΩ T)
    (u : ReverseTimeL2V hΩ T) (v : H10HilbertGraph hΩ) : ℝ :=
  reverseTimeDualPairingRightCLM hΩ T
    (affineReverseTimeVTest hΩ T hT v) (A u)

private noncomputable def affineReverseTimeInitialPairing
    {d : ℕ} {Ω : Set (PDE.Vec d)}
    (hΩ : IsOpen Ω) (v : H10HilbertGraph hΩ)
    (initial : PDE.ScalarLp Ω (2 : ℝ≥0∞)) : ℝ :=
  inner ℝ (valueCLM hΩ v) initial


private theorem neg_add_sub_of_pairing_eq
    (source sourceRaw form formRaw initial : ℝ)
    (hSource : source = sourceRaw) (hForm : form = formRaw) :
    -sourceRaw + formRaw - initial = -source + form - initial := by
  rw [← hSource, ← hForm]

private theorem reverseTimeDualPairingRightCLM_sub
    {d : ℕ} {Ω : Set (PDE.Vec d)}
    (hΩ : IsOpen Ω) (T : ℝ) (z : ReverseTimeL2V hΩ T)
    (f g : ReverseTimeL2VStar hΩ T) :
    reverseTimeDualPairingRightCLM hΩ T z (f - g) =
      reverseTimeDualPairingRightCLM hΩ T z f -
        reverseTimeDualPairingRightCLM hΩ T z g :=
  (reverseTimeDualPairingRightCLM hΩ T z).map_sub f g




private theorem finite_affine_boundary_pairing_wrapped
    {d : ℕ} {Ω : Set (PDE.Vec d)}
    (r₀ r₁ lam : ℝ) (h₀₁ : r₀ < r₁) (hlam : 0 < lam)
    (hΩ : IsOpen Ω) (hΩbounded : Bornology.IsBounded Ω)
    (a : CoefficientField d)
    (b : ℝ → PDE.Vec d → PDE.Vec d) (c F : ℝ → PDE.Vec d → ℝ)
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
      z ∈ scalarParabolicClosedCylinder r₀ r₁ Ω → lam • (1 : PDE.Mat d) ≤ a z.1 z.2)
    (hcNonpos : ∀ z : TimeVelocity d,
      z ∈ scalarParabolicClosedCylinder r₀ r₁ Ω → c z.1 z.2 ≤ 0)
    (initial : PDE.ScalarLp Ω (2 : ℝ≥0∞)) (N k : ℕ) (hNk : k + 1 ≤ N) :
    affineReverseTimeMassPairing hΩ (r₁ - r₀) (sub_pos.mpr h₀₁)
        (reverseTimeGalerkinPrimal r₀ r₁ lam h₀₁ hlam hΩ hΩbounded a b c F
          haSmooth hbSmooth hcSmooth hFSmooth hLower hcNonpos N initial)
        (galerkinVector hΩ k) =
      -affineReverseTimeSourcePairing hΩ (r₁ - r₀) (sub_pos.mpr h₀₁)
          (reverseTimeNegativeSource r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth)
          (galerkinVector hΩ k) +
        affineReverseTimeFormPairing hΩ (r₁ - r₀) (sub_pos.mpr h₀₁)
          (reverseTimeSpatialFormBochnerAction r₀ r₁ h₀₁ hΩ hΩbounded a b c
            haSmooth hbSmooth hcSmooth)
          (reverseTimeGalerkinPrimal r₀ r₁ lam h₀₁ hlam hΩ hΩbounded a b c F
            haSmooth hbSmooth hcSmooth hFSmooth hLower hcNonpos N initial)
          (galerkinVector hΩ k) -
        affineReverseTimeInitialPairing hΩ (galerkinVector hΩ k) initial      := by
  have inner_value_galerkinInitialProjection_eq {Ω : Set (PDE.Vec d)} (hΩ : IsOpen Ω) {M : ℕ} {N : ℕ} (hMN : M ≤ N) (initial : PDE.ScalarLp Ω 2) (v : galerkinSpace hΩ M) :
      inner ℝ (valueCLM hΩ (v : H10HilbertGraph hΩ))
      (valueCLM hΩ (galerkinInitialProjection hΩ N initial :
        H10HilbertGraph hΩ)) =
      inner ℝ (valueCLM hΩ (v : H10HilbertGraph hΩ)) initial := by
    let K := galerkinValueSpace hΩ N
    have hvN : (v : H10HilbertGraph hΩ) ∈ galerkinSpace hΩ N :=
      galerkinSpace_mono hΩ hMN v.property
    let u : K := ⟨valueCLM hΩ (v : H10HilbertGraph hΩ), ⟨v, hvN, rfl⟩⟩
    rw [value_galerkinInitialProjection]
    change inner ℝ (u : PDE.ScalarLp Ω 2) (K.orthogonalProjection initial) =
      inner ℝ (u : PDE.ScalarLp Ω 2) initial
    exact Submodule.inner_orthogonalProjection_eq_of_mem_left u initial
  have integrable_form_raw_mul_multiplier {d : ℕ} {Ω : Set (PDE.Vec d)} (r₀ r₁ : ℝ) (h₀₁ : r₀ < r₁) (hΩ : IsOpen Ω) (hΩbounded : Bornology.IsBounded Ω) (a : CoefficientField d) (b : ℝ → PDE.Vec d → PDE.Vec d) (c : ℝ → PDE.Vec d → ℝ) (haSmooth : IsSmoothOnNeighborhood
      (fun z => a z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω)) (hbSmooth : IsSmoothOnNeighborhood
      (fun z => b z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω)) (hcSmooth : IsSmoothOnNeighborhood
      (fun z => c z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω)) (u : ReverseTimeL2V hΩ (r₁ - r₀)) (q : ℝ → ℝ) (hq : MemLp q (∞ : ℝ≥0∞) (reverseTimeVolume (r₁ - r₀))) (v : H10HilbertGraph hΩ) :
      Integrable (fun tau => reverseTimeSpatialForm hΩ r₁ tau a b c (u tau) v * q tau)
      (reverseTimeVolume (r₁ - r₀)) := by
    let A := reverseTimeSpatialFormBochnerAction r₀ r₁ h₀₁ hΩ hΩbounded a b c
      haSmooth hbSmooth hcSmooth u
    let z := reverseTimeSeparatedVTestOfMemLp hΩ q hq v
    refine (integrable_reverseTimeDualPairing hΩ (r₁ - r₀) z A).congr ?_
    filter_upwards [ae_reverseTimeSpatialFormBochnerAction_apply r₀ r₁ h₀₁ hΩ hΩbounded
      a b c haSmooth hbSmooth hcSmooth u, ae_reverseTimeSeparatedVTestOfMemLp hΩ q hq v]
      with tau hA hz
    rw [hz, ContinuousLinearMap.map_smul]
    change q tau * A tau v = _
    rw [hA v]
    ring
  have integrable_source_raw_mul_multiplier {d : ℕ} {Ω : Set (PDE.Vec d)} (r₀ r₁ : ℝ) (h₀₁ : r₀ < r₁) (hΩ : IsOpen Ω) (hΩbounded : Bornology.IsBounded Ω) (F : ℝ → PDE.Vec d → ℝ) (hFSmooth : IsSmoothOnNeighborhood
      (fun z => F z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω)) (q : ℝ → ℝ) (hq : MemLp q (∞ : ℝ≥0∞) (reverseTimeVolume (r₁ - r₀))) (v : H10HilbertGraph hΩ) :
      Integrable (fun tau =>
      reverseTimeNegativeSourceRaw r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth tau v * q tau)
      (reverseTimeVolume (r₁ - r₀)) := by
    let S := reverseTimeNegativeSource r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth
    let z := reverseTimeSeparatedVTestOfMemLp hΩ q hq v
    refine (integrable_reverseTimeDualPairing hΩ (r₁ - r₀) z S).congr ?_
    filter_upwards [(memLp_reverseTimeNegativeSourceRaw r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth).coeFn_toLp,
      ae_reverseTimeSeparatedVTestOfMemLp hΩ q hq v] with tau hS hz
    rw [hz, ContinuousLinearMap.map_smul]
    change q tau *
        ((memLp_reverseTimeNegativeSourceRaw r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth).toLp
          (reverseTimeNegativeSourceRaw r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth) tau) v = _
    rw [hS]
    ring
  have reverseTimeSpatialForm_pairing_ofMemLp_eq_integral {d : ℕ} {Ω : Set (PDE.Vec d)} (r₀ r₁ : ℝ) (h₀₁ : r₀ < r₁) (hΩ : IsOpen Ω) (hΩbounded : Bornology.IsBounded Ω) (a : CoefficientField d) (b : ℝ → PDE.Vec d → PDE.Vec d) (c : ℝ → PDE.Vec d → ℝ) (haSmooth : IsSmoothOnNeighborhood
      (fun z => a z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω)) (hbSmooth : IsSmoothOnNeighborhood
      (fun z => b z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω)) (hcSmooth : IsSmoothOnNeighborhood
      (fun z => c z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω)) (u : ReverseTimeL2V hΩ (r₁ - r₀)) (q : ℝ → ℝ) (hq : MemLp q (∞ : ℝ≥0∞) (reverseTimeVolume (r₁ - r₀))) (v : H10HilbertGraph hΩ) :
      reverseTimeDualPairingRightCLM hΩ (r₁ - r₀)
        (reverseTimeSeparatedVTestOfMemLp hΩ q hq v)
        (reverseTimeSpatialFormBochnerAction r₀ r₁ h₀₁ hΩ hΩbounded a b c
          haSmooth hbSmooth hcSmooth u) =
      ∫ tau, reverseTimeSpatialForm hΩ r₁ tau a b c (u tau) v * q tau
        ∂reverseTimeVolume (r₁ - r₀) := by
    let A := reverseTimeSpatialFormBochnerAction r₀ r₁ h₀₁ hΩ hΩbounded a b c
      haSmooth hbSmooth hcSmooth u
    calc
      reverseTimeDualPairingRightCLM hΩ (r₁ - r₀)
          (reverseTimeSeparatedVTestOfMemLp hΩ q hq v) A =
          ∫ tau, A tau v * q tau ∂reverseTimeVolume (r₁ - r₀) :=
        reverseTimeDualPairingRightCLM_ofMemLp_eq_integral hΩ A q hq v
      _ = _ := by
        apply integral_congr_ae
        filter_upwards [ae_reverseTimeSpatialFormBochnerAction_apply r₀ r₁ h₀₁ hΩ hΩbounded
          a b c haSmooth hbSmooth hcSmooth u] with tau hA
        exact congrArg (fun s => s * q tau) (hA v)
  have reverseTimeNegativeSource_pairing_ofMemLp_eq_integral_raw {d : ℕ} {Ω : Set (PDE.Vec d)} (r₀ r₁ : ℝ) (h₀₁ : r₀ < r₁) (hΩ : IsOpen Ω) (hΩbounded : Bornology.IsBounded Ω) (F : ℝ → PDE.Vec d → ℝ) (hFSmooth : IsSmoothOnNeighborhood
      (fun z => F z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω)) (q : ℝ → ℝ) (hq : MemLp q (∞ : ℝ≥0∞) (reverseTimeVolume (r₁ - r₀))) (v : H10HilbertGraph hΩ) :
      reverseTimeDualPairingRightCLM hΩ (r₁ - r₀)
        (reverseTimeSeparatedVTestOfMemLp hΩ q hq v)
        (reverseTimeNegativeSource r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth) =
      ∫ tau, reverseTimeNegativeSourceRaw r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth tau v * q tau
        ∂reverseTimeVolume (r₁ - r₀) := by
    let S := reverseTimeNegativeSource r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth
    calc
      reverseTimeDualPairingRightCLM hΩ (r₁ - r₀)
          (reverseTimeSeparatedVTestOfMemLp hΩ q hq v) S =
          ∫ tau, S tau v * q tau ∂reverseTimeVolume (r₁ - r₀) :=
        reverseTimeDualPairingRightCLM_ofMemLp_eq_integral hΩ S q hq v
      _ = _ := by
        apply integral_congr_ae
        filter_upwards [
          (memLp_reverseTimeNegativeSourceRaw r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth).coeFn_toLp]
          with tau hS
        simpa only [S, reverseTimeNegativeSource] using
          congrArg (fun s => s v * q tau) hS
  let T := r₁ - r₀
  let eta := affineReverseTimeMultiplier T
  let etaDeriv := affineReverseTimeDerivative T
  let hEta := memLp_affine_reverseTime_multiplier (sub_pos.mpr h₀₁)
  let hEtaDeriv := memLp_affine_reverseTime_deriv (sub_pos.mpr h₀₁)
  let S := reverseTimeNegativeSource r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth
  let A := reverseTimeSpatialFormBochnerAction r₀ r₁ h₀₁ hΩ hΩbounded a b c
    haSmooth hbSmooth hcSmooth
  let v : galerkinSpace hΩ N := ⟨galerkinVector hΩ k,
    galerkinSpace_mono hΩ hNk (by
      change galerkinVector hΩ k ∈ Submodule.span ℝ
        (Set.range fun i : Fin (k + 1) => galerkinVector hΩ i)
      apply Submodule.subset_span
      exact ⟨⟨k, Nat.lt_succ_self k⟩, rfl⟩)⟩
  let vk : galerkinSpace hΩ (k + 1) := ⟨galerkinVector hΩ k, by
    change galerkinVector hΩ k ∈ Submodule.span ℝ
      (Set.range fun i : Fin (k + 1) => galerkinVector hΩ i)
    apply Submodule.subset_span
    exact ⟨⟨k, Nat.lt_succ_self k⟩, rfl⟩⟩
  let UN := reverseTimeGalerkinPrimal r₀ r₁ lam h₀₁ hlam hΩ hΩbounded a b c F
    haSmooth hbSmooth hcSmooth hFSmooth hLower hcNonpos N initial
  change affineReverseTimeMassPairing hΩ T (sub_pos.mpr h₀₁) UN (galerkinVector hΩ k) =
    -affineReverseTimeSourcePairing hΩ T (sub_pos.mpr h₀₁) S (galerkinVector hΩ k) +
      affineReverseTimeFormPairing hΩ T (sub_pos.mpr h₀₁) A UN (galerkinVector hΩ k) -
      affineReverseTimeInitialPairing hΩ (galerkinVector hΩ k) initial
  have hT : 0 < T := by
    simpa only [T] using sub_pos.mpr h₀₁
  have hEtaDerivWithin : ∀ tau ∈ Icc 0 T,
      HasDerivWithinAt eta (etaDeriv tau) (Icc 0 T) tau := by
    intro tau _
    dsimp only [eta, etaDeriv]
    unfold affineReverseTimeMultiplier affineReverseTimeDerivative
    simpa [div_eq_mul_inv, Pi.sub_def] using
      (hasDerivAt_const (x := tau) 1).sub
        ((hasDerivAt_id (x := tau)).mul_const T⁻¹) |>.hasDerivWithinAt
  have hEtaTerminal : eta T = 0 := by
    dsimp only [eta, affineReverseTimeMultiplier]
    rw [div_self hT.ne']
    ring
  obtain ⟨_hMass, _hResidual, hBoundary⟩ :=
    reverseTimeGalerkinPrimal_boundaryTime r₀ r₁ lam h₀₁ hlam hΩ hΩbounded a b c F
      haSmooth hbSmooth hcSmooth hFSmooth hLower hcNonpos N initial v eta etaDeriv
      (by simpa only [T] using hEtaDerivWithin) continuousOn_const
      (by simpa only [T] using hEtaTerminal)
  have hUNraw := ae_reverseTimeGalerkinPrimal_eq_raw r₀ r₁ lam h₀₁ hlam hΩ hΩbounded a b c F
    haSmooth hbSmooth hcSmooth hFSmooth hLower hcNonpos N initial
  have hMass : reverseTimeDualPairingRightCLM hΩ T
      (reverseTimeSeparatedVTestOfMemLp hΩ etaDeriv hEtaDeriv (galerkinVector hΩ k))
      (reverseTimeGelfandCLM hΩ T UN) =
      ∫ tau, inner ℝ (valueCLM hΩ (galerkinVector hΩ k))
        (valueCLM hΩ
          (reverseTimeGalerkinPrimalRaw r₀ r₁ lam h₀₁ hlam hΩ hΩbounded a b c F
            haSmooth hbSmooth hcSmooth hFSmooth hLower hcNonpos N initial tau)) * etaDeriv tau
        ∂reverseTimeVolume T := by
    calc
      _ = ∫ tau, inner ℝ (valueCLM hΩ (galerkinVector hΩ k)) (valueCLM hΩ (UN tau)) *
          etaDeriv tau ∂reverseTimeVolume T :=
        reverseTimeGelfand_pairing_multiplier_eq_integral hΩ UN etaDeriv hEtaDeriv
          (galerkinVector hΩ k)
      _ = _ := by
        apply integral_congr_ae
        filter_upwards [hUNraw] with tau hUNtau
        rw [hUNtau]
  have hSource' :
      affineReverseTimeSourcePairing hΩ T (sub_pos.mpr h₀₁) S (galerkinVector hΩ k) =
        ∫ tau, reverseTimeNegativeSourceRaw r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth tau
          (galerkinVector hΩ k) * eta tau ∂reverseTimeVolume T := by
    change reverseTimeDualPairingRightCLM hΩ T
        (affineReverseTimeVTest hΩ T (sub_pos.mpr h₀₁) (galerkinVector hΩ k)) S = _
    simpa only [T, eta, hEta, affineReverseTimeVTest] using (reverseTimeNegativeSource_pairing_ofMemLp_eq_integral_raw r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth eta hEta (galerkinVector hΩ k))
  have hForm' :
      affineReverseTimeFormPairing hΩ T (sub_pos.mpr h₀₁) A UN (galerkinVector hΩ k) =
        ∫ tau, reverseTimeSpatialForm hΩ r₁ tau a b c (UN tau) (galerkinVector hΩ k) * eta tau
          ∂reverseTimeVolume T := by
    change reverseTimeDualPairingRightCLM hΩ T
        (affineReverseTimeVTest hΩ T (sub_pos.mpr h₀₁) (galerkinVector hΩ k)) (A UN) = _
    simpa only [T, eta, hEta, affineReverseTimeVTest] using (reverseTimeSpatialForm_pairing_ofMemLp_eq_integral r₀ r₁ h₀₁ hΩ hΩbounded a b c haSmooth hbSmooth hcSmooth UN eta hEta (galerkinVector hΩ k))
  have hInitial' :
      inner ℝ (valueCLM hΩ (galerkinVector hΩ k))
        (valueCLM hΩ (galerkinInitialProjection hΩ N initial : H10HilbertGraph hΩ)) =
      inner ℝ (valueCLM hΩ (galerkinVector hΩ k)) initial := by
    simpa only [vk] using (inner_value_galerkinInitialProjection_eq hΩ hNk initial vk)
  have hRaw :
      (∫ tau, inner ℝ (valueCLM hΩ (galerkinVector hΩ k))
        (valueCLM hΩ
          (reverseTimeGalerkinPrimalRaw r₀ r₁ lam h₀₁ hlam hΩ hΩbounded a b c F
            haSmooth hbSmooth hcSmooth hFSmooth hLower hcNonpos N initial tau)) * etaDeriv tau
        ∂reverseTimeVolume T) =
      -(∫ tau, reverseTimeNegativeSourceRaw r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth tau
          (galerkinVector hΩ k) * eta tau ∂reverseTimeVolume T) +
        ∫ tau, reverseTimeSpatialForm hΩ r₁ tau a b c (UN tau) (galerkinVector hΩ k) * eta tau
          ∂reverseTimeVolume T - inner ℝ (valueCLM hΩ (galerkinVector hΩ k)) initial := by
    calc
      _ = -(∫ tau,
          (reverseTimeNegativeSourceRaw r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth tau
            (galerkinVector hΩ k) -
          reverseTimeSpatialForm hΩ r₁ tau a b c
            (reverseTimeGalerkinPrimalRaw r₀ r₁ lam h₀₁ hlam hΩ hΩbounded a b c F
              haSmooth hbSmooth hcSmooth hFSmooth hLower hcNonpos N initial tau)
            (galerkinVector hΩ k)) * eta tau ∂reverseTimeVolume T) -
          inner ℝ (valueCLM hΩ (galerkinVector hΩ k))
            (valueCLM hΩ (galerkinInitialProjection hΩ N initial : H10HilbertGraph hΩ)) *
              eta 0 := by
          simpa only [T, v, UN] using hBoundary
      _ = -(∫ tau, reverseTimeNegativeSourceRaw r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth tau
          (galerkinVector hΩ k) * eta tau -
          reverseTimeSpatialForm hΩ r₁ tau a b c (UN tau) (galerkinVector hΩ k) * eta tau
            ∂reverseTimeVolume T) -
          inner ℝ (valueCLM hΩ (galerkinVector hΩ k))
            (valueCLM hΩ (galerkinInitialProjection hΩ N initial : H10HilbertGraph hΩ)) *
              eta 0 := by
          congr 2
          apply integral_congr_ae
          filter_upwards [hUNraw] with tau hUNtau
          rw [hUNtau]
          ring
      _ = -(∫ tau, reverseTimeNegativeSourceRaw r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth tau
          (galerkinVector hΩ k) * eta tau ∂reverseTimeVolume T -
          ∫ tau, reverseTimeSpatialForm hΩ r₁ tau a b c (UN tau) (galerkinVector hΩ k) * eta tau
            ∂reverseTimeVolume T) -
          inner ℝ (valueCLM hΩ (galerkinVector hΩ k)) initial := by
          rw [integral_sub (integrable_source_raw_mul_multiplier r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth eta hEta (galerkinVector hΩ k)) (integrable_form_raw_mul_multiplier r₀ r₁ h₀₁ hΩ hΩbounded a b c haSmooth hbSmooth hcSmooth UN eta hEta (galerkinVector hΩ k))]
          rw [hInitial']
          dsimp only [eta, affineReverseTimeMultiplier]
          ring
      _ = _ := by ring
  calc
    affineReverseTimeMassPairing hΩ T (sub_pos.mpr h₀₁) UN (galerkinVector hΩ k) =
        ∫ tau, inner ℝ (valueCLM hΩ (galerkinVector hΩ k))
          (valueCLM hΩ
            (reverseTimeGalerkinPrimalRaw r₀ r₁ lam h₀₁ hlam hΩ hΩbounded a b c F
              haSmooth hbSmooth hcSmooth hFSmooth hLower hcNonpos N initial tau)) * etaDeriv tau
          ∂reverseTimeVolume T := by
        simpa only [affineReverseTimeMassPairing, affineReverseTimeDerivativeVTest, T, etaDeriv,
          hEtaDeriv, UN] using hMass
    _ = -(∫ tau, reverseTimeNegativeSourceRaw r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth tau
          (galerkinVector hΩ k) * eta tau ∂reverseTimeVolume T) +
        ∫ tau, reverseTimeSpatialForm hΩ r₁ tau a b c (UN tau) (galerkinVector hΩ k) * eta tau
          ∂reverseTimeVolume T - inner ℝ (valueCLM hΩ (galerkinVector hΩ k)) initial := hRaw
    _ = -affineReverseTimeSourcePairing hΩ T (sub_pos.mpr h₀₁) S (galerkinVector hΩ k) +
        affineReverseTimeFormPairing hΩ T (sub_pos.mpr h₀₁) A UN (galerkinVector hΩ k) -
        affineReverseTimeInitialPairing hΩ (galerkinVector hΩ k) initial := by
        exact neg_add_sub_of_pairing_eq _ _ _ _ _ hSource' hForm'


variable {d : ℕ} {Ω : Set (PDE.Vec d)}
variable
  (r₀ r₁ lam : ℝ) (h₀₁ : r₀ < r₁) (hlam : 0 < lam)
  (hΩ : IsOpen Ω) (hΩbounded : Bornology.IsBounded Ω)
  (a : CoefficientField d)
  (b : ℝ → PDE.Vec d → PDE.Vec d) (c F : ℝ → PDE.Vec d → ℝ)
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
    z ∈ scalarParabolicClosedCylinder r₀ r₁ Ω → lam • (1 : PDE.Mat d) ≤ a z.1 z.2)
  (hcNonpos : ∀ z : TimeVelocity d,
    z ∈ scalarParabolicClosedCylinder r₀ r₁ Ω → c z.1 z.2 ≤ 0)

include lam hlam hLower hcNonpos

private theorem reverseTimeGalerkinPrimal_initialTrace_pairing
    (initial : PDE.ScalarLp Ω (2 : ℝ≥0∞))
    (U : ReverseTimeL2V hΩ (r₁ - r₀))
    (phi : ℕ → ℕ) (hphi : StrictMono phi)
    (hclm : ∀ ell : ReverseTimeL2V hΩ (r₁ - r₀) →L[ℝ] ℝ,
      Tendsto (fun n => ell
        (reverseTimeGalerkinPrimal r₀ r₁ lam h₀₁ hlam hΩ hΩbounded a b c F
          haSmooth hbSmooth hcSmooth hFSmooth hLower hcNonpos (phi n) initial))
        atTop (𝓝 (ell U)))
    (hdu : HasGelfandWeakTimeDerivative hΩ (r₁ - r₀) (sub_pos.mpr h₀₁) U
      (reverseTimeFormResidual r₀ r₁ h₀₁ hΩ hΩbounded a b c
        haSmooth hbSmooth hcSmooth F hFSmooth U))
    (k : ℕ) :
    inner ℝ (valueCLM hΩ (galerkinVector hΩ k))
      (reverseTimeInitialTrace hΩ (r₁ - r₀) (sub_pos.mpr h₀₁) U
        (reverseTimeFormResidual r₀ r₁ h₀₁ hΩ hΩbounded a b c
          haSmooth hbSmooth hcSmooth F hFSmooth U) hdu) =
      inner ℝ (valueCLM hΩ (galerkinVector hΩ k)) initial    := by
  let affineReverseTimeResidualPairing {d : ℕ} {Ω : Set (PDE.Vec d)} (hΩ : IsOpen Ω) (T : ℝ) (hT : 0 < T) (g : ReverseTimeL2VStar hΩ T) (v : H10HilbertGraph hΩ) :=
    reverseTimeDualPairingRightCLM hΩ T (affineReverseTimeVTest hΩ T hT v) g
  have reverseTimeHilbertRepresentative_affine_initial_pairing_wrapped {d : ℕ} {Ω : Set (PDE.Vec d)} (hΩ : IsOpen Ω) (T : ℝ) (hT : 0 < T) (u : ReverseTimeL2V hΩ T) (g : ReverseTimeL2VStar hΩ T) (hdu : HasGelfandWeakTimeDerivative hΩ T hT u g) (v : H10HilbertGraph hΩ) :
      (∫ tau, inner ℝ (valueCLM hΩ v)
        (Set.IccExtend hT.le (reverseTimeHilbertRepresentative hΩ T hT u g hdu) tau) *
          affineReverseTimeDerivative T tau ∂reverseTimeVolume T) =
      -affineReverseTimeResidualPairing hΩ T hT g v -
        affineReverseTimeInitialPairing hΩ v
          (reverseTimeInitialTrace hΩ T hT u g hdu) := by
    have hBoundary := reverseTimeHilbertRepresentative_affine_initial_pairing hΩ T hT u g hdu v
    calc
      _ = -(∫ tau, g tau v * affineReverseTimeMultiplier T tau ∂reverseTimeVolume T) -
            inner ℝ (valueCLM hΩ v) (reverseTimeInitialTrace hΩ T hT u g hdu) := by
            simpa only [affineReverseTimeMultiplier, affineReverseTimeDerivative] using hBoundary
      _ = -reverseTimeDualPairingRightCLM hΩ T
            (reverseTimeSeparatedVTestOfMemLp hΩ (affineReverseTimeMultiplier T)
              (memLp_affine_reverseTime_multiplier hT) v) g -
            inner ℝ (valueCLM hΩ v) (reverseTimeInitialTrace hΩ T hT u g hdu) := by
            rw [← (reverseTimeDualPairingRightCLM_ofMemLp_eq_integral hΩ g (affineReverseTimeMultiplier T) (memLp_affine_reverseTime_multiplier hT) v)]
      _ = _ := rfl
  have canonical_affine_mass_eq_gelfand_mass {d : ℕ} {Ω : Set (PDE.Vec d)} (hΩ : IsOpen Ω) (T : ℝ) (hT : 0 < T) (u : ReverseTimeL2V hΩ T) (g : ReverseTimeL2VStar hΩ T) (hdu : HasGelfandWeakTimeDerivative hΩ T hT u g) (v : H10HilbertGraph hΩ) (qDeriv : ℝ → ℝ) (hqDeriv : MemLp qDeriv (∞ : ℝ≥0∞) (reverseTimeVolume T)) :
      (∫ tau, inner ℝ (valueCLM hΩ v)
      (Set.IccExtend hT.le (reverseTimeHilbertRepresentative hΩ T hT u g hdu) tau) * qDeriv tau
      ∂reverseTimeVolume T) =
      reverseTimeDualPairingRightCLM hΩ T
        (reverseTimeSeparatedVTestOfMemLp hΩ qDeriv hqDeriv v)
        (reverseTimeGelfandCLM hΩ T u) := by
    have hcanonical :
        (fun tau => inner ℝ (valueCLM hΩ v)
          (Set.IccExtend hT.le (reverseTimeHilbertRepresentative hΩ T hT u g hdu) tau) *
            qDeriv tau) =ᵐ[
            reverseTimeVolume T]
          fun tau => inner ℝ (valueCLM hΩ v) (valueCLM hΩ (u tau)) * qDeriv tau := by
      filter_upwards [((reverseTimeHilbertRepresentative_spec hΩ T hT u g hdu).1), ae_restrict_mem measurableSet_Ioo] with tau hrepTau ht
      have htIcc : tau ∈ Icc 0 T := ⟨le_of_lt ht.1, le_of_lt ht.2⟩
      rw [Set.IccExtend_of_mem hT.le _ htIcc, hrepTau ht]
    calc
      (∫ tau, inner ℝ (valueCLM hΩ v)
        (Set.IccExtend hT.le (reverseTimeHilbertRepresentative hΩ T hT u g hdu) tau) * qDeriv tau
        ∂reverseTimeVolume T) =
          ∫ tau, inner ℝ (valueCLM hΩ v) (valueCLM hΩ (u tau)) * qDeriv tau
            ∂reverseTimeVolume T := integral_congr_ae hcanonical
      _ = _ := (reverseTimeGelfand_pairing_multiplier_eq_integral hΩ u qDeriv hqDeriv v).symm
  let T := r₁ - r₀
  let eta := affineReverseTimeMultiplier T
  let etaDeriv := affineReverseTimeDerivative T
  let hEta := memLp_affine_reverseTime_multiplier (sub_pos.mpr h₀₁)
  let hEtaDeriv := memLp_affine_reverseTime_deriv (sub_pos.mpr h₀₁)
  let S := reverseTimeNegativeSource r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth
  let A := reverseTimeSpatialFormBochnerAction r₀ r₁ h₀₁ hΩ hΩbounded a b c
    haSmooth hbSmooth hcSmooth
  let g := reverseTimeFormResidual r₀ r₁ h₀₁ hΩ hΩbounded a b c
    haSmooth hbSmooth hcSmooth F hFSmooth U
  let trace := reverseTimeInitialTrace hΩ T (sub_pos.mpr h₀₁) U g hdu
  change inner ℝ (valueCLM hΩ (galerkinVector hΩ k)) trace =
    inner ℝ (valueCLM hΩ (galerkinVector hΩ k)) initial
  let massEll : ReverseTimeL2V hΩ T →L[ℝ] ℝ :=
    (reverseTimeDualPairingRightCLM hΩ T
      (reverseTimeSeparatedVTestOfMemLp hΩ etaDeriv hEtaDeriv (galerkinVector hΩ k))).comp
      (reverseTimeGelfandCLM hΩ T)
  let formEll : ReverseTimeL2V hΩ T →L[ℝ] ℝ :=
    (reverseTimeDualPairingRightCLM hΩ T
      (reverseTimeSeparatedVTestOfMemLp hΩ eta hEta (galerkinVector hΩ k))).comp A
  let source : ℝ := reverseTimeDualPairingRightCLM hΩ T
    (reverseTimeSeparatedVTestOfMemLp hΩ eta hEta (galerkinVector hΩ k)) S
  have hIndex : ∀ᶠ n in atTop, k + 1 ≤ phi n := by
    filter_upwards [eventually_ge_atTop (k + 1)] with n hn
    exact hn.trans (hphi.id_le n)
  have hFinite :
      (fun n => massEll
        (reverseTimeGalerkinPrimal r₀ r₁ lam h₀₁ hlam hΩ hΩbounded a b c F
          haSmooth hbSmooth hcSmooth hFSmooth hLower hcNonpos (phi n) initial)) =ᶠ[atTop]
      fun n => -source + formEll
        (reverseTimeGalerkinPrimal r₀ r₁ lam h₀₁ hlam hΩ hΩbounded a b c F
          haSmooth hbSmooth hcSmooth hFSmooth hLower hcNonpos (phi n) initial) -
          inner ℝ (valueCLM hΩ (galerkinVector hΩ k)) initial := by
    filter_upwards [hIndex] with n hn
    simpa [massEll, formEll, source, T, eta, etaDeriv, hEta, hEtaDeriv, S, A, affineReverseTimeMassPairing, affineReverseTimeSourcePairing, affineReverseTimeFormPairing, affineReverseTimeInitialPairing, affineReverseTimeVTest, affineReverseTimeDerivativeVTest] using
        finite_affine_boundary_pairing_wrapped r₀ r₁ lam h₀₁ hlam hΩ hΩbounded a b c F
          haSmooth hbSmooth hcSmooth hFSmooth hLower hcNonpos initial (phi n) k hn
  have hRight : Tendsto
      (fun n => -source + formEll
        (reverseTimeGalerkinPrimal r₀ r₁ lam h₀₁ hlam hΩ hΩbounded a b c F
          haSmooth hbSmooth hcSmooth hFSmooth hLower hcNonpos (phi n) initial) -
        inner ℝ (valueCLM hΩ (galerkinVector hΩ k)) initial)
      atTop (𝓝 (-source + formEll U -
        inner ℝ (valueCLM hΩ (galerkinVector hΩ k)) initial)) :=
    ((tendsto_const_nhds.neg.add (hclm formEll)).sub tendsto_const_nhds)
  have hLimit : massEll U = -source + formEll U -
      inner ℝ (valueCLM hΩ (galerkinVector hΩ k)) initial :=
    tendsto_nhds_unique_of_eventuallyEq (hclm massEll) hRight hFinite
  have hResidual : reverseTimeDualPairingRightCLM hΩ T
      (reverseTimeSeparatedVTestOfMemLp hΩ eta hEta (galerkinVector hΩ k)) g =
      source - formEll U := by
    exact reverseTimeDualPairingRightCLM_sub hΩ T
      (reverseTimeSeparatedVTestOfMemLp hΩ eta hEta (galerkinVector hΩ k)) S (A U)
  have hTrace : massEll U =
      -affineReverseTimeResidualPairing hΩ T (sub_pos.mpr h₀₁) g (galerkinVector hΩ k) -
      affineReverseTimeInitialPairing hΩ (galerkinVector hΩ k) trace := by
    calc
      massEll U =
          (∫ tau, inner ℝ (valueCLM hΩ (galerkinVector hΩ k))
            (Set.IccExtend (sub_pos.mpr h₀₁).le
              (reverseTimeHilbertRepresentative hΩ T (sub_pos.mpr h₀₁) U g hdu) tau) *
              etaDeriv tau ∂reverseTimeVolume T) := (canonical_affine_mass_eq_gelfand_mass hΩ T (sub_pos.mpr h₀₁) U g hdu (galerkinVector hΩ k) etaDeriv hEtaDeriv).symm
      _ = -affineReverseTimeResidualPairing hΩ T (sub_pos.mpr h₀₁) g (galerkinVector hΩ k) -
            affineReverseTimeInitialPairing hΩ (galerkinVector hΩ k) trace := by
            simpa only [etaDeriv] using
              reverseTimeHilbertRepresentative_affine_initial_pairing_wrapped hΩ T
                (sub_pos.mpr h₀₁) U g hdu (galerkinVector hΩ k)
  dsimp only [massEll, formEll, source, affineReverseTimeResidualPairing,
    affineReverseTimeInitialPairing, affineReverseTimeVTest, eta, hEta,
    affineReverseTimeMultiplier] at hLimit hTrace hResidual
  linarith


/-- A reverse-time Galerkin limit has the prescribed canonical initial trace. -/
theorem exists_reverseTimeGalerkinPrimal_initialTrace
    (initial : PDE.ScalarLp Ω (2 : ℝ≥0∞)) :
    ∃ (U : ReverseTimeL2V hΩ (r₁ - r₀)),
      ∃ hdu : HasGelfandWeakTimeDerivative hΩ (r₁ - r₀) (sub_pos.mpr h₀₁) U
        (reverseTimeFormResidual r₀ r₁ h₀₁ hΩ hΩbounded a b c
          haSmooth hbSmooth hcSmooth F hFSmooth U),
        reverseTimeInitialTrace hΩ (r₁ - r₀) (sub_pos.mpr h₀₁) U
          (reverseTimeFormResidual r₀ r₁ h₀₁ hΩ hΩbounded a b c
            haSmooth hbSmooth hcSmooth F hFSmooth U) hdu = initial := by
  obtain ⟨U, phi, hphi, hclm, hdu⟩ :=
    exists_strictMono_tendsto_clm_reverseTimeGalerkinPrimal_residual_derivative
      r₀ r₁ lam h₀₁ hlam hΩ hΩbounded a b c F haSmooth hbSmooth hcSmooth hFSmooth
      hLower hcNonpos initial
  let T := r₁ - r₀
  let g := reverseTimeFormResidual r₀ r₁ h₀₁ hΩ hΩbounded a b c
    haSmooth hbSmooth hcSmooth F hFSmooth U
  let trace := reverseTimeInitialTrace hΩ T (sub_pos.mpr h₀₁) U g hdu
  refine ⟨U, hdu, ?_⟩
  apply scalarLpToH10HilbertGraphDual_injective hΩ
  apply ContinuousLinearMap.ext
  intro v
  have hvClosure : v ∈ closure (Set.range (galerkinVector hΩ)) := by
    rw [(denseRange_galerkinVector hΩ).closure_range]
    exact mem_univ _
  obtain ⟨vN, hvN, hv⟩ := mem_closure_iff_seq_limit.mp hvClosure
  choose k hk using hvN
  have hPair : ∀ k : ℕ,
      inner ℝ (valueCLM hΩ (galerkinVector hΩ k)) trace =
        inner ℝ (valueCLM hΩ (galerkinVector hΩ k)) initial := by
    intro k
    simpa only [T, g, trace] using
      reverseTimeGalerkinPrimal_initialTrace_pairing r₀ r₁ lam h₀₁ hlam hΩ hΩbounded a b c F
        haSmooth hbSmooth hcSmooth hFSmooth hLower hcNonpos initial U phi hphi hclm hdu k
  have hLeft : Tendsto (fun n =>
      scalarLpToH10HilbertGraphDual hΩ trace (vN n)) atTop
      (𝓝 (scalarLpToH10HilbertGraphDual hΩ trace v)) :=
    (scalarLpToH10HilbertGraphDual hΩ trace).continuous.tendsto v |>.comp hv
  have hRight : Tendsto (fun n =>
      scalarLpToH10HilbertGraphDual hΩ initial (vN n)) atTop
      (𝓝 (scalarLpToH10HilbertGraphDual hΩ initial v)) :=
    (scalarLpToH10HilbertGraphDual hΩ initial).continuous.tendsto v |>.comp hv
  have hRange : ∀ n,
      scalarLpToH10HilbertGraphDual hΩ trace (vN n) =
        scalarLpToH10HilbertGraphDual hΩ initial (vN n) := by
    intro n
    simpa only [scalarLpToH10HilbertGraphDual_apply, hk n] using hPair (k n)
  exact tendsto_nhds_unique_of_eventuallyEq hLeft hRight (Eventually.of_forall hRange)



end

/-- The homogeneous-lateral reverse-time Dirichlet problem has a variational
energy solution with the prescribed canonical initial trace. -/
theorem exists_reverseTime_variational_energy_solution
    {d : ℕ} {Ω : Set (PDE.Vec d)}
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
    (initial : PDE.ScalarLp Ω (2 : ℝ≥0∞)) :
    ∃ (u : ReverseTimeL2V hΩ (r₁ - r₀)),
      ∃ (g : ReverseTimeL2VStar hΩ (r₁ - r₀)),
        ∃ hdu : HasGelfandWeakTimeDerivative hΩ (r₁ - r₀)
          (sub_pos.mpr h₀₁) u g,
          IsReverseTimeVariationalEnergySolution
            r₀ r₁ h₀₁ hΩ hΩbounded a b c F hFSmooth initial u g hdu := by
  obtain ⟨U, hdu, htrace⟩ :=
    exists_reverseTimeGalerkinPrimal_initialTrace r₀ r₁ lam h₀₁ hlam hΩ hΩbounded
      a b c F haSmooth hbSmooth hcSmooth hFSmooth hLower hcNonpos initial
  refine ⟨U,
    reverseTimeFormResidual r₀ r₁ h₀₁ hΩ hΩbounded a b c
      haSmooth hbSmooth hcSmooth F hFSmooth U,
    hdu, ?_⟩
  exact ⟨htrace,
    ae_reverseTimeFormResidual_apply r₀ r₁ h₀₁ hΩ hΩbounded a b c
      haSmooth hbSmooth hcSmooth F hFSmooth U⟩

end HypoellipticAleksandrov.Parabolic.Dirichlet

