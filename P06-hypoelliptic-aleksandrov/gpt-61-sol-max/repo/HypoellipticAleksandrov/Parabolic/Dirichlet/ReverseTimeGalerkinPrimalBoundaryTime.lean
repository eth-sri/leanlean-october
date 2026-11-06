module

public import HypoellipticAleksandrov.Parabolic.Dirichlet.ReverseTimeGalerkinPrimalBase
import Batteries.Tactic.Alias
import Batteries.Tactic.OpenPrivate
import all HypoellipticAleksandrov.Parabolic.Dirichlet.ReverseTimeGalerkinCompactTime

open private HypoellipticAleksandrov.Parabolic.Dirichlet.hasDerivWithinAt_fixed_galerkin_pairing from HypoellipticAleksandrov.Parabolic.Dirichlet.ReverseTimeGalerkinCompactTime
open private HypoellipticAleksandrov.Parabolic.Dirichlet.continuousOn_fixed_galerkin_pairing from HypoellipticAleksandrov.Parabolic.Dirichlet.ReverseTimeGalerkinCompactTime
open private HypoellipticAleksandrov.Parabolic.Dirichlet.continuousOn_galerkin_reconstruct from HypoellipticAleksandrov.Parabolic.Dirichlet.ReverseTimeGalerkinCompactTime


/-!
# Boundary-time identity for a finite reverse-time Galerkin curve

This file keeps the finite Galerkin calculation at the raw Sobolev level.  In
particular, its endpoint is the actual finite initial projection, rather than
an endpoint value of a quotient-valued limiting curve.
-/

 public section



namespace HypoellipticAleksandrov.Parabolic.Dirichlet

open MeasureTheory Set
open scoped ENNReal Matrix Matrix.Norms.Elementwise MatrixOrder










private theorem boundaryTime_scalar_identity
    (T : ℝ) (hT : 0 < T) (pairing residual eta etaDeriv : ℝ → ℝ)
    (hpairing : ContinuousOn pairing (Icc 0 T))
    (hresidual : IntegrableOn residual (Icc 0 T) )
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
  have hresidualInterval : IntervalIntegrable residual volume 0 T :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hT.le).mpr hresidual
  have hderivInterval : IntervalIntegrable etaDeriv volume 0 T :=
    hDerivCont.intervalIntegrable_of_Icc hT.le
  have hinterval := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivWithinAt
    (a := 0) (b := T) (u := pairing) (u' := residual) (v := eta) (v' := etaDeriv)
    (by rw [uIcc_of_le hT.le]; exact hderivPairing)
    (by rw [uIcc_of_le hT.le]; exact hEta) hresidualInterval hderivInterval
  have hintervalBoundary : (∫ τ in 0..T, pairing τ * etaDeriv τ) =
      -(∫ τ in 0..T, residual τ * eta τ) - pairing 0 * eta 0 := by
    calc
      (∫ τ in 0..T, pairing τ * etaDeriv τ) =
          pairing T * eta T - pairing 0 * eta 0 - ∫ τ in 0..T, residual τ * eta τ :=
        hinterval
      _ = -(∫ τ in 0..T, residual τ * eta τ) - pairing 0 * eta 0 := by
        rw [hEtaT]
        ring
  have hleftIcc : IntegrableOn (fun τ => pairing τ * etaDeriv τ) (Icc 0 T)  :=
    (hpairing.mul hDerivCont).integrableOn_Icc
  have hEtaBounded  :=
    (isCompact_Icc.image_of_continuousOn hEtaCont).isBounded
  obtain ⟨C, hC⟩ := hEtaBounded.exists_norm_le
  have hrightIcc : IntegrableOn (fun τ => residual τ * eta τ) (Icc 0 T)  := by
    apply hresidual.mul_bdd (hEtaCont.aestronglyMeasurable measurableSet_Icc)
    filter_upwards [ae_restrict_mem measurableSet_Icc] with τ hτ
    exact hC (eta τ) ⟨τ, hτ, rfl⟩



  exact ⟨(by
      simpa only [reverseTimeVolume, reverseTimeOpenInterval, restrict_Ioo_eq_restrict_Icc,
        IntegrableOn]
        using hleftIcc), (show _ by
      simpa only [reverseTimeVolume, reverseTimeOpenInterval, restrict_Ioo_eq_restrict_Icc,
        IntegrableOn]
        using hrightIcc), (show _ by
      simpa only [reverseTimeVolume, reverseTimeOpenInterval, restrict_Ioo_eq_restrict_Icc,
        restrict_Ioc_eq_restrict_Icc, intervalIntegral.integral_of_le hT.le]
        using hintervalBoundary)⟩

variable {d : ℕ} {Ω : PDE.VelocityRegion d}

/-- The selected finite reverse-time Galerkin raw curve obeys the terminal-zero
boundary-time identity, including its initial projected datum. -/
theorem reverseTimeGalerkinPrimal_boundaryTime

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
    (N : ℕ) (initial : PDE.ScalarLp Ω (2 ))
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
          H10HilbertGraph hΩ)) * eta 0 := by
  let sharedTerm_2eed35dd82 := ((Fin (Module.finrank ℝ (galerkinSpace hΩ N)) → ℝ))
  let sharedTerm_90ceac819f := ((valueCLM hΩ (v : H10HilbertGraph hΩ)))
  let selected :=
    ((exists_reverseTimeGalerkin_uniform_energy_solution r₀ r₁ lam h₀₁ hlam hΩ hΩbounded a b c F
      haSmooth hbSmooth hcSmooth hFSmooth hLower hcNonpos).choose_spec.2).choose_spec.2
      N initial
  let curveSpec := selected.choose_spec
  have hspec := curveSpec.choose_spec
  let x := reverseTimeGalerkinPrimalCoordinate r₀ r₁ lam h₀₁ hlam hΩ hΩbounded
    a b c F haSmooth hbSmooth hcSmooth hFSmooth hLower hcNonpos N initial
  let T : ℝ := r₁ - r₀
  have hT : 0 ≤ T := sub_nonneg.mpr h₀₁.le
  let A : ℝ → sharedTerm_2eed35dd82 →L[ℝ]
      sharedTerm_2eed35dd82 := fun τ =>
    reverseTimeGalerkinLinearPart r₀ r₁ h₀₁ hΩ hΩbounded a b c
      haSmooth hbSmooth hcSmooth N (Set.projIcc 0 T hT τ)
  let f : ℝ → sharedTerm_2eed35dd82 := fun τ =>
    reverseTimeGalerkinForcing r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth N
      (Set.projIcc 0 T hT τ)
  let xdot : ℝ → sharedTerm_2eed35dd82 := fun τ =>
    A τ (x τ) + f τ
  have hx : ContinuousOn x (Icc 0 T) := by
    simpa only [x, T, reverseTimeGalerkinPrimalCoordinate] using hspec.2.2.1

  have hderiv : ∀ τ ∈ Icc 0 T,
      HasDerivWithinAt x (xdot τ) (Icc 0 T) τ := by
    intro τ hτ
    let τ' : Icc 0 (r₁ - r₀) := ⟨τ, hτ⟩

    simpa only [x, xdot, A, f, T, (Set.projIcc_of_mem hT hτ), reverseTimeGalerkinPrimalCoordinate] using
      (hspec.2.2.2.2.1 τ').1

  let pairing : ℝ → ℝ := fun τ =>
    inner ℝ sharedTerm_90ceac819f
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


  have hrec : ContinuousOn
      (fun τ => (galerkinReconstruct hΩ N (x τ) : H10HilbertGraph hΩ)) (Icc 0 T) :=
    _root_.HypoellipticAleksandrov.Parabolic.Dirichlet.continuousOn_galerkin_reconstruct hΩ N x (Icc 0 T) hx
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
      haSmooth hbSmooth hcSmooth).continuousOn.clm_apply hrec).clm_apply
      continuous_const.continuousOn




  have hscalar := boundaryTime_scalar_identity T (show 0 < T by dsimp only [T]; linarith) pairing residual eta etaDeriv (show ContinuousOn pairing (Icc 0 T) by
      simpa only [pairing] using _root_.HypoellipticAleksandrov.Parabolic.Dirichlet.continuousOn_fixed_galerkin_pairing hΩ N x v (Icc 0 T) hx)
    (by
        apply Integrable.congr (show ContinuousOn clampedResidual (Icc 0 T) by
            simpa only [clampedResidual, Pi.sub_def] using hsource.continuousOn.sub hclampedForm).integrableOn_Icc
        filter_upwards [(show ∀ᵐ τ ∂volume.restrict (Icc 0 T),
      reverseTimeSpatialFormOperatorClamp r₀ r₁ h₀₁ hΩ hΩbounded a b c
        haSmooth hbSmooth hcSmooth τ
        (galerkinReconstruct hΩ N (x τ) : H10HilbertGraph hΩ)
        (v : H10HilbertGraph hΩ) =
      reverseTimeSpatialForm hΩ r₁ τ a b c
        (galerkinReconstruct hΩ N (x τ) : H10HilbertGraph hΩ)
        (v : H10HilbertGraph hΩ) by

            filter_upwards [(show ∀ᵐ τ ∂volume.restrict (Icc 0 T), ∀ u v : H10HilbertGraph hΩ,
                reverseTimeSpatialFormOperatorClamp r₀ r₁ h₀₁ hΩ hΩbounded a b c
                  haSmooth hbSmooth hcSmooth τ u v =
                reverseTimeSpatialForm hΩ r₁ τ a b c u v by
                simpa only [T, reverseTimeVolume, reverseTimeOpenInterval, restrict_Ioo_eq_restrict_Icc]
                  using ae_reverseTimeSpatialFormOperatorClamp_apply r₀ r₁ h₀₁ hΩ hΩbounded a b c
                    haSmooth hbSmooth hcSmooth)] with τ hτ
            exact hτ _ _)] with τ hτ
        dsimp only [residual, clampedResidual]
        exact congrArg
          (fun z  => reverseTimeNegativeSourceRaw r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth τ
            (v : H10HilbertGraph hΩ) - z) hτ) (by
        intro τ hτ

        let τT : Icc 0 T := ⟨τ, hτ⟩
        let τ' : Icc 0 (r₁ - r₀) := ⟨τ, hτ⟩
        have hrow := reverseTimeGalerkin_basisRows_forall r₀ r₁ h₀₁ hΩ hΩbounded a b c F
          haSmooth hbSmooth hcSmooth hFSmooth N τ' (x τ) (xdot τ) ((show ∀ τ : Icc 0 T,
      ∀ i : Fin (Module.finrank ℝ (galerkinSpace hΩ N)),
        inner ℝ
            (valueCLM hΩ (galerkinReconstruct hΩ N (xdot τ.1) :
              H10HilbertGraph hΩ))
            (valueCLM hΩ (galerkinSpaceBasis hΩ N i : H10HilbertGraph hΩ)) +
          reverseTimeSpatialForm hΩ r₁ τ.1 a b c
            (galerkinReconstruct hΩ N (x τ.1) : H10HilbertGraph hΩ)
            (galerkinSpaceBasis hΩ N i : H10HilbertGraph hΩ) =
          reverseTimeGalerkinSource r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth N
            ⟨τ.1, τ.2⟩ i by
              intro τ i
              let τ' : Icc 0 (r₁ - r₀) := ⟨τ.1, τ.2⟩


              simpa only [x, xdot, A, f, T, (Set.projIcc_of_mem hT τ.2), reverseTimeGalerkinPrimalCoordinate, hspec.2.1] using
                (hspec.2.2.2.2.1 τ').2 i) τT) v
        have hrate :
            inner ℝ sharedTerm_90ceac819f
              (valueCLM hΩ (galerkinReconstruct hΩ N (xdot τ) : H10HilbertGraph hΩ)) =
            residual τ := by
          rw [real_inner_comm]
          dsimp only [residual]
          linarith
        rw [← hrate]
        exact (_root_.HypoellipticAleksandrov.Parabolic.Dirichlet.hasDerivWithinAt_fixed_galerkin_pairing hΩ N x (xdot τ) v (hderiv τ hτ))) (hEta)
    (hDerivCont) (hEtaT)
  have hpairingZero : pairing 0 =
      inner ℝ sharedTerm_90ceac819f
        (valueCLM hΩ (galerkinInitialProjection hΩ N initial : H10HilbertGraph hΩ)) := by
    simpa only [pairing, reverseTimeGalerkinPrimalRaw, x] using congrArg
      (fun w  =>
        inner ℝ sharedTerm_90ceac819f (valueCLM hΩ w))
      (reverseTimeGalerkinPrimalRaw_zero r₀ r₁ lam h₀₁ hlam hΩ hΩbounded a b c F
        haSmooth hbSmooth hcSmooth hFSmooth hLower hcNonpos N initial)
  rw [hpairingZero] at hscalar
  simpa only [reverseTimeGalerkinPrimalRaw, x, pairing, residual, T] using hscalar

/-- A fixed lower Galerkin test pairs the higher initial projection exactly as
it pairs the original spatial initial datum. -/
theorem inner_value_galerkinInitialProjection_eq

    (hΩ : IsOpen Ω) {M N : ℕ} (hMN : M ≤ N)
    (initial : PDE.ScalarLp Ω (2 ))
    (v : galerkinSpace hΩ M) :
    inner ℝ (valueCLM hΩ (v : H10HilbertGraph hΩ))
      (valueCLM hΩ (galerkinInitialProjection hΩ N initial :
        H10HilbertGraph hΩ)) =
      inner ℝ (valueCLM hΩ (v : H10HilbertGraph hΩ)) initial := by
  let K := galerkinValueSpace hΩ N

  let u : K := ⟨_, ⟨v, (galerkinSpace_mono hΩ hMN v.property), rfl⟩⟩
  rw [value_galerkinInitialProjection]
  change inner ℝ (u : PDE.ScalarLp Ω (2 )) (K.orthogonalProjection initial) =
    inner ℝ (u : PDE.ScalarLp Ω (2 )) initial
  exact Submodule.inner_orthogonalProjection_eq_of_mem_left u initial

end HypoellipticAleksandrov.Parabolic.Dirichlet
