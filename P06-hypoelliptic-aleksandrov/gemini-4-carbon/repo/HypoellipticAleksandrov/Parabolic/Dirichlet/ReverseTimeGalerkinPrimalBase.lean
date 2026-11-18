module

public import HypoellipticAleksandrov.Parabolic.Dirichlet.ReverseTimeGalerkinCoordinatesBase
public import HypoellipticAleksandrov.Parabolic.Dirichlet.TimeTests
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
public import HypoellipticAleksandrov.Parabolic.Dirichlet.ReverseTimeGalerkinEnergy

@[expose] public noncomputable section

namespace HypoellipticAleksandrov.Parabolic.Dirichlet
open MeasureTheory Set
open scoped BigOperators ENNReal Matrix Matrix.Norms.Elementwise RealInnerProductSpace MatrixOrder



/-- Exact finite Galerkin basis rows hold against every finite Galerkin test. -/
theorem reverseTimeGalerkin_basisRows_forall
    {d : ℕ} {Ω : Set (PDE.Vec d)}
    (r₀ r₁ : ℝ) (h₀₁ : r₀ < r₁)
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
    (N : ℕ) (τ : Set.Icc 0 (r₁ - r₀))
    (x xdot : Fin (Module.finrank ℝ (galerkinSpace hΩ N)) → ℝ)
    (hrows : ∀ i : Fin (Module.finrank ℝ (galerkinSpace hΩ N)),
      inner ℝ
          (valueCLM hΩ (galerkinReconstruct hΩ N xdot : H10HilbertGraph hΩ))
          (valueCLM hΩ (galerkinSpaceBasis hΩ N i : H10HilbertGraph hΩ)) +
        reverseTimeSpatialForm hΩ r₁ τ.1 a b c
          (galerkinReconstruct hΩ N x : H10HilbertGraph hΩ)
          (galerkinSpaceBasis hΩ N i : H10HilbertGraph hΩ) =
        reverseTimeGalerkinSource r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth N τ i)
    (v : galerkinSpace hΩ N) :
    inner ℝ
        (valueCLM hΩ (galerkinReconstruct hΩ N xdot : H10HilbertGraph hΩ))
        (valueCLM hΩ (v : H10HilbertGraph hΩ)) +
      reverseTimeSpatialForm hΩ r₁ τ.1 a b c
        (galerkinReconstruct hΩ N x : H10HilbertGraph hΩ)
        (v : H10HilbertGraph hΩ) =
      reverseTimeNegativeSourceRaw r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth τ.1
        (v : H10HilbertGraph hΩ)  := by
  have map_galerkinReconstruct_sum {Ω : Set (PDE.Vec d)} (hΩ : IsOpen Ω) (N : ℕ) {Z : Type} [NormedAddCommGroup Z] [NormedSpace ℝ Z] (Q : H10HilbertGraph hΩ →L[ℝ] Z) (x : Fin (Module.finrank ℝ (galerkinSpace hΩ N)) → ℝ) :
      Q (galerkinReconstruct hΩ N x : H10HilbertGraph hΩ) =
      ∑ i, x i • Q (galerkinSpaceBasis hΩ N i : H10HilbertGraph hΩ) := by
    calc
      Q (galerkinReconstruct hΩ N x : H10HilbertGraph hΩ) =
          Q (↑(∑ i, x i • galerkinSpaceBasis hΩ N i) : H10HilbertGraph hΩ) := by
        exact congrArg Q (congrArg (fun w : galerkinSpace hΩ N =>
          (w : H10HilbertGraph hΩ)) (galerkinReconstruct_apply hΩ N x))
      _ = Q (∑ i, x i • (galerkinSpaceBasis hΩ N i : H10HilbertGraph hΩ)) := by
        have hcoe : (↑(∑ i, x i • galerkinSpaceBasis hΩ N i) : H10HilbertGraph hΩ) =
            ∑ i, x i • (galerkinSpaceBasis hΩ N i : H10HilbertGraph hΩ) := by
          simpa using
            (Submodule.coe_sum (p := galerkinSpace hΩ N)
              (fun i => x i • galerkinSpaceBasis hΩ N i) Finset.univ)
        exact congrArg Q hcoe
      _ = ∑ i, x i • Q (galerkinSpaceBasis hΩ N i : H10HilbertGraph hΩ) := by
        calc
          Q (∑ i, x i • (galerkinSpaceBasis hΩ N i : H10HilbertGraph hΩ)) =
              ∑ i, Q (x i • (galerkinSpaceBasis hΩ N i : H10HilbertGraph hΩ)) :=
            map_sum Q (fun i => x i • (galerkinSpaceBasis hΩ N i : H10HilbertGraph hΩ))
              Finset.univ
          _ = _ := by
            apply Finset.sum_congr rfl
            intro i _
            exact Q.map_smul (x i) (galerkinSpaceBasis hΩ N i : H10HilbertGraph hΩ)
  let q :=
    (galerkinSpaceBasis hΩ N).equivFun v
  let u := galerkinReconstruct hΩ N x
  let udot :=
    valueCLM hΩ (galerkinReconstruct hΩ N xdot : H10HilbertGraph hΩ)
  let e : Fin (Module.finrank ℝ (galerkinSpace hΩ N)) → H10HilbertGraph hΩ :=
    fun i => galerkinSpaceBasis hΩ N i
  let B :=
    reverseTimeSpatialFormOperator r₀ r₁ h₀₁ hΩ hΩbounded a b c
      haSmooth hbSmooth hcSmooth τ u
  let A :=
    (innerSL ℝ udot).comp (valueCLM hΩ)
  let T := A + B
  let S :=
    reverseTimeNegativeSourceRaw r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth τ.1
  have hu : (galerkinReconstruct hΩ N q : H10HilbertGraph hΩ) = v := by
    exact congrArg (fun w : galerkinSpace hΩ N => (w : H10HilbertGraph hΩ))
      (galerkinReconstruct_equivFun hΩ N v)
  have hrow : ∀ i, T (e i) = S (e i) := by
    intro i
    simpa [T, A, B, S, e, udot, u, innerSL_apply_apply, reverseTimeSpatialFormOperator_apply, reverseTimeGalerkinSource] using hrows i
  have hsum : ∑ i, q i • T (e i) = ∑ i, q i • S (e i) := by
    apply Finset.sum_congr rfl
    intro i _
    exact congrArg (fun z => q i • z) (hrow i)
  have hT := map_galerkinReconstruct_sum hΩ N T q
  have hS := map_galerkinReconstruct_sum hΩ N S q
  have hresult :=
    hT.trans (hsum.trans hS.symm)
  rw [hu] at hresult
  simpa [T, A, B, S, udot, u, innerSL_apply_apply, reverseTimeSpatialFormOperator_apply]
    using hresult






private theorem compactTime_scalar_identity
    (T : ℝ) (hT : 0 < T) (pairing residual : ℝ → ℝ)
    (hpairing : ContinuousOn pairing (Icc 0 T))
    (hresidual : IntegrableOn residual (Icc 0 T) volume)
    (hderivPairing : ∀ τ ∈ Icc 0 T,
      HasDerivWithinAt pairing (residual τ) (Icc 0 T) τ)
    (eta : ReverseTimeScalarTest T) :
    Integrable (fun τ => pairing τ * eta.deriv τ) (reverseTimeVolume T) ∧
    Integrable (fun τ => residual τ * eta τ) (reverseTimeVolume T) ∧
    (∫ τ, pairing τ * eta.deriv τ ∂reverseTimeVolume T) =
      -(∫ τ, residual τ * eta τ ∂reverseTimeVolume T) := by
  have hetaDeriv : ∀ τ ∈ Icc 0 T,
      HasDerivWithinAt (eta : ℝ → ℝ) (eta.deriv τ) (Icc 0 T) τ := by
    intro τ _
    rw [ReverseTimeScalarTest.deriv_apply]
    exact ((eta.contDiff.differentiable (by simp)).differentiableAt.hasDerivAt).hasDerivWithinAt
  have hpairingIntegrable :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hT.le).mpr hresidual
  have hetaIntegrable : IntervalIntegrable eta.deriv volume 0 T :=
    eta.contDiff_deriv.continuous.continuousOn.intervalIntegrable_of_Icc hT.le
  have heta0 : eta 0 = 0 := by
    apply image_eq_zero_of_notMem_tsupport
    intro hsupport
    have hmem := eta.tsupport_subset hsupport
    have hmem' : 0 < 0 ∧ 0 < T := by
      simpa [reverseTimeOpenInterval] using hmem
    exact lt_irrefl 0 hmem'.1
  have hetaT : eta T = 0 := by
    apply image_eq_zero_of_notMem_tsupport
    intro hsupport
    have hmem := eta.tsupport_subset hsupport
    exact lt_irrefl T hmem.2
  have hinterval := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivWithinAt
    (a := 0) (b := T) (u := pairing) (u' := residual) (v := eta) (v' := eta.deriv)
    (by rw [uIcc_of_le hT.le]; exact hderivPairing)
    (by rw [uIcc_of_le hT.le]; exact hetaDeriv) hpairingIntegrable hetaIntegrable
  have hintervalZero : (∫ τ in 0..T, pairing τ * eta.deriv τ) =
      -(∫ τ in 0..T, residual τ * eta τ) := by
    calc
      (∫ τ in 0..T, pairing τ * eta.deriv τ) =
          pairing T * eta T - pairing 0 * eta 0 - ∫ τ in 0..T, residual τ * eta τ := hinterval
      _ = -(∫ τ in 0..T, residual τ * eta τ) := by
        rw [heta0, hetaT]
        ring
  have hleftIcc : IntegrableOn (fun τ => pairing τ * eta.deriv τ) (Icc 0 T) volume :=
    (hpairing.mul eta.contDiff_deriv.continuous.continuousOn).integrableOn_Icc
  obtain ⟨C, hC⟩ := eta.exists_norm_le
  have hrightIcc :=
    hresidual.mul_bdd eta.contDiff.continuous.aestronglyMeasurable (ae_of_all _ hC)
  have hleft : Integrable (fun τ => pairing τ * eta.deriv τ) (reverseTimeVolume T) := by
    simpa only [reverseTimeVolume, reverseTimeOpenInterval,
      restrict_Ioo_eq_restrict_Icc, IntegrableOn] using
      hleftIcc
  have hright : Integrable (fun τ => residual τ * eta τ) (reverseTimeVolume T) := by
    simpa only [reverseTimeVolume, reverseTimeOpenInterval,
      restrict_Ioo_eq_restrict_Icc, IntegrableOn] using
      hrightIcc
  have hcompact : (∫ τ, pairing τ * eta.deriv τ ∂reverseTimeVolume T) =
      -(∫ τ, residual τ * eta τ ∂reverseTimeVolume T) := by
    simpa only [reverseTimeVolume, reverseTimeOpenInterval, restrict_Ioo_eq_restrict_Icc,
      restrict_Ioc_eq_restrict_Icc,
      intervalIntegral.integral_of_le hT.le] using hintervalZero
  exact ⟨hleft, hright, hcompact⟩

/-- The finite Galerkin row equation yields the compactly supported scalar time identity. -/
theorem reverseTimeGalerkin_compactTime_identity_of_basisRows
    {d : ℕ} {Ω : Set (PDE.Vec d)}
    (r₀ r₁ : ℝ) (h₀₁ : r₀ < r₁)
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
    (N : ℕ)
    (x xdot : ℝ → Fin (Module.finrank ℝ (galerkinSpace hΩ N)) → ℝ)
    (hx : ContinuousOn x (Set.Icc 0 (r₁ - r₀)))
    (hderiv : ∀ τ ∈ Set.Icc 0 (r₁ - r₀),
      HasDerivWithinAt x (xdot τ) (Set.Icc 0 (r₁ - r₀)) τ)
    (hrows : ∀ τ : Set.Icc 0 (r₁ - r₀),
      ∀ i : Fin (Module.finrank ℝ (galerkinSpace hΩ N)),
        inner ℝ
            (valueCLM hΩ (galerkinReconstruct hΩ N (xdot τ.1) :
              H10HilbertGraph hΩ))
            (valueCLM hΩ (galerkinSpaceBasis hΩ N i :
              H10HilbertGraph hΩ)) +
          reverseTimeSpatialForm hΩ r₁ τ.1 a b c
            (galerkinReconstruct hΩ N (x τ.1) : H10HilbertGraph hΩ)
            (galerkinSpaceBasis hΩ N i : H10HilbertGraph hΩ) =
          reverseTimeGalerkinSource r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth N τ i)
    (v : galerkinSpace hΩ N)
    (eta : ReverseTimeScalarTest (r₁ - r₀)) :
    MeasureTheory.Integrable
      (fun τ =>
        inner ℝ (valueCLM hΩ (v : H10HilbertGraph hΩ))
          (valueCLM hΩ
            (galerkinReconstruct hΩ N (x τ) : H10HilbertGraph hΩ)) *
          eta.deriv τ)
      (reverseTimeVolume (r₁ - r₀)) ∧
    MeasureTheory.Integrable
      (fun τ =>
        (reverseTimeNegativeSourceRaw r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth τ
            (v : H10HilbertGraph hΩ) -
          reverseTimeSpatialForm hΩ r₁ τ a b c
            (galerkinReconstruct hΩ N (x τ) : H10HilbertGraph hΩ)
            (v : H10HilbertGraph hΩ)) * eta τ)
      (reverseTimeVolume (r₁ - r₀)) ∧
    (∫ τ,
      inner ℝ (valueCLM hΩ (v : H10HilbertGraph hΩ))
        (valueCLM hΩ
          (galerkinReconstruct hΩ N (x τ) : H10HilbertGraph hΩ)) *
        eta.deriv τ ∂reverseTimeVolume (r₁ - r₀)) =
      -(∫ τ,
        (reverseTimeNegativeSourceRaw r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth τ
            (v : H10HilbertGraph hΩ) -
          reverseTimeSpatialForm hΩ r₁ τ a b c
            (galerkinReconstruct hΩ N (x τ) : H10HilbertGraph hΩ)
            (v : H10HilbertGraph hΩ)) * eta τ
        ∂reverseTimeVolume (r₁ - r₀))    := by
  have continuousOn_galerkin_reconstruct {Ω : Set (PDE.Vec d)} (hΩ : IsOpen Ω) (N : ℕ) (x : ℝ → Fin (Module.finrank ℝ (galerkinSpace hΩ N)) → ℝ) (s : Set ℝ) (hx : ContinuousOn x s) :
      ContinuousOn
      (fun t => (galerkinReconstruct hΩ N (x t) : H10HilbertGraph hΩ)) s := by
    let R : (Fin (Module.finrank ℝ (galerkinSpace hΩ N)) → ℝ) →L[ℝ]
        H10HilbertGraph hΩ :=
      (galerkinSpace hΩ N).subtypeL.comp
        (LinearMap.toContinuousLinearMap (galerkinReconstruct hΩ N))
    have hR : ContinuousOn (fun t => R (x t)) s :=
      R.continuous.continuousOn.comp hx fun _ _ => Set.mem_univ _
    simpa [R, ContinuousLinearMap.coe_coe, Submodule.subtypeL_apply, LinearMap.coe_toContinuousLinearMap'] using hR
  have continuousOn_fixed_galerkin_pairing {Ω : Set (PDE.Vec d)} (hΩ : IsOpen Ω) (N : ℕ) (x : ℝ → Fin (Module.finrank ℝ (galerkinSpace hΩ N)) → ℝ) (v : galerkinSpace hΩ N) (s : Set ℝ) (hx : ContinuousOn x s) :
      ContinuousOn
      (fun t =>
        inner ℝ (valueCLM hΩ (v : H10HilbertGraph hΩ))
          (valueCLM hΩ
            (galerkinReconstruct hΩ N (x t) : H10HilbertGraph hΩ))) s := by
    let R : (Fin (Module.finrank ℝ (galerkinSpace hΩ N)) → ℝ) →L[ℝ]
        H10HilbertGraph hΩ :=
      (galerkinSpace hΩ N).subtypeL.comp
        (LinearMap.toContinuousLinearMap (galerkinReconstruct hΩ N))
    let V : (Fin (Module.finrank ℝ (galerkinSpace hΩ N)) → ℝ) →L[ℝ]
        PDE.ScalarLp Ω 2 :=
      (valueCLM hΩ).comp R
    let I : PDE.ScalarLp Ω 2 →L[ℝ] ℝ :=
      innerSL ℝ (valueCLM hΩ (v : H10HilbertGraph hΩ))
    have hV : ContinuousOn (fun t => V (x t)) s :=
      V.continuous.continuousOn.comp hx fun _ _ => Set.mem_univ _
    simpa [I, V, R, ContinuousLinearMap.coe_coe, Submodule.subtypeL_apply, innerSL_apply_apply, Function.comp_def, LinearMap.coe_toContinuousLinearMap'] using
      I.continuous.continuousOn.comp hV fun _ _ => Set.mem_univ _
  have hasDerivWithinAt_fixed_galerkin_pairing {Ω : Set (PDE.Vec d)} (hΩ : IsOpen Ω) (N : ℕ) (x : ℝ → Fin (Module.finrank ℝ (galerkinSpace hΩ N)) → ℝ) (xdot : Fin (Module.finrank ℝ (galerkinSpace hΩ N)) → ℝ) (v : galerkinSpace hΩ N) {s : Set ℝ} {τ : ℝ} (hx : HasDerivWithinAt x xdot s τ) :
      HasDerivWithinAt
      (fun t =>
        inner ℝ (valueCLM hΩ (v : H10HilbertGraph hΩ))
          (valueCLM hΩ
            (galerkinReconstruct hΩ N (x t) : H10HilbertGraph hΩ)))
      (inner ℝ (valueCLM hΩ (v : H10HilbertGraph hΩ))
        (valueCLM hΩ (galerkinReconstruct hΩ N xdot : H10HilbertGraph hΩ))) s τ := by
    let R : (Fin (Module.finrank ℝ (galerkinSpace hΩ N)) → ℝ) →L[ℝ]
        H10HilbertGraph hΩ :=
      (galerkinSpace hΩ N).subtypeL.comp
        (LinearMap.toContinuousLinearMap (galerkinReconstruct hΩ N))
    let V : (Fin (Module.finrank ℝ (galerkinSpace hΩ N)) → ℝ) →L[ℝ]
        PDE.ScalarLp Ω 2 :=
      (valueCLM hΩ).comp R
    let I : PDE.ScalarLp Ω 2 →L[ℝ] ℝ :=
      innerSL ℝ (valueCLM hΩ (v : H10HilbertGraph hΩ))
    have hV := (V.hasFDerivAt).comp_hasDerivWithinAt τ hx
    have hI := (I.hasFDerivAt).comp_hasDerivWithinAt τ hV
    simpa [I, V, R, ContinuousLinearMap.coe_coe, Submodule.subtypeL_apply, innerSL_apply_apply, Function.comp_def, LinearMap.coe_toContinuousLinearMap'] using hI
  let T : ℝ := r₁ - r₀
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
  have hT : 0 < T := by
    dsimp only [T]
    linarith
  have hpairing : ContinuousOn pairing (Icc 0 T) := by
    simpa only [pairing, T] using continuousOn_fixed_galerkin_pairing hΩ N x v
      (Icc 0 (r₁ - r₀)) hx
  have hrec : ContinuousOn
      (fun τ => (galerkinReconstruct hΩ N (x τ) : H10HilbertGraph hΩ)) (Icc 0 T) := by
    simpa only [T] using continuousOn_galerkin_reconstruct hΩ N x (Icc 0 (r₁ - r₀)) hx
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
  have hclampedResidualIcc : IntegrableOn clampedResidual (Icc 0 T) volume :=
    hclampedResidual.integrableOn_Icc
  have hresidualIcc : IntegrableOn residual (Icc 0 T) volume := by
    apply Integrable.congr hclampedResidualIcc
    filter_upwards [hformAE] with τ hτ
    dsimp only [residual, clampedResidual]
    exact congrArg
      (fun z : ℝ => reverseTimeNegativeSourceRaw r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth τ
        (v : H10HilbertGraph hΩ) - z) hτ
  have hderivPairing : ∀ τ ∈ Icc 0 T,
      HasDerivWithinAt pairing (residual τ) (Icc 0 T) τ := by
    intro τ hτ
    have hfixed := hasDerivWithinAt_fixed_galerkin_pairing hΩ N x (xdot τ) v
      (hderiv τ (by simpa only [T] using hτ))
    have hrow := reverseTimeGalerkin_basisRows_forall r₀ r₁ h₀₁ hΩ hΩbounded a b c F
      haSmooth hbSmooth hcSmooth hFSmooth N ⟨τ, by simpa only [T] using hτ⟩
      (x τ) (xdot τ) (hrows ⟨τ, by simpa only [T] using hτ⟩) v
    have hrate :
        inner ℝ (valueCLM hΩ (v : H10HilbertGraph hΩ))
          (valueCLM hΩ (galerkinReconstruct hΩ N (xdot τ) : H10HilbertGraph hΩ)) =
        residual τ := by
      rw [real_inner_comm]
      dsimp only [residual, T]
      linarith
    rw [← hrate]
    simpa only [pairing] using hfixed
  exact compactTime_scalar_identity T hT pairing residual hpairing hresidualIcc
    hderivPairing eta



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
    z ∈ scalarParabolicClosedCylinder r₀ r₁ Ω →
      lam • (1 : PDE.Mat d) ≤ a z.1 z.2)
  (hcNonpos : ∀ z : TimeVelocity d,
    z ∈ scalarParabolicClosedCylinder r₀ r₁ Ω → c z.1 z.2 ≤ 0)

/-- The existence witness used to select the uniform Galerkin curves and constants. -/
noncomputable def reverseTimeGalerkinPrimalWitness :=
  exists_reverseTimeGalerkin_uniform_energy_solution r₀ r₁ lam h₀₁ hlam
    hΩ hΩbounded a b c F haSmooth hbSmooth hcSmooth hFSmooth hLower hcNonpos

/-- The first globally uniform energy constant selected from the finite
Galerkin energy existence theorem. -/
noncomputable def reverseTimeGalerkinPrimalK : ℝ :=
  (reverseTimeGalerkinPrimalWitness r₀ r₁ lam h₀₁ hlam hΩ hΩbounded a b c F
    haSmooth hbSmooth hcSmooth hFSmooth hLower hcNonpos).choose

/-- The second globally uniform energy constant from the same selected
existence witness as `reverseTimeGalerkinPrimalK`. -/
noncomputable def reverseTimeGalerkinPrimalM : ℝ :=
  ((reverseTimeGalerkinPrimalWitness r₀ r₁ lam h₀₁ hlam hΩ hΩbounded a b c F
    haSmooth hbSmooth hcSmooth hFSmooth hLower hcNonpos).choose_spec.2).choose

/-- The selected finite-coordinate reverse-time Galerkin curve. -/
noncomputable def reverseTimeGalerkinPrimalCoordinate
    (N : ℕ) (initial : PDE.ScalarLp Ω (2 : ℝ≥0∞)) :
    ℝ → Fin (Module.finrank ℝ (galerkinSpace hΩ N)) → ℝ :=
  (((reverseTimeGalerkinPrimalWitness r₀ r₁ lam h₀₁ hlam hΩ hΩbounded a b c F
    haSmooth hbSmooth hcSmooth hFSmooth hLower hcNonpos).choose_spec.2).choose_spec.2
      N initial).choose

/-- The raw Sobolev curve reconstructed directly from the selected coordinates.
This curve is not quotient-valued. -/
noncomputable def reverseTimeGalerkinPrimalRaw
    (N : ℕ) (initial : PDE.ScalarLp Ω (2 : ℝ≥0∞)) :
    ℝ → H10HilbertGraph hΩ :=
  fun τ => (galerkinReconstruct hΩ N
    (reverseTimeGalerkinPrimalCoordinate r₀ r₁ lam h₀₁ hlam hΩ hΩbounded
      a b c F haSmooth hbSmooth hcSmooth hFSmooth hLower hcNonpos N initial τ) :
      H10HilbertGraph hΩ)

/-- The globally selected first energy constant is nonnegative. -/
theorem reverseTimeGalerkinPrimalK_nonneg :
    0 ≤ reverseTimeGalerkinPrimalK r₀ r₁ lam h₀₁ hlam hΩ hΩbounded a b c F
      haSmooth hbSmooth hcSmooth hFSmooth hLower hcNonpos := by
  exact (reverseTimeGalerkinPrimalWitness r₀ r₁ lam h₀₁ hlam hΩ hΩbounded a b c F
    haSmooth hbSmooth hcSmooth hFSmooth hLower hcNonpos).choose_spec.1

/-- The selected raw Galerkin reconstruction is continuous on the closed
reverse-time interval. -/
theorem continuousOn_reverseTimeGalerkinPrimalRaw
    (N : ℕ) (initial : PDE.ScalarLp Ω (2 : ℝ≥0∞)) :
    ContinuousOn
      (reverseTimeGalerkinPrimalRaw r₀ r₁ lam h₀₁ hlam hΩ hΩbounded a b c F
        haSmooth hbSmooth hcSmooth hFSmooth hLower hcNonpos N initial)
      (Set.Icc 0 (r₁ - r₀)) := by
  let selected :=
    ((reverseTimeGalerkinPrimalWitness r₀ r₁ lam h₀₁ hlam hΩ hΩbounded a b c F
      haSmooth hbSmooth hcSmooth hFSmooth hLower hcNonpos).choose_spec.2).choose_spec.2
      N initial
  let curveSpec := selected.choose_spec
  have hspec := curveSpec.choose_spec
  have hx : ContinuousOn selected.choose (Set.Icc 0 (r₁ - r₀)) :=
    hspec.2.2.1
  let R : (Fin (Module.finrank ℝ (galerkinSpace hΩ N)) → ℝ) →L[ℝ]
      H10HilbertGraph hΩ :=
    (galerkinSpace hΩ N).subtypeL.comp
      (LinearMap.toContinuousLinearMap (galerkinReconstruct hΩ N))
  have hR : ContinuousOn (fun τ => R (selected.choose τ)) (Set.Icc 0 (r₁ - r₀)) :=
    R.continuous.continuousOn.comp hx fun _ _ => Set.mem_univ _
  unfold reverseTimeGalerkinPrimalRaw reverseTimeGalerkinPrimalCoordinate
  simpa [R, ContinuousLinearMap.coe_coe, Submodule.subtypeL_apply, LinearMap.coe_toContinuousLinearMap'] using hR

/-- At reverse time zero, the selected raw curve is the finite Galerkin
projection of the prescribed initial datum. -/
theorem reverseTimeGalerkinPrimalRaw_zero
    (N : ℕ) (initial : PDE.ScalarLp Ω (2 : ℝ≥0∞)) :
    reverseTimeGalerkinPrimalRaw r₀ r₁ lam h₀₁ hlam hΩ hΩbounded a b c F
      haSmooth hbSmooth hcSmooth hFSmooth hLower hcNonpos N initial 0 =
      (galerkinInitialProjection hΩ N initial : H10HilbertGraph hΩ) := by
  let selected :=
    ((reverseTimeGalerkinPrimalWitness r₀ r₁ lam h₀₁ hlam hΩ hΩbounded a b c F
      haSmooth hbSmooth hcSmooth hFSmooth hLower hcNonpos).choose_spec.2).choose_spec.2
      N initial
  let curveSpec := selected.choose_spec
  have hspec := curveSpec.choose_spec
  have hx0 : selected.choose 0 = (galerkinSpaceBasis hΩ N).equivFun
      (galerkinInitialProjection hΩ N initial) := hspec.1
  calc
    reverseTimeGalerkinPrimalRaw r₀ r₁ lam h₀₁ hlam hΩ hΩbounded a b c F
        haSmooth hbSmooth hcSmooth hFSmooth hLower hcNonpos N initial 0 =
        (galerkinReconstruct hΩ N (selected.choose 0) : H10HilbertGraph hΩ) := by
      rfl
    _ = (galerkinReconstruct hΩ N ((galerkinSpaceBasis hΩ N).equivFun
        (galerkinInitialProjection hΩ N initial)) : H10HilbertGraph hΩ) := by
      exact congrArg (fun z => (galerkinReconstruct hΩ N z : H10HilbertGraph hΩ)) hx0
    _ = (galerkinInitialProjection hΩ N initial : H10HilbertGraph hΩ) := by
      exact congrArg (fun z : galerkinSpace hΩ N => (z : H10HilbertGraph hΩ))
        (galerkinReconstruct_equivFun hΩ N (galerkinInitialProjection hΩ N initial))

/-- The selected raw curve obeys the sharp pointwise value-energy estimate. -/
theorem reverseTimeGalerkinPrimal_value_energy
    (N : ℕ) (initial : PDE.ScalarLp Ω (2 : ℝ≥0∞))
    (t : ℝ) (ht : t ∈ Set.Icc 0 (r₁ - r₀)) :
    ‖valueCLM hΩ
      (reverseTimeGalerkinPrimalRaw r₀ r₁ lam h₀₁ hlam hΩ hΩbounded a b c F
        haSmooth hbSmooth hcSmooth hFSmooth hLower hcNonpos N initial t)‖ ^ 2 ≤
      gronwallBound (‖initial‖ ^ 2)
        (2 * reverseTimeGalerkinPrimalK r₀ r₁ lam h₀₁ hlam hΩ hΩbounded a b c F
          haSmooth hbSmooth hcSmooth hFSmooth hLower hcNonpos + 1)
        (reverseTimeGalerkinPrimalM r₀ r₁ lam h₀₁ hlam hΩ hΩbounded a b c F
          haSmooth hbSmooth hcSmooth hFSmooth hLower hcNonpos ^ 2) t := by
  let selected :=
    ((reverseTimeGalerkinPrimalWitness r₀ r₁ lam h₀₁ hlam hΩ hΩbounded a b c F
      haSmooth hbSmooth hcSmooth hFSmooth hLower hcNonpos).choose_spec.2).choose_spec.2
      N initial
  let curveSpec := selected.choose_spec
  have hspec := curveSpec.choose_spec
  have hu := hspec.2.1
  have hvalue := hspec.2.2.2.2.2.1
  simpa only [reverseTimeGalerkinPrimalRaw, reverseTimeGalerkinPrimalCoordinate,
    reverseTimeGalerkinPrimalK, reverseTimeGalerkinPrimalM, hu] using hvalue t ht

/-- The selected raw curve obeys the sharp integrated gradient-energy estimate. -/
theorem reverseTimeGalerkinPrimal_gradient_energy
    (N : ℕ) (initial : PDE.ScalarLp Ω (2 : ℝ≥0∞))
    (t : ℝ) (ht : t ∈ Set.Icc 0 (r₁ - r₀)) :
    lam * ∫ τ in Set.Ioc 0 t,
      ‖gradientCLM hΩ
        (reverseTimeGalerkinPrimalRaw r₀ r₁ lam h₀₁ hlam hΩ hΩbounded a b c F
          haSmooth hbSmooth hcSmooth hFSmooth hLower hcNonpos N initial τ)‖ ^ 2 ≤
      ‖initial‖ ^ 2 +
        (2 * reverseTimeGalerkinPrimalK r₀ r₁ lam h₀₁ hlam hΩ hΩbounded a b c F
          haSmooth hbSmooth hcSmooth hFSmooth hLower hcNonpos + 1) * t *
          gronwallBound (‖initial‖ ^ 2)
            (2 * reverseTimeGalerkinPrimalK r₀ r₁ lam h₀₁ hlam hΩ hΩbounded a b c F
              haSmooth hbSmooth hcSmooth hFSmooth hLower hcNonpos + 1)
            (reverseTimeGalerkinPrimalM r₀ r₁ lam h₀₁ hlam hΩ hΩbounded a b c F
              haSmooth hbSmooth hcSmooth hFSmooth hLower hcNonpos ^ 2)
            (r₁ - r₀) +
        (reverseTimeGalerkinPrimalM r₀ r₁ lam h₀₁ hlam hΩ hΩbounded a b c F
          haSmooth hbSmooth hcSmooth hFSmooth hLower hcNonpos ^ 2) * t := by
  let selected :=
    ((reverseTimeGalerkinPrimalWitness r₀ r₁ lam h₀₁ hlam hΩ hΩbounded a b c F
      haSmooth hbSmooth hcSmooth hFSmooth hLower hcNonpos).choose_spec.2).choose_spec.2
      N initial
  let curveSpec := selected.choose_spec
  have hspec := curveSpec.choose_spec
  have hu := hspec.2.1
  have hgradient := hspec.2.2.2.2.2.2
  simpa only [reverseTimeGalerkinPrimalRaw, reverseTimeGalerkinPrimalCoordinate,
    reverseTimeGalerkinPrimalK, reverseTimeGalerkinPrimalM, hu] using hgradient t ht

/-- The selected finite Galerkin curve satisfies the compactly supported
reverse-time scalar identity against every finite-space test vector. -/
theorem reverseTimeGalerkinPrimal_compactTime
    (N : ℕ) (initial : PDE.ScalarLp Ω (2 : ℝ≥0∞))
    (v : galerkinSpace hΩ N) (eta : ReverseTimeScalarTest (r₁ - r₀)) :
    MeasureTheory.Integrable
      (fun τ =>
        inner ℝ (valueCLM hΩ (v : H10HilbertGraph hΩ))
          (valueCLM hΩ
            (reverseTimeGalerkinPrimalRaw r₀ r₁ lam h₀₁ hlam hΩ hΩbounded a b c F
              haSmooth hbSmooth hcSmooth hFSmooth hLower hcNonpos N initial τ)) *
          eta.deriv τ)
      (reverseTimeVolume (r₁ - r₀)) ∧
    MeasureTheory.Integrable
      (fun τ =>
        (reverseTimeNegativeSourceRaw r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth τ
            (v : H10HilbertGraph hΩ) -
          reverseTimeSpatialForm hΩ r₁ τ a b c
            (reverseTimeGalerkinPrimalRaw r₀ r₁ lam h₀₁ hlam hΩ hΩbounded a b c F
              haSmooth hbSmooth hcSmooth hFSmooth hLower hcNonpos N initial τ)
            (v : H10HilbertGraph hΩ)) * eta τ)
      (reverseTimeVolume (r₁ - r₀)) ∧
    (∫ τ,
      inner ℝ (valueCLM hΩ (v : H10HilbertGraph hΩ))
        (valueCLM hΩ
          (reverseTimeGalerkinPrimalRaw r₀ r₁ lam h₀₁ hlam hΩ hΩbounded a b c F
            haSmooth hbSmooth hcSmooth hFSmooth hLower hcNonpos N initial τ)) *
        eta.deriv τ ∂reverseTimeVolume (r₁ - r₀)) =
      -(∫ τ,
        (reverseTimeNegativeSourceRaw r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth τ
            (v : H10HilbertGraph hΩ) -
          reverseTimeSpatialForm hΩ r₁ τ a b c
            (reverseTimeGalerkinPrimalRaw r₀ r₁ lam h₀₁ hlam hΩ hΩbounded a b c F
              haSmooth hbSmooth hcSmooth hFSmooth hLower hcNonpos N initial τ)
            (v : H10HilbertGraph hΩ)) * eta τ
        ∂reverseTimeVolume (r₁ - r₀)) := by
  let selected :=
    ((reverseTimeGalerkinPrimalWitness r₀ r₁ lam h₀₁ hlam hΩ hΩbounded a b c F
      haSmooth hbSmooth hcSmooth hFSmooth hLower hcNonpos).choose_spec.2).choose_spec.2
      N initial
  let curveSpec := selected.choose_spec
  have hspec := curveSpec.choose_spec
  let x := reverseTimeGalerkinPrimalCoordinate r₀ r₁ lam h₀₁ hlam hΩ hΩbounded
    a b c F haSmooth hbSmooth hcSmooth hFSmooth hLower hcNonpos N initial
  let T : ℝ := r₁ - r₀
  have hT : 0 ≤ T := sub_nonneg.mpr h₀₁.le
  let A : ℝ → (Fin (Module.finrank ℝ (galerkinSpace hΩ N)) → ℝ) →L[ℝ]
      (Fin (Module.finrank ℝ (galerkinSpace hΩ N)) → ℝ) := fun τ =>
    reverseTimeGalerkinLinearPart r₀ r₁ h₀₁ hΩ hΩbounded a b c
      haSmooth hbSmooth hcSmooth N (Set.projIcc 0 T hT τ)
  let f : ℝ → Fin (Module.finrank ℝ (galerkinSpace hΩ N)) → ℝ := fun τ =>
    reverseTimeGalerkinForcing r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth N
      (Set.projIcc 0 T hT τ)
  let xdot : ℝ → Fin (Module.finrank ℝ (galerkinSpace hΩ N)) → ℝ := fun τ =>
    A τ (x τ) + f τ
  have hx : ContinuousOn x (Set.Icc 0 T) := by
    simpa only [x, T, reverseTimeGalerkinPrimalCoordinate] using
      hspec.2.2.1
  have hderiv : ∀ τ ∈ Set.Icc 0 T,
      HasDerivWithinAt x (xdot τ) (Set.Icc 0 T) τ := by
    intro τ hτ
    let τ' : Set.Icc 0 (r₁ - r₀) := ⟨τ, by simpa only [T] using hτ⟩
    have hproj : Set.projIcc 0 T hT τ = τ' := Set.projIcc_of_mem hT hτ
    simpa only [x, xdot, A, f, T, hproj,
      reverseTimeGalerkinPrimalCoordinate] using (hspec.2.2.2.2.1 τ').1
  have hrows : ∀ τ : Set.Icc 0 T,
      ∀ i : Fin (Module.finrank ℝ (galerkinSpace hΩ N)),
        inner ℝ
            (valueCLM hΩ (galerkinReconstruct hΩ N (xdot τ.1) :
              H10HilbertGraph hΩ))
            (valueCLM hΩ (galerkinSpaceBasis hΩ N i : H10HilbertGraph hΩ)) +
          reverseTimeSpatialForm hΩ r₁ τ.1 a b c
            (galerkinReconstruct hΩ N (x τ.1) : H10HilbertGraph hΩ)
            (galerkinSpaceBasis hΩ N i : H10HilbertGraph hΩ) =
          reverseTimeGalerkinSource r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth N
            ⟨τ.1, by simpa only [T] using τ.2⟩ i := by
    intro τ i
    let τ' : Set.Icc 0 (r₁ - r₀) := ⟨τ.1, by simpa only [T] using τ.2⟩
    have hproj : Set.projIcc 0 T hT τ.1 = τ' := Set.projIcc_of_mem hT τ.2
    have hu := hspec.2.1
    simpa only [x, xdot, A, f, T, hproj,
      reverseTimeGalerkinPrimalCoordinate, hu] using
      (hspec.2.2.2.2.1 τ').2 i
  simpa only [reverseTimeGalerkinPrimalRaw, x] using
    (reverseTimeGalerkin_compactTime_identity_of_basisRows r₀ r₁ h₀₁ hΩ hΩbounded
      a b c F haSmooth hbSmooth hcSmooth hFSmooth N x xdot hx hderiv hrows v eta)

end HypoellipticAleksandrov.Parabolic.Dirichlet

