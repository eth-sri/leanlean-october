module

public import HypoellipticAleksandrov.Parabolic.Dirichlet.ReverseTimeGalerkinPrimalResidualDerivative
public import HypoellipticAleksandrov.Parabolic.Dirichlet.TimeHilbertBoundaryPairing
public import HypoellipticAleksandrov.Parabolic.Dirichlet.ReverseTimeGalerkinPrimalBoundaryTime
public import HypoellipticAleksandrov.Parabolic.Dirichlet.ReverseTimeGalerkinPrimalBochner
public import HypoellipticAleksandrov.Parabolic.Dirichlet.ReverseTimeGelfandPairing
public import HypoellipticAleksandrov.Parabolic.Dirichlet.ReverseTimeSeparatedMultiplier
import Batteries.Tactic.Alias
import Batteries.Tactic.OpenPrivate
import all HypoellipticAleksandrov.Parabolic.Dirichlet.ReverseTimeGalerkinPrimalResidualDerivative

open private HypoellipticAleksandrov.Parabolic.Dirichlet.reverseTimeDualPairingRightCLM_sub from HypoellipticAleksandrov.Parabolic.Dirichlet.ReverseTimeGalerkinPrimalResidualDerivative


/-!
# Canonical initial trace of the reverse-time Galerkin limit

This module transfers the finite projected initial datum through the common
Galerkin subsequence to the canonical Gelfand initial trace.  The affine time
multiplier is deliberately handled here as a bounded Bochner multiplier: it
does not vanish at the initial endpoint and is therefore not a scalar test.
-/

@[expose] public section

open Filter MeasureTheory Set Topology
open scoped ENNReal Matrix Matrix.Norms.Elementwise MatrixOrder RealInnerProductSpace

noncomputable section

namespace HypoellipticAleksandrov.Parabolic.Dirichlet

variable (T : ℝ)

private def affineReverseTimeMultiplier  : ℝ → ℝ := fun tau => 1 - tau / T

private def affineReverseTimeDerivative  : ℝ → ℝ := fun _tau => -(T⁻¹)

variable {T : ℝ}

private theorem memLp_affine_reverseTime_multiplier  (hT : 0 < T) :
    MemLp (affineReverseTimeMultiplier T) (∞ ) (reverseTimeVolume T) := by
  letI : IsFiniteMeasure (reverseTimeVolume T) := by
    change IsFiniteMeasure (volume.restrict (Ioo (0 : ℝ) T))
    infer_instance
  apply memLp_of_bounded (a := 0) (b := 1) ?_ ?_ _
  · filter_upwards [ae_restrict_mem measurableSet_Ioo] with tau ht
    change 1 - tau / T ∈ Icc 0 1
    have hquotient_nonneg  := le_of_lt (div_pos ht.1 hT)
    have hquotient_le_one  := (div_le_one₀ hT).2 ht.2.le
    constructor <;> linarith
  · exact (continuous_const.sub (continuous_id.div_const T)).aestronglyMeasurable

private theorem memLp_affine_reverseTime_deriv  (_hT : 0 < T) :
    MemLp (affineReverseTimeDerivative T) (∞ ) (reverseTimeVolume T) := by
  letI : IsFiniteMeasure (reverseTimeVolume T) := by
    change IsFiniteMeasure (volume.restrict (Ioo (0 : ℝ) T))
    infer_instance
  exact memLp_const _

variable {d : ℕ} {Ω : PDE.VelocityRegion d}

section
variable (hΩ : IsOpen Ω) (T : ℝ) (hT : 0 < T) (v : H10HilbertGraph hΩ)

private def affineReverseTimeVTest
      : ReverseTimeL2V hΩ T :=
  reverseTimeSeparatedVTestOfMemLp hΩ _
    (memLp_affine_reverseTime_multiplier hT) v

private def affineReverseTimeDerivativeVTest
      : ReverseTimeL2V hΩ T :=
  reverseTimeSeparatedVTestOfMemLp hΩ _
    (memLp_affine_reverseTime_deriv hT) v
end


private theorem reverseTimeDualPairingRightCLM_ofMemLp_eq_integral
     {T : ℝ}
    (hΩ : IsOpen Ω) (g : ReverseTimeL2VStar hΩ T)
    (q : ℝ → ℝ) (hq : MemLp q (∞ ) (reverseTimeVolume T))
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

section
variable (r₀ r₁ : ℝ) (h₀₁ : r₀ < r₁) (hΩ : IsOpen Ω) (hΩbounded : Bornology.IsBounded Ω)

private theorem reverseTimeNegativeSource_pairing_ofMemLp_eq_integral_raw


    (F : PDE.TimeScalarField d)
    (hFSmooth : IsSmoothOnNeighborhood
      (fun z : TimeVelocity d => F z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (q : ℝ → ℝ) (hq : MemLp q (∞ ) (reverseTimeVolume (r₁ - r₀)))
    (v : H10HilbertGraph hΩ) :
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

private theorem reverseTimeSpatialForm_pairing_ofMemLp_eq_integral


    (a : CoefficientField d)
    (b : PDE.TimeVectorField d) (c : PDE.TimeScalarField d)
    (haSmooth : IsSmoothOnNeighborhood
      (fun z : TimeVelocity d => a z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hbSmooth : IsSmoothOnNeighborhood
      (fun z : TimeVelocity d => b z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hcSmooth : IsSmoothOnNeighborhood
      (fun z : TimeVelocity d => c z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (u : ReverseTimeL2V hΩ (r₁ - r₀))
    (q : ℝ → ℝ) (hq : MemLp q (∞ ) (reverseTimeVolume (r₁ - r₀)))
    (v : H10HilbertGraph hΩ) :
    reverseTimeDualPairingRightCLM hΩ (r₁ - r₀)
        (reverseTimeSeparatedVTestOfMemLp hΩ q hq v)
        (reverseTimeSpatialFormBochnerAction r₀ r₁ h₀₁ hΩ hΩbounded a b c
          haSmooth hbSmooth hcSmooth u) =
      ∫ tau, reverseTimeSpatialForm hΩ r₁ tau a b c (u tau) v * q tau
        ∂reverseTimeVolume (r₁ - r₀) := (Trans.trans
  (reverseTimeDualPairingRightCLM_ofMemLp_eq_integral hΩ
    ((reverseTimeSpatialFormBochnerAction r₀ r₁ h₀₁ hΩ hΩbounded a b c haSmooth hbSmooth hcSmooth) u) q hq v)
  (integral_congr_ae
    (mp_mem (ae_reverseTimeSpatialFormBochnerAction_apply r₀ r₁ h₀₁ hΩ hΩbounded a b c haSmooth hbSmooth hcSmooth u)
      (univ_mem' (id fun tau hA => congrArg (fun s => s * q tau) (hA v))))))

private theorem integrable_source_raw_mul_multiplier


    (F : PDE.TimeScalarField d)
    (hFSmooth : IsSmoothOnNeighborhood
      (fun z : TimeVelocity d => F z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (q : ℝ → ℝ) (hq : MemLp q (∞ ) (reverseTimeVolume (r₁ - r₀)))
    (v : H10HilbertGraph hΩ) :
    Integrable (fun tau =>
      reverseTimeNegativeSourceRaw r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth tau v * q tau)
      (reverseTimeVolume (r₁ - r₀)) := by


  refine (integrable_reverseTimeDualPairing hΩ (r₁ - r₀) (reverseTimeSeparatedVTestOfMemLp hΩ q hq v) (reverseTimeNegativeSource r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth)).congr ?_
  filter_upwards [(memLp_reverseTimeNegativeSourceRaw r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth).coeFn_toLp,
    ae_reverseTimeSeparatedVTestOfMemLp hΩ q hq v] with tau hS hz
  rw [hz, ContinuousLinearMap.map_smul]
  change q tau *
      ((memLp_reverseTimeNegativeSourceRaw r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth).toLp
        (reverseTimeNegativeSourceRaw r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth) tau) v = _
  rw [hS]
  ring

include h₀₁ hΩbounded in
private theorem integrable_form_raw_mul_multiplier


    (a : CoefficientField d)
    (b : PDE.TimeVectorField d) (c : PDE.TimeScalarField d)
    (haSmooth : IsSmoothOnNeighborhood
      (fun z : TimeVelocity d => a z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hbSmooth : IsSmoothOnNeighborhood
      (fun z : TimeVelocity d => b z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hcSmooth : IsSmoothOnNeighborhood
      (fun z : TimeVelocity d => c z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (u : ReverseTimeL2V hΩ (r₁ - r₀))
    (q : ℝ → ℝ) (hq : MemLp q (∞ ) (reverseTimeVolume (r₁ - r₀)))
    (v : H10HilbertGraph hΩ) :
    Integrable (fun tau => reverseTimeSpatialForm hΩ r₁ tau a b c (u tau) v * q tau)
      (reverseTimeVolume (r₁ - r₀)) := by
  let A := reverseTimeSpatialFormBochnerAction r₀ r₁ h₀₁ hΩ hΩbounded a b c
    haSmooth hbSmooth hcSmooth u

  refine (integrable_reverseTimeDualPairing hΩ (r₁ - r₀) (reverseTimeSeparatedVTestOfMemLp hΩ q hq v) A).congr ?_
  filter_upwards [ae_reverseTimeSpatialFormBochnerAction_apply r₀ r₁ h₀₁ hΩ hΩbounded
    a b c haSmooth hbSmooth hcSmooth u, ae_reverseTimeSeparatedVTestOfMemLp hΩ q hq v]
    with tau hA hz
  rw [hz, ContinuousLinearMap.map_smul]
  change q tau * A tau v = _
  rw [hA v]
  ring
end


section
variable (hΩ : IsOpen Ω)

section
variable (T : ℝ) (hT : 0 < T)

variable (u : ReverseTimeL2V hΩ T)

private theorem canonical_affine_mass_eq_gelfand_mass


     (g : ReverseTimeL2VStar hΩ T)
    (hdu : HasGelfandWeakTimeDerivative hΩ T hT u g)
    (v : H10HilbertGraph hΩ)
    (qDeriv : ℝ → ℝ) (hqDeriv : MemLp qDeriv (∞ ) (reverseTimeVolume T)) :
    (∫ tau, inner ℝ (valueCLM hΩ v)
      (Set.IccExtend hT.le (reverseTimeHilbertRepresentative hΩ T hT u g hdu) tau) * qDeriv tau
      ∂reverseTimeVolume T) =
      reverseTimeDualPairingRightCLM hΩ T
        (reverseTimeSeparatedVTestOfMemLp hΩ qDeriv hqDeriv v)
        (reverseTimeGelfandCLM hΩ T u) := by


  calc
    (∫ tau, inner ℝ (valueCLM hΩ v)
      (Set.IccExtend hT.le (reverseTimeHilbertRepresentative hΩ T hT u g hdu) tau) * qDeriv tau
      ∂reverseTimeVolume T) =
        ∫ tau, inner ℝ (valueCLM hΩ v) (valueCLM hΩ (u tau)) * qDeriv tau
          ∂reverseTimeVolume T := integral_congr_ae (by
              filter_upwards [((reverseTimeHilbertRepresentative_spec hΩ T hT u g hdu).1), ae_restrict_mem measurableSet_Ioo] with tau hrepTau ht

              rw [Set.IccExtend_of_mem hT.le _ (⟨le_of_lt ht.1, le_of_lt ht.2⟩), hrepTau ht])
    _ = _ := (reverseTimeGelfand_pairing_multiplier_eq_integral hΩ u qDeriv hqDeriv v).symm

private def affineReverseTimeMassPairing


     (v : H10HilbertGraph hΩ) : ℝ :=
  reverseTimeDualPairingRightCLM hΩ T
    (affineReverseTimeDerivativeVTest hΩ T hT v)
    (reverseTimeGelfandCLM hΩ T u)

private def affineReverseTimeSourcePairing


    (S : ReverseTimeL2VStar hΩ T) (v : H10HilbertGraph hΩ) : ℝ :=
  reverseTimeDualPairingRightCLM hΩ T
    (affineReverseTimeVTest hΩ T hT v) S

private def affineReverseTimeFormPairing


    (A : ReverseTimeL2V hΩ T →L[ℝ] ReverseTimeL2VStar hΩ T)
    (u : ReverseTimeL2V hΩ T) (v : H10HilbertGraph hΩ) : ℝ :=
  reverseTimeDualPairingRightCLM hΩ T
    (affineReverseTimeVTest hΩ T hT v) (A u)
end


private def affineReverseTimeInitialPairing

     (v : H10HilbertGraph hΩ)
    (initial : PDE.ScalarLp Ω (2 )) : ℝ :=
  inner ℝ (valueCLM hΩ v) initial

private def affineReverseTimeResidualPairing

     (T : ℝ) (hT : 0 < T)
    (g : ReverseTimeL2VStar hΩ T) (v : H10HilbertGraph hΩ) : ℝ :=
  reverseTimeDualPairingRightCLM hΩ T (affineReverseTimeVTest hΩ T hT v) g
end


private theorem neg_add_sub_of_pairing_eq
    (source sourceRaw form formRaw initial : ℝ)
    (hSource : source = sourceRaw) (hForm : form = formRaw) :
    -sourceRaw + formRaw - initial = -source + form - initial := by
  rw [← hSource, ← hForm]

variable {d : ℕ} {Ω : PDE.VelocityRegion d}

section
variable (hΩ : IsOpen Ω) (T : ℝ)

private alias reverseTimeDualPairingRightCLM_sub := _root_.HypoellipticAleksandrov.Parabolic.Dirichlet.reverseTimeDualPairingRightCLM_sub


private theorem reverseTimeHilbertRepresentative_affine_initial_pairing_wrapped

     (hT : 0 < T)
    (u : ReverseTimeL2V hΩ T) (g : ReverseTimeL2VStar hΩ T)
    (hdu : HasGelfandWeakTimeDerivative hΩ T hT u g)
    (v : H10HilbertGraph hΩ) :
    (∫ tau, inner ℝ (valueCLM hΩ v)
        (Set.IccExtend hT.le (reverseTimeHilbertRepresentative hΩ T hT u g hdu) tau) *
          affineReverseTimeDerivative T tau ∂reverseTimeVolume T) =
      -affineReverseTimeResidualPairing hΩ T hT g v -
        affineReverseTimeInitialPairing hΩ v
          (reverseTimeInitialTrace hΩ T hT u g hdu) := by
  let sharedTerm_835d748c38 := (inner ℝ (valueCLM hΩ v) (reverseTimeInitialTrace hΩ T hT u g hdu))

  have hPair := reverseTimeDualPairingRightCLM_ofMemLp_eq_integral hΩ g
    _ (memLp_affine_reverseTime_multiplier hT) v
  calc
    _ = -(∫ tau, g tau v * affineReverseTimeMultiplier T tau ∂reverseTimeVolume T) -
          sharedTerm_835d748c38 := (reverseTimeHilbertRepresentative_affine_initial_pairing hΩ T hT u g hdu v)
    _ = -reverseTimeDualPairingRightCLM hΩ T
          (reverseTimeSeparatedVTestOfMemLp hΩ _
            (memLp_affine_reverseTime_multiplier hT) v) g -
          sharedTerm_835d748c38 := by
          rw [← hPair]
    _ = _ := rfl
end




private theorem finite_affine_boundary_pairing_wrapped

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
      z ∈ scalarParabolicClosedCylinder r₀ r₁ Ω → lam • (1 : PDE.Mat d) ≤ a z.1 z.2)
    (hcNonpos : ∀ z : TimeVelocity d,
      z ∈ scalarParabolicClosedCylinder r₀ r₁ Ω → c z.1 z.2 ≤ 0)
    (initial : PDE.ScalarLp Ω (2 )) (N k : ℕ) (hNk : k + 1 ≤ N) :
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
        affineReverseTimeInitialPairing hΩ (galerkinVector hΩ k) initial := by
  let sharedTerm_ec782f7400 := ((valueCLM hΩ (galerkinVector hΩ k)))
  let sharedTerm_d1a6e96cba := ((valueCLM hΩ (galerkinInitialProjection hΩ N initial : H10HilbertGraph hΩ)))
  let sharedTerm_7166759c7a := (galerkinVector hΩ k ∈ Submodule.span ℝ (Set.range fun i : Fin (k + 1) => galerkinVector hΩ i))
  let T := r₁ - r₀
  let eta := affineReverseTimeMultiplier T
  let etaDeriv := affineReverseTimeDerivative T
  let hEta := memLp_affine_reverseTime_multiplier (sub_pos.mpr h₀₁)

  let S := reverseTimeNegativeSource r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth
  let A := reverseTimeSpatialFormBochnerAction r₀ r₁ h₀₁ hΩ hΩbounded a b c
    haSmooth hbSmooth hcSmooth
  let v : galerkinSpace hΩ N := ⟨galerkinVector hΩ k,
    galerkinSpace_mono hΩ hNk (by
      change sharedTerm_7166759c7a
      apply Submodule.subset_span
      exact ⟨⟨k, Nat.lt_succ_self k⟩, rfl⟩)⟩
  let vk : galerkinSpace hΩ (k + 1) := ⟨galerkinVector hΩ k, by
    change sharedTerm_7166759c7a
    apply Submodule.subset_span
    exact ⟨⟨k, Nat.lt_succ_self k⟩, rfl⟩⟩
  let UN := reverseTimeGalerkinPrimal r₀ r₁ lam h₀₁ hlam hΩ hΩbounded a b c F
    haSmooth hbSmooth hcSmooth hFSmooth hLower hcNonpos N initial
  change affineReverseTimeMassPairing hΩ T (sub_pos.mpr h₀₁) UN (galerkinVector hΩ k) =
    -affineReverseTimeSourcePairing hΩ T (sub_pos.mpr h₀₁) S (galerkinVector hΩ k) +
      affineReverseTimeFormPairing hΩ T (sub_pos.mpr h₀₁) A UN (galerkinVector hΩ k) -
      affineReverseTimeInitialPairing hΩ (galerkinVector hΩ k) initial



  obtain ⟨_hMass, _hResidual, hBoundary⟩ :=
    reverseTimeGalerkinPrimal_boundaryTime r₀ r₁ lam h₀₁ hlam hΩ hΩbounded a b c F
      haSmooth hbSmooth hcSmooth hFSmooth hLower hcNonpos N initial v eta etaDeriv
      ((by
          intro tau _
          dsimp only [eta, etaDeriv]
          unfold affineReverseTimeMultiplier affineReverseTimeDerivative
          simpa only [div_eq_mul_inv, zero_sub, one_mul, Pi.sub_def, id_eq] using
            (hasDerivAt_const (x := tau) (1 : ℝ)).sub
              ((hasDerivAt_id (x := tau)).mul_const T⁻¹) |>.hasDerivWithinAt)) continuousOn_const
      ((by
          dsimp only [eta, affineReverseTimeMultiplier]
          rw [div_self (show 0 < T by
              exact sub_pos.mpr h₀₁).ne']
          ring))
  have hUNraw := ae_reverseTimeGalerkinPrimal_eq_raw r₀ r₁ lam h₀₁ hlam hΩ hΩbounded a b c F
    haSmooth hbSmooth hcSmooth hFSmooth hLower hcNonpos N initial

  have hSource := reverseTimeNegativeSource_pairing_ofMemLp_eq_integral_raw
    r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth eta hEta (galerkinVector hΩ k)
  have hForm := reverseTimeSpatialForm_pairing_ofMemLp_eq_integral
    r₀ r₁ h₀₁ hΩ hΩbounded a b c haSmooth hbSmooth hcSmooth UN eta hEta
      (galerkinVector hΩ k)
  have hSourceInt := integrable_source_raw_mul_multiplier
    r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth eta hEta (galerkinVector hΩ k)
  have hFormInt := integrable_form_raw_mul_multiplier
    r₀ r₁ h₀₁ hΩ hΩbounded a b c haSmooth hbSmooth hcSmooth UN eta hEta
      (galerkinVector hΩ k)



  have hInitial' :
      inner ℝ sharedTerm_ec782f7400
        sharedTerm_d1a6e96cba =
      inner ℝ sharedTerm_ec782f7400 initial := by
    simpa only [vk] using (inner_value_galerkinInitialProjection_eq hΩ hNk initial vk)

  calc
    affineReverseTimeMassPairing hΩ T (sub_pos.mpr h₀₁) UN (galerkinVector hΩ k) =
        ∫ tau, inner ℝ sharedTerm_ec782f7400
          (valueCLM hΩ
            (reverseTimeGalerkinPrimalRaw r₀ r₁ lam h₀₁ hlam hΩ hΩbounded a b c F
              haSmooth hbSmooth hcSmooth hFSmooth hLower hcNonpos N initial tau)) * etaDeriv tau
          ∂reverseTimeVolume T := (by
              calc
                _ = ∫ tau, inner ℝ sharedTerm_ec782f7400 (valueCLM hΩ (UN tau)) *
                    etaDeriv tau ∂reverseTimeVolume T :=
                  reverseTimeGelfand_pairing_multiplier_eq_integral hΩ UN etaDeriv (memLp_affine_reverseTime_deriv (sub_pos.mpr h₀₁))
                    _
                _ = _ := by
                  apply integral_congr_ae
                  filter_upwards [hUNraw] with tau hUNtau
                  rw [hUNtau])
    _ = -(∫ tau, reverseTimeNegativeSourceRaw r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth tau
          (galerkinVector hΩ k) * eta tau ∂reverseTimeVolume T) +
        ∫ tau, reverseTimeSpatialForm hΩ r₁ tau a b c (UN tau) (galerkinVector hΩ k) * eta tau
          ∂reverseTimeVolume T - inner ℝ sharedTerm_ec782f7400 initial := (by
              calc
                _ = -(∫ tau,
                    (reverseTimeNegativeSourceRaw r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth tau
                      (galerkinVector hΩ k) -
                    reverseTimeSpatialForm hΩ r₁ tau a b c
                      (reverseTimeGalerkinPrimalRaw r₀ r₁ lam h₀₁ hlam hΩ hΩbounded a b c F
                        haSmooth hbSmooth hcSmooth hFSmooth hLower hcNonpos N initial tau)
                      (galerkinVector hΩ k)) * eta tau ∂reverseTimeVolume T) -
                    inner ℝ sharedTerm_ec782f7400
                      sharedTerm_d1a6e96cba *
                        eta 0 := (id hBoundary)
                _ = -(∫ tau, reverseTimeNegativeSourceRaw r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth tau
                    (galerkinVector hΩ k) * eta tau -
                    reverseTimeSpatialForm hΩ r₁ tau a b c (UN tau) (galerkinVector hΩ k) * eta tau
                      ∂reverseTimeVolume T) -
                    inner ℝ sharedTerm_ec782f7400
                      sharedTerm_d1a6e96cba *
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
                    inner ℝ sharedTerm_ec782f7400 initial := by
                    rw [integral_sub hSourceInt hFormInt]
                    rw [hInitial']
                    dsimp only [eta, affineReverseTimeMultiplier]
                    ring
                _ = _ := by ring)
    _ = -affineReverseTimeSourcePairing hΩ T (sub_pos.mpr h₀₁) S (galerkinVector hΩ k) +
        affineReverseTimeFormPairing hΩ T (sub_pos.mpr h₀₁) A UN (galerkinVector hΩ k) -
        affineReverseTimeInitialPairing hΩ (galerkinVector hΩ k) initial := neg_add_sub_of_pairing_eq _ _ _ _ _ (by
            change reverseTimeDualPairingRightCLM hΩ T
                (affineReverseTimeVTest hΩ T (sub_pos.mpr h₀₁) (galerkinVector hΩ k)) S = _
            simpa only [T, eta, hEta, affineReverseTimeVTest] using hSource) (by
            change reverseTimeDualPairingRightCLM hΩ T
                (affineReverseTimeVTest hΩ T (sub_pos.mpr h₀₁) (galerkinVector hΩ k)) (A UN) = _
            simpa only [T, eta, hEta, affineReverseTimeVTest] using hForm)


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
    z ∈ scalarParabolicClosedCylinder r₀ r₁ Ω → lam • (1 : PDE.Mat d) ≤ a z.1 z.2)
  (hcNonpos : ∀ z : TimeVelocity d,
    z ∈ scalarParabolicClosedCylinder r₀ r₁ Ω → c z.1 z.2 ≤ 0)

include lam hlam hLower hcNonpos

variable (initial : PDE.ScalarLp Ω (2 ))

private theorem reverseTimeGalerkinPrimal_initialTrace_pairing

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
      inner ℝ (valueCLM hΩ (galerkinVector hΩ k)) initial := by
  let sharedTerm_a280ab2f6f := ((valueCLM hΩ (galerkinVector hΩ k)))
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
  change inner ℝ sharedTerm_a280ab2f6f trace =
    inner ℝ sharedTerm_a280ab2f6f initial
  let massEll : ReverseTimeL2V hΩ T →L[ℝ] ℝ :=
    (reverseTimeDualPairingRightCLM hΩ T
      (reverseTimeSeparatedVTestOfMemLp hΩ etaDeriv hEtaDeriv (galerkinVector hΩ k))).comp
      (reverseTimeGelfandCLM hΩ T)
  let formEll : ReverseTimeL2V hΩ T →L[ℝ] ℝ :=
    (reverseTimeDualPairingRightCLM hΩ T
      (reverseTimeSeparatedVTestOfMemLp hΩ eta hEta (galerkinVector hΩ k))).comp A
  let source : ℝ := reverseTimeDualPairingRightCLM hΩ T
    (reverseTimeSeparatedVTestOfMemLp hΩ eta hEta (galerkinVector hΩ k)) S





  have hLimit : massEll U = -source + formEll U -
      inner ℝ sharedTerm_a280ab2f6f initial :=
    tendsto_nhds_unique_of_eventuallyEq (hclm massEll) (((tendsto_const_nhds.neg.add (hclm formEll)).sub tendsto_const_nhds)) (by
        filter_upwards [(by
            filter_upwards [eventually_ge_atTop (k + 1)] with n hn
            exact hn.trans (hphi.id_le n))] with n hn
        simpa only [massEll, formEll, source, ContinuousLinearMap.comp_apply, T, eta, etaDeriv,
          hEta, hEtaDeriv, S, A, affineReverseTimeMassPairing,
          affineReverseTimeSourcePairing, affineReverseTimeFormPairing,
          affineReverseTimeInitialPairing, affineReverseTimeVTest,
          affineReverseTimeDerivativeVTest] using
            finite_affine_boundary_pairing_wrapped r₀ r₁ lam h₀₁ hlam hΩ hΩbounded a b c F
              haSmooth hbSmooth hcSmooth hFSmooth hLower hcNonpos initial (phi n) k hn)
  have hResidual : reverseTimeDualPairingRightCLM hΩ T
      (reverseTimeSeparatedVTestOfMemLp hΩ eta hEta (galerkinVector hΩ k)) g =
      source - formEll U := by
    exact _root_.HypoellipticAleksandrov.Parabolic.Dirichlet.reverseTimeDualPairingRightCLM_sub hΩ T
      _ S (A U)

  have hCanonical := canonical_affine_mass_eq_gelfand_mass hΩ T (sub_pos.mpr h₀₁) U g hdu
    (galerkinVector hΩ k) etaDeriv hEtaDeriv
  have hTrace : massEll U =
      -affineReverseTimeResidualPairing hΩ T (sub_pos.mpr h₀₁) g (galerkinVector hΩ k) -
      affineReverseTimeInitialPairing hΩ (galerkinVector hΩ k) trace := by
    calc
      massEll U =
          (∫ tau, inner ℝ sharedTerm_a280ab2f6f
            (Set.IccExtend (sub_pos.mpr h₀₁).le
              (reverseTimeHilbertRepresentative hΩ T (sub_pos.mpr h₀₁) U g hdu) tau) *
              etaDeriv tau ∂reverseTimeVolume T) := hCanonical.symm
      _ = -affineReverseTimeResidualPairing hΩ T (sub_pos.mpr h₀₁) g (galerkinVector hΩ k) -
            affineReverseTimeInitialPairing hΩ (galerkinVector hΩ k) trace := by
            solve_by_elim (maxDepth := 4) [@_root_.HypoellipticAleksandrov.Parabolic.Dirichlet.reverseTimeHilbertRepresentative_affine_initial_pairing_wrapped]
  dsimp only [massEll, formEll, source, affineReverseTimeResidualPairing,
    affineReverseTimeInitialPairing, affineReverseTimeVTest, eta, hEta,
    affineReverseTimeMultiplier] at hLimit hTrace hResidual
  linarith


/-- A reverse-time Galerkin limit has the prescribed canonical initial trace. -/
theorem exists_reverseTimeGalerkinPrimal_initialTrace
     :
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

  obtain ⟨vN, hvN, hv⟩ := mem_closure_iff_seq_limit.mp (show v ∈ closure (Set.range (galerkinVector hΩ)) by
      rw [(denseRange_galerkinVector hΩ).closure_range]
      exact mem_univ _)
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
  have hRight  :=
    (scalarLpToH10HilbertGraphDual hΩ initial).continuous.tendsto v |>.comp hv

  exact tendsto_nhds_unique_of_eventuallyEq hLeft hRight (Eventually.of_forall (show ∀ n,
      scalarLpToH10HilbertGraphDual hΩ trace (vN n) =
        scalarLpToH10HilbertGraphDual hΩ initial (vN n) by
      intro n
      simpa only [scalarLpToH10HilbertGraphDual_apply, hk n] using hPair (k n)))


/-- A supplied common reverse-time Galerkin subsequence has the prescribed
canonical initial trace. -/
theorem reverseTimeGalerkinPrimal_initialTrace_of_strictMono_tendsto_clm

    (U : ReverseTimeL2V hΩ (r₁ - r₀))
    (phi : ℕ → ℕ) (hphi : StrictMono phi)
    (hclm : ∀ ell : ReverseTimeL2V hΩ (r₁ - r₀) →L[ℝ] ℝ,
      Tendsto (fun n => ell
        (reverseTimeGalerkinPrimal r₀ r₁ lam h₀₁ hlam hΩ hΩbounded a b c F
          haSmooth hbSmooth hcSmooth hFSmooth hLower hcNonpos (phi n) initial))
        atTop (𝓝 (ell U)))
    (hdu : HasGelfandWeakTimeDerivative hΩ (r₁ - r₀) (sub_pos.mpr h₀₁) U
      (reverseTimeFormResidual r₀ r₁ h₀₁ hΩ hΩbounded a b c
        haSmooth hbSmooth hcSmooth F hFSmooth U)) :
    reverseTimeInitialTrace hΩ (r₁ - r₀) (sub_pos.mpr h₀₁) U
      (reverseTimeFormResidual r₀ r₁ h₀₁ hΩ hΩbounded a b c
        haSmooth hbSmooth hcSmooth F hFSmooth U) hdu = initial := by
  let T := r₁ - r₀
  let g := reverseTimeFormResidual r₀ r₁ h₀₁ hΩ hΩbounded a b c
    haSmooth hbSmooth hcSmooth F hFSmooth U
  let trace := reverseTimeInitialTrace hΩ T (sub_pos.mpr h₀₁) U g hdu
  apply scalarLpToH10HilbertGraphDual_injective hΩ
  apply ContinuousLinearMap.ext
  intro v

  obtain ⟨vN, hvN, hv⟩ := mem_closure_iff_seq_limit.mp (show v ∈ closure (Set.range (galerkinVector hΩ)) by
      rw [(denseRange_galerkinVector hΩ).closure_range]
      exact mem_univ _)
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
  have hRight  :=
    (scalarLpToH10HilbertGraphDual hΩ initial).continuous.tendsto v |>.comp hv

  exact tendsto_nhds_unique_of_eventuallyEq hLeft hRight (Eventually.of_forall (show ∀ n,
      scalarLpToH10HilbertGraphDual hΩ trace (vN n) =
        scalarLpToH10HilbertGraphDual hΩ initial (vN n) by
      intro n
      simpa only [scalarLpToH10HilbertGraphDual_apply, hk n] using hPair (k n)))

end HypoellipticAleksandrov.Parabolic.Dirichlet
