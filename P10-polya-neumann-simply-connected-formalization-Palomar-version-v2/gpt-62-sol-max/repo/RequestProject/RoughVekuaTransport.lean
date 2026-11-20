module

public import RequestProject.RoughNormalizedPrimitive
public import RequestProject.PhysicalDrivenIntegrable
public import RequestProject.PhysicalDrivenHardyRegularity
public import RequestProject.ObservationLp

/-!
# A true regular correction for the rough driven equation

The mean-zero primitive is an actual BoundaryL2 element. Subtracting its
zeroth coordinate leaves an ordinary L2-forced Banach ODE, whose correction
is constructed by the genuine transport and Bochner primitive. Thus its
positive coordinates are absolutely continuous without taking an endpoint
value of the original half-order primitive.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace PolyaNeumann

open MeasureTheory Set Filter Metric
open scoped InnerProductSpace ComplexConjugate Topology

local notation "μB" => volume.restrict (Ioc (0 : ℝ) (2 * Real.pi))

local notation "L" => (2 * Real.pi)
local notation "J" => Icc (0 : ℝ) L
local notation "κ" => -(Complex.I / (Real.sqrt 2 : ℂ))

private theorem boundary_smul_intervalIntegrable (p : BoundaryL2) {k : ℝ → Ell2}
    (hk : ContinuousOn k J) : IntervalIntegrable (fun θ => p θ • k θ) volume 0 L := by
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le Real.two_pi_pos.le]
  exact ((intervalIntegrable_iff_integrableOn_Icc_of_le Real.two_pi_pos.le).mp
    (intervalIntegrable_boundaryL2 p)).smul_continuousOn hk isCompact_Icc

def roughNormalizedMean : L2Z →L[ℂ] ℂ :=
  ((Real.sqrt (2 * Real.pi) : ℂ)⁻¹) • innerSL ℂ (stdBasisZ 0)

theorem roughNormalizedMean_apply (y : L2Z) :
    roughNormalizedMean y = y 0 / (Real.sqrt (2 * Real.pi) : ℂ) := by
  have h : ⟪stdBasisZ 0, y⟫_ℂ = y 0 := by
    rw [stdBasisZ_apply, lp.inner_single_left]
    simp
  simp only [roughNormalizedMean, ContinuousLinearMap.smul_apply, innerSL_apply_apply,
    h]
  ring

/-- True ordinary L2 forcing after the rough primitive is removed. -/
def roughVekuaRegularForce (γ : ℝ → ℂ) (E : ℝ) (p : BoundaryL2) (m : ℂ) (θ : ℝ) : Ell2 :=
  p θ • transportCoeff γ E θ (basisVec 0) + m • basisVec 0

section

variable (γ : ℝ → ℂ) (E : ℝ) (W : ℝ → Ell2 →L[ℂ] Ell2) (p : BoundaryL2) (m α : ℂ) (θ : ℝ)
include γ E W p m α θ

/-- The genuine correction; no endpoint of p occurs in this definition. -/
def roughVekuaRegularCorrection  : Ell2 :=
  transportResponse W (α • basisVec 0) κ (roughVekuaRegularForce γ E p m) θ

/-- Only coordinate zero contains the rough L2 primitive. -/
def roughVekuaDrivenVector  : Ell2 :=
  (-(Complex.I / (Real.sqrt 2 : ℂ)) * p θ) • basisVec 0 +
    roughVekuaRegularCorrection γ E W p m α θ

end

section GenuineTransport

variable {γ : ℝ → ℂ} {K : NNReal} (hK : LipschitzWith K γ)
    (hγ : ContDiff ℝ 1 γ) {E : ℝ} {W : ℝ → Ell2 →L[ℂ] Ell2}
    (hW : IsTransport γ E W)

include hγ in
private theorem roughForce_intervalIntegrable (p : BoundaryL2) (m : ℂ) :
    IntervalIntegrable (roughVekuaRegularForce γ E p m) volume 0 L :=
  (boundary_smul_intervalIntegrable p ((continuous_transportCoeff_of_contDiff hγ E).continuousOn.clm_apply
    continuousOn_const)).add intervalIntegrable_const

include hγ hW in
theorem roughVekuaRegularCorrection_continuousOn (p : BoundaryL2) (m α : ℂ) :
    ContinuousOn (roughVekuaRegularCorrection γ E W p m α) J :=
  transportResponse_continuousOn hW.1 _ _ (roughForce_intervalIntegrable hγ p m)

include hK hγ hW in
theorem roughVekuaRegularCorrection_absolutelyContinuous (p : BoundaryL2) (m α : ℂ) :
    AbsolutelyContinuousOnInterval (roughVekuaRegularCorrection γ E W p m α) 0 L :=
  transportResponse_absolutelyContinuous hK hW _ _ (roughForce_intervalIntegrable hγ p m)

include hK hγ hW in
theorem roughVekuaRegularCorrection_ae_hasDerivAt (p : BoundaryL2) (m α : ℂ) :
    ∀ᵐ θ, θ ∈ Ioo 0 L →
      HasDerivAt (roughVekuaRegularCorrection γ E W p m α)
        (transportCoeff γ E θ (roughVekuaRegularCorrection γ E W p m α θ) +
          κ • roughVekuaRegularForce γ E p m θ) θ :=
  transportResponse_ae_hasDerivAt hK hγ hW _ _ (roughForce_intervalIntegrable hγ p m)

include hγ hW in
private theorem rough_adjoint_transport_row_hasDerivAt {θ : ℝ}
    (hθ : θ ∈ Ioo 0 (2 * Real.pi)) :
    HasDerivAt (fun t => ContinuousLinearMap.adjoint (W t) (basisVec 0))
      (-(ContinuousLinearMap.adjoint (W θ)
        (transportCoeff γ E θ (basisVec 0)))) θ := by
  have hdW := hasDerivAt_transport_of_contDiff hγ hW hθ
  have hdA : HasDerivAt (fun t => ContinuousLinearMap.adjoint (W t))
      (-(ContinuousLinearMap.adjoint (W θ) * transportCoeff γ E θ)) θ := by
    have hs :=
      transportCoeff_star γ E θ
    have hstar := hdW.star
    rw [star_mul, hs] at hstar
    have h_simpa := hstar
    simp   at h_simpa ⊢
    assumption
  simpa only [ContinuousLinearMap.neg_apply, ContinuousLinearMap.mul_apply,
    map_zero, add_zero] using
    hasDerivAt_clm_apply_real hdA (hasDerivAt_const θ (basisVec 0))

/-- The actual derivative of the projected observation test. -/
def roughProjectedObservationDerivative (γ : ℝ → ℂ) (E : ℝ)
    (W : ℝ → Ell2 →L[ℂ] Ell2) (v : Ell2) (θ : ℝ) : ℂ :=
  -⟪ContinuousLinearMap.adjoint (W θ) (transportCoeff γ E θ (basisVec 0)),
    cutProj (cutC (W (2 * Real.pi)) (basisVec 0)) v⟫_ℂ

include hγ hW in
theorem roughProjectedObservation_hasDerivAt (v : Ell2) {θ : ℝ}
    (hθ : θ ∈ Ioo 0 (2 * Real.pi)) :
    HasDerivAt (fun t => ⟪projObsRow W t, v⟫_ℂ)
      (roughProjectedObservationDerivative γ E W v θ) θ := by
  let Q := cutProj (cutC (W (2 * Real.pi)) (basisVec 0))
  have hp := (Q.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt θ
    (rough_adjoint_transport_row_hasDerivAt hγ hW hθ)
  convert hp.inner ℂ (hasDerivAt_const θ v) using 1 <;>
    simp [projObsRow, roughProjectedObservationDerivative, Q, Function.comp_def,
      ContinuousLinearMap.coe_restrictScalars, map_neg, inner_zero_right,
      inner_neg_left, inner_cutProj_left, inner_conj_symm]

include hγ hW in
theorem roughProjectedObservationDerivative_memLp (v : Ell2) :
    MemLp (roughProjectedObservationDerivative γ E W v) 2 μB := by
  have hc : ContinuousOn (roughProjectedObservationDerivative γ E W v)
      (Icc 0 (2 * Real.pi)) :=
    ((ContinuousLinearMap.adjoint.continuous.comp_continuousOn hW.1).clm_apply
      ((continuous_transportCoeff_of_contDiff hγ E).continuousOn.clm_apply
        continuousOn_const)).inner continuousOn_const |>.neg
  exact hc.memLp_Ioc

include hK hW in
theorem roughProjectedObservation_absolutelyContinuous (v : Ell2) :
    AbsolutelyContinuousOnInterval (fun t => ⟪projObsRow W t, v⟫_ℂ)
      0 (2 * Real.pi) := by
  let M : NNReal := ⟨Real.sqrt E * shiftConst * K * ‖v‖, by
    exact mul_nonneg (mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) shiftConst_nonneg)
      K.coe_nonneg) (norm_nonneg _)⟩
  have hl : LipschitzOnWith M (fun t => ⟪projObsRow W t, v⟫_ℂ)
      (Icc 0 (2 * Real.pi)) := by
    apply LipschitzOnWith.of_dist_le_mul
    intro x hx y hy
    rw [dist_eq_norm, ← inner_sub_left]
    calc
      _ ≤ ‖projObsRow W x - projObsRow W y‖ * ‖v‖ := norm_inner_le_norm _ _
      _ ≤ (Real.sqrt E * shiftConst * K * |x - y|) * ‖v‖ :=
        mul_le_mul_of_nonneg_right (norm_projObsRow_sub_le hK hW hx hy) (norm_nonneg _)
      _ = M * dist x y := by
        rw [Real.dist_eq]
        change _ = (Real.sqrt E * shiftConst * K * ‖v‖) * |x - y|
        ring
  apply LipschitzOnWith.absolutelyContinuousOnInterval
  simpa only [uIcc_of_le Real.two_pi_pos.le] using hl

include hK hγ hW in
theorem boundaryFourier_projectedObservation_sobolev_one (v : Ell2) :
    IsSobolevSeq 1
      (boundaryFourier (projectedObservationBoundary hK hW v) : ℤ → ℂ) := by
  have hp : (⟪projObsRow W 0, v⟫_ℂ) = ⟪projObsRow W (2 * Real.pi), v⟫_ℂ := by
    rw [projObsRow_endpoint hW]
  have hr := isSobolevSeq_one_fourierCoeffOn_of_ac_ae_hasDerivAt
    (roughProjectedObservation_absolutelyContinuous hK hW v)
    (roughProjectedObservationDerivative_memLp hγ hW v)
    (Eventually.of_forall fun θ hθ => roughProjectedObservation_hasDerivAt hγ hW v hθ) hp
  have hcoef : (boundaryFourier (projectedObservationBoundary hK hW v) : ℤ → ℂ) =
      (Real.sqrt (2 * Real.pi) : ℂ) •
        fourierCoeffOn Real.two_pi_pos (fun θ => ⟪projObsRow W θ, v⟫_ℂ) := by
    funext n
    rw [boundaryFourier_apply,
      fourierCoeffOn_congr_ae Real.two_pi_pos (projectedObservationBoundary_coe hK hW v)]
    rfl
  rw [hcoef]
  exact isSobolevSeq_smul _ hr

include hK hγ hW in
theorem roughProjectedObservation_fourier_derivative (v : Ell2) :
    roughFourierTestDerivative
      (boundaryFourier (projectedObservationBoundary hK hW v))
      (boundaryFourier_projectedObservation_sobolev_one hK hγ hW v) =
    boundaryFourier ((roughProjectedObservationDerivative_memLp hγ hW v).toLp
      (roughProjectedObservationDerivative γ E W v)) := by
  apply lp.ext
  funext n
  rw [roughFourierTestDerivative_apply]
  simp only [boundaryFourier_apply]
  rw [fourierCoeffOn_congr_ae Real.two_pi_pos
      (roughProjectedObservationDerivative_memLp hγ hW v).coeFn_toLp,
    fourierCoeffOn_of_ac_ae_hasDerivAt
      (roughProjectedObservation_absolutelyContinuous hK hW v)
      (roughProjectedObservationDerivative_memLp hγ hW v)
      (Eventually.of_forall fun θ hθ => roughProjectedObservation_hasDerivAt hγ hW v hθ)
      (by rw [projObsRow_endpoint hW]),
    fourierCoeffOn_congr_ae Real.two_pi_pos (projectedObservationBoundary_coe hK hW v)]
  ring

include hγ hW in
theorem rough_endpoint_kernel_continuousOn :
    ContinuousOn (fun θ => ContinuousLinearMap.adjoint (W θ)
      (transportCoeff γ E θ (basisVec 0))) (Icc 0 (2 * Real.pi)) :=
  (ContinuousLinearMap.adjoint.continuous.comp_continuousOn hW.1).clm_apply
    ((continuous_transportCoeff_of_contDiff hγ E).continuousOn.clm_apply continuousOn_const)

/-- The endpoint source split into its primitive and mean parts. -/
def roughVekuaEndpointCore (γ : ℝ → ℂ) (E : ℝ) (W : ℝ → Ell2 →L[ℂ] Ell2) (y : L2Z) : Ell2 :=
  (∫ θ in (0 : ℝ)..L, roughNormalizedPrimitive y θ •
    (ContinuousLinearMap.adjoint (W θ)) (transportCoeff γ E θ (basisVec 0))) +
  roughNormalizedMean y • (∫ θ in (0 : ℝ)..L, (ContinuousLinearMap.adjoint (W θ)) (basisVec 0))

include hγ hW in
theorem roughVekuaEndpointCore_apply (y : L2Z) :
    roughVekuaEndpointCore γ E W y =
      ∫ θ in (0 : ℝ)..(2 * Real.pi), ContinuousLinearMap.adjoint (W θ)
        (roughVekuaRegularForce γ E (roughNormalizedPrimitive y) (roughNormalizedMean y) θ) := by
  have hk := rough_endpoint_kernel_continuousOn hγ hW
  have h0 := continuousOn_adjoint_apply hW.1 (basisVec 0)
  have hi0 : IntervalIntegrable (fun θ => roughNormalizedMean y •
      ContinuousLinearMap.adjoint (W θ) (basisVec 0)) volume 0 (2 * Real.pi) := by
    apply ContinuousOn.intervalIntegrable
    have h_simpa := h0.const_smul (roughNormalizedMean y)
    simp  [uIcc_of_le Real.two_pi_pos.le] at h_simpa ⊢
    assumption
  rw [roughVekuaEndpointCore, ← intervalIntegral.integral_smul, ← intervalIntegral.integral_add
    (boundary_smul_intervalIntegrable (roughNormalizedPrimitive y) hk) hi0]
  apply intervalIntegral.integral_congr
  intro θ _
  simp  [roughVekuaRegularForce, map_add, map_smul]

include hK hγ hW in
private theorem rough_projectedObservation_weightedFourier (v : Ell2) :
    sobVec (1 / 2 : ℝ)
      (boundaryFourier (projectedObservationBoundary hK hW v) : ℤ → ℂ)
      ((sobNormSq_mono (by norm_num : (1 / 2 : ℝ) ≤ 1)
        (boundaryFourier_projectedObservation_sobolev_one hK hγ hW v)).1) =
    (Real.sqrt (2 * Real.pi) : ℂ) •
      rowAnalysis (normProjObsRow W) (summable_normProjObsRow hK hW) v := by
  apply lp.ext
  funext n
  simp only [sobVec_apply, boundaryFourier_projectedObservation hK hW,
    lp.coeFn_smul, Pi.smul_apply, rowAnalysis_apply, normProjObsRow,
    inner_smul_left, Complex.conj_ofReal]
  rw [← Real.sqrt_eq_rpow]
  change (Real.sqrt (sobWeight n) : ℂ) *
      ((Real.sqrt (2 * Real.pi) : ℂ) * ⟪projObsCoeffVec W n, v⟫_ℂ) =
    (Real.sqrt (2 * Real.pi) : ℂ) *
      ((Real.sqrt (sobWeight n) : ℂ) * ⟪projObsCoeffVec W n, v⟫_ℂ)
  ring

include hK hγ hW in
private theorem rough_endpoint_mean_pairing (y : L2Z) (v : Ell2) :
    ⟪cutProj (cutC (W (2 * Real.pi)) (basisVec 0)) v,
      roughNormalizedMean y • (∫ θ in (0 : ℝ)..(2 * Real.pi),
        ContinuousLinearMap.adjoint (W θ) (basisVec 0))⟫_ℂ =
    ⟪sobVec (1 / 2 : ℝ)
      (boundaryFourier (projectedObservationBoundary hK hW v) : ℤ → ℂ)
      ((sobNormSq_mono (by norm_num : (1 / 2 : ℝ) ≤ 1)
        (boundaryFourier_projectedObservation_sobolev_one hK hγ hW v)).1),
      zeroModeProjection y⟫_ℂ := by
  have hi : IntervalIntegrable (fun θ => ContinuousLinearMap.adjoint (W θ) (basisVec 0))
      volume 0 (2 * Real.pi) := by
    apply ContinuousOn.intervalIntegrable
    simpa only [uIcc_of_le Real.two_pi_pos.le] using
      continuousOn_adjoint_apply hW.1 (basisVec 0)
  rw [inner_smul_right]
  have hcomp := ContinuousLinearMap.intervalIntegral_comp_comm
    (innerSL ℂ (cutProj (cutC (W (2 * Real.pi)) (basisVec 0)) v)) hi
  simp   at hcomp
  rw [← hcomp]
  simp only 
  have hinner (θ : ℝ) :
      ⟪cutProj (cutC (W (2 * Real.pi)) (basisVec 0)) v,
        ContinuousLinearMap.adjoint (W θ) (basisVec 0)⟫_ℂ =
      conj (⟪projObsRow W θ, v⟫_ℂ) := by
    rw [projObsRow]
    exact (inner_cutProj_left _ v _).trans (inner_conj_symm v _).symm
  simp_rw [hinner]
  rw [intervalIntegral.intervalIntegral_conj, zeroModeProjection_eq_single, lp.inner_single_right,
    RCLike.inner_apply']
  simp  [sobWeight, abs_zero, add_zero, Real.one_rpow,
    Complex.ofReal_one, one_mul]
  rw [boundaryFourier_apply,
    fourierCoeffOn_congr_ae Real.two_pi_pos (projectedObservationBoundary_coe hK hW v),
    fourierCoeffOn_eq_integral]
  simp only [neg_zero, fourier_zero, one_smul, sub_zero, Complex.real_smul,
    map_mul, Complex.conj_ofReal]
  rw [roughNormalizedMean_apply]
  have hs : (Real.sqrt (2 * Real.pi) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr Real.two_pi_pos).ne'
  have hT : ((2 * Real.pi : ℝ) : ℂ) ≠ 0 := by simp
  have hsq : (Real.sqrt (2 * Real.pi) : ℂ) ^ 2 = ((2 * Real.pi : ℝ) : ℂ) := by
    exact_mod_cast Real.sq_sqrt Real.two_pi_pos.le
  field_simp [hs, hT, Real.pi_ne_zero]
  rw [hsq]
  have hprod : ((Real.pi * 2 : ℝ) : ℂ) *
      ((Real.pi⁻¹ * (1 / 2) : ℝ) : ℂ) = 1 := by
    exact_mod_cast (by
      field_simp [Real.pi_ne_zero] :
        (Real.pi * 2) * (Real.pi⁻¹ * (1 / 2)) = (1 : ℝ))
  calc
    _ = (y 0) *
        (starRingEnd ℂ) (∫ (x : ℝ) in 0..Real.pi * 2,
          ⟪projObsRow W x, v⟫_ℂ) * 1 := by ring
    _ = (y 0) *
        (starRingEnd ℂ) (∫ (x : ℝ) in 0..Real.pi * 2,
          ⟪projObsRow W x, v⟫_ℂ) *
        (((Real.pi * 2 : ℝ) : ℂ) * ((Real.pi⁻¹ * (1 / 2) : ℝ) : ℂ)) := by tauto
    _ = _ := by ring

include hK hγ hW in
private theorem rough_endpoint_primitive_pairing (y : L2Z) (v : Ell2) :
    ⟪cutProj (cutC (W (2 * Real.pi)) (basisVec 0)) v,
      ∫ θ in (0 : ℝ)..L, roughNormalizedPrimitive y θ •
        (ContinuousLinearMap.adjoint (W θ)) (transportCoeff γ E θ (basisVec 0))⟫_ℂ =
    -⟪roughFourierTestDerivative
      (boundaryFourier (projectedObservationBoundary hK hW v))
      (boundaryFourier_projectedObservation_sobolev_one hK hγ hW v),
      boundaryFourier (roughNormalizedPrimitive y)⟫_ℂ := by
  rw [roughProjectedObservation_fourier_derivative hK hγ hW,
    boundaryFourier.inner_map_map, L2.inner_def]
  have hcomp := ContinuousLinearMap.intervalIntegral_comp_comm
    (innerSL ℂ (cutProj (cutC (W (2 * Real.pi)) (basisVec 0)) v))
    (boundary_smul_intervalIntegrable (roughNormalizedPrimitive y) (rough_endpoint_kernel_continuousOn hγ hW))
  simp only [innerSL_apply_apply] at hcomp
  rw [← hcomp, intervalIntegral.integral_of_le Real.two_pi_pos.le, ← integral_neg]
  apply integral_congr_ae
  filter_upwards [(roughProjectedObservationDerivative_memLp hγ hW v).coeFn_toLp]
    with θ hθ
  simp only [innerSL_apply_apply, inner_smul_right, RCLike.inner_apply', hθ,
    roughProjectedObservationDerivative, map_neg, inner_conj_symm]
  ring

include hK hγ hW in
/-- The true endpoint defect agrees with the original projected observation
for every normalized negative-half-order load. The proof uses actual H1
observation tests and Fourier weak integration by parts; no primitive
endpoint value is assigned. -/
theorem roughVekuaEndpointCore_projected (y : L2Z) :
    cutProj (cutC (W (2 * Real.pi)) (basisVec 0))
      (roughVekuaEndpointCore γ E W y) =
    (Real.sqrt (2 * Real.pi) : ℂ) • projObsDual W y := by
  apply ext_inner_left ℂ
  intro v
  rw [← inner_cutProj_left]
  simp only [roughVekuaEndpointCore, inner_add_right]
  rw [rough_endpoint_primitive_pairing hK hγ hW,
    rough_endpoint_mean_pairing hK hγ hW,
    roughNormalizedPrimitive_weak_pairing, neg_neg, ← inner_add_right, sub_add_cancel,
    rough_projectedObservation_weightedFourier hK hγ hW,
    inner_smul_left, Complex.conj_ofReal, inner_smul_right,
    projObsDual_eq hK hW]
  congr 1
  exact (ContinuousLinearMap.adjoint_inner_right
    (rowAnalysis (normProjObsRow W) (summable_normProjObsRow hK hW)) v y).symm

include hK hγ hW in
theorem roughVekuaEndpointCore_eq_smul_of_projObsDual_eq_zero (y : L2Z)
    (hy : projObsDual W y = 0) :
    ∃ β : ℂ, roughVekuaEndpointCore γ E W y =
      β • cutC (W (2 * Real.pi)) (basisVec 0) := by
  have hp := roughVekuaEndpointCore_projected hK hγ hW y
  rw [hy, smul_zero] at hp
  refine ⟨(((‖cutC (W (2 * Real.pi)) (basisVec 0)‖ ^ 2 : ℝ) : ℂ)⁻¹ *
    ⟪cutC (W (2 * Real.pi)) (basisVec 0), roughVekuaEndpointCore γ E W y⟫_ℂ), ?_⟩
  simp only [cutProj, ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply, InnerProductSpace.rankOne_apply, smul_smul] at hp
  exact sub_eq_zero.mp hp

include hW in
theorem roughVekuaRegularCorrection_zero (p : BoundaryL2) (m α : ℂ) :
    roughVekuaRegularCorrection γ E W p m α 0 = α • basisVec 0 := by
  simp [roughVekuaRegularCorrection, transportResponse, transport_zero_eq hW]

include hK hγ hW in
/-- The actual endpoint compatibility is an explicit computed source
integral; it does not involve an endpoint value of the rough primitive. -/
theorem roughVekuaRegularCorrection_endpoint_of_core_eq_smul (y : L2Z) (β : ℂ)
    (hcore : roughVekuaEndpointCore γ E W y =
      β • cutC (W (2 * Real.pi)) (basisVec 0)) :
    roughVekuaRegularCorrection γ E W (roughNormalizedPrimitive y) (roughNormalizedMean y)
      (-(Complex.I / (Real.sqrt 2 : ℂ)) * β) (2 * Real.pi) =
    roughVekuaRegularCorrection γ E W (roughNormalizedPrimitive y) (roughNormalizedMean y)
      (-(Complex.I / (Real.sqrt 2 : ℂ)) * β) 0 := by
  rw [roughVekuaRegularCorrection_zero hW]
  change W (2 * Real.pi)
    ((-(Complex.I / (Real.sqrt 2 : ℂ)) * β) • basisVec 0 +
      (-(Complex.I / (Real.sqrt 2 : ℂ))) •
        (∫ θ in (0 : ℝ)..(2 * Real.pi), ContinuousLinearMap.adjoint (W θ)
          (roughVekuaRegularForce γ E (roughNormalizedPrimitive y) (roughNormalizedMean y) θ))) = _
  rw [← roughVekuaEndpointCore_apply hγ hW, hcore, smul_smul, ← smul_add]
  have hu := transport_mul_adjoint hK hW ⟨Real.two_pi_pos.le, le_rfl⟩
  have hcut : basisVec 0 + cutC (W (2 * Real.pi)) (basisVec 0) =
      ContinuousLinearMap.adjoint (W (2 * Real.pi)) (basisVec 0) := by
    simp only [cutC]
    abel
  rw [hcut, map_smul, ← ContinuousLinearMap.mul_apply, hu, ContinuousLinearMap.one_apply]

include hK hγ hW in
/-- Original projected-observation nullity supplies the actual periodic
regular correction. Only this continuous correction has endpoint values. -/
theorem roughVekuaRegularCorrection_exists_periodic_of_projObsDual_eq_zero
    (y : L2Z) (hy : projObsDual W y = 0) :
    ∃ α : ℂ,
      roughVekuaRegularCorrection γ E W (roughNormalizedPrimitive y) (roughNormalizedMean y)
        α 0 = α • basisVec 0 ∧
      roughVekuaRegularCorrection γ E W (roughNormalizedPrimitive y) (roughNormalizedMean y)
        α (2 * Real.pi) = α • basisVec 0 := by
  obtain ⟨β, hβ⟩ := roughVekuaEndpointCore_eq_smul_of_projObsDual_eq_zero hK hγ hW y hy
  refine ⟨-(Complex.I / (Real.sqrt 2 : ℂ)) * β,
    roughVekuaRegularCorrection_zero hW _ _ _, ?_⟩
  rw [roughVekuaRegularCorrection_endpoint_of_core_eq_smul hK hγ hW y β hβ,
    roughVekuaRegularCorrection_zero hW]

section

variable (p : BoundaryL2) (m α : ℂ)
include p m α

theorem roughVekuaRegularCorrection_derivative_eq_transportCoeff
     (θ : ℝ) :
    transportCoeff γ E θ (roughVekuaRegularCorrection γ E W p m α θ) +
      (-(Complex.I / (Real.sqrt 2 : ℂ))) • roughVekuaRegularForce γ E p m θ =
    transportCoeff γ E θ (roughVekuaDrivenVector γ E W p m α θ) +
      (-(Complex.I / (Real.sqrt 2 : ℂ)) * m) • basisVec 0 := by
  simp only [roughVekuaRegularForce, roughVekuaDrivenVector, map_add, map_smul,
    smul_add, smul_smul]
  abel

end

end GenuineTransport

end PolyaNeumann
end
