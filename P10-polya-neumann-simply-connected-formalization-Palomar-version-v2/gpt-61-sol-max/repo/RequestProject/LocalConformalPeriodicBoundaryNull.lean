module

public import RequestProject.LocalConformalHerglotzBoundaryTransfer


public import RequestProject.PlanarTypes
public import RequestProject.CirclePeriod

public import RequestProject.PlanarGeometry

public import RequestProject.NormalizedPeriodicBoundary
public import RequestProject.LocalConformalRegularObservation
public import RequestProject.LocalConformalVekuaForward
public import RequestProject.LocalConformalVekuaConormalBridge

/-!
# The genuine full periodic family on the actual Vekua conormal range

At a nonresonant energy the actual Vekua weak equation identifies its
vector with the original normalized Neumann Poisson solution. The
ordinary L2 periodic expression agrees with the normalized Fourier
operator, including the constant mode. Finite Fourier density then
extends its proved vanishing to every original Hardy input.

The supplied physical boundary parametrization and its genuine C1
arclength coordinate are retained. No L2 representative is asserted for
an arbitrary normalized rough load. This source awaits root compilation.
-/

@[expose] public section

open scoped ContDiff
set_option maxHeartbeats 4000000

namespace PolyaNeumann

open Set MeasureTheory Filter Metric Real
open scoped InnerProductSpace ComplexConjugate


local notation "μB" => volume.restrict boundaryHalfOpenInterval

/-- The actual circle kernel action on a genuine boundary L2 lift is its
ordinary interval integral, without a pointwise bound on the load. -/
theorem kernelL2Action_boundaryCircleLift {r : ℝ → ComplexCurve} 
    hmeas (hbd : ∀ θ s, ‖r θ s‖ ≤ M)
    g θ :
    kernelL2Action hmeas hbd (boundaryCircleLift g) θ =
      ∫ s in (0 : ℝ)..circlePeriod, r θ s * g s := by
  rw [kernelL2Action_eq_haar_integral]
  have he : (fun x : AddCircle circlePeriod =>
      r θ (circRep x) * boundaryCircleLift g x) =ᵐ[AddCircle.haarAddCircle]
      AddCircle.liftIco circlePeriod 0 (fun s => r θ s * g s) := by
    filter_upwards [boundaryCircleLift_coe g,
      boundary_liftIoc_eq_liftIco_ae g] with x hx hrep
    measurability
  rw [integral_congr_ae he]
  exact two_pi_mul_integral_liftIco _

section
variable {γ } {L } {E } {W } (hγLip : LipschitzWith L γ) (hW : IsTransport γ E W)

section
include γ L E W hγLip hW

/-- All L2 inputs, including unbounded representatives, have the actual
corrected-kernel Fourier action. This follows from the genuine circle
kernel operator and its true representative, not a density premise. -/
theorem regularCorrectedBoundaryOperator_fourier_integral_L2
    hc
    g n :
    boundaryFourier (regularCorrectedBoundaryOperator hγLip hW hc g) n =
      (Real.sqrt circlePeriod : ℂ) * fourierCoeffOn Real.two_pi_pos
        (fun θ => ∫ s in (0 : ℝ)..circlePeriod, correctedKernel W θ s * g s) n := by
  change (fourierBasis (T := 2 * Real.pi)).repr
    (boundaryCircleUnitary (boundaryCircleUnitary.symm
      (correctedKernelL2Op hγLip hW hc (boundaryCircleUnitary g)))) n = _
  rw [LinearIsometryEquiv.apply_symm_apply]
  change (fourierBasis (T := 2 * Real.pi)).repr
    (correctedKernelL2Op hγLip hW hc
      ((Real.sqrt circlePeriod : ℂ) • boundaryCircleLift g)) n = _
  rw [map_smul, map_smul]
  change (Real.sqrt circlePeriod) *
    (fourierBasis (T := 2 * Real.pi)).repr
      (correctedKernelL2Op hγLip hW hc (boundaryCircleLift g)) n = _
  congr 1
  rw [fourierBasis_repr]
  change fourierCoeff ((memLp_kernelL2Action (measurable_ckPer hW)
    (norm_ckPer_le hγLip hW) (fun θ θ' s _ => ckPer_lip hγLip hW hc θ θ' s)
      (boundaryCircleLift g)).toLp _) n = _
  rw [fourierCoeff_congr_ae (MemLp.coeFn_toLp
    (memLp_kernelL2Action (measurable_ckPer hW) (norm_ckPer_le hγLip hW)
      (fun θ θ' s _ => ckPer_lip hγLip hW hc θ θ' s) (boundaryCircleLift g))),
    fourierCoeff_liftIco_two_pi]
  refine congrFun (fourierCoeffOn_congr_ae Real.two_pi_pos ?_) n
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with θ hθ
  rw [kernelL2Action_boundaryCircleLift
    (r := ckPer W) (M := 4 + ‖cutBE W‖)
    (measurable_ckPer hW) (norm_ckPer_le hγLip hW) g θ]
  apply intervalIntegral.integral_congr
  intro s hs
  rw [uIcc_of_le Real.two_pi_pos.le] at hs
  change ckPer W θ s * g s = correctedKernel W θ s * g s
  rw [ckPer_eq hγLip hW hc (Ioc_subset_Icc_self hθ) hs]

theorem regularCorrectedBoundaryOperator_eq_integral_L2
    hc g :
    regularCorrectedBoundaryOperator hγLip hW hc g =
      (memLp_regularCorrectedAction hγLip hW
        ((Lp.memLp g).integrable (by norm_num : (1 : ENNReal) ≤ 2))).toLp _ := by
  apply boundaryFourier.injective
  apply lp.ext
  funext n
  rw [regularCorrectedBoundaryOperator_fourier_integral_L2 hγLip hW hc g n,
    boundaryFourier_apply]
  congr 1
  exact (congrFun (fourierCoeffOn_congr_ae Real.two_pi_pos
    (MemLp.coeFn_toLp (memLp_regularCorrectedAction hγLip hW
      ((Lp.memLp g).integrable (by norm_num))))) n).symm

end


private theorem periodic_null_continuous_row_intervalIntegrable
     (ha : ContinuousOn a boundaryInterval)
    (g : BoundaryL2)  (hs : s ∈ boundaryInterval)
    (ht : t ∈ boundaryInterval) :
    IntervalIntegrable (fun x => a x * g x) volume s t := by
  obtain ⟨B, hB⟩ := isCompact_Icc.exists_bound_of_continuousOn ha
  have hi : Integrable (fun x => a x * g x) μB := by
    apply ((Lp.memLp g).integrable (by norm_num)).bdd_mul (c := B)
      ((ha.mono Ioc_subset_Icc_self).aestronglyMeasurable measurableSet_Ioc)
    exact ae_restrict_of_forall_mem measurableSet_Ioc fun x hx =>
      hB x (Ioc_subset_Icc_self hx)
  apply IntervalIntegrable.mono_set'
    ((intervalIntegrable_iff_integrableOn_Ioc_of_le Real.two_pi_pos.le).mpr hi)
  grind

/- The original kernel decomposition is valid on actual L2 loads. Its
proof uses integrable continuous rows and the true observation integral;
it never inserts a bounded representative of the load. -/
include γ L E W hγLip hW in
theorem periodicP_eq_kernel_integrals_boundaryL2
    t (g : BoundaryL2) 
    (hθ : θ ∈ boundaryInterval) :
    periodicP W t (g : ComplexCurve) θ = 2 * t θ +
      (∫ s in (0 : ℝ)..circlePeriod, sawtoothKernel θ s * g s) +
      (∫ s in (0 : ℝ)..circlePeriod, correctedKernel W θ s * g s) := by
  have h0 : (0 : ℝ) ∈ boundaryInterval := ⟨le_rfl, Real.two_pi_pos.le⟩
  have hT : circlePeriod ∈ boundaryInterval := ⟨Real.two_pi_pos.le, le_rfl⟩
  have hwc  :=
    continuousOn_volterraKernel hW.1 θ
  have hwi : ∀ {s t : ℝ}, s ∈ boundaryInterval → t ∈ boundaryInterval →
      IntervalIntegrable (fun x => volterraKernel W θ x * g x) volume s t :=
    (periodic_null_continuous_row_intervalIntegrable hwc g)
  have hk := conj_volterraKernel W θ
  have hv : Complex.I * (volterraOp W (g : ComplexCurve) θ -
      volterraOpAdj W (g : ComplexCurve) θ) =
      ∫ s in (0 : ℝ)..circlePeriod, Complex.I *
        ((Real.sign (θ - s) : ℂ) * (volterraKernel W θ s * g s)) := by
    rw [intervalIntegral.integral_const_mul,
      intervalIntegral_sign_mul_of_integrable hθ (hwi h0 hθ) (hwi hθ hT)]
    simp_all [volterraOp, volterraOpAdj]
  have hbi  :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le Real.two_pi_pos.le).mpr
      (integrable_boundary_observation_load hγLip hW g)
  let A  := (innerSL ℂ (basisVec 0)).comp ((W θ).comp (cutBE W))
  have hobs := A.intervalIntegral_comp_comm hbi
  simp only [A, ContinuousLinearMap.comp_apply, innerSL_apply_apply,
    map_smul, smul_eq_mul] at hobs
  have ho : observation W (cutBE W (observationAdj W (g : ComplexCurve))) θ =
      ∫ s in (0 : ℝ)..circlePeriod,
        ⟪basisVec 0, W θ (cutBE W (ContinuousLinearMap.adjoint (W s) (basisVec 0)))⟫_ℂ * g s := by
    rw [observation, observationAdj, ← hobs]
    apply intervalIntegral.integral_congr
    intro s _
    ring
  have hs : IntervalIntegrable (fun s =>
      Complex.I * ((Real.sign (θ - s) : ℂ) * (volterraKernel W θ s * g s)))
      volume 0 circlePeriod :=
    (intervalIntegrable_sign_mul_of_integrable hθ (hwi h0 hθ) (hwi hθ hT)).const_mul _
  have hoc : ContinuousOn (fun s =>
      ⟪basisVec 0, W θ (cutBE W (ContinuousLinearMap.adjoint (W s) (basisVec 0)))⟫_ℂ)
      boundaryInterval :=
    ((innerSL ℂ (basisVec 0)).comp ((W θ).comp (cutBE W))).continuous.comp_continuousOn
      (continuousOn_adjoint_apply hW.1 (basisVec 0))
  have hoi := periodic_null_continuous_row_intervalIntegrable hoc g h0 hT
  have hgi : ∀ {s t : ℝ}, s ∈ boundaryInterval → t ∈ boundaryInterval →
      IntervalIntegrable (fun x => (1 : ℂ) * g x) volume s t :=
    (periodic_null_continuous_row_intervalIntegrable (continuousOn_const (c := 1)) g)
  have hsign : IntervalIntegrable (fun s => (Real.sign (θ - s) : ℂ) * g s)
      volume 0 circlePeriod := by
    apply intervalIntegrable_sign_mul_of_integrable hθ
    · simpa only [one_mul] using hgi h0 hθ
    · simpa only [one_mul] using hgi hθ hT
  have hlin : IntervalIntegrable (fun s => (((θ - s) / Real.pi : ℝ) : ℂ) * g s)
      volume 0 circlePeriod :=
    periodic_null_continuous_row_intervalIntegrable
      (by fun_prop) g h0 hT
  have hsaw : IntervalIntegrable (fun s => sawtoothKernel θ s * g s)
      volume 0 circlePeriod := by
    refine ((hsign.const_mul Complex.I).sub (hlin.const_mul Complex.I)).congr fun s _ => ?_
    simp only [sawtoothKernel]
    push_cast
    ring
  have hcorr : IntervalIntegrable (fun s => correctedKernel W θ s * g s)
      volume 0 circlePeriod := by
    refine ((hs.add hoi).sub hsaw).congr fun s _ => ?_
    have he := sawtoothKernel_add_correctedKernel (W := W) θ s
    calc
      _ = (Complex.I * (Real.sign (θ - s)) * volterraKernel W θ s +
          ⟪basisVec 0, W θ (cutBE W (ContinuousLinearMap.adjoint (W s) (basisVec 0)))⟫_ℂ) * g s -
          sawtoothKernel θ s * g s := by ring
      _ = correctedKernel W θ s * g s := by rw [← he]; ring
  rw [periodicP_eq_doubleTrace_add_correctedVolterraAction, correctedVolterraAction, hv, ho]
  rw [← intervalIntegral.integral_add hs hoi, add_assoc,
    ← intervalIntegral.integral_add hsaw hcorr]
  congr 1
  apply intervalIntegral.integral_congr
  intro s _
  have he := sawtoothKernel_add_correctedKernel (W := W) θ s
  calc
    _ = (Complex.I * (Real.sign (θ - s)) * volterraKernel W θ s +
        ⟪basisVec 0, W θ (cutBE W (ContinuousLinearMap.adjoint (W s) (basisVec 0)))⟫_ℂ) * g s := by ring
    _ = (sawtoothKernel θ s + correctedKernel W θ s) * g s := by rw [← he]
    _ = sawtoothKernel θ s * g s + correctedKernel W θ s * g s := by ring

end


section ActualPeriodicL2

variable {R } (hR : 1 < R) (F )
    (hFs : RealSmoothOnBall F R)
    (hL : IsLipschitzDomain (F '' unitDisk))

local notation "ΩP" => F '' unitDisk
local notation "QP" => localConformalDiskHalfTrace hR F hFs hL
local notation "TP" => localConformalDiskH1Trace hR F hFs hL

/-- The genuine regular periodic boundary operator has its actual
periodic expression on every ordinary L2 load. No continuity or bounded
representative of the load is required. -/
theorem localConformalRegularPeriodicOperator_apply_ae_boundaryL2 (E₀ E : ℝ)
    {γ : ComplexCurve} {L : NNReal} {W : ℝ → ComplexEnd Ell2}
    (hγLip : LipschitzWith L γ) (hW : IsTransport γ E W)
    (hc : cutC (W circlePeriod) (basisVec 0) ≠ 0) (g : BoundaryL2) :
    (localConformalRegularPeriodicOperator hR F hFs hL E₀ E hγLip hW hc g : ComplexCurve)
      =ᵐ[μB] periodicP W
        (TP (h1RegularResolvent ΩP E₀ E (ContinuousLinearMap.adjoint QP
          (sobolevSmoothing (1 / 2) (by norm_num) (boundaryFourier g)))) : ComplexCurve)
        (g : ComplexCurve) := by
  let t  := TP (h1RegularResolvent ΩP E₀ E (ContinuousLinearMap.adjoint QP
    (sobolevSmoothing (1 / 2) (by norm_num) (boundaryFourier g))))
  have hfI := (Lp.memLp g).integrable (by norm_num)
  let k  := (memLp_regularCorrectedAction hγLip hW hfI).toLp _
  have hop : localConformalRegularPeriodicOperator hR F hFs hL E₀ E hγLip hW hc g =
      (2 : ℂ) • t + sawtoothBoundaryAction g + k := by
    change (2 : ℂ) • t + sawtoothBoundaryOperator g +
      regularCorrectedBoundaryOperator hγLip hW hc g = _
    rw [sawtoothBoundaryOperator_eq_action,
      regularCorrectedBoundaryOperator_eq_integral_L2 hγLip hW hc g]
  rw [hop]
  filter_upwards [Lp.coeFn_add ((2 : ℂ) • t + sawtoothBoundaryAction g) k,
    Lp.coeFn_add ((2 : ℂ) • t) (sawtoothBoundaryAction g), Lp.coeFn_smul (2 : ℂ) t,
    MemLp.coeFn_toLp (memLp_sawtoothAction hfI),
    MemLp.coeFn_toLp (memLp_regularCorrectedAction hγLip hW hfI),
    ae_restrict_mem measurableSet_Ioc] with θ ha hb hc' hs hk hθ
  simp only [ha, hb, hc', Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  dsimp only [sawtoothBoundaryAction, k]
  rw [hs, hk]
  exact (periodicP_eq_kernel_integrals_boundaryL2 hγLip hW t g
    (Ioc_subset_Icc_self hθ)).symm

end ActualPeriodicL2

section SuppliedCoordinates

variable {R C K } (hR : 1 < R) (F )
    (hFs : RealSmoothOnBall F R)
    (hb : Bornology.IsBounded (F '' unitDisk))
    (hL : IsLipschitzDomain (F '' unitDisk))
    (hhol : DifferentiableOn ℂ F unitDisk)
    (hinj : InjOn F unitDisk)
    (hC : DiskInverseJacobianBound F C)
    (hK : DiskDerivativeBound F K)
    (e : OpenPartialHomeomorph ℂ ℂ) (he : (e : PlaneMap) = F)
    (hsource : closedUnitDisk ⊆ e.source)
    (hes : RealSmoothOn e.symm e.target)
    {γ } (hγ : IsBoundaryParam (F '' unitDisk) γ)
    {τ } {c } (hτ : IsC1TraceReparam τ c)
    (hcoord : ∀ θ, F (unitCircleMap θ) = γ (τ θ))

local notation "ΩF" => F '' unitDisk
local notation "ΓF" => physicalCircleTrace F
local notation "QF" => localConformalDiskHalfTrace hR F hFs hL
local notation "TF" => localConformalDiskH1Trace hR F hFs hL
local notation "VF" => localConformalVekuaH1 hR F hFs hb hL hhol hinj hC hK
  e he hsource hes
local notation "hβF" => localConformalVelocityCircle_isWL1_half hR F hFs
local notation "haF" => localConformalHardyPrimitiveMultiplier_isWL1 hR F hFs
local notation "hgF" => localConformalCenteredCircle_isWL1_half hR F hFs
local notation "NF" => normalizedConormal hβF haF hgF

include hγ hτ hcoord in
/-- The genuine Vekua vector has the original physical Neumann weak
equation for its actual normalized conormal. This holds for every Hardy
input, without a Sobolev regularity premise. -/
theorem localConformalVekuaH1_isNormalizedNeumannSolution
    E (b : L2Z) (hbn : IsNonpositiveFourierSupport b) :
    IsNormalizedNeumannSolution QF E (NF (E : ℂ) b) (VF (F 1) (E : ℂ) b) := by
  intro w
  exact localConformalVekuaH1_normalizedConormal_weak_form hR F hFs hb hL hhol hinj hC hK
    e he hsource hes hγ hτ hcoord E b hbn w

section
variable {E : ℝ} (hE : 0 ≤ E)
include E hE

section
include hγ hτ hcoord

/-- Original spectral nonresonance, not a fictitious spectrum, identifies
the Vekua vector with the actual normalized Neumann Poisson solution. -/
theorem localConformalVekuaH1_eq_normalizedNeumannPoisson
    (hnr : ∀ j, neumannEigenvalue ΩF j ≠ ENNReal.ofReal E)
    (b : L2Z) (hbn : IsNonpositiveFourierSupport b) :
    VF (F 1) (E : ℂ) b = normalizedNeumannPoisson QF E (NF (E : ℂ) b) := by
  have hu := (isNormalizedNeumannSolution_iff QF E (NF E b) _).mp
    (localConformalVekuaH1_isNormalizedNeumannSolution hR F hFs hb hL hhol hinj hC hK
      e he hsource hes hγ hτ hcoord E b hbn)
  have hp := (isNormalizedNeumannSolution_iff QF E (NF E b) _).mp
    (normalizedNeumannPoisson_isSolution QF (h1HelmholtzForm_isUnit hb hL hE hnr) _)
  exact h1HelmholtzForm_injective hb hL hE hnr (hu.trans hp.symm)

theorem normalizedNeumannBoundary_localConformalVekuaConormal
    (hnr : ∀ j, neumannEigenvalue ΩF j ≠ ENNReal.ofReal E)
    (b : L2Z) (hbn : IsNonpositiveFourierSupport b) :
    normalizedNeumannBoundary QF E (NF (E : ℂ) b) = QF (VF (F 1) (E : ℂ) b) := by
  change QF (normalizedNeumannPoisson QF E (NF E b)) = _
  rw [← localConformalVekuaH1_eq_normalizedNeumannPoisson hR F hFs hb hL hhol hinj hC hK
    e he hsource hes hγ hτ hcoord hE hnr b hbn]

private theorem periodic_null_regular_trace_eq_Vekua
    (hnr : ∀ j, neumannEigenvalue ΩF j ≠ ENNReal.ofReal E)
    (b : L2Z) (hbn : IsNonpositiveFourierSupport b) :
    TF (h1RegularResolvent ΩF E E (ContinuousLinearMap.adjoint QF (NF (E : ℂ) b))) =
      TF (VF (F 1) (E : ℂ) b) := by
  apply boundaryFourier.injective
  rw [← localConformal_halfSmoothing_halfTrace hR F hFs hL,
    ← localConformal_halfSmoothing_halfTrace hR F hFs hL]
  change sobolevSmoothing (1 / 2) (by norm_num)
    (normalizedNeumannRegular QF E E (NF E b)) = _
  rw [← normalizedNeumannBoundary_eq_regular_at_nonresonant_reference QF hb hL hE
    (h1HelmholtzForm_isUnit hb hL hE hnr),
    normalizedNeumannBoundary_localConformalVekuaConormal hR F hFs hb hL hhol hinj hC hK
      e he hsource hes hγ hτ hcoord hE hnr b hbn]

end


end


section
variable (Ws : ℝ → ℝ → ComplexEnd Ell2) {E : ℝ} (hE : 0 ≤ E)

include hb hhol hinj hC hK e he hsource hes hγ hτ hcoord in
include Ws E hE in
/-- Half-regular inputs have true L2 conormal loads. Their actual
periodic expression is zero, and its true Fourier normalization is the
full Neumann periodic family at the original nonresonant energy. -/
theorem localConformalPeriodicBoundaryNull_of_half_regular
    (hnr : ∀ j, neumannEigenvalue ΩF j ≠ ENNReal.ofReal E)
     (hΓLip : LipschitzWith L ΓF) (hW : IsTransport ΓF E (Ws E))
    (hc : cutC (Ws E circlePeriod) (basisVec 0) ≠ 0)
    (b : L2Z) (hbn : IsNonpositiveFourierSupport b)
    (hbhalf : IsSobolevSeq (1 / 2 : ℝ) (b : FourierSeq)) :
    normalizedPeriodicBoundaryFamily QF Ws E (NF (E : ℂ) b) = 0 := by
  let g  := localConformalVekuaForwardLoad hR F hFs E b hbhalf
  have hload  :=
    localConformalVekuaForwardLoad_normalized hR F hFs E b hbhalf
  have hbase := localConformal_correctedRemainderMatrix_summable hR F hFs hΓLip hW hc
  have hop := localConformalRegularPeriodicOperator_apply_ae_boundaryL2 hR F hFs hL
    E E hΓLip hW hc g
  rw [hload, periodic_null_regular_trace_eq_Vekua hR F hFs hb hL hhol hinj hC hK
    e he hsource hes hγ hτ hcoord hE hnr b hbn] at hop
  have htrace := localConformalVekua_coordinate_trace_reconstruction_ae hR F hFs hb hL
    hhol hinj hC hK e he hsource hes E b hbn
    (isSobolevSeq_one_fromL2_half_of_half_regular b hbhalf)
  have hz : localConformalRegularPeriodicOperator hR F hFs hL E E hΓLip hW hc g = 0 := by
    apply Lp.ext
    filter_upwards [hop, htrace, Lp.coeFn_zero ℂ 2 μB,
      ae_restrict_mem measurableSet_Ioc] with θ hp ht hzero hθ
    rw [hzero]
    have hnull := localConformalVekuaForward_periodicP_eq_zero hR F hFs hb hL hhol hinj hC hK
      e he hsource hes E hE b hbn hbhalf hΓLip hW hc (Ioc_subset_Icc_self hθ)
    exact hp.trans (by
      simpa only [periodicP, periodicA, ht, g, localConformalVekuaTraceRow, pow_zero,
        ContinuousLinearMap.one_apply, Pi.zero_apply] using hnull)
  have hfour := localConformalRegularPeriodicOperator_fourier hR F hFs hL
    E E hΓLip hW hc hbase g
  rw [hload] at hfour
  have hfamily : normalizedPeriodicBoundaryFamily QF Ws E =
      normalizedPeriodicRegularOperator QF E E (Ws E) hbase := by
    rw [normalizedPeriodicBoundaryFamily_eq_regular_at_nonresonant_reference QF hb hL Ws hE
      (h1HelmholtzForm_isUnit hb hL hE hnr),
      normalizedPeriodicRegularFamily_eq QF E E Ws hbase]
  apply common_regular_halfSmoothing_injective
  rw [map_zero, hfamily, ← hfour, hz, map_zero]

section
include hb hhol hinj hC hK e he hsource hes hγ hτ hcoord Ws E hE

/-- The true normalized periodic boundary family annihilates the
actual conormal of every original nonpositive input. Only finite modes
are realized as ordinary L2 loads in the density proof. -/
theorem localConformalPeriodicBoundaryNull
    (hnr : ∀ j, neumannEigenvalue ΩF j ≠ ENNReal.ofReal E)
     (hΓLip : LipschitzWith L ΓF) (hW : IsTransport ΓF E (Ws E))
    (hc : cutC (Ws E circlePeriod) (basisVec 0) ≠ 0)
    (b : L2Z) (hbn : IsNonpositiveFourierSupport b) :
    normalizedPeriodicBoundaryFamily QF Ws E (NF (E : ℂ) b) = 0 := by
  let A  :=
    (normalizedPeriodicBoundaryFamily QF Ws E).comp (NF E)
  have hop : A.comp (1 - posProj) = 0 := by
    apply ContinuousLinearMap.ext_on
      ((Submodule.dense_iff_topologicalClosure_eq_top).2 stdBasisZ.dense_span)
    rintro _ ⟨n, rfl⟩
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.zero_apply]
    by_cases hn : 0 < n
    · have hzero : (1 - posProj) (stdBasisZ n) = 0 := by
        apply lp.ext
        funext k
        by_cases hkn : k = n
        · simp_all [posProj, PolyaNeumann.L2Z, PolyaNeumann.posProj]
        · simp [ posProj, diagOp_apply, stdBasisZ_apply, lp.single_apply, hkn]
      rw [hzero, map_zero]
    · have hkeep : (1 - posProj) (stdBasisZ n) = stdBasisZ n := by
        apply lp.ext
        funext k
        by_cases hkn : k = n
        · simp_all [posProj, PolyaNeumann.L2Z, PolyaNeumann.posProj]
        · simp [ 
            posProj, diagOp_apply, stdBasisZ_apply, lp.single_apply, hkn]
      rw [hkeep]
      change normalizedPeriodicBoundaryFamily QF Ws E (NF E (stdBasisZ n)) = 0
      apply localConformalPeriodicBoundaryNull_of_half_regular hR F hFs hb hL hhol hinj hC hK
        e he hsource hes hγ hτ hcoord Ws hE hnr hΓLip hW hc (stdBasisZ n) _
        (common_forward_half_regular_stdBasis n)
      intro k hk
      have hkn : k ≠ n := by omega
      simp [stdBasisZ_apply, lp.single_apply, hkn]
  have hkeep : (1 - posProj) b = b := by
    apply lp.ext
    funext n
    by_cases hn : 0 < n
    · simp [ 
        posProj, diagOp_apply, hn, hbn n hn]
    simp_all [posProj, PolyaNeumann.L2Z, PolyaNeumann.posProj]
  have h := congrArg (fun T : L2Z →L[ℂ] L2Z => T b) hop
  simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.zero_apply, hkeep, A] using h

/-- The exact operator null identity on the genuine closed Hardy space,
including its zero Fourier mode. -/
theorem localConformalPeriodicBoundaryNull_comp_subtype
    (hnr : ∀ j, neumannEigenvalue ΩF j ≠ ENNReal.ofReal E)
    {L : NNReal} (hΓLip : LipschitzWith L ΓF) (hW : IsTransport ΓF E (Ws E))
    (hc : cutC (Ws E circlePeriod) (basisVec 0) ≠ 0) :
    (normalizedPeriodicBoundaryFamily QF Ws E).comp
      ((NF (E : ℂ)).comp nonpositiveFourierSubspace.subtypeL) = 0 := by
  apply ContinuousLinearMap.ext
  intro b
  exact localConformalPeriodicBoundaryNull hR F hFs hb hL hhol hinj hC hK
    e he hsource hes hγ hτ hcoord Ws hE hnr hΓLip hW hc b b.property

end


end


end SuppliedCoordinates

end PolyaNeumann