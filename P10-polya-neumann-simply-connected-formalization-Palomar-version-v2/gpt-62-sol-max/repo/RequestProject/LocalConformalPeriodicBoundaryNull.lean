module

public import RequestProject.CircleFourier
public import RequestProject.ConformalDiskCoordinates

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
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace PolyaNeumann

open Set MeasureTheory Filter Metric Real
open scoped Topology InnerProductSpace ComplexConjugate

local notation "μB" => volume.restrict (Ioc (0 : ℝ) (2 * Real.pi))

/-- The actual circle kernel action on a genuine boundary L2 lift is its
ordinary interval integral, without a pointwise bound on the load. -/
theorem kernelL2Action_boundaryCircleLift {r : ℝ → ℝ → ℂ} {M : ℝ}
    (hmeas : ∀ θ, Measurable (r θ)) (hbd : ∀ θ s, ‖r θ s‖ ≤ M)
    (g : BoundaryL2) (θ : ℝ) :
    kernelL2Action hmeas hbd (boundaryCircleLift g) θ =
      ∫ s in (0 : ℝ)..(2 * Real.pi), r θ s * g s := by
  rw [kernelL2Action_eq_haar_integral]
  have he : (fun x : AddCircle (2 * Real.pi) =>
      r θ (circRep x) * boundaryCircleLift g x) =ᵐ[AddCircle.haarAddCircle]
      AddCircle.liftIco (2 * Real.pi) 0 (fun s => r θ s * g s) := by
    filter_upwards [boundaryCircleLift_coe g, boundary_liftIoc_eq_liftIco_ae (g : ℝ → ℂ)] with x; aesop
  rw [integral_congr_ae he]
  exact two_pi_mul_integral_liftIco _

/-- All L2 inputs, including unbounded representatives, have the actual
corrected-kernel Fourier action. This follows from the genuine circle
kernel operator and its true representative, not a density premise. -/
theorem regularCorrectedBoundaryOperator_fourier_integral_L2
    {γ : ℝ → ℂ} {L : NNReal} {E : ℝ} {W : ℝ → Ell2 →L[ℂ] Ell2}
    (hγLip : LipschitzWith L γ) (hW : IsTransport γ E W)
    (hc : cutC (W (2 * Real.pi)) (basisVec 0) ≠ 0)
    (g : BoundaryL2) (n : ℤ) :
    boundaryFourier (regularCorrectedBoundaryOperator hγLip hW hc g) n =
      (Real.sqrt (2 * Real.pi) : ℂ) * fourierCoeffOn Real.two_pi_pos
        (fun θ => ∫ s in (0 : ℝ)..(2 * Real.pi), correctedKernel W θ s * g s) n := by
  change (fourierBasis (T := 2 * Real.pi)).repr
    (boundaryCircleUnitary (boundaryCircleUnitary.symm
      (correctedKernelL2Op hγLip hW hc (boundaryCircleUnitary g)))) n = _
  rw [LinearIsometryEquiv.apply_symm_apply]
  change (fourierBasis (T := 2 * Real.pi)).repr
    (correctedKernelL2Op hγLip hW hc
      ((Real.sqrt (2 * Real.pi) : ℂ) • boundaryCircleLift g)) n = _
  rw [map_smul, map_smul]
  change (Real.sqrt (2 * Real.pi) : ℂ) *
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
    {γ : ℝ → ℂ} {L : NNReal} {E : ℝ} {W : ℝ → Ell2 →L[ℂ] Ell2}
    (hγLip : LipschitzWith L γ) (hW : IsTransport γ E W)
    (hc : cutC (W (2 * Real.pi)) (basisVec 0) ≠ 0) (g : BoundaryL2) :
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
      ((Lp.memLp g).integrable (by norm_num : (1 : ENNReal) ≤ 2))))) n).symm

private theorem periodic_null_continuous_row_intervalIntegrable
    {a : ℝ → ℂ} (ha : ContinuousOn a (Icc 0 (2 * Real.pi)))
    (g : BoundaryL2) {s t : ℝ} (hs : s ∈ Icc 0 (2 * Real.pi))
    (ht : t ∈ Icc 0 (2 * Real.pi)) :
    IntervalIntegrable (fun x => a x * g x) volume s t := by
  have hst : uIcc s t ⊆ Icc 0 (2 * Real.pi) := uIcc_subset_Icc hs ht
  exact ((intervalIntegrable_boundaryL2 g).mono_set' (uIoc_subset_uIoc_of_uIcc_subset_uIcc
    (by simpa only [uIcc_of_le Real.two_pi_pos.le] using hst))).continuousOn_mul (ha.mono hst)

/- The original kernel decomposition is valid on actual L2 loads. Its
proof uses integrable continuous rows and the true observation integral;
it never inserts a bounded representative of the load. -/
theorem periodicP_eq_kernel_integrals_boundaryL2
    {γ : ℝ → ℂ} {L : NNReal} {E : ℝ} {W : ℝ → Ell2 →L[ℂ] Ell2}
    (hγLip : LipschitzWith L γ) (hW : IsTransport γ E W)
    (t : ℝ → ℂ) (g : BoundaryL2) {θ : ℝ}
    (hθ : θ ∈ Icc 0 (2 * Real.pi)) :
    periodicP W t (g : ℝ → ℂ) θ = 2 * t θ +
      (∫ s in (0 : ℝ)..(2 * Real.pi), sawtoothKernel θ s * g s) +
      (∫ s in (0 : ℝ)..(2 * Real.pi), correctedKernel W θ s * g s) := by
  have h0 : (0 : ℝ) ∈ Icc 0 (2 * Real.pi) := ⟨le_rfl, Real.two_pi_pos.le⟩
  have hT : (2 * Real.pi) ∈ Icc 0 (2 * Real.pi) := ⟨Real.two_pi_pos.le, le_rfl⟩
  have hwc :=
    ((innerSL ℂ (basisVec 0)).comp (W θ)).continuous.comp_continuousOn
      (continuousOn_adjoint_apply hW.1 (basisVec 0))
  have hwi : ∀ {s t : ℝ}, s ∈ Icc 0 (2 * Real.pi) → t ∈ Icc 0 (2 * Real.pi) →
      IntervalIntegrable (fun x => volterraKernel W θ x * g x) volume s t :=
    fun hs ht => periodic_null_continuous_row_intervalIntegrable hwc g hs ht
  obtain ⟨hSignW, hIntW⟩ := sign_mul_intervalIntegral hθ.1 hθ.2 (hwi h0 hθ) (hwi hθ hT)
  have hk (s : ℝ) : conj (volterraKernel W s θ) = volterraKernel W θ s := by
    simp only [volterraKernel]
    rw [inner_conj_symm, ← ContinuousLinearMap.adjoint_inner_right,
      ContinuousLinearMap.adjoint_inner_left]
  have hv : Complex.I * (volterraOp W (g : ℝ → ℂ) θ -
      volterraOpAdj W (g : ℝ → ℂ) θ) =
      ∫ s in (0 : ℝ)..(2 * Real.pi), Complex.I *
        ((Real.sign (θ - s) : ℂ) * (volterraKernel W θ s * g s)) := by
    rw [intervalIntegral.integral_const_mul, hIntW]
    simp only [volterraOp, volterraOpAdj, hk]
  have hbi : IntervalIntegrable
      (fun s => g s • ContinuousLinearMap.adjoint (W s) (basisVec 0)) volume 0 (2 * Real.pi) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le Real.two_pi_pos.le).mpr
      (integrable_boundary_observation_load hγLip hW g)
  let A : Ell2 →L[ℂ] ℂ := (innerSL ℂ (basisVec 0)).comp ((W θ).comp (cutBE W))
  have hobs := A.intervalIntegral_comp_comm hbi
  simp only [A, ContinuousLinearMap.comp_apply, innerSL_apply_apply,
    map_smul] at hobs
  have ho : observation W (cutBE W (observationAdj W (g : ℝ → ℂ))) θ =
      ∫ s in (0 : ℝ)..(2 * Real.pi),
        ⟪basisVec 0, W θ (cutBE W (ContinuousLinearMap.adjoint (W s) (basisVec 0)))⟫_ℂ * g s := by
    rw [observation, observationAdj, ← hobs]
    apply intervalIntegral.integral_congr
    intro s _
    ring
  have hs := hSignW.const_mul Complex.I
  have hoc : ContinuousOn (fun s =>
      ⟪basisVec 0, W θ (cutBE W (ContinuousLinearMap.adjoint (W s) (basisVec 0)))⟫_ℂ)
      (Icc 0 (2 * Real.pi)) :=
    ((innerSL ℂ (basisVec 0)).comp ((W θ).comp (cutBE W))).continuous.comp_continuousOn
      (continuousOn_adjoint_apply hW.1 (basisVec 0))
  have hoi := periodic_null_continuous_row_intervalIntegrable hoc g h0 hT
  have hgi := intervalIntegrable_boundaryL2 g
  have hsign := (sign_mul_intervalIntegral hθ.1 hθ.2 (hgi.mono_set' (by grind [uIoc_of_le]))
    (hgi.mono_set' (by grind [uIoc_of_le]))).1
  have hlin : IntervalIntegrable (fun s => (((θ - s) / Real.pi : ℝ) : ℂ) * g s)
      volume 0 (2 * Real.pi) :=
    periodic_null_continuous_row_intervalIntegrable
      (by fun_prop) g h0 hT
  have hsaw : IntervalIntegrable (fun s => sawtoothKernel θ s * g s)
      volume 0 (2 * Real.pi) := by
    refine ((hsign.const_mul Complex.I).sub (hlin.const_mul Complex.I)).congr fun s _ => ?_
    simp only [sawtoothKernel]
    push_cast
    ring
  have hker (s : ℝ) := congrArg (fun x : ℂ => x * g s)
    (sawtoothKernel_add_correctedKernel (W := W) θ s)
  simp_rw [add_mul, mul_assoc] at hker
  have hcorr : IntervalIntegrable (fun s => correctedKernel W θ s * g s) volume 0 (2 * π) :=
    ((hs.add hoi).sub hsaw).congr fun s _ => by linear_combination -(hker s)
  rw [periodicP_eq_doubleTrace_add_correctedVolterraAction, correctedVolterraAction, hv, ho,
    ← intervalIntegral.integral_add hs hoi, add_assoc,
    ← intervalIntegral.integral_add hsaw hcorr]
  exact congrArg (2 * t θ + ·) (intervalIntegral.integral_congr fun s _ => (hker s).symm)

section ActualPeriodicL2

variable {γ : ℝ → ℂ} {L : NNReal} {E : ℝ} {W : ℝ → Ell2 →L[ℂ] Ell2}
    (hγLip : LipschitzWith L γ) (hW : IsTransport γ E W)
    (hc : cutC (W (2 * Real.pi)) (basisVec 0) ≠ 0)

/-- The periodic expression on an ordinary trace and load. -/
def periodicBoundaryL2 (t g : BoundaryL2) : BoundaryL2 :=
  (2 : ℂ) • t + sawtoothBoundaryAction g + regularCorrectedBoundaryOperator hγLip hW hc g

theorem periodicBoundaryL2_ae (t g : BoundaryL2) :
    (periodicBoundaryL2 hγLip hW hc t g : ℝ → ℂ) =ᵐ[μB]
      periodicP W (t : ℝ → ℂ) (g : ℝ → ℂ) := by
  have hgi := (Lp.memLp g).integrable (by norm_num : (1 : ENNReal) ≤ 2)
  let k := (memLp_regularCorrectedAction hγLip hW hgi).toLp _
  unfold periodicBoundaryL2
  rw [regularCorrectedBoundaryOperator_eq_integral_L2 hγLip hW hc g]
  filter_upwards [Lp.coeFn_add ((2 : ℂ) • t + sawtoothBoundaryAction g) k,
    Lp.coeFn_add ((2 : ℂ) • t) (sawtoothBoundaryAction g), Lp.coeFn_smul (2 : ℂ) t,
    MemLp.coeFn_toLp (memLp_sawtoothAction hgi),
    MemLp.coeFn_toLp (memLp_regularCorrectedAction hγLip hW hgi),
    ae_restrict_mem measurableSet_Ioc] with θ ha hb ht hs hk hθ
  change ((2 : ℂ) • t + sawtoothBoundaryAction g + k : BoundaryL2) θ = _
  simp only [ha, hb, ht, Pi.add_apply, smul_eq_mul]
  dsimp only [sawtoothBoundaryAction]
  rw [hs, hk]
  exact (periodicP_eq_kernel_integrals_boundaryL2 hγLip hW (t : ℝ → ℂ) g
    (Ioc_subset_Icc_self hθ)).symm

end ActualPeriodicL2


section SuppliedCoordinates

variable {R : ℝ}
    (hR : 1 < R)
    (F : ℂ → ℂ)
    (hFs : ContDiffOn ℝ (⊤ : ℕ∞) F (ball (0 : ℂ) R))
    (coords : ConformalDiskCoordinates F)
    {γ : ℝ → ℂ}
    (hγ : IsBoundaryParam (F '' ball (0 : ℂ) 1) γ)
    {τ : ℝ → ℝ}
    {c : ℝ}
    (hτ : IsC1TraceReparam τ c)
    (hcoord : ∀ θ, F (circleMap 0 1 θ) = γ (τ θ))

local notation "ΩF" => F '' ball (0 : ℂ) 1
local notation "ΓF" => physicalCircleTrace F
local notation "QF" => coords.halfTrace
local notation "TF" => coords.trace
local notation "VF" => localConformalVekuaH1 coords
local notation "UR" => localConformalVekuaTraceRow coords
local notation "hβF" => localConformalVelocityCircle_isWL1_half coords.one_lt_radius F coords.smooth
local notation "haF" => localConformalHardyPrimitiveMultiplier_isWL1 coords.one_lt_radius F coords.smooth
local notation "hgF" => localConformalCenteredCircle_isWL1_half coords.one_lt_radius F coords.smooth
local notation "NF" => normalizedConormal hβF haF hgF

include hR hFs in
/-- On a genuine normalized Neumann solution, the full operator has
exactly the Fourier coefficients of the ordinary periodic expression.
This single identity applies to both Vekua solutions and Herglotz waves. -/
theorem normalizedPeriodicBoundaryFamily_fourier_of_solution
    (hb : Bornology.IsBounded ΩF) (hL : IsLipschitzDomain ΩF)
    (Ws : ℝ → ℝ → Ell2 →L[ℂ] Ell2) {E : ℝ} (hE : 0 ≤ E)
    (hnr : ∀ j, neumannEigenvalue ΩF j ≠ ENNReal.ofReal E)
    {L : NNReal} (hΓLip : LipschitzWith L ΓF) (hW : IsTransport ΓF E (Ws E))
    (hc : cutC (Ws E (2 * Real.pi)) (basisVec 0) ≠ 0)
    (g : BoundaryL2) (u : NeumannH1 ΩF)
    (hu : IsNormalizedNeumannSolution (localConformalDiskHalfTrace hR F hFs hL) E
      (sobolevSmoothing (1 / 2) (by norm_num) (boundaryFourier g)) u) :
    boundaryFourier (periodicBoundaryL2 hΓLip hW hc (localConformalDiskH1Trace hR F hFs hL u) g) =
      sobolevSmoothing (1 / 2) (by norm_num) (normalizedPeriodicBoundaryFamily
        (localConformalDiskHalfTrace hR F hFs hL) Ws E
        (sobolevSmoothing (1 / 2) (by norm_num) (boundaryFourier g))) := by
  let Q := localConformalDiskHalfTrace hR F hFs hL
  let T := localConformalDiskH1Trace hR F hFs hL
  let S : L2Z →L[ℂ] L2Z := sobolevSmoothing (1 / 2) (by norm_num)
  let b : L2Z := S (boundaryFourier g)
  have hunit := h1HelmholtzForm_isUnit hb hL hE hnr
  have hsol : normalizedNeumannPoisson Q E b = u :=
    h1HelmholtzForm_injective hb hL hE hnr
      (((isNormalizedNeumannSolution_iff Q E b _).mp (normalizedNeumannPoisson_isSolution Q hunit b)).trans
        ((isNormalizedNeumannSolution_iff Q E b _).mp hu).symm)
  have ht : S (normalizedNeumannBoundary Q E b) = boundaryFourier (T u) := by
    change S (Q (normalizedNeumannPoisson Q E b)) = _
    rw [hsol, localConformal_halfSmoothing_halfTrace]
  have hbase := summable_correctedRemainderMatrix hΓLip hW hc
  let hr := summable_regularKernelIntegralMatrix (Ws E) hbase
  have hraw : regularRawInverseDerivative (boundaryFourier g) =
      S (principalNormalized b) - (2 : ℂ) • S (normalizedInverseAbsOperator b) := by
    simp only [regularRawInverseDerivative, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply, map_sub, map_smul]
    rfl
  have hHS : S (hsMatrixOp (correctedRemainderMatrix (Ws E)) hbase b) =
      hsMatrixOp (kernelIntegralMatrix (r := correctedKernel (Ws E))) hr (boundaryFourier g) :=
    correctedRemainderOp_half_smoothing (Ws E) hbase hr (boundaryFourier g)
  change boundaryFourier ((2 : ℂ) • T u + sawtoothBoundaryAction g +
    regularCorrectedBoundaryOperator hΓLip hW hc g) = S (normalizedPeriodicBoundaryFamily Q Ws E b)
  rw [← sawtoothBoundaryOperator_eq_action g, map_add, map_add, map_smul,
    regularCorrectedBoundaryOperator_fourier hΓLip hW hc hr g]
  have hsaw : boundaryFourier (sawtoothBoundaryOperator g) = regularRawInverseDerivative (boundaryFourier g) :=
    boundaryFourier.apply_symm_apply _
  rw [hsaw, hraw, normalizedPeriodicBoundaryFamily, correctedRemainderOperator_eq _ hbase]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, ContinuousLinearMap.sub_apply,
    map_add, map_smul, map_sub, smul_sub, ht, hHS]
  abel

section

variable {F}
include coords

include hγ hτ hcoord in
/-- The genuine Vekua vector has the original physical Neumann weak
equation for its actual normalized conormal. This holds for every Hardy
input, without a Sobolev regularity premise. -/
theorem localConformalVekuaH1_isNormalizedNeumannSolution
    (E : ℝ) (b : L2Z) (hbn : IsNonpositiveFourierSupport b) :
    IsNormalizedNeumannSolution QF E (NF (E : ℂ) b) (VF (F 1) (E : ℂ) b) := by
  intro w
  exact localConformalVekuaH1_normalizedConormal_weak_form coords hγ hτ hcoord (E : ℂ) b hbn w

include hγ hτ hcoord in
/-- Half-regular inputs have true L2 conormal loads. Their actual
periodic expression is zero, and its true Fourier normalization is the
full Neumann periodic family at the original nonresonant energy. -/
theorem localConformalPeriodicBoundaryNull_of_half_regular
    (Ws : ℝ → ℝ → Ell2 →L[ℂ] Ell2) {E : ℝ} (hE : 0 ≤ E)
    (hnr : ∀ j, neumannEigenvalue ΩF j ≠ ENNReal.ofReal E)
    {L : NNReal} (hΓLip : LipschitzWith L ΓF) (hW : IsTransport ΓF E (Ws E))
    (hc : cutC (Ws E (2 * Real.pi)) (basisVec 0) ≠ 0)
    (b : L2Z) (hbn : IsNonpositiveFourierSupport b)
    (hbhalf : IsSobolevSeq (1 / 2 : ℝ) (b : ℤ → ℂ)) :
    normalizedPeriodicBoundaryFamily QF Ws E (NF (E : ℂ) b) = 0 := by
  let g := localConformalVekuaForwardLoad coords (E : ℂ) b hbhalf
  have hload :=
    localConformalVekuaForwardLoad_normalized coords (E : ℂ) b hbhalf
  let u := VF (F 1) (E : ℂ) b
  let p := periodicBoundaryL2 hΓLip hW hc (TF u) g
  have hu := localConformalVekuaH1_isNormalizedNeumannSolution coords hγ hτ hcoord E b hbn
  rw [← hload] at hu
  have hfour := normalizedPeriodicBoundaryFamily_fourier_of_solution coords.one_lt_radius F coords.smooth
    coords.bounded coords.lipschitz Ws hE hnr hΓLip hW hc g u hu
  have htrace : (TF u : ℝ → ℂ) =ᵐ[μB] UR (E : ℂ) b 0 := by
    simpa only [pow_zero, ContinuousLinearMap.one_apply] using
      localConformalVekuaTraceRow_ae coords (E : ℂ) b hbn ((isSobolevSeq_one_fromL2_half_iff b).2 hbhalf) 0
  have hz : p = 0 := by
    apply Lp.ext
    filter_upwards [periodicBoundaryL2_ae hΓLip hW hc (TF u) g, htrace, Lp.coeFn_zero ℂ 2 μB,
      ae_restrict_mem measurableSet_Ioc] with θ hp ht hz hθ
    rw [hz]
    exact hp.trans (by
      unfold periodicP periodicA
      rw [ht]
      simpa only [periodicP, periodicA, g, Pi.zero_apply] using
        localConformalVekuaForward_periodicP_eq_zero coords E hE b hbn hbhalf hΓLip hW hc (Ioc_subset_Icc_self hθ))
  change boundaryFourier p = _ at hfour
  rw [hz, map_zero, hload] at hfour
  apply sobolevSmoothing_injective (1 / 2 : ℝ) (by norm_num)
  rw [← hfour, map_zero]


include hγ hτ hcoord in
/-- The true normalized periodic boundary family annihilates the
actual conormal of every original nonpositive input. Only finite modes
are realized as ordinary L2 loads in the density proof. -/
theorem localConformalPeriodicBoundaryNull
    (Ws : ℝ → ℝ → Ell2 →L[ℂ] Ell2) {E : ℝ} (hE : 0 ≤ E)
    (hnr : ∀ j, neumannEigenvalue ΩF j ≠ ENNReal.ofReal E)
    {L : NNReal} (hΓLip : LipschitzWith L ΓF) (hW : IsTransport ΓF E (Ws E))
    (hc : cutC (Ws E (2 * Real.pi)) (basisVec 0) ≠ 0)
    (b : L2Z) (hbn : IsNonpositiveFourierSupport b) :
    normalizedPeriodicBoundaryFamily QF Ws E (NF (E : ℂ) b) = 0 := by
  exact eq_zero_of_nonpositive_modes ((normalizedPeriodicBoundaryFamily QF Ws E).comp (NF (E : ℂ)))
    (fun n hn => localConformalPeriodicBoundaryNull_of_half_regular coords hγ hτ hcoord Ws hE hnr
      hΓLip hW hc (stdBasisZ n) (stdBasisZ_mem_nonpositive hn) (stdBasisZ_isSobolevSeq _ n)) hbn

include hγ hτ hcoord in
/-- The exact operator null identity on the genuine closed Hardy space,
including its zero Fourier mode. -/
theorem localConformalPeriodicBoundaryNull_comp_subtype
    (Ws : ℝ → ℝ → Ell2 →L[ℂ] Ell2) {E : ℝ} (hE : 0 ≤ E)
    (hnr : ∀ j, neumannEigenvalue ΩF j ≠ ENNReal.ofReal E)
    {L : NNReal} (hΓLip : LipschitzWith L ΓF) (hW : IsTransport ΓF E (Ws E))
    (hc : cutC (Ws E (2 * Real.pi)) (basisVec 0) ≠ 0) :
    (normalizedPeriodicBoundaryFamily QF Ws E).comp
      ((NF (E : ℂ)).comp nonpositiveFourierSubspace.subtypeL) = 0 := by
  apply ContinuousLinearMap.ext
  intro b
  simp only [ContinuousLinearMap.zero_apply,
    Submodule.subtypeL_apply]
  exact localConformalPeriodicBoundaryNull coords hγ hτ hcoord Ws hE hnr hΓLip hW hc (b : L2Z) b.property

end

end SuppliedCoordinates

end PolyaNeumann
end
