module

public import RequestProject.CircleAnalysisNotation

public import RequestProject.DiskCoordinates

public import RequestProject.NormalizedPeriodicBoundary
public import RequestProject.LocalConformalRegularObservation
public import RequestProject.LocalConformalVekuaForward
public import RequestProject.LocalConformalVekuaConormalBridge
public import RequestProject.LocalConformalHerglotzBoundaryTransfer
public import RequestProject.PlanarNotation

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
open scoped ContDiff

namespace PolyaNeumann

open Set MeasureTheory Filter Metric Real
open scoped Topology InnerProductSpace ComplexConjugate

local notation "μB" => angleMeasure

/-- The actual circle kernel action on a genuine boundary L2 lift is its
ordinary interval integral, without a pointwise bound on the load. -/
theorem kernelL2Action_boundaryCircleLift {r : ℝ → ℝ → ℂ} {M : ℝ}
    (hmeas : ∀ θ, Measurable (r θ)) (hbd : ∀ θ s, ‖r θ s‖ ≤ M)
    (g : BoundaryL2) (θ : ℝ) :
    kernelL2Action hmeas hbd (boundaryCircleLift g) θ =
      ∫ₚ s, r θ s * g s := by
  rw [kernelL2Action_eq_haar_integral]
  have he : (fun x : ParamCircle =>
      r θ (circRep x) * boundaryCircleLift g x) =ᵐ[AddCircle.haarAddCircle]
      AddCircle.liftIco anglePeriod 0 (fun s => r θ s * g s) := by
    filter_upwards [boundaryCircleLift_coe g,
      boundary_liftIoc_eq_liftIco_ae (g : ℝ → ℂ)] with x hx hrep
    simp [hx, hrep, liftIco_eq_comp]
  rw [integral_congr_ae he]
  exact two_pi_mul_integral_liftIco _

/-- All L2 inputs, including unbounded representatives, have the actual
corrected-kernel Fourier action. This follows from the genuine circle
kernel operator and its true representative, not a density premise. -/
theorem regularCorrectedBoundaryOperator_fourier_integral_L2
    {γ : ℝ → ℂ} {L : NNReal} {E : ℝ} {W : TransportPath}
    (hγLip : LipschitzWith L γ) (hW : IsTransport γ E W)
    (hc : cutVector W ≠ 0)
    (g : BoundaryL2) (n : ℤ) :
    boundaryFourier (regularCorrectedBoundaryOperator hγLip hW hc g) n =
      fourierScale * angleCoeff
        (fun θ => ∫ₚ s, correctedKernel W θ s * g s) n := by
  change (fourierBasis (T := anglePeriod)).repr
    (boundaryCircleUnitary (boundaryCircleUnitary.symm
      (correctedKernelL2Op hγLip hW hc (boundaryCircleUnitary g)))) n = _
  rw [LinearIsometryEquiv.apply_symm_apply]
  change (fourierBasis (T := anglePeriod)).repr
    (correctedKernelL2Op hγLip hW hc
      (fourierScale • boundaryCircleLift g)) n = _
  rw [map_smul, map_smul]
  change fourierScale *
    (fourierBasis ).repr
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
     
    (measurable_ckPer hW) (norm_ckPer_le hγLip hW) g θ]
  apply intervalIntegral.integral_congr
  intro s hs
  rw [uIcc_of_le Real.two_pi_pos.le] at hs
  change ckPer W θ s * g s = correctedKernel W θ s * g s
  rw [ckPer_eq hγLip hW hc (Ioc_subset_Icc_self hθ) hs]

theorem regularCorrectedBoundaryOperator_eq_integral_L2
    {γ : ℝ → ℂ} {L : NNReal} {E : ℝ} {W : TransportPath}
    (hγLip : LipschitzWith L γ) (hW : IsTransport γ E W)
    (hc : cutVector W ≠ 0) (g : BoundaryL2) :
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

private theorem periodic_null_continuous_row_intervalIntegrable
    {a : ℝ → ℂ} (ha : ContinuousOn a angleInterval)
    (g : BoundaryL2) {s t : ℝ} (hs : s ∈ angleInterval)
    (ht : t ∈ angleInterval) :
    IntervalIntegrable (fun x => a x * g x) volume s t := by
  obtain ⟨B, hB⟩ := isCompact_Icc.exists_bound_of_continuousOn ha
  have hi : Integrable (fun x => a x * g x) μB := by
    apply ((Lp.memLp g).integrable (by norm_num)).bdd_mul (c := B)
      ((ha.mono Ioc_subset_Icc_self).aestronglyMeasurable measurableSet_Ioc)
    exact ae_restrict_of_forall_mem measurableSet_Ioc (by grind)
  apply IntervalIntegrable.mono_set'
    ((intervalIntegrable_iff_integrableOn_Ioc_of_le Real.two_pi_pos.le).mpr hi)
  grind [uIoc_subset_uIoc_of_uIcc_subset_uIcc]

/- The original kernel decomposition is valid on actual L2 loads. Its
proof uses integrable continuous rows and the true observation integral;
it never inserts a bounded representative of the load. -/
theorem periodicP_eq_kernel_integrals_boundaryL2
    {γ : ℝ → ℂ} {L : NNReal} {E : ℝ} {W : TransportPath}
    (hγLip : LipschitzWith L γ) (hW : IsTransport γ E W)
    (t : ℝ → ℂ) (g : BoundaryL2) {θ : ℝ}
    (hθ : θ ∈ angleInterval) :
    periodicP W t (g : ℝ → ℂ) θ = 2 * t θ +
      (∫ₚ s, sawtoothKernel θ s * g s) +
      (∫ₚ s, correctedKernel W θ s * g s) := by
  have h0 : 0 ∈ angleInterval := ⟨le_rfl, Real.two_pi_pos.le⟩
  have hT : anglePeriod ∈ angleInterval := ⟨Real.two_pi_pos.le, le_rfl⟩
  
  have hwi : ∀ {s t : ℝ}, s ∈ angleInterval → t ∈ angleInterval →
      IntervalIntegrable (fun x => volterraKernel W θ x * g x) volume s t :=
    periodic_null_continuous_row_intervalIntegrable (((innerSL ℂ (basisVec 0)).comp (W θ)).continuous.comp_continuousOn
      (continuousOn_adjoint_apply hW.1 (basisVec 0))) g
  have hk (s : ℝ) : conj (volterraKernel W s θ) = volterraKernel W θ s := by
    simp only [volterraKernel]
    rw [inner_conj_symm, ← ContinuousLinearMap.adjoint_inner_right,
      ContinuousLinearMap.adjoint_inner_left]
  have hv : Complex.I * (volterraOp W (g : ℝ → ℂ) θ -
      volterraOpAdj W (g : ℝ → ℂ) θ) =
      ∫ₚ s, Complex.I *
        ((Real.sign (θ - s) : ℂ) * (volterraKernel W θ s * g s)) := by
    rw [intervalIntegral.integral_const_mul,
      (sign_split hθ (hwi h0 hθ) (hwi hθ hT)).2]
    simp [volterraOp, volterraOpAdj, hk]
  
  let A  := (innerSL ℂ (basisVec 0)).comp ((W θ).comp (cutBE W))
  have hobs := A.intervalIntegral_comp_comm ((intervalIntegrable_iff_integrableOn_Ioc_of_le Real.two_pi_pos.le).mpr
    (integrable_boundary_observation_load hγLip hW g))
  simp only [A, ContinuousLinearMap.comp_apply, innerSL_apply_apply,
    map_smul, smul_eq_mul] at hobs
  have ho : observation W (cutBE W (observationAdj W (g : ℝ → ℂ))) θ =
      ∫ₚ s,
        ⟪basisVec 0, W θ (cutBE W (ContinuousLinearMap.adjoint (W s) (basisVec 0)))⟫_ℂ * g s := by
    rw [observation, observationAdj, ← hobs]
    apply intervalIntegral.integral_congr
    intro s _
    ring
  have hs : IntervalIntegrable (fun s =>
      Complex.I * ((Real.sign (θ - s) : ℂ) * (volterraKernel W θ s * g s)))
      volume 0 anglePeriod :=
    (sign_split hθ (hwi h0 hθ) (hwi hθ hT)).1.const_mul _
  have hoc : ContinuousOn (fun s =>
      ⟪basisVec 0, W θ (cutBE W (ContinuousLinearMap.adjoint (W s) (basisVec 0)))⟫_ℂ)
      angleInterval :=
    ((innerSL ℂ (basisVec 0)).comp ((W θ).comp (cutBE W))).continuous.comp_continuousOn
      (continuousOn_adjoint_apply hW.1 (basisVec 0))
  have hoi := periodic_null_continuous_row_intervalIntegrable hoc g h0 hT
  have hgi : ∀ {s t : ℝ}, s ∈ angleInterval → t ∈ angleInterval →
      IntervalIntegrable (fun x => (1 : ℂ) * g x) volume s t :=
    periodic_null_continuous_row_intervalIntegrable
      (continuousOn_const ) g
  have hsign : IntervalIntegrable (fun s => (Real.sign (θ - s)) * g s)
      volume 0 anglePeriod := by
    refine (sign_split hθ ?_ ?_).1
    · simpa using hgi h0 hθ
    · simpa using hgi hθ hT
  have hlin : IntervalIntegrable (fun s => (((θ - s) / Real.pi : ℝ) : ℂ) * g s)
      volume 0 anglePeriod :=
    periodic_null_continuous_row_intervalIntegrable
      (by fun_prop) g h0 hT
  have hsaw : IntervalIntegrable (fun s => sawtoothKernel θ s * g s)
      volume 0 anglePeriod := by
    refine ((hsign.const_mul Complex.I).sub (hlin.const_mul Complex.I)).congr fun s _ => ?_
    simp only [sawtoothKernel]
    push_cast
    ring
  have hcorr : IntervalIntegrable (fun s => correctedKernel W θ s * g s)
      volume 0 anglePeriod := by
    refine ((hs.add hoi).sub hsaw).congr fun s _ => ?_
    
    calc
      _ = (Complex.I * (Real.sign (θ - s)) * volterraKernel W θ s +
          ⟪basisVec 0, W θ (cutBE W (ContinuousLinearMap.adjoint (W s) (basisVec 0)))⟫_ℂ) * g s -
          sawtoothKernel θ s * g s := by ring
      _ = _ := by rw [← (sawtoothKernel_add_correctedKernel (W := W) θ s)]; ring
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
    _ = (sawtoothKernel θ s + correctedKernel W θ s) * g s := by simp [*]
    _ = _ := by ring

section ActualPeriodicL2

/-- The genuine regular periodic boundary operator has its actual
periodic expression on every ordinary L2 load. No continuity or bounded
representative of the load is required. -/
theorem localConformalRegularPeriodicOperator_apply_ae_boundaryL2 (Φ : SmoothDiskMap)
    (hL : IsLipschitzDomain Φ.domain) (E₀ E : ℝ) {γ : ℝ → ℂ} {L : NNReal} {W : TransportPath}
    (hγLip : LipschitzWith L γ) (hW : IsTransport γ E W)
    (hc : cutVector W ≠ 0) (g : BoundaryL2) :
    (Φ.regularPeriodicOperator hL E₀ E hγLip hW hc g : ℝ → ℂ)
      =ᵐ[μB] periodicP W
        ((Φ.pulledBackTrace hL) (h1RegularResolvent Φ.domain E₀ E (ContinuousLinearMap.adjoint (Φ.pulledBackHalfTrace hL)
          (sobolevSmoothing (1 / 2) (by norm_num) (boundaryFourier g)))) : ℝ → ℂ)
        (g : ℝ → ℂ) := by
  let t  := (Φ.pulledBackTrace hL) (h1RegularResolvent Φ.domain E₀ E (ContinuousLinearMap.adjoint (Φ.pulledBackHalfTrace hL)
    (sobolevSmoothing (1 / 2) (by norm_num) (boundaryFourier g))))
  have hfI := (Lp.memLp g).integrable (by norm_num)
  let k  := (memLp_regularCorrectedAction hγLip hW hfI).toLp _
  have hop : Φ.regularPeriodicOperator hL E₀ E hγLip hW hc g =
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
  dsimp [sawtoothBoundaryAction, k]
  rw [hs, hk]
  exact (periodicP_eq_kernel_integrals_boundaryL2 hγLip hW t g
    (Ioc_subset_Icc_self hθ)).symm

end ActualPeriodicL2

section SuppliedCoordinates

section

variable (Φ : DiskCoordinates)

/-- The genuine Vekua vector has the original physical Neumann weak
equation for its actual normalized conormal. This holds for every Hardy
input, without a Sobolev regularity premise. -/
theorem localConformalVekuaH1_isNormalizedNeumannSolution {γ : ℝ → ℂ}
    (hγ : IsBoundaryParam Φ.domain γ) {τ : ℝ → ℝ} {c : ℝ} (hτ : IsC1TraceReparam τ c)
    (hcoord : ∀ θ, Φ.map (unitCirclePt θ) = γ (τ θ)) (E : ℝ) (b : L2Z)
    (hbn : IsNonpositiveFourierSupport b) :
    IsNormalizedNeumannSolution (Φ.pulledBackHalfTrace Φ.lipschitzDomain) E (Φ.conormal (E : ℂ) b) (Φ.vekuaH1 (Φ.map 1) (E : ℂ) b) := by
  intro w
  exact localConformalVekuaH1_normalizedConormal_weak_form Φ hγ hτ hcoord (E : ℂ) b hbn w

/-- Original spectral nonresonance, not a fictitious spectrum, identifies
the Vekua vector with the actual normalized Neumann Poisson solution. -/
theorem localConformalVekuaH1_eq_normalizedNeumannPoisson {γ : ℝ → ℂ}
    (hγ : IsBoundaryParam Φ.domain γ) {τ : ℝ → ℝ} {c : ℝ} (hτ : IsC1TraceReparam τ c)
    (hcoord : ∀ θ, Φ.map (unitCirclePt θ) = γ (τ θ)) {E : ℝ} (hE : 0 ≤ E)
    (hnr : ∀ j, neumannEigenvalue Φ.domain j ≠ ENNReal.ofReal E) (b : L2Z)
    (hbn : IsNonpositiveFourierSupport b) :
    Φ.vekuaH1 (Φ.map 1) (E : ℂ) b = normalizedNeumannPoisson (Φ.pulledBackHalfTrace Φ.lipschitzDomain) E (Φ.conormal (E : ℂ) b) := by
  have hu := (isNormalizedNeumannSolution_iff (Φ.pulledBackHalfTrace Φ.lipschitzDomain) E (Φ.conormal (E : ℂ) b) _).mp
    (localConformalVekuaH1_isNormalizedNeumannSolution Φ hγ hτ hcoord E b hbn)
  have hp := (isNormalizedNeumannSolution_iff (Φ.pulledBackHalfTrace Φ.lipschitzDomain) E (Φ.conormal (E : ℂ) b) _).mp
    (normalizedNeumannPoisson_isSolution (Φ.pulledBackHalfTrace Φ.lipschitzDomain) (h1HelmholtzForm_isUnit Φ.bounded Φ.lipschitzDomain hE hnr) _)
  exact h1HelmholtzForm_injective Φ.bounded Φ.lipschitzDomain hE hnr (hu.trans hp.symm)

theorem normalizedNeumannBoundary_localConformalVekuaConormal {γ : ℝ → ℂ}
    (hγ : IsBoundaryParam Φ.domain γ) {τ : ℝ → ℝ} {c : ℝ} (hτ : IsC1TraceReparam τ c)
    (hcoord : ∀ θ, Φ.map (unitCirclePt θ) = γ (τ θ)) {E : ℝ} (hE : 0 ≤ E)
    (hnr : ∀ j, neumannEigenvalue Φ.domain j ≠ ENNReal.ofReal E) (b : L2Z)
    (hbn : IsNonpositiveFourierSupport b) :
    normalizedNeumannBoundary (Φ.pulledBackHalfTrace Φ.lipschitzDomain) E (Φ.conormal (E : ℂ) b) = (Φ.pulledBackHalfTrace Φ.lipschitzDomain) (Φ.vekuaH1 (Φ.map 1) (E : ℂ) b) := by
  change (Φ.pulledBackHalfTrace Φ.lipschitzDomain) (normalizedNeumannPoisson (Φ.pulledBackHalfTrace Φ.lipschitzDomain) E (Φ.conormal (E : ℂ) b)) = _
  rw [← localConformalVekuaH1_eq_normalizedNeumannPoisson Φ hγ hτ hcoord hE hnr b hbn]

private theorem periodic_null_regular_trace_eq_Vekua {γ : ℝ → ℂ}
    (hγ : IsBoundaryParam Φ.domain γ) {τ : ℝ → ℝ} {c : ℝ} (hτ : IsC1TraceReparam τ c)
    (hcoord : ∀ θ, Φ.map (unitCirclePt θ) = γ (τ θ)) {E : ℝ} (hE : 0 ≤ E)
    (hnr : ∀ j, neumannEigenvalue Φ.domain j ≠ ENNReal.ofReal E) (b : L2Z)
    (hbn : IsNonpositiveFourierSupport b) :
    (Φ.pulledBackTrace Φ.lipschitzDomain) (h1RegularResolvent Φ.domain E E (ContinuousLinearMap.adjoint (Φ.pulledBackHalfTrace Φ.lipschitzDomain) (Φ.conormal (E : ℂ) b))) =
      (Φ.pulledBackTrace Φ.lipschitzDomain) (Φ.vekuaH1 (Φ.map 1) (E : ℂ) b) := by
  apply boundaryFourier.injective
  rw [← localConformal_halfSmoothing_halfTrace Φ Φ.lipschitzDomain,
    ← localConformal_halfSmoothing_halfTrace Φ Φ.lipschitzDomain]
  change sobolevSmoothing (1 / 2) (by norm_num)
    (normalizedNeumannRegular (Φ.pulledBackHalfTrace Φ.lipschitzDomain) E E (Φ.conormal (E : ℂ) b)) = _
  rw [← normalizedNeumannBoundary_eq_regular_at_nonresonant_reference (Φ.pulledBackHalfTrace Φ.lipschitzDomain) Φ.bounded Φ.lipschitzDomain hE
    (h1HelmholtzForm_isUnit Φ.bounded Φ.lipschitzDomain hE hnr),
    normalizedNeumannBoundary_localConformalVekuaConormal Φ hγ hτ hcoord hE hnr b hbn]

/-- Half-regular inputs have true L2 conormal loads. Their actual
periodic expression is zero, and its true Fourier normalization is the
full Neumann periodic family at the original nonresonant energy. -/
theorem localConformalPeriodicBoundaryNull_of_half_regular {γ : ℝ → ℂ}
    (hγ : IsBoundaryParam Φ.domain γ) {τ : ℝ → ℝ} {c : ℝ} (hτ : IsC1TraceReparam τ c)
    (hcoord : ∀ θ, Φ.map (unitCirclePt θ) = γ (τ θ)) (Ws : ℝ → TransportPath) {E : ℝ} (hE : 0 ≤ E)
    (hnr : ∀ j, neumannEigenvalue Φ.domain j ≠ ENNReal.ofReal E) {L : NNReal}
    (hΓLip : LipschitzWith L Φ.boundary)
    (hW : IsTransport Φ.boundary E (Ws E))
    (hc : cutVector (Ws E) ≠ 0) (b : L2Z) (hbn : IsNonpositiveFourierSupport b)
    (hbhalf : IsSobolevSeq halfOrder (b : ℤ → ℂ)) :
    normalizedPeriodicBoundaryFamily (Φ.pulledBackHalfTrace Φ.lipschitzDomain) Ws E (Φ.conormal (E : ℂ) b) = 0 := by
  let g  := Φ.vekuaForwardLoad (E : ℂ) b hbhalf
  have hload  :=
    localConformalVekuaForwardLoad_normalized Φ (E : ℂ) b hbhalf
  have hbase := herglotz_transfer_kernel_summable Φ hΓLip hW hc
  have hop := localConformalRegularPeriodicOperator_apply_ae_boundaryL2 Φ Φ.lipschitzDomain
    E E hΓLip hW hc g
  rw [hload, periodic_null_regular_trace_eq_Vekua Φ hγ hτ hcoord hE hnr b hbn] at hop
  have htrace := localConformalVekua_coordinate_trace_reconstruction_ae Φ (E : ℂ) b hbn
    (isSobolevSeq_one_fromL2_half_of_half_regular b hbhalf)
  have hz : Φ.regularPeriodicOperator Φ.lipschitzDomain E E hΓLip hW hc g = 0 := by
    apply Lp.ext
    filter_upwards [hop, htrace, Lp.coeFn_zero ℂ 2 μB,
      ae_restrict_mem measurableSet_Ioc] with θ hp ht hzero hθ
    rw [hzero]
    have hnull := localConformalVekuaForward_periodicP_eq_zero Φ E hE b hbn hbhalf hΓLip hW hc (Ioc_subset_Icc_self hθ)
    exact hp.trans (by
      simpa only [periodicP, periodicA, ht, g, DiskCoordinates.vekuaTraceRow, pow_zero,
        ContinuousLinearMap.one_apply, Pi.zero_apply] using hnull)
  have hfour := localConformalRegularPeriodicOperator_fourier Φ Φ.lipschitzDomain
    E E hΓLip hW hc hbase g
  rw [hload] at hfour
  have hfamily : normalizedPeriodicBoundaryFamily (Φ.pulledBackHalfTrace Φ.lipschitzDomain) Ws E =
      normalizedPeriodicRegularOperator (Φ.pulledBackHalfTrace Φ.lipschitzDomain) E E (Ws E) hbase := by
    rw [normalizedPeriodicBoundaryFamily_eq_regular_at_nonresonant_reference (Φ.pulledBackHalfTrace Φ.lipschitzDomain) Φ.bounded Φ.lipschitzDomain Ws hE
      (h1HelmholtzForm_isUnit Φ.bounded Φ.lipschitzDomain hE hnr),
      normalizedPeriodicRegularFamily_eq (Φ.pulledBackHalfTrace Φ.lipschitzDomain) E E Ws hbase]
  apply regular_halfSmoothing_injective
  rw [map_zero, hfamily, ← hfour, hz, map_zero]

/-- The true normalized periodic boundary family annihilates the
actual conormal of every original nonpositive input. Only finite modes
are realized as ordinary L2 loads in the density proof. -/
theorem localConformalPeriodicBoundaryNull {γ : ℝ → ℂ}
    (hγ : IsBoundaryParam Φ.domain γ) {τ : ℝ → ℝ} {c : ℝ} (hτ : IsC1TraceReparam τ c)
    (hcoord : ∀ θ, Φ.map (unitCirclePt θ) = γ (τ θ)) (Ws : ℝ → TransportPath) {E : ℝ} (hE : 0 ≤ E)
    (hnr : ∀ j, neumannEigenvalue Φ.domain j ≠ ENNReal.ofReal E) {L : NNReal}
    (hΓLip : LipschitzWith L Φ.boundary)
    (hW : IsTransport Φ.boundary E (Ws E))
    (hc : cutVector (Ws E) ≠ 0) (b : L2Z) (hbn : IsNonpositiveFourierSupport b) :
    normalizedPeriodicBoundaryFamily (Φ.pulledBackHalfTrace Φ.lipschitzDomain) Ws E (Φ.conormal (E : ℂ) b) = 0 := by
  let A  :=
    (normalizedPeriodicBoundaryFamily (Φ.pulledBackHalfTrace Φ.lipschitzDomain) Ws E).comp (Φ.conormal (E : ℂ))
  have hop : A.comp (1 - posProj) = 0 := by
    apply ContinuousLinearMap.ext_on
      (Submodule.dense_iff_topologicalClosure_eq_top.2 stdBasisZ.dense_span)
    rintro _ ⟨n, rfl⟩
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.zero_apply]
    by_cases hn : 0 < n
    · have hzero : (1 - posProj) (stdBasisZ n) = 0 := by
        apply lp.ext
        funext k
        by_cases hkn : k = n
        · subst k
          simp [posProj, hn]
        · simp [ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply,
            posProj, diagOp_apply, stdBasisZ_apply, lp.single_apply, hkn]
      rw [hzero, map_zero]
    · have hkeep : (1 - posProj) (stdBasisZ n) = stdBasisZ n := by
        apply lp.ext
        funext k
        by_cases hkn : k = n
        · subst k
          simp [posProj, hn]
        · simp [ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply,
            posProj, diagOp_apply, stdBasisZ_apply, lp.single_apply, hkn]
      rw [hkeep]
      
      apply localConformalPeriodicBoundaryNull_of_half_regular Φ hγ hτ hcoord Ws hE hnr hΓLip hW hc (stdBasisZ n) _
        (forward_half_regular_stdBasis n)
      intro k hk
      have hkn : k ≠ n := by omega
      simp [stdBasisZ_apply, lp.single_apply, hkn]
  have hkeep : (1 - posProj) b = b := by
    apply lp.ext
    funext n
    by_cases hn : 0 < n
    · simp [posProj, hn, hbn n hn]
    · simp [posProj, hn]
  have h := congrArg (fun T : FourierOp => T b) hop
  simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.zero_apply, hkeep, A] using h

/-- The exact operator null identity on the genuine closed Hardy space,
including its zero Fourier mode. -/
theorem localConformalPeriodicBoundaryNull_comp_subtype {γ : ℝ → ℂ}
    (hγ : IsBoundaryParam Φ.domain γ) {τ : ℝ → ℝ} {c : ℝ} (hτ : IsC1TraceReparam τ c)
    (hcoord : ∀ θ, Φ.map (unitCirclePt θ) = γ (τ θ)) (Ws : ℝ → TransportPath) {E : ℝ} (hE : 0 ≤ E)
    (hnr : ∀ j, neumannEigenvalue Φ.domain j ≠ ENNReal.ofReal E) {L : NNReal}
    (hΓLip : LipschitzWith L Φ.boundary)
    (hW : IsTransport Φ.boundary E (Ws E))
    (hc : cutVector (Ws E) ≠ 0) :
    (normalizedPeriodicBoundaryFamily (Φ.pulledBackHalfTrace Φ.lipschitzDomain) Ws E).comp
      ((Φ.conormal (E : ℂ)).comp nonpositiveFourierSubspace.subtypeL) = 0 := by
  apply ContinuousLinearMap.ext
  intro b
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.zero_apply,
    Submodule.subtypeL_apply]
  exact localConformalPeriodicBoundaryNull Φ hγ hτ hcoord Ws hE hnr hΓLip hW hc (b : L2Z) b.property

end

end SuppliedCoordinates

end PolyaNeumann
end
