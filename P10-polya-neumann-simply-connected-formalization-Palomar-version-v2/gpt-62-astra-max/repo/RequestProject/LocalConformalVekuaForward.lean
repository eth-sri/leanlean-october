module

public import RequestProject.CircleAnalysisNotation

public import RequestProject.DiskCoordinates

public import RequestProject.LocalConformalReducedCoercivity
public import RequestProject.PeriodicForm
public import RequestProject.PlanarNotation

/-!
# Genuine forward Vekua transport with ordinary L2 forcing

The actual Fourier conormal identity is inverted using an interval
primitive of an ordinary boundary L2 element. This retains frequency zero
and the actual initial value; absolute continuity is a conclusion. The
positive rows are the already constructed absolutely convergent Ell2
series. Together they give the true driven integral equation and its
periodic observation identity.

All statements are conditional on the supplied conformal coordinates.
No existence of those coordinates or regularity of arbitrary negative
half-order boundary loads is inferred. These statements are part of the
verified dependency chain.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open scoped ContDiff

namespace PolyaNeumann

open Set MeasureTheory Filter Metric
open scoped Topology ComplexConjugate InnerProductSpace

/-- Fourier inversion for an actual L2 derivative. No absolute continuity
or differentiability of the original continuous function is assumed. -/
theorem eq_add_integral_of_L2_periodic_fourier_derivative
    {v : ℝ → ℂ} (hv : Continuous v)
    (hvper : Function.Periodic v anglePeriod) (d : BoundaryL2)
    (hcoeff : ∀ n : ℤ, angleCoeff (d : ℝ → ℂ) n =
      (Complex.I * (n : ℂ)) * angleCoeff v n)
    {θ : ℝ} (hθ : θ ∈ angleInterval) :
    v θ = v 0 + ∫ s in (0 : ℝ)..θ, d s := by
  let P  := fun t => ∫ s in 0..t, d s
  have hPi := intervalIntegrable_boundaryL2 d
  have hPAC  :=
    absolutelyContinuousOnInterval_intervalIntegral_banach hPi
      (by rw [uIcc_of_le Real.two_pi_pos.le]; exact ⟨le_rfl, Real.two_pi_pos.le⟩)
  have hPC : ContinuousOn P angleInterval := by
    simpa only [uIcc_of_le Real.two_pi_pos.le] using hPAC.continuousOn
  
  have hP0 : P 0 = 0 := by simp [P]
  have hPT : P anglePeriod = 0 :=
    integral_eq_zero_of_periodic_fourier_derivative hcoeff
  have hPc (n : ℤ)  :=
    fourierCoeffOn_of_ac_ae_hasDerivAt hPAC (Lp.memLp d) (ae_hasDerivAt_intervalIntegral_banach Real.two_pi_pos.le hPi) (hP0.trans hPT.symm) n
  have hncoeff (n : ℤ) (hn : n ≠ 0)  :=
    mul_left_cancel₀ (mul_ne_zero Complex.I_ne_zero ((by positivity)))
      ((hcoeff n).symm.trans (hPc n))
  let f  := fun t => v t - P t
  have hfc  := hv.continuousOn.sub hPC
  have hfe : f 0 = f anglePeriod := by
    simpa [f, hP0, hPT] using (hvper 0).symm
  let F : ℝ → ℂ := fun t => AddCircle.liftIco anglePeriod 0 f
    t
  have hFc : Continuous F :=
    (AddCircle.liftIco_zero_continuous hfe hfc).comp (AddCircle.continuous_mk' _)
  
  have hFf : EqOn F f angleInterval := by
    intro t ht
    by_cases htT : t = anglePeriod
    · subst t
      have hzero : AddCircle.liftIco anglePeriod 0 f
          (0 : ParamCircle) = f 0 :=
        AddCircle.liftIco_zero_coe_apply ⟨le_rfl, Real.two_pi_pos⟩
      simp [F, AddCircle.coe_period, hzero, hfe]
    · exact AddCircle.liftIco_zero_coe_apply ⟨ht.1, lt_of_le_of_ne ht.2 htT⟩
  have hcoeffF (n : ℤ) (hn : n ≠ 0) : angleCoeff F n = 0 := by
    rw [fourierCoeffOn_congr_Icc hFf n]
    rw [fourierCoeffOn_sub_of_continuousOn hv.continuousOn hPC n, hncoeff n hn, sub_self]
  have hconst := eq_at_zero_of_periodic_nonzero_fourier_eq_zero hFc (by
    simp [F, AddCircle.coe_add_period]) hcoeffF θ
  rw [hFf hθ, hFf ⟨le_rfl, Real.two_pi_pos.le⟩] at hconst
  change v θ - P θ = v 0 - P 0 at hconst
  simpa [hP0] using sub_eq_iff_eq_add.mp hconst

/-- Exact shift of the genuine Fourier Sobolev weights. -/
theorem isSobolevSeq_fromL2_shift_iff (s t : ℝ) (b : L2Z) :
    IsSobolevSeq (s + t) (fromL2 t b) ↔ IsSobolevSeq s (b : ℤ → ℂ) := by
  have he (n : ℤ) :
      (sobWeight n ^ (s + t) * ‖fromL2 t b n‖) ^ 2 =
        (sobWeight n ^ s * ‖b n‖) ^ 2 := by
    rw [fromL2, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.rpow_pos_of_pos (sobWeight_pos n) (-t)),
      ← mul_assoc, ← Real.rpow_add (sobWeight_pos n)]
    simp
  simp [IsSobolevSeq, he]

theorem isSobolevSeq_one_fromL2_half_of_half_regular (b : L2Z)
    (hb : IsSobolevSeq halfOrder (b : ℤ → ℂ)) :
    IsSobolevSeq 1 (fromL2 halfOrder b) := by
  simpa only [show halfOrder + halfOrder = 1 by norm_num] using
    (isSobolevSeq_fromL2_shift_iff halfOrder halfOrder b).mpr hb

/-- The normalized conormal preserves true half-order regularity because
its difference from inclusion is the actual one-order smoothing map. -/
theorem normalizedConormal_preserves_half_regular
    {β a g : ℤ → ℂ} (hβ : IsWL1 halfOrder β)
    (ha : IsWL1 halfOrder a) (hg : IsWL1 halfOrder g)
    (E : ℂ) (b : L2Z) (hb : IsSobolevSeq halfOrder (b : ℤ → ℂ)) :
    IsSobolevSeq halfOrder (normalizedConormal hβ ha hg E b : ℤ → ℂ) := by
  have he := congrArg (fun A : FourierOp => A b)
    (normalizedConormal_sub_one_eq hβ ha hg E)
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply,
    ContinuousLinearMap.comp_apply] at he
  have hr : IsSobolevSeq halfOrder
      (sobolevSmoothing 1 zero_le_one (conormalRemOp (by norm_num) hβ ha hg E b - b) : ℤ → ℂ) := by
    exact (sobNormSq_mono (by norm_num : halfOrder ≤ 1)
      (isSobolevSeq_fromL2 1 _)).1
  have hsum := isSobolevSeq_add hb hr
  have heq : normalizedConormal hβ ha hg E b =
      b + sobolevSmoothing 1 zero_le_one (conormalRemOp (by norm_num) hβ ha hg E b - b) := by
    rw [← he]
    abel
  rw [heq]
  exact hsum

/-- Variation of constants for actual ordinary L2 scalar forcing. The
inhomogeneous part is the genuine Duhamel construction. Uniqueness is
applied only to the homogeneous difference, whose forcing is zero. -/
theorem driven_eq_transport_add_physicalDrivenVector_boundaryL2
    {γ : ℝ → ℂ} {L : NNReal} (hγLip : LipschitzWith L γ)
    (hγ : ContDiff ℝ 1 γ) {E : ℝ}
    {W : TransportPath} (hW : IsTransport γ E W)
    (g : BoundaryL2) {y : ℝ → Ell2} (hy : ContinuousOn y angleInterval)
    (hyint : ∀ θ ∈ angleInterval,
      y θ = y 0 + ∫ s in (0 : ℝ)..θ, transportCoeff γ E s (y s) +
        (-(Complex.I / vacuumWeight) * g s) • basisVec 0)
    {θ : ℝ} (hθ : θ ∈ angleInterval) :
    y θ = W θ (y 0) + physicalDrivenVector W (g : ℝ → ℂ) θ := by
  let Y := physicalDrivenVector W (g : ℝ → ℂ)
  let f  := fun s => (-(Complex.I / vacuumWeight) * g s) • basisVec 0
  have hg := intervalIntegrable_boundaryL2 g
  have hY := physicalDrivenVector_continuousOn_of_intervalIntegrable hW.1
    g hg
  have hC : Continuous (transportCoeff γ E) := by
    
    
    unfold transportCoeff
    fun_prop
  have hfi : IntegrableOn f angleInterval := by
    have hgi : IntegrableOn g angleInterval := by
      rw [integrableOn_Icc_iff_integrableOn_Ioc]
      exact (intervalIntegrable_iff_integrableOn_Ioc_of_le Real.two_pi_pos.le).mp hg
    exact (hgi.const_mul (-(Complex.I / vacuumWeight))).smul_const _
  have hyi := ((hC.continuousOn.clm_apply hy).integrableOn_Icc).add hfi
  have hYi := ((hC.continuousOn.clm_apply hY).integrableOn_Icc).add hfi
  have hdiff (t : ℝ) (ht : t ∈ angleInterval) :
      (y t - Y t) = (y 0 - Y 0) + ∫ s in 0..t,
        transportCoeff γ E s (y s - Y s) + 0 := by
    have hs : uIcc 0 t ⊆ angleInterval := by
      rw [uIcc_of_le ht.1]
      exact Icc_subset_Icc le_rfl ht.2
    
    
    dsimp [Y]
    rw [hyint t ht, physicalDrivenVector_integral_eq_of_intervalIntegrable hγLip hγ hW
      g hg ht]
    simp only [physicalDrivenVector_zero, sub_zero]
    rw [show (fun s => transportCoeff γ E s (y s - Y s) + 0) =
      fun s => (transportCoeff γ E s (y s) + f s) -
        (transportCoeff γ E s (Y s) + f s) by simp,
      intervalIntegral.integral_sub (by
        apply intervalIntegrable_iff.mpr
        apply MeasureTheory.IntegrableOn.mono_set hyi
        intro s hs'
        exact hs ⟨hs'.1.le, hs'.2⟩) (by
        apply intervalIntegrable_iff.mpr
        apply MeasureTheory.IntegrableOn.mono_set hYi
        intro s hs'
        exact hs ⟨hs'.1.le, hs'.2⟩)]
    abel
  have hd := driven_eq_transport hγLip hW
    continuous_const.aestronglyMeasurable
    (B := 0) (fun _ => by simp) (hy.sub hY) hdiff θ hθ
  have heq : y θ - Y θ = W θ (y 0) := by
    simpa only [Y, physicalDrivenVector_zero, sub_zero, map_zero, Pi.sub_apply,
      intervalIntegral.integral_zero, add_zero] using hd
  exact sub_eq_iff_eq_add.mp heq

/-- The actual observation integral and Volterra trace agree for every
ordinary L2 input, including unbounded representatives. -/
theorem inner_transport_integral_boundaryL2
    {γ : ℝ → ℂ} {L : NNReal} (hγLip : LipschitzWith L γ) {E : ℝ}
    {W : TransportPath} (hW : IsTransport γ E W) (g : BoundaryL2)
    {θ : ℝ} (hθ : θ ∈ angleInterval) :
    ⟪basisVec 0, W θ (∫ s in (0 : ℝ)..θ,
      g s • ContinuousLinearMap.adjoint (W s) (basisVec 0))⟫_ℂ =
        volterraOp W (g : ℝ → ℂ) θ := by
  have hi : IntervalIntegrable
      (fun s => g s • ContinuousLinearMap.adjoint (W s) (basisVec 0))
      volume 0 θ := by
    apply intervalIntegrable_iff.mpr
    apply MeasureTheory.IntegrableOn.mono_set
      (integrable_boundary_observation_load hγLip hW g)
    grind [Ioc_subset_Ioc]
  have h := ((innerSL ℂ (basisVec 0)).comp (W θ)).intervalIntegral_comp_comm hi
  simp only [ContinuousLinearMap.comp_apply, innerSL_apply_apply] at h
  rw [← h, volterraOp]
  apply intervalIntegral.integral_congr
  intro s hs
  simp [map_smul, inner_smul_right, volterraKernel]
  ring

/-- The true Volterra plus adjoint identity holds for ordinary L2 inputs. -/
theorem volterraOp_add_adj_boundaryL2
    {γ : ℝ → ℂ} {L : NNReal} (hγLip : LipschitzWith L γ) {E : ℝ}
    {W : TransportPath} (hW : IsTransport γ E W) (g : BoundaryL2)
    {θ : ℝ} (hθ : θ ∈ angleInterval) :
    volterraOp W (g : ℝ → ℂ) θ + volterraOpAdj W (g : ℝ → ℂ) θ =
      observation W (observationAdj W (g : ℝ → ℂ)) θ := by
  have hk (s : ℝ) : conj (volterraKernel W s θ) = volterraKernel W θ s := by
    simp only [volterraKernel]
    rw [inner_conj_symm, ← ContinuousLinearMap.adjoint_inner_right,
      ContinuousLinearMap.adjoint_inner_left]
  have hkc  :=
    ((innerSL ℂ (basisVec 0)).comp (W θ)).continuous.comp_continuousOn
      (continuousOn_adjoint_apply hW.1 (basisVec 0))
  
  have hint := (intervalIntegrable_boundaryL2 g).continuousOn_mul
      (by simpa only [uIcc_of_le Real.two_pi_pos.le] using hkc)
  have hi0 : IntervalIntegrable (fun s => volterraKernel W θ s * g s) volume 0 θ :=
    hint.mono_set' (by simp only [uIoc_of_le hθ.1, uIoc_of_le Real.two_pi_pos.le]
                       exact Ioc_subset_Ioc le_rfl hθ.2)
  have hi1 : IntervalIntegrable (fun s => volterraKernel W θ s * g s)
      volume θ anglePeriod :=
    hint.mono_set' (by simp only [uIoc_of_le hθ.2, uIoc_of_le Real.two_pi_pos.le]
                       exact Ioc_subset_Ioc hθ.1 le_rfl)
  simp [volterraOp, volterraOpAdj, hk]
  rw [intervalIntegral.integral_add_adjacent_intervals hi0 hi1, observation, observationAdj]
  have hi : IntervalIntegrable
      (fun s => g s • ContinuousLinearMap.adjoint (W s) (basisVec 0))
      volume 0 anglePeriod :=
    by
      apply intervalIntegrable_iff.mpr
      simpa only [IntegrableOn, uIoc_of_le Real.two_pi_pos.le] using
        (integrable_boundary_observation_load hγLip hW g)
  have h := ((innerSL ℂ (basisVec 0)).comp (W θ)).intervalIntegral_comp_comm hi
  simp only [ContinuousLinearMap.comp_apply, innerSL_apply_apply] at h
  rw [← h]
  apply intervalIntegral.integral_congr
  intro s hs
  simp [map_smul, inner_smul_right, volterraKernel]
  ring

section PhysicalCoordinates

section

variable (Φ : SmoothDiskMap) (E : ℂ) (b : L2Z) (hbhalf : IsSobolevSeq halfOrder (b : ℤ → ℂ))
include E hbhalf Φ

/-- The ordinary coordinate load exists here as a conclusion of genuine
half-order input regularity and the proved normalized smoothing formula. -/
def SmoothDiskMap.vekuaForwardLoad : BoundaryL2 :=
  halfRegularCoordinateLoad (Φ.conormal E b)
    (normalizedConormal_preserves_half_regular (localConformalVelocityCircle_isWL1_half Φ) (localConformalHardyPrimitiveMultiplier_isWL1 Φ) (localConformalCenteredCircle_isWL1_half Φ) E b hbhalf)

theorem localConformalVekuaForwardLoad_normalized :
    sobolevSmoothing halfOrder (by norm_num)
      (boundaryFourier (Φ.vekuaForwardLoad E b hbhalf)) = Φ.conormal E b :=
  halfRegularCoordinateLoad_normalized _ _

end

section

variable (Φ : DiskCoordinates) (E : ℂ) (b : L2Z) (hbn : IsNonpositiveFourierSupport b)
    (hbhalf : IsSobolevSeq halfOrder (b : ℤ → ℂ))
include hbn

/-- Actual Fourier inversion of the exceptional zeroth row with its
genuine coordinate L2 conormal forcing. The zeroth coefficient is used. -/
theorem localConformalVekuaForward_zero_fourier_derivative
    (n : ℤ) :
    angleCoeff
      (((2 * (-E / 4)) •
        boundaryContinuousMultiplier (localConformalVelocityCircle Φ.map)
          ((Φ.pulledBackTrace Φ.lipschitzDomain) (Φ.vekuaH1 (Φ.map 1) E (Φ.hardyPrimitive b))) -
        Complex.I • Φ.vekuaForwardLoad E b hbhalf : BoundaryL2) : ℝ → ℂ) n =
      (Complex.I * (n : ℂ)) * angleCoeff (Φ.vekuaTraceRow E b 0) n := by
  have hb1 := isSobolevSeq_one_fromL2_half_of_half_regular b hbhalf
  let G  := boundaryContinuousMultiplier (localConformalVelocityCircle Φ.map)
    ((Φ.pulledBackTrace Φ.lipschitzDomain) (Φ.vekuaH1 (Φ.map 1) E (Φ.hardyPrimitive b)))
  let g := Φ.vekuaForwardLoad E b hbhalf
  let L  := (2 * (-E / 4)) • G - Complex.I • g
  have ht0 : ((Φ.pulledBackTrace Φ.lipschitzDomain) (Φ.vekuaH1 (Φ.map 1) E b) : ℝ → ℂ)
      =ᵐ[angleMeasure] Φ.vekuaTraceRow E b 0 := by
    exact localConformalVekua_coordinate_trace_reconstruction_ae Φ E b hbn hb1
  have hNC := localConformalVekua_normalizedConormal_fourier Φ E b hbn hb1 n
  have hload := congrArg (fun v : L2Z => v n)
    (localConformalVekuaForwardLoad_normalized Φ E b hbhalf)
  
  simp only [localConformalVekuaGradientA_apply, map_smul, lp.coeFn_smul,
    Pi.smul_apply, smul_eq_mul] at hNC
  have hw : ((sobWeight n ^ (-halfOrder) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.rpow_pos_of_pos (sobWeight_pos n) (-halfOrder)).ne'
  have hn : -(n : ℂ) * boundaryFourier ((Φ.pulledBackTrace Φ.lipschitzDomain) (Φ.vekuaH1 (Φ.map 1) E b)) n -
      2 * Complex.I * ((-E / 4) * boundaryFourier G n) = boundaryFourier g n :=
    mul_left_cancel₀ hw (hNC.symm.trans hload.symm)
  have hs0 : fourierScale ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr Real.two_pi_pos).ne'
  apply mul_left_cancel₀ hs0
  calc
    _ = boundaryFourier L n := (boundaryFourier_apply L n).symm
    _ = (Complex.I * (n : ℂ)) * boundaryFourier ((Φ.pulledBackTrace Φ.lipschitzDomain) (Φ.vekuaH1 (Φ.map 1) E b)) n := by
      simp only [L, map_sub, map_smul, lp.coeFn_sub, Pi.sub_apply,
        lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]
      rw [← hn]
      ring_nf
      simp
    _ = _ := by rw [kernel_conormal_coeff_ae _ ht0]; ring

private theorem forward_zero_derivative_ae :
    (((2 * (-E / 4)) •
      boundaryContinuousMultiplier (localConformalVelocityCircle Φ.map)
        ((Φ.pulledBackTrace Φ.lipschitzDomain) (Φ.vekuaH1 (Φ.map 1) E (Φ.hardyPrimitive b))) -
      Complex.I • Φ.vekuaForwardLoad E b hbhalf : BoundaryL2) : ℝ → ℂ)
      =ᵐ[angleMeasure]
        fun t => 2 * (-E / 4) * deriv Φ.boundary t * Φ.vekuaTraceRow E b 1 t -
          Complex.I * Φ.vekuaForwardLoad E b hbhalf t := by
  have hb1 := isSobolevSeq_one_fromL2_half_of_half_regular b hbhalf
  let G  := boundaryContinuousMultiplier (localConformalVelocityCircle Φ.map)
    ((Φ.pulledBackTrace Φ.lipschitzDomain) (Φ.vekuaH1 (Φ.map 1) E (Φ.hardyPrimitive b)))
  let g := Φ.vekuaForwardLoad E b hbhalf
  have hJbn := localConformalHardyPrimitive_nonpositive Φ Φ.holomorphic b hbn
  have hJ1 := kernel_conormal_primitive_raw_H1 Φ b hb1 1
  have ht1 := localConformalVekua_coordinate_trace_reconstruction_ae Φ E (Φ.hardyPrimitive b) hJbn hJ1
  filter_upwards [Lp.coeFn_sub ((2 * (-E / 4)) • G) (Complex.I • g),
    Lp.coeFn_smul (2 * (-E / 4)) G, Lp.coeFn_smul Complex.I g,
    boundaryContinuousMultiplier_ae (localConformalVelocityCircle Φ.map)
      ((Φ.pulledBackTrace Φ.lipschitzDomain) (Φ.vekuaH1 (Φ.map 1) E (Φ.hardyPrimitive b))), ht1] with t hsub hs ht hG htrace
  rw [hsub]
  simp
  rw [hs, ht]
  simp only [Pi.smul_apply, smul_eq_mul, G, g, hG, htrace,
    localConformalVelocityCircle_apply Φ, DiskCoordinates.vekuaTraceRow, pow_one]
  ring

/-- The exceptional zero row has its true inhomogeneous primitive
formula, with the actual initial constant and ordinary L2 coordinate load. -/
theorem localConformalVekuaForward_zero_integral_eq
    {θ : ℝ} (hθ : θ ∈ angleInterval) :
    Φ.vekuaTraceRow E b 0 θ = Φ.vekuaTraceRow E b 0 0 + ∫ t in (0 : ℝ)..θ,
      2 * (-E / 4) * deriv Φ.boundary t * Φ.vekuaTraceRow E b 1 t -
        Complex.I * Φ.vekuaForwardLoad E b hbhalf t := by
  have hb1 := isSobolevSeq_one_fromL2_half_of_half_regular b hbhalf
  let L  := (2 * (-E / 4)) •
    boundaryContinuousMultiplier (localConformalVelocityCircle Φ.map) ((Φ.pulledBackTrace Φ.lipschitzDomain) (Φ.vekuaH1 (Φ.map 1) E (Φ.hardyPrimitive b))) -
      Complex.I • Φ.vekuaForwardLoad E b hbhalf
  have hprimitive := eq_add_integral_of_L2_periodic_fourier_derivative
    (localConformalVekuaTraceRow_continuous Φ E b hbn hb1 0)
    (localConformalVekuaTraceRow_periodic Φ E b 0) L
    (localConformalVekuaForward_zero_fourier_derivative Φ E b hbn hbhalf) hθ
  rw [hprimitive]
  congr 1
  apply intervalIntegral.integral_congr_ae
  have hAE := (ae_restrict_iff' measurableSet_Ioc).mp
    (forward_zero_derivative_ae Φ E b hbn hbhalf)
  filter_upwards [hAE] with t ht hmem
  rw [uIoc_of_le hθ.1] at hmem
  exact ht ⟨hmem.1, hmem.2.trans hθ.2⟩

end

section

variable (Φ : DiskCoordinates) (E : ℝ) (hE : 0 ≤ E) (b : L2Z)
    (hbn : IsNonpositiveFourierSupport b) (hbhalf : IsSobolevSeq halfOrder (b : ℤ → ℂ))
include hE hbn

private theorem forward_zero_transportCoeff
    (hb1 : IsSobolevSeq 1 (fromL2 halfOrder b)) {θ : ℝ} (hθ : θ ∈ angleInterval) :
    (2 * (-(E : ℂ) / 4) * deriv Φ.boundary θ * Φ.vekuaTraceRow (E : ℂ) b 1 θ) /
        vacuumWeight =
      (transportCoeff Φ.boundary E θ (Φ.vekuaTransportVector E b θ) : ℕ → ℂ) 0 := by
  rw [transportCoeff_coord_zero,
    localConformalVekuaTransportVector_coord Φ E b hbn hb1 hθ 1]
  simp only [DiskCoordinates.vekuaTransportCoordinate, if_false, Nat.one_ne_zero, pow_one]
  change _ = physicalDrivenQ E * _
  rw [← physicalDrivenQ_sq hE]
  have hs : vacuumWeight ^ 2 = 2 := by
    exact_mod_cast (by norm_num)
  have hs0 : vacuumWeight ≠ 0 := by
    simp
  field_simp [hs0]
  linear_combination -(physicalDrivenQ E ^ 2 * deriv Φ.boundary θ *
    Φ.vekuaTraceRow (E : ℂ) b 1 θ) * hs

/-- The full actual Ell2 trace vector obeys the driven integral equation.
Positive rows come from the genuine factorial series; only the exceptional
zeroth row uses the actual L2 primitive inversion. -/
theorem localConformalVekuaForward_transport_integral_eq {θ : ℝ} (hθ : θ ∈ angleInterval) :
    Φ.vekuaTransportVector E b θ = Φ.vekuaTransportVector E b 0 + ∫ s in (0 : ℝ)..θ,
      transportCoeff Φ.boundary E s (Φ.vekuaTransportVector E b s) +
        (-(Complex.I / vacuumWeight) *
          Φ.vekuaForwardLoad (E : ℂ) b hbhalf s) • basisVec 0 := by
  have hb1 := isSobolevSeq_one_fromL2_half_of_half_regular b hbhalf
  let y := Φ.vekuaTransportVector E b
  let p := Φ.vekuaPositiveTransportVector E b
  let z  := fun s => Φ.vekuaTraceRow (E : ℂ) b 0 s / vacuumWeight
  let g := Φ.vekuaForwardLoad (E : ℂ) b hbhalf
  let Cg := fun s => transportCoeff Φ.boundary E s (y s)
  let a  := fun s =>
    (2 * (-(E : ℂ) / 4) * deriv Φ.boundary s * Φ.vekuaTraceRow (E : ℂ) b 1 s -
      Complex.I * g s) / vacuumWeight
  have hy := localConformalVekuaTransportVector_continuousOn Φ E b hbn hb1
  have hΓ  :=
    Φ.boundaryC1
  have hCoeff : Continuous (transportCoeff Φ.boundary E) := by
    have hd := hΓ.continuous_deriv_one
    
    unfold transportCoeff
    fun_prop
  have hCg : ContinuousOn Cg angleInterval := hCoeff.continuousOn.clm_apply hy
  have hC0 : ContinuousOn (fun s => (Cg s : ℕ → ℂ) 0) angleInterval := by
    have h := (innerSL ℂ (basisVec 0)).continuous.continuousOn.comp hCg
      (fun _ _ => Set.mem_univ _)
    convert h using 1
    · funext s
      simp [inner_basisVec]
  have hpd : ContinuousOn (fun s => Cg s - ((Cg s : ℕ → ℂ) 0) • basisVec 0)
      angleInterval := hCg.sub (hC0.smul continuousOn_const)
  have hz : Continuous z :=
    (localConformalVekuaTraceRow_continuous Φ (E : ℂ) b hbn hb1 0).div_const _
  have hsplit (s : ℝ) (hs : s ∈ angleInterval) : y s = z s • basisVec 0 + p s :=
    localConformalVekuaTransportVector_zero_add_positive Φ E b hbn hb1 hs
  have hp : ContinuousOn p angleInterval := by
    apply (hy.sub (hz.continuousOn.smul
      (continuousOn_const : ContinuousOn (fun _ : ℝ => basisVec 0)
        angleInterval))).congr
    intro s hs
    change p s = y s - z s • basisVec 0
    simp [*]
  have hsub : Icc 0 θ ⊆ angleInterval := Icc_subset_Icc le_rfl hθ.2
  have hpi : IntervalIntegrable (fun s => Cg s - ((Cg s : ℕ → ℂ) 0) • basisVec 0)
      volume 0 θ := by
    exact (hpd.mono (by simpa only [uIcc_of_le hθ.1] using hsub)).intervalIntegrable
  have hip := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hθ.1 (hp.mono hsub)
    (fun s hs => (localConformalVekuaPositiveTransportVector_hasDerivAt Φ E b hbn hb1 ⟨hs.1, hs.2.trans_le hθ.2⟩).congr_deriv (localConformalVekuaPositiveTransportDerivative_tsum_eq Φ E hE b hbn hb1 ⟨hs.1.le, hs.2.le.trans hθ.2⟩)) hpi
  have hzp : z θ = z 0 + ∫ s in (0 : ℝ)..θ, a s := by
    have h := congrArg (fun v : ℂ => v / vacuumWeight)
      (localConformalVekuaForward_zero_integral_eq Φ (E : ℂ) b hbn hbhalf hθ)
    simpa [z, a, g, add_div, intervalIntegral.integral_div] using h
  have hac : Continuous (fun s => 2 * (-(E : ℂ) / 4) * deriv Φ.boundary s *
      Φ.vekuaTraceRow (E : ℂ) b 1 s) := (continuous_const.mul hΓ.continuous_deriv_one).mul
        (localConformalVekuaTraceRow_continuous Φ (E : ℂ) b hbn hb1 1)
  have hgi : IntervalIntegrable (g : ℝ → ℂ) volume 0 θ :=
    (intervalIntegrable_boundaryL2 g).mono_set' (by
      simp only [uIoc_of_le hθ.1, uIoc_of_le Real.two_pi_pos.le]
      exact Ioc_subset_Ioc le_rfl hθ.2)
  have hai : IntervalIntegrable a volume 0 θ :=
    ((hac.intervalIntegrable 0 θ).sub (hgi.const_mul Complex.I)).div_const _
  calc
    _ = z θ • basisVec 0 + p θ := hsplit θ hθ
    _ = (z 0 • basisVec 0 + p 0) +
        ((∫ s in (0 : ℝ)..θ, a s) • basisVec 0 +
          ∫ s in (0 : ℝ)..θ, Cg s - ((Cg s : ℕ → ℂ) 0) • basisVec 0) := by
      rw [hzp, sub_eq_iff_eq_add.mp hip.symm, add_smul]
      abel
    _ = y 0 + ∫ s in (0 : ℝ)..θ,
        (a s • basisVec 0 + (Cg s - ((Cg s : ℕ → ℂ) 0) • basisVec 0)) := by
      have hai' : IntervalIntegrable (fun s => a s • basisVec 0)
          volume 0 θ := by
        exact ⟨MeasureTheory.Integrable.smul_const hai.1 _,
          MeasureTheory.Integrable.smul_const hai.2 _⟩
      rw [← hsplit 0 ⟨le_rfl, Real.two_pi_pos.le⟩,
        ← intervalIntegral.integral_smul_const,
        ← intervalIntegral.integral_add hai' hpi]
    _ = _ := by
      congr 1
      apply intervalIntegral.integral_congr
      intro s hs
      rw [uIcc_of_le hθ.1] at hs
      have hsc : s ∈ angleInterval := ⟨hs.1, hs.2.trans hθ.2⟩
      have hzero := forward_zero_transportCoeff Φ E hE b hbn hb1 hsc
      have haeq : a s = (Cg s : ℕ → ℂ) 0 - (Complex.I / vacuumWeight) * g s := by
        dsimp only [a]
        rw [sub_div, hzero]
        ring
      change a s • basisVec 0 + (Cg s - ((Cg s : ℕ → ℂ) 0) • basisVec 0) =
        Cg s + (-(Complex.I / vacuumWeight) * g s) • basisVec 0
      rw [haeq, sub_smul]
      simp only [neg_mul, neg_smul]
      abel

/-- The actual forward vector equals genuine homogeneous transport plus
the true L2 Duhamel vector. No forced ODE is assumed. -/
theorem localConformalVekuaForward_transport_eq {L : NNReal}
    (hΓLip : LipschitzWith L Φ.boundary) {W : TransportPath}
    (hW : IsTransport Φ.boundary E W) {θ : ℝ} (hθ : θ ∈ angleInterval) :
    Φ.vekuaTransportVector E b θ = W θ (Φ.vekuaTransportVector E b 0) +
      physicalDrivenVector W (Φ.vekuaForwardLoad (E : ℂ) b hbhalf : ℝ → ℂ) θ := by
  have hb1 := isSobolevSeq_one_fromL2_half_of_half_regular b hbhalf
  exact driven_eq_transport_add_physicalDrivenVector_boundaryL2 hΓLip
    Φ.boundaryC1 hW
    (Φ.vekuaForwardLoad (E : ℂ) b hbhalf)
    (localConformalVekuaTransportVector_continuousOn Φ E b hbn hb1)
    (fun t ht => localConformalVekuaForward_transport_integral_eq Φ E hE b hbn hbhalf ht) hθ

/-- The periodic endpoint of the actual trace vector determines its true
adjoint observation, with the original initial constant and sqrt(2) scale. -/
theorem localConformalVekuaForward_observationAdj_eq_cut {L : NNReal}
    (hΓLip : LipschitzWith L Φ.boundary) {W : TransportPath}
    (hW : IsTransport Φ.boundary E W) :
    observationAdj W
      (Φ.vekuaForwardLoad (E : ℂ) b hbhalf : ℝ → ℂ) =
        (Complex.I * hardyFourierTrace (normalizedHardyAverage b) 0) •
          cutVector W := by
  have hb1 := isSobolevSeq_one_fromL2_half_of_half_regular b hbhalf
  let y := Φ.vekuaTransportVector E b
  let g := Φ.vekuaForwardLoad (E : ℂ) b hbhalf
  let h0 := hardyFourierTrace (normalizedHardyAverage b) 0
  let s := h0 / vacuumWeight
  have hinit : y 0 = s • basisVec 0 :=
    localConformalVekuaTransportVector_origin Φ E b hbn hb1
  have hper : y anglePeriod = y 0 := by
    simpa only [zero_add] using localConformalVekuaTransportVector_periodic Φ E b 0
  have hT : anglePeriod ∈ angleInterval := ⟨Real.two_pi_pos.le, le_rfl⟩
  have hform := localConformalVekuaForward_transport_eq Φ E hE b hbn hbhalf hΓLip hW hT
  change y anglePeriod = W anglePeriod (y 0) +
    (-(Complex.I / vacuumWeight)) • W anglePeriod
      (observationAdj W (g : ℝ → ℂ)) at hform
  rw [hper] at hform
  have hu : ContinuousLinearMap.adjoint (W anglePeriod) * W anglePeriod = 1 := by
    
    exact (transport_mem_unitary hΓLip hW hT).1
  have hadj := congrArg (ContinuousLinearMap.adjoint (W anglePeriod)) hform
  
  rw [map_add, map_smul, ← ContinuousLinearMap.mul_apply, hu,
    ContinuousLinearMap.one_apply, ← ContinuousLinearMap.mul_apply, hu,
    ContinuousLinearMap.one_apply] at hadj
  have hsub : ContinuousLinearMap.adjoint (W anglePeriod) (y 0) - y 0 =
      (-(Complex.I / vacuumWeight)) • observationAdj W (g : ℝ → ℂ) := by
    simp [hadj]
  have hs0 : vacuumWeight ≠ 0 := by
    simp
  have hcancel : vacuumWeight * Complex.I * -(Complex.I / vacuumWeight) = 1 := by
    field_simp [hs0] ; simp
  have hO : observationAdj W (g : ℝ → ℂ) = (vacuumWeight * Complex.I) •
      (ContinuousLinearMap.adjoint (W anglePeriod) (y 0) - y 0) := by
    rw [hsub, smul_smul, hcancel, one_smul]
  rw [hO, hinit, map_smul, ← smul_sub, smul_smul]
  have hscalar : (vacuumWeight * Complex.I) * s = Complex.I * h0 := by
    dsimp only [s]
    field_simp [hs0]
  simp [hscalar, h0, cutC]

include hbhalf in
/-- The projected observation annihilates the genuine normalized conormal
range on every half-regular full Hardy input, including frequency zero. -/
theorem localConformalVekuaForward_projObsDual_eq_zero_of_half_regular {L : NNReal}
    (hΓLip : LipschitzWith L Φ.boundary) {W : TransportPath}
    (hW : IsTransport Φ.boundary E W) :
    projObsDual W (Φ.conormal (E : ℂ) b) = 0 := by
  have h := projObsDual_boundary_normalized hΓLip hW
    (Φ.vekuaForwardLoad (E : ℂ) b hbhalf)
  rw [localConformalVekuaForwardLoad_normalized, map_smul,
    localConformalVekuaForward_observationAdj_eq_cut Φ E hE b hbn hbhalf hΓLip hW,
    map_smul, cutProj_eq_starProjection,
    Submodule.starProjection_orthogonal_apply_eq_zero (Submodule.mem_span_singleton_self _),
    smul_zero] at h
  exact (smul_eq_zero.mp h).resolve_left (by
    exact_mod_cast (by positivity))

/-- The actual coordinate trace obeys the true forward observation and
Volterra identity for its derived ordinary L2 conormal load. -/
theorem localConformalVekuaForward_trace_eq {L : NNReal}
    (hΓLip : LipschitzWith L Φ.boundary) {W : TransportPath}
    (hW : IsTransport Φ.boundary E W) {θ : ℝ} (hθ : θ ∈ angleInterval) :
    Φ.vekuaTraceRow (E : ℂ) b 0 θ = hardyFourierTrace (normalizedHardyAverage b) 0 *
      observation W (basisVec 0) θ - Complex.I *
        volterraOp W (Φ.vekuaForwardLoad (E : ℂ) b hbhalf : ℝ → ℂ) θ := by
  have hb1 := isSobolevSeq_one_fromL2_half_of_half_regular b hbhalf
  let g := Φ.vekuaForwardLoad (E : ℂ) b hbhalf
  have hform := localConformalVekuaForward_transport_eq Φ E hE b hbn hbhalf hΓLip hW hθ
  have hinner := congrArg (fun v : Ell2 => ⟪basisVec 0, v⟫_ℂ) hform
  simp only [inner_add_right] at hinner
  have hleft : ⟪basisVec 0, Φ.vekuaTransportVector E b θ⟫_ℂ = Φ.vekuaTraceRow (E : ℂ) b 0 θ / vacuumWeight := by
    simpa only [inner_basisVec, DiskCoordinates.vekuaTransportCoordinate, if_true] using
      localConformalVekuaTransportVector_coord Φ E b hbn hb1 hθ 0
  have hinit : ⟪basisVec 0, W θ (Φ.vekuaTransportVector E b 0)⟫_ℂ =
      (hardyFourierTrace (normalizedHardyAverage b) 0 / vacuumWeight) *
        observation W (basisVec 0) θ := by
    change ⟪basisVec 0, W θ (Φ.vekuaTransportVector E b 0)⟫_ℂ =
      (hardyFourierTrace (normalizedHardyAverage b) 0 / vacuumWeight) *
        ⟪basisVec 0, W θ (basisVec 0)⟫_ℂ
    rw [localConformalVekuaTransportVector_origin Φ E b hbn hb1, map_smul, inner_smul_right]
  have hforced : ⟪basisVec 0, physicalDrivenVector W (g : ℝ → ℂ) θ⟫_ℂ =
      -(Complex.I / vacuumWeight) * volterraOp W (g : ℝ → ℂ) θ := by
    rw [physicalDrivenVector, inner_smul_right, inner_transport_integral_boundaryL2 hΓLip hW g hθ]
  rw [hleft, hinit, hforced] at hinner
  have hs0 : vacuumWeight ≠ 0 := by
    simp
  apply (div_left_inj' hs0).mp
  rw [hinner]
  ring

/-- The genuine periodic form vanishes on the actual forward Vekua trace
and its actual L2 load. A nonzero cut is used only by the correction B. -/
theorem localConformalVekuaForward_periodicP_eq_zero {L : NNReal}
    (hΓLip : LipschitzWith L Φ.boundary) {W : TransportPath}
    (hW : IsTransport Φ.boundary E W) (hc : cutVector W ≠ 0)
    {θ : ℝ} (hθ : θ ∈ angleInterval) :
    periodicP W (Φ.vekuaTraceRow (E : ℂ) b 0)
      (Φ.vekuaForwardLoad (E : ℂ) b hbhalf : ℝ → ℂ) θ = 0 := by
  let g := Φ.vekuaForwardLoad (E : ℂ) b hbhalf
  let h0 := hardyFourierTrace (normalizedHardyAverage b) 0
  have hsum := volterraOp_add_adj_boundaryL2 hΓLip hW g hθ
  have hO := localConformalVekuaForward_observationAdj_eq_cut Φ E hE b hbn hbhalf hΓLip hW
  change observationAdj W (g : ℝ → ℂ) = (Complex.I * h0) •
    cutVector W at hO
  have hS : cutS (W anglePeriod) (basisVec 0) =
      (2 : ℂ) • basisVec 0 + cutVector W := by
    simp [cutS, cutC, two_smul]
  have hA : periodicA W (Φ.vekuaTraceRow (E : ℂ) b 0) (g : ℝ → ℂ) θ =
      h0 * observation W (cutS (W anglePeriod) (basisVec 0)) θ := by
    rw [hO] at hsum
    rw [periodicA, localConformalVekuaForward_trace_eq Φ E hE b hbn hbhalf hΓLip hW hθ, hS]
    simp only [observation, map_add, map_smul, inner_add_right, inner_smul_right] at hsum ⊢
    linear_combination (-Complex.I) * hsum - Complex.I_sq *
      (h0 * ⟪basisVec 0, W θ (cutVector W)⟫_ℂ)
  have hBc := (cutB_transport (transport_mem_unitary hΓLip hW
    ⟨Real.two_pi_pos.le, le_rfl⟩) (basisVec 0) hc).2
  rw [periodicP, hA, hO, map_smul, hBc, smul_smul]
  simp [observation, map_smul, inner_smul_right]
  linear_combination Complex.I_sq *
    (h0 * ⟪basisVec 0, W θ (cutS (W anglePeriod) (basisVec 0))⟫_ℂ)

end

theorem forward_half_regular_stdBasis (n : ℤ) :
    IsSobolevSeq halfOrder (stdBasisZ n : ℤ → ℂ) := by
  apply summable_of_ne_finset_zero (s := {n})
  intro k hk
  have hkn : k ≠ n := by simpa only [Finset.mem_singleton] using hk
  simp [stdBasisZ_apply, lp.single_apply, hkn]

/-- Genuine finite Fourier density extends the bounded projected-null
identity to every normalized full Hardy input. No L2 load for those
possibly rough inputs is asserted by this extension. -/
theorem localConformalVekuaForward_projObsDual_eq_zero (Φ : DiskCoordinates) (E : ℝ)
    (hE : 0 ≤ E) {L : NNReal} (hΓLip : LipschitzWith L Φ.boundary)
    {W : TransportPath} (hW : IsTransport Φ.boundary E W) (b : L2Z)
    (hbn : IsNonpositiveFourierSupport b) :
    projObsDual W (Φ.conormal (E : ℂ) b) = 0 := by
  have hop : (projObsDual W).comp ((Φ.conormal (E : ℂ)).comp (1 - posProj)) = 0 := by
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
      rw [hzero, map_zero, map_zero]
    · have hkeep : (1 - posProj) (stdBasisZ n) = stdBasisZ n := by
        apply lp.ext
        funext k
        by_cases hkn : k = n
        · subst k
          simp [posProj, hn]
        · simp [ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply,
            posProj, diagOp_apply, stdBasisZ_apply, lp.single_apply, hkn]
      rw [hkeep]
      apply localConformalVekuaForward_projObsDual_eq_zero_of_half_regular Φ E hE (stdBasisZ n) _
        (forward_half_regular_stdBasis n) hΓLip hW
      intro k hk
      have hkn : k ≠ n := by omega
      simp [stdBasisZ_apply, lp.single_apply, hkn]
  have hkeep : (1 - posProj) b = b := by
    apply lp.ext
    funext n
    by_cases hn : 0 < n
    · simp [posProj, hn, hbn n hn]
    · simp [posProj, hn]
  
  simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.zero_apply, hkeep] using congrArg (fun A : L2Z →L[ℂ] Ell2 => A b) hop

end PhysicalCoordinates

end PolyaNeumann

end
