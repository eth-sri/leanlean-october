module

public import RequestProject.LocalConformalReducedCoercivity
public import RequestProject.PeriodicForm

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

namespace PolyaNeumann

open Set MeasureTheory Filter Metric
open scoped Topology ComplexConjugate InnerProductSpace

local instance forwardTwoPiPos : Fact (0 < 2 * Real.pi) := ⟨Real.two_pi_pos⟩

variable (b : L2Z) {γ : ℝ → ℂ} {L : NNReal}

/-- Fourier inversion for an actual L2 derivative. No absolute continuity
or differentiability of the original continuous function is assumed. -/
theorem eq_add_integral_of_L2_periodic_fourier_derivative
    {v : ℝ → ℂ} (hv : Continuous v)
    (hvper : Function.Periodic v (2 * Real.pi)) (d : BoundaryL2)
    (hcoeff : ∀ n : ℤ, fourierCoeffOn Real.two_pi_pos d n =
      (Complex.I * n) * fourierCoeffOn Real.two_pi_pos v n)
    {θ : ℝ} (hθ : θ ∈ Icc 0 (2 * Real.pi)) :
    v θ = v 0 + ∫ s in 0..θ, d s := by
  let P  := fun t => ∫ s in 0..t, d s
  have hPi := intervalIntegrable_boundaryL2 d
  have hPAC  :=
    absolutelyContinuousOnInterval_intervalIntegral_banach hPi
      (by rw [uIcc_of_le Real.two_pi_pos.le]; exact ⟨le_rfl, Real.two_pi_pos.le⟩)
  have hPC : ContinuousOn P (Icc 0 (2 * Real.pi)) := by
    simpa only [uIcc_of_le Real.two_pi_pos.le] using hPAC.continuousOn
  have hP0 : P 0 = 0 := by simp [P]
  have hPT : P (2 * Real.pi) = 0 :=
    integral_eq_zero_of_periodic_fourier_derivative hcoeff
  have hPc (n : ℤ) : fourierCoeffOn Real.two_pi_pos d n =
      (Complex.I * n) * fourierCoeffOn Real.two_pi_pos P n :=
    fourierCoeffOn_of_ac_ae_hasDerivAt hPAC (Lp.memLp d) (ae_hasDerivAt_intervalIntegral_banach Real.two_pi_pos.le hPi) (hP0.trans hPT.symm) n
  have hncoeff (n : ℤ) (hn : n ≠ 0) :
      fourierCoeffOn Real.two_pi_pos v n = fourierCoeffOn Real.two_pi_pos P n :=
    mul_left_cancel₀ (mul_ne_zero Complex.I_ne_zero (Int.cast_ne_zero.mpr hn))
      ((hcoeff n).symm.trans (hPc n))
  let f  := fun t => v t - P t
  have hfe : f 0 = f (2 * Real.pi) := by
    dsimp only [f]
    rw [hP0, hPT, sub_zero, sub_zero]
    simpa only [zero_add] using (hvper 0).symm
  let F : ℝ → ℂ := fun t => AddCircle.liftIco (2 * Real.pi) 0 f
    t
  have hFc : Continuous F :=
    (AddCircle.liftIco_zero_continuous hfe (hv.continuousOn.sub hPC)).comp (AddCircle.continuous_mk' _)
  have hFf : EqOn F f (Icc 0 (2 * Real.pi)) := by
    intro t ht
    by_cases htT : t = 2 * Real.pi
    · subst t
      have hzero : AddCircle.liftIco (2 * Real.pi) 0 f
          0 = f 0 :=
        AddCircle.liftIco_zero_coe_apply ⟨le_rfl, Real.two_pi_pos⟩
      simp [F, AddCircle.coe_period, hzero, hfe]
    · exact AddCircle.liftIco_zero_coe_apply ⟨ht.1, lt_of_le_of_ne ht.2 htT⟩
  have hcoeffF (n : ℤ) (hn : n ≠ 0) : fourierCoeffOn Real.two_pi_pos F n = 0 := by
    rw [fourierCoeffOn_congr_Icc hFf n]
    rw [fourierCoeffOn_sub_of_continuousOn hv.continuousOn hPC n, hncoeff n hn, sub_self]
  have hconst := eq_at_zero_of_periodic_nonzero_fourier_eq_zero hFc (by
    continuity) hcoeffF θ
  rw [hFf ⟨le_rfl, Real.two_pi_pos.le⟩] at hconst
  grind

/-- Exact shift of the genuine Fourier Sobolev weights. -/
theorem isSobolevSeq_fromL2_shift_iff (s t : ℝ) (b : L2Z) :
    IsSobolevSeq (s + t) (fromL2 t b) ↔ IsSobolevSeq s b := by
  have he (n : ℤ) :
      (sobWeight n ^ (s + t) * ‖fromL2 t b n‖) ^ 2 =
        (sobWeight n ^ s * ‖b n‖) ^ 2 := by
    simp [fromL2, abs_of_pos (Real.rpow_pos_of_pos (sobWeight_pos n) (-t)), ← mul_assoc, ← Real.rpow_add (sobWeight_pos n)]
  simp [IsSobolevSeq, he]

theorem isSobolevSeq_one_fromL2_half_of_half_regular (hb : IsSobolevSeq (1 / 2) b) :
    IsSobolevSeq 1 (fromL2 (1 / 2) b) := by
  simpa only [show (1 / 2 : ℝ) + 1 / 2 = 1 by norm_num] using
    (isSobolevSeq_fromL2_shift_iff (1 / 2) (1 / 2) b).mpr hb

/-- The normalized conormal preserves true half-order regularity because
its difference from inclusion is the actual one-order smoothing map. -/
theorem normalizedConormal_preserves_half_regular
    {β a g : ℤ → ℂ} (hβ : IsWL1 (1 / 2) β)
    (ha : IsWL1 (1 / 2) a) (hg : IsWL1 (1 / 2) g)
    (E : ℂ) (b : L2Z) (hb : IsSobolevSeq (1 / 2) b) :
    IsSobolevSeq (1 / 2) (normalizedConormal hβ ha hg E b) := by
  have he := congrArg (fun A  => A b)
    (normalizedConormal_sub_one_eq hβ ha hg E)
  have hr : IsSobolevSeq (1 / 2)
      (sobolevSmoothing 1 zero_le_one (conormalRemOp (by norm_num) hβ ha hg E b - b)) := (sobNormSq_mono (by norm_num)
      (isSobolevSeq_fromL2 1 _)).1
  have hsum := isSobolevSeq_add hb hr
  have heq : normalizedConormal hβ ha hg E b =
      b + sobolevSmoothing 1 zero_le_one (conormalRemOp (by norm_num) hβ ha hg E b - b) := by
    grind
  continuity

/-- Variation of constants for actual ordinary L2 scalar forcing. The
inhomogeneous part is the genuine Duhamel construction. Uniqueness is
applied only to the homogeneous difference, whose forcing is zero. -/
theorem driven_eq_transport_add_physicalDrivenVector_boundaryL2
    (hγLip : LipschitzWith L γ)
    (hγ : ContDiff ℝ 1 γ) {E : ℝ}
    {W : ℝ → Ell2 →L[ℂ] Ell2} (hW : IsTransport γ E W)
    (g : BoundaryL2) {y : ℝ → Ell2} (hy : ContinuousOn y (Icc 0 (2 * Real.pi)))
    (hyint : ∀ θ ∈ Icc 0 (2 * Real.pi),
      y θ = y 0 + ∫ s in 0..θ, transportCoeff γ E s (y s) +
        (-(Complex.I / Real.sqrt 2) * g s) • basisVec 0)
    {θ : ℝ} (hθ : θ ∈ Icc 0 (2 * Real.pi)) :
    y θ = W θ (y 0) + physicalDrivenVector W g θ := by
  let Y := physicalDrivenVector W g
  let f  := fun s => (-(Complex.I / Real.sqrt 2) * g s) • basisVec 0
  have hg := intervalIntegrable_boundaryL2 g
  have hY := physicalDrivenVector_continuousOn_of_intervalIntegrable hW.1
    g hg
  have hC : Continuous (transportCoeff γ E) := by
    unfold transportCoeff
    fun_prop
  have hfi : IntegrableOn f (Icc 0 (2 * Real.pi)) := by
    have hgi : IntegrableOn g (Icc 0 (2 * Real.pi)) := by
      rw [integrableOn_Icc_iff_integrableOn_Ioc]
      exact (intervalIntegrable_iff_integrableOn_Ioc_of_le Real.two_pi_pos.le).mp hg
    exact (hgi.const_mul (-(Complex.I / Real.sqrt 2))).smul_const _
  have hYi := ((hC.continuousOn.clm_apply hY).integrableOn_Icc).add hfi
  have hdiff (t : ℝ) (ht : t ∈ Icc 0 (2 * Real.pi)) :
      (y t - Y t) = (y 0 - Y 0) + ∫ s in 0..t,
        transportCoeff γ E s (y s - Y s) + 0 := by
    have hs : uIcc 0 t ⊆ Icc 0 (2 * Real.pi) := by
      rw [uIcc_of_le ht.1]
      grind
    dsimp only [Y]
    rw [hyint t ht, physicalDrivenVector_integral_eq_of_intervalIntegrable hγLip hγ hW
      g hg ht]
    simp only [physicalDrivenVector_zero]
    rw [show (fun s => transportCoeff γ E s (y s - Y s) + 0) =
      fun s => (transportCoeff γ E s (y s) + f s) -
        (transportCoeff γ E s (Y s) + f s) by norm_num,
      intervalIntegral.integral_sub (by
      apply intervalIntegrable_iff.mpr
      apply MeasureTheory.IntegrableOn.mono_set (((hC.continuousOn.clm_apply hy).integrableOn_Icc).add hfi)
      grind) (by
      apply intervalIntegrable_iff.mpr
      apply MeasureTheory.IntegrableOn.mono_set hYi
      grind)]
    abel
  have hd := driven_eq_transport hγLip hW
    continuous_const.aestronglyMeasurable
    (B := 0) (fun _ => by simp) (hy.sub hY) hdiff θ hθ
  have heq : y θ - Y θ = W θ (y 0) := by
    continuity
  grind

/-- The actual observation integral and Volterra trace agree for every
ordinary L2 input, including unbounded representatives. -/
theorem inner_transport_integral_boundaryL2
    (hγLip : LipschitzWith L γ) {E : ℝ}
    {W : ℝ → Ell2 →L[ℂ] Ell2} (hW : IsTransport γ E W) (g : BoundaryL2)
    {θ : ℝ} (hθ : θ ∈ Icc 0 (2 * Real.pi)) :
    ⟪basisVec 0, W θ (∫ s in 0..θ,
      g s • ContinuousLinearMap.adjoint (W s) (basisVec 0))⟫_ℂ =
        volterraOp W g θ := by
  have hi : IntervalIntegrable
      (fun s => g s • ContinuousLinearMap.adjoint (W s) (basisVec 0))
      volume 0 θ := by
    apply intervalIntegrable_iff.mpr
    apply MeasureTheory.IntegrableOn.mono_set
      (integrable_boundary_observation_load hγLip hW g)
    grind
  have h := ((innerSL ℂ (basisVec 0)).comp (W θ)).intervalIntegral_comp_comm hi
  simp  at h
  rw [← h]
  apply intervalIntegral.integral_congr
  intro s hs
  simp only [volterraKernel]
  ring

/-- The true Volterra plus adjoint identity holds for ordinary L2 inputs. -/
theorem volterraOp_add_adj_boundaryL2
    (hγLip : LipschitzWith L γ) {E : ℝ}
    {W : ℝ → Ell2 →L[ℂ] Ell2} (hW : IsTransport γ E W) (g : BoundaryL2)
    {θ : ℝ} (hθ : θ ∈ Icc 0 (2 * Real.pi)) :
    volterraOp W g θ + volterraOpAdj W g θ =
      observation W (observationAdj W g) θ := by
  have hk (s : ℝ) : conj (volterraKernel W s θ) = volterraKernel W θ s := by
    simp [volterraKernel, ← ContinuousLinearMap.adjoint_inner_right]
  have hkc : ContinuousOn (volterraKernel W θ) (Icc 0 (2 * Real.pi)) :=
    ((innerSL ℂ (basisVec 0)).comp (W θ)).continuous.comp_continuousOn
      (continuousOn_adjoint_apply hW.1 (basisVec 0))
  have hint : IntervalIntegrable (fun s => volterraKernel W θ s * g s)
      volume 0 (2 * Real.pi) := (intervalIntegrable_boundaryL2 g).continuousOn_mul
      (by simp_all [uIcc_of_le Real.two_pi_pos.le])
  simp only [volterraOp, volterraOpAdj, hk]
  rw [intervalIntegral.integral_add_adjacent_intervals (hint.mono_set' (by grind)) (hint.mono_set' (by grind)), observation, observationAdj]
  have hi : IntervalIntegrable
      (fun s => g s • ContinuousLinearMap.adjoint (W s) (basisVec 0))
      volume 0 (2 * Real.pi) :=
    by
      apply intervalIntegrable_iff.mpr
      simpa only [IntegrableOn, uIoc_of_le Real.two_pi_pos.le] using
        (integrable_boundary_observation_load hγLip hW g)
  have h := ((innerSL ℂ (basisVec 0)).comp (W θ)).intervalIntegral_comp_comm hi
  simp  at h
  rw [← h]
  apply intervalIntegral.integral_congr
  intro s hs
  simp only [volterraKernel]
  ring

section PhysicalCoordinates

variable {R C K : ℝ} (hR : 1 < R) (F : ℂ → ℂ)
    (hFs : ContDiffOn ℝ (⊤ : ℕ∞) F (ball (0 : ℂ) R))
    (hb : Bornology.IsBounded (F '' ball (0 : ℂ) 1))
    (hL : IsLipschitzDomain (F '' ball (0 : ℂ) 1))
    (hhol : DifferentiableOn ℂ F (ball (0 : ℂ) 1))
    (hinj : InjOn F (ball (0 : ℂ) 1))
    (hC : ∀ z ∈ ball (0 : ℂ) 1, 1 ≤ C * ‖deriv F z‖ ^ 2)
    (hK : ∀ z ∈ ball (0 : ℂ) 1, ‖fderiv ℝ F z 1‖ ≤ K)
    (e : OpenPartialHomeomorph ℂ ℂ) (he : (e : ℂ → ℂ) = F)
    (hsource : closedBall (0 : ℂ) 1 ⊆ e.source)
    (hes : ContDiffOn ℝ (⊤ : ℕ∞) e.symm e.target)

local notation "JF" => localConformalHardyPrimitive hR F hFs
local notation "VF" => localConformalVekuaH1 hR F hFs hb hL hhol hinj hC hK e he hsource hes
local notation "TF" => localConformalDiskH1Trace hR F hFs hL
local notation "UR" => localConformalVekuaTraceRow hR F hFs hb hL hhol hinj hC hK e he hsource hes
local notation "YF" => localConformalVekuaTransportVector hR F hFs hb hL hhol hinj hC hK e he hsource hes
local notation "hβF" => localConformalVelocityCircle_isWL1_half hR F hFs
local notation "haF" => localConformalHardyPrimitiveMultiplier_isWL1 hR F hFs
local notation "hgF" => localConformalCenteredCircle_isWL1_half hR F hFs
local notation "NF" => normalizedConormal hβF haF hgF

/-- The ordinary coordinate load exists here as a conclusion of genuine
half-order input regularity and the proved normalized smoothing formula. -/
def localConformalVekuaForwardLoad (E : ℂ) (b : L2Z)
    (hbhalf : IsSobolevSeq (1 / 2 : ℝ) (b : ℤ → ℂ)) : BoundaryL2 :=
  halfRegularCoordinateLoad (NF E b)
    (normalizedConormal_preserves_half_regular hβF haF hgF E b hbhalf)

variable (E : ℝ)

theorem localConformalVekuaForwardLoad_normalized (E : ℂ) (b : L2Z)
    (hbhalf : IsSobolevSeq (1 / 2) b) :
    sobolevSmoothing (1 / 2) (by norm_num)
      (boundaryFourier (localConformalVekuaForwardLoad hR F hFs E b hbhalf)) = NF E b :=
  halfRegularCoordinateLoad_normalized _ _

private theorem forward_fourier_coeff_ae {f : ℝ → ℂ} (v : BoundaryL2)
    (hv : (v : ℝ → ℂ) =ᵐ[volume.restrict (Ioc 0 (2 * Real.pi))] f) (n : ℤ) :
    boundaryFourier v n = (Real.sqrt (2 * Real.pi) : ℂ) *
      fourierCoeffOn Real.two_pi_pos f n := by
  rw [boundaryFourier_apply, fourierCoeffOn_congr_ae Real.two_pi_pos hv]

/-- Actual Fourier inversion of the exceptional zeroth row with its
genuine coordinate L2 conormal forcing. The zeroth coefficient is used. -/
theorem localConformalVekuaForward_zero_fourier_derivative
    (E : ℂ) (b : L2Z) (hbn : IsNonpositiveFourierSupport b)
    (hbhalf : IsSobolevSeq (1 / 2) b) (n : ℤ) :
    fourierCoeffOn Real.two_pi_pos
      ((2 * (-E / 4)) •
        boundaryContinuousMultiplier (localConformalVelocityCircle F)
          (TF (VF (F 1) E (JF b))) -
        Complex.I • localConformalVekuaForwardLoad hR F hFs E b hbhalf) n =
      (Complex.I * n) * fourierCoeffOn Real.two_pi_pos (UR E b 0) n := by
  have hb1  := isSobolevSeq_one_fromL2_half_of_half_regular b hbhalf
  let G  := boundaryContinuousMultiplier (localConformalVelocityCircle F)
    (TF (VF (F 1) E (JF b)))
  let g := localConformalVekuaForwardLoad hR F hFs E b hbhalf
  let L  := (2 * (-E / 4)) • G - Complex.I • g
  have ht0 : TF (VF (F 1) E b)
      =ᵐ[volume.restrict (Ioc 0 (2 * Real.pi))] UR E b 0 := by
    unfold localConformalVekuaTraceRow
    simpa only [pow_zero, ContinuousLinearMap.one_apply] using
      localConformalVekua_coordinate_trace_reconstruction_ae hR F hFs hb hL hhol hinj hC hK
        e he hsource hes E b hbn hb1
  have hNC := localConformalVekua_normalizedConormal_fourier hR F hFs hb hL hhol hinj hC hK
    e he hsource hes E b hbn hb1 n
  simp only [localConformalVekuaGradientA_apply, map_smul] at hNC
  have hw : (((sobWeight n ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)) ≠ 0 := by
    exact_mod_cast (Real.rpow_pos_of_pos (sobWeight_pos n) (-(1 / 2))).ne'
  have hn : -n * boundaryFourier (TF (VF (F 1) E b)) n -
      2 * Complex.I * ((-E / 4) * boundaryFourier G n) = boundaryFourier g n :=
    mul_left_cancel₀ hw (hNC.symm.trans (congrArg (fun v  => v n)
    (localConformalVekuaForwardLoad_normalized hR F hFs E b hbhalf)).symm)
  have hs0 : (Real.sqrt (2 * Real.pi) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr Real.two_pi_pos).ne'
  apply mul_left_cancel₀ hs0
  calc
    _ = boundaryFourier L n := (boundaryFourier_apply L n).symm
    _ = (Complex.I * n) * boundaryFourier (TF (VF (F 1) E b)) n := by
      simp only [L, map_sub, map_smul, lp.coeFn_sub, Pi.sub_apply,
        lp.coeFn_smul, Pi.smul_apply]
      rw [← hn]
      ring_nf
      simp 
    _ = _ := by rw [forward_fourier_coeff_ae _ ht0]; ring

private theorem forward_zero_derivative_ae
    (E : ℂ) (b : L2Z) (hbn : IsNonpositiveFourierSupport b)
    (hbhalf : IsSobolevSeq (1 / 2) b) :
    (2 * (-E / 4)) •
      boundaryContinuousMultiplier (localConformalVelocityCircle F)
        (TF (VF (F 1) E (JF b))) -
      Complex.I • localConformalVekuaForwardLoad hR F hFs E b hbhalf
      =ᵐ[volume.restrict (Ioc 0 (2 * Real.pi))]
        fun t => 2 * (-E / 4) * deriv (physicalCircleTrace F) t * UR E b 1 t -
          Complex.I * localConformalVekuaForwardLoad hR F hFs E b hbhalf t := by
  let G  := boundaryContinuousMultiplier (localConformalVelocityCircle F)
    (TF (VF (F 1) E (JF b)))
  let g := localConformalVekuaForwardLoad hR F hFs E b hbhalf
  filter_upwards [Lp.coeFn_sub ((2 * (-E / 4)) • G) (Complex.I • g),
    Lp.coeFn_smul (2 * (-E / 4)) G, Lp.coeFn_smul Complex.I g,
    boundaryContinuousMultiplier_ae (localConformalVelocityCircle F)
      (TF (VF (F 1) E (JF b))), localConformalVekua_coordinate_trace_reconstruction_ae hR F hFs hb hL hhol
    hinj hC hK e he hsource hes E (JF b) (localConformalHardyPrimitive_nonpositive hR F hFs hhol b hbn) (by
    simpa only [pow_one] using localConformalHardyPrimitive_pow_raw_H1 hR F hFs b (isSobolevSeq_one_fromL2_half_of_half_regular b hbhalf) 1)] with t hsub hs ht hG htrace
  rw [hsub]
  simp 
  rw [hs, ht]
  simp only [Pi.smul_apply, smul_eq_mul, G, g, hG, htrace,
    localConformalVelocityCircle_apply hR F hFs, localConformalVekuaTraceRow]
  ring

/-- The exceptional zero row has its true inhomogeneous primitive
formula, with the actual initial constant and ordinary L2 coordinate load. -/
theorem localConformalVekuaForward_zero_integral_eq
    (E : ℂ) (b : L2Z) (hbn : IsNonpositiveFourierSupport b)
    (hbhalf : IsSobolevSeq (1 / 2) b)
    {θ : ℝ} (hθ : θ ∈ Icc 0 (2 * Real.pi)) :
    UR E b 0 θ = UR E b 0 0 + ∫ t in 0..θ,
      2 * (-E / 4) * deriv (physicalCircleTrace F) t * UR E b 1 t -
        Complex.I * localConformalVekuaForwardLoad hR F hFs E b hbhalf t := by
  let L  := (2 * (-E / 4)) •
    boundaryContinuousMultiplier (localConformalVelocityCircle F) (TF (VF (F 1) E (JF b))) -
      Complex.I • localConformalVekuaForwardLoad hR F hFs E b hbhalf
  rw [eq_add_integral_of_L2_periodic_fourier_derivative
    (localConformalVekuaTraceRow_continuous hR F hFs hb hL hhol hinj hC hK
      e he hsource hes E b hbn (isSobolevSeq_one_fromL2_half_of_half_regular b hbhalf) 0)
    (localConformalVekuaTraceRow_periodic hR F hFs hb hL hhol hinj hC hK
      e he hsource hes E b 0) L
    (localConformalVekuaForward_zero_fourier_derivative hR F hFs hb hL hhol hinj hC hK
      e he hsource hes E b hbn hbhalf) hθ]
  congr 1
  apply intervalIntegral.integral_congr_ae
  filter_upwards [(ae_restrict_iff' measurableSet_Ioc).mp
    (forward_zero_derivative_ae hR F hFs hb hL hhol hinj hC hK
      e he hsource hes E b hbn hbhalf)] with t ht hmem
  grind

private theorem forward_zero_transportCoeff
    (hE : 0 ≤ E) (b : L2Z) (hbn : IsNonpositiveFourierSupport b)
    (hb1 : IsSobolevSeq 1 (fromL2 (1 / 2 : ℝ) b))
    {θ : ℝ} (hθ : θ ∈ Icc 0 (2 * Real.pi)) :
    (2 * (-(E : ℂ) / 4) * deriv (physicalCircleTrace F) θ * UR (E : ℂ) b 1 θ) /
        (Real.sqrt 2 : ℂ) =
      (transportCoeff (physicalCircleTrace F) E θ (YF E b θ) : ℕ → ℂ) 0 := by
  rw [transportCoeff_coord_zero,
    localConformalVekuaTransportVector_coord hR F hFs hb hL hhol hinj hC hK
      e he hsource hes E b hbn hb1 hθ 1]
  simp only [localConformalVekuaTransportCoordinate, if_false, Nat.one_ne_zero, pow_one]
  change _ = physicalDrivenQ E * _
  rw [← physicalDrivenQ_sq hE]
  have hs : (Real.sqrt 2 : ℂ) ^ 2 = 2 := by
    exact_mod_cast Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  grind

/-- The full actual Ell2 trace vector obeys the driven integral equation.
Positive rows come from the genuine factorial series; only the exceptional
zeroth row uses the actual L2 primitive inversion. -/
theorem localConformalVekuaForward_transport_integral_eq
    (E : ℝ) (hE : 0 ≤ E) (b : L2Z) (hbn : IsNonpositiveFourierSupport b)
    (hbhalf : IsSobolevSeq (1 / 2) b)
    {θ : ℝ} (hθ : θ ∈ Icc 0 (2 * Real.pi)) :
    YF E b θ = YF E b 0 + ∫ s in 0..θ,
      transportCoeff (physicalCircleTrace F) E s (YF E b s) +
        (-(Complex.I / Real.sqrt 2) *
          localConformalVekuaForwardLoad hR F hFs E b hbhalf s) • basisVec 0 := by
  have hb1 : IsSobolevSeq 1 (fromL2 (1 / 2) b) := isSobolevSeq_one_fromL2_half_of_half_regular b hbhalf
  let y := YF E b
  let p := localConformalVekuaPositiveTransportVector hR F hFs hb hL hhol hinj hC hK
    e he hsource hes E b
  let z  := fun s => UR E b 0 s / Real.sqrt 2
  let g := localConformalVekuaForwardLoad hR F hFs E b hbhalf
  let Cg := fun s => transportCoeff (physicalCircleTrace F) E s (y s)
  let a  := fun s =>
    (2 * (-E / 4) * deriv (physicalCircleTrace F) s * UR E b 1 s -
      Complex.I * g s) / Real.sqrt 2
  have hy := localConformalVekuaTransportVector_continuousOn hR F hFs hb hL hhol hinj hC hK
    e he hsource hes E b hbn hb1
  have hΓ  :=
    contDiff_physicalCircleTrace_of_neighborhood hR F (hFs.of_le (WithTop.coe_le_coe.mpr le_top))
  have hCoeff : Continuous (transportCoeff (physicalCircleTrace F) E) := by
    unfold transportCoeff
    fun_prop
  have hCg : ContinuousOn Cg (Icc 0 (2 * Real.pi)) := hCoeff.continuousOn.clm_apply hy
  have hC0 : ContinuousOn (fun s => Cg s 0) (Icc 0 (2 * Real.pi)) := by
    convert (innerSL ℂ (basisVec 0)).continuous.continuousOn.comp hCg
      (fun _ _ => Set.mem_univ _) using 1
    · funext s
      simp [Function.comp_apply, inner_basisVec]
  have hsplit (s : ℝ) (hs : s ∈ Icc 0 (2 * Real.pi)) : y s = z s • basisVec 0 + p s :=
    localConformalVekuaTransportVector_zero_add_positive hR F hFs hb hL hhol hinj hC hK
      e he hsource hes E b hbn hb1 hs
  have hp : ContinuousOn p (Icc 0 (2 * Real.pi)) := by
    apply (hy.sub (((localConformalVekuaTraceRow_continuous hR F hFs hb hL hhol hinj hC hK
      e he hsource hes E b hbn hb1 0).div_const _).continuousOn.smul
      continuousOn_const)).congr
    intro s hs
    change p s = y s - z s • basisVec 0
    simp_all
  have hsub : Icc 0 θ ⊆ Icc 0 (2 * Real.pi) := Icc_subset_Icc le_rfl hθ.2
  have hpi : IntervalIntegrable (fun s => Cg s - (Cg s 0) • basisVec 0)
      volume 0 θ := ((hCg.sub (hC0.smul continuousOn_const)).mono (by simp_all)).intervalIntegrable
  have hzp : z θ = z 0 + ∫ s in 0..θ, a s := by
    simpa only [a, add_div, intervalIntegral.integral_div] using congrArg (fun v : ℂ => v / Real.sqrt 2)
      (localConformalVekuaForward_zero_integral_eq hR F hFs hb hL hhol hinj hC hK
        e he hsource hes E b hbn hbhalf hθ)
  have hai : IntervalIntegrable a volume 0 θ :=
    ((((continuous_const.mul hΓ.continuous_deriv_one).mul
        (localConformalVekuaTraceRow_continuous hR F hFs hb hL hhol hinj hC hK
          e he hsource hes E b hbn hb1 1)).intervalIntegrable 0 θ).sub (((intervalIntegrable_boundaryL2 g).mono_set' (by
      grind)).const_mul Complex.I)).div_const _
  calc
    y θ = z θ • basisVec 0 + p θ := hsplit θ hθ
    _ = (z 0 • basisVec 0 + p 0) +
        ((∫ s in 0..θ, a s) • basisVec 0 +
          ∫ s in 0..θ, Cg s - (Cg s 0) • basisVec 0) := by
      rw [hzp, sub_eq_iff_eq_add.mp (intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hθ.1 (hp.mono hsub)
    (fun s hs => (localConformalVekuaPositiveTransportVector_hasDerivAt hR F hFs hb hL
      hhol hinj hC hK e he hsource hes E b hbn hb1 ⟨hs.1, hs.2.trans_le hθ.2⟩).congr_deriv (localConformalVekuaPositiveTransportDerivative_tsum_eq hR F hFs hb hL
        hhol hinj hC hK e he hsource hes E hE b hbn hb1 ⟨hs.1.le, hs.2.le.trans hθ.2⟩)) hpi).symm, add_smul]
      abel
    _ = y 0 + ∫ s in 0..θ,
        (a s • basisVec 0 + (Cg s - (Cg s 0) • basisVec 0)) := by
      simp [← hsplit 0 ⟨le_rfl, Real.two_pi_pos.le⟩, ← intervalIntegral.integral_smul_const, ← intervalIntegral.integral_add ⟨MeasureTheory.Integrable.smul_const hai.1 _,           MeasureTheory.Integrable.smul_const hai.2 _⟩ hpi]
    _ = _ := by
      congr 1
      apply intervalIntegral.integral_congr
      intro s hs
      rw [uIcc_of_le hθ.1] at hs
      have hzero := forward_zero_transportCoeff hR F hFs hb hL hhol hinj hC hK
        e he hsource hes E hE b hbn hb1 ⟨hs.1, hs.2.trans hθ.2⟩
      have haeq : a s = Cg s 0 - (Complex.I / Real.sqrt 2) * g s := by
        grind
      change a s • basisVec 0 + (Cg s - (Cg s 0) • basisVec 0) =
        Cg s + (-(Complex.I / Real.sqrt 2) * g s) • basisVec 0
      rw [haeq, sub_smul]
      continuity

/-- The actual forward vector equals genuine homogeneous transport plus
the true L2 Duhamel vector. No forced ODE is assumed. -/
theorem localConformalVekuaForward_transport_eq
    (hE : 0 ≤ E) (b : L2Z) (hbn : IsNonpositiveFourierSupport b)
    (hbhalf : IsSobolevSeq (1 / 2) b)
    {L : NNReal} (hΓLip : LipschitzWith L (physicalCircleTrace F))
    {W : ℝ → Ell2 →L[ℂ] Ell2} (hW : IsTransport (physicalCircleTrace F) E W)
    {θ : ℝ} (hθ : θ ∈ Icc 0 (2 * Real.pi)) :
    YF E b θ = W θ (YF E b 0) +
      physicalDrivenVector W (localConformalVekuaForwardLoad hR F hFs E b hbhalf) θ := driven_eq_transport_add_physicalDrivenVector_boundaryL2 hΓLip
    (contDiff_physicalCircleTrace_of_neighborhood hR F
      (hFs.of_le (WithTop.coe_le_coe.mpr le_top))) hW
    (localConformalVekuaForwardLoad hR F hFs E b hbhalf)
    (localConformalVekuaTransportVector_continuousOn hR F hFs hb hL hhol hinj hC hK
      e he hsource hes E b hbn (isSobolevSeq_one_fromL2_half_of_half_regular b hbhalf))
    (fun t ht => localConformalVekuaForward_transport_integral_eq hR F hFs hb hL hhol
      hinj hC hK e he hsource hes E hE b hbn hbhalf ht) hθ

include hb hL hhol hinj hC hK e he hsource hes in
/-- The periodic endpoint of the actual trace vector determines its true
adjoint observation, with the original initial constant and sqrt(2) scale. -/
theorem localConformalVekuaForward_observationAdj_eq_cut
    (hE : 0 ≤ E) (b : L2Z) (hbn : IsNonpositiveFourierSupport b)
    (hbhalf : IsSobolevSeq (1 / 2) b)
    {L : NNReal} (hΓLip : LipschitzWith L (physicalCircleTrace F))
    {W : ℝ → Ell2 →L[ℂ] Ell2} (hW : IsTransport (physicalCircleTrace F) E W) :
    observationAdj W
      (localConformalVekuaForwardLoad hR F hFs E b hbhalf) =
        (Complex.I * hardyFourierTrace (normalizedHardyAverage b) 0) •
          cutC (W (2 * Real.pi)) (basisVec 0) := by
  let y := YF E b
  let g := localConformalVekuaForwardLoad hR F hFs E b hbhalf
  let h0 := hardyFourierTrace (normalizedHardyAverage b) 0
  let s := h0 / Real.sqrt 2
  have hinit : y 0 = s • basisVec 0 :=
    localConformalVekuaTransportVector_origin hR F hFs hb hL hhol hinj hC hK
      e he hsource hes E b hbn (isSobolevSeq_one_fromL2_half_of_half_regular b hbhalf)
  have hper : y (2 * Real.pi) = y 0 := by
    simpa only [zero_add] using localConformalVekuaTransportVector_periodic hR F hFs
      hb hL hhol hinj hC hK e he hsource hes E b 0
  have hT : (2 * Real.pi) ∈ Icc 0 (2 * Real.pi) := ⟨Real.two_pi_pos.le, le_rfl⟩
  have hform := localConformalVekuaForward_transport_eq hR F hFs hb hL hhol hinj hC hK
    e he hsource hes E hE b hbn hbhalf hΓLip hW hT
  change y (2 * Real.pi) = W (2 * Real.pi) (y 0) +
    (-(Complex.I / Real.sqrt 2)) • W (2 * Real.pi)
      (observationAdj W g) at hform
  rw [hper] at hform
  have hu : ContinuousLinearMap.adjoint (W (2 * Real.pi)) * W (2 * Real.pi) = 1 := by
    exact (transport_mem_unitary hΓLip hW hT).1
  have hadj := congrArg (fun z  => ContinuousLinearMap.adjoint (W (2 * Real.pi)) z) hform
  rw [map_add, map_smul, ← ContinuousLinearMap.mul_apply, ← ContinuousLinearMap.mul_apply, hu] at hadj
  have hsub : ContinuousLinearMap.adjoint (W (2 * Real.pi)) (y 0) - y 0 =
      (-(Complex.I / Real.sqrt 2)) • observationAdj W g := by
    grind
  have hcancel : Real.sqrt 2 * Complex.I * -(Complex.I / Real.sqrt 2) = 1 := by
    field_simp  ; simp 
  have hO : observationAdj W g = (Real.sqrt 2 * Complex.I) •
      (ContinuousLinearMap.adjoint (W (2 * Real.pi)) (y 0) - y 0) := by
    rw [hsub, smul_smul, hcancel, one_smul]
  rw [hO, hinit, map_smul, ← smul_sub, smul_smul]
  have hscalar : (Real.sqrt 2 * Complex.I) * s = Complex.I * h0 := by
    grind 
  simp [hscalar, h0, cutC]

include hb hL hhol hinj hC hK e he hsource hes in
/-- The projected observation annihilates the genuine normalized conormal
range on every half-regular full Hardy input, including frequency zero. -/
theorem localConformalVekuaForward_projObsDual_eq_zero_of_half_regular
    (hE : 0 ≤ E) (b : L2Z) (hbn : IsNonpositiveFourierSupport b)
    (hbhalf : IsSobolevSeq (1 / 2) b)
    {L : NNReal} (hΓLip : LipschitzWith L (physicalCircleTrace F))
    {W : ℝ → Ell2 →L[ℂ] Ell2} (hW : IsTransport (physicalCircleTrace F) E W) :
    projObsDual W (NF E b) = 0 := by
  have h := projObsDual_boundary_normalized hΓLip hW
    (localConformalVekuaForwardLoad hR F hFs E b hbhalf)
  rw [localConformalVekuaForwardLoad_normalized, map_smul,
    localConformalVekuaForward_observationAdj_eq_cut hR F hFs hb hL hhol hinj hC hK
      e he hsource hes E hE b hbn hbhalf hΓLip hW,
    map_smul, cutProj_eq_starProjection,
    Submodule.starProjection_orthogonal_apply_eq_zero (Submodule.mem_span_singleton_self _),
    smul_zero] at h
  exact (smul_eq_zero.mp h).resolve_left (by
    exact_mod_cast (Real.sqrt_pos.mpr Real.two_pi_pos).ne')

/-- The actual coordinate trace obeys the true forward observation and
Volterra identity for its derived ordinary L2 conormal load. -/
theorem localConformalVekuaForward_trace_eq
    (hE : 0 ≤ E) (b : L2Z) (hbn : IsNonpositiveFourierSupport b)
    (hbhalf : IsSobolevSeq (1 / 2) b)
    {L : NNReal} (hΓLip : LipschitzWith L (physicalCircleTrace F))
    {W : ℝ → Ell2 →L[ℂ] Ell2} (hW : IsTransport (physicalCircleTrace F) E W)
    {θ : ℝ} (hθ : θ ∈ Icc 0 (2 * Real.pi)) :
    UR E b 0 θ = hardyFourierTrace (normalizedHardyAverage b) 0 *
      observation W (basisVec 0) θ - Complex.I *
        volterraOp W (localConformalVekuaForwardLoad hR F hFs E b hbhalf) θ := by
  have hb1  := isSobolevSeq_one_fromL2_half_of_half_regular b hbhalf
  let g := localConformalVekuaForwardLoad hR F hFs E b hbhalf
  have hinner := congrArg (fun v  => ⟪basisVec 0, v⟫_ℂ) (localConformalVekuaForward_transport_eq hR F hFs hb hL hhol hinj hC hK
    e he hsource hes E hE b hbn hbhalf hΓLip hW hθ)
  simp only [inner_add_right] at hinner
  have hleft : ⟪basisVec 0, YF E b θ⟫_ℂ = UR E b 0 θ / Real.sqrt 2 := by
    simpa only [inner_basisVec, localConformalVekuaTransportCoordinate, if_true] using
      localConformalVekuaTransportVector_coord hR F hFs hb hL hhol hinj hC hK
        e he hsource hes E b hbn hb1 hθ 0
  have hinit : ⟪basisVec 0, W θ (YF E b 0)⟫_ℂ =
      (hardyFourierTrace (normalizedHardyAverage b) 0 / Real.sqrt 2) *
        observation W (basisVec 0) θ := by
    change ⟪basisVec 0, W θ (YF E b 0)⟫_ℂ =
      (hardyFourierTrace (normalizedHardyAverage b) 0 / Real.sqrt 2) *
        ⟪basisVec 0, W θ (basisVec 0)⟫_ℂ
    rw [localConformalVekuaTransportVector_origin hR F hFs hb hL hhol hinj hC hK
      e he hsource hes E b hbn hb1, map_smul, inner_smul_right]
  have hforced : ⟪basisVec 0, physicalDrivenVector W g θ⟫_ℂ =
      -(Complex.I / Real.sqrt 2) * volterraOp W g θ := by
    rw [physicalDrivenVector, inner_smul_right, inner_transport_integral_boundaryL2 hΓLip hW g hθ]
  have hs0 : (Real.sqrt 2 : ℂ) ≠ 0 := by
    norm_num
  grind

/-- The genuine periodic form vanishes on the actual forward Vekua trace
and its actual L2 load. A nonzero cut is used only by the correction B. -/
theorem localConformalVekuaForward_periodicP_eq_zero
    (hE : 0 ≤ E) (b : L2Z) (hbn : IsNonpositiveFourierSupport b)
    (hbhalf : IsSobolevSeq (1 / 2) b)
    {L : NNReal} (hΓLip : LipschitzWith L (physicalCircleTrace F))
    {W : ℝ → Ell2 →L[ℂ] Ell2} (hW : IsTransport (physicalCircleTrace F) E W)
    (hc : cutC (W (2 * Real.pi)) (basisVec 0) ≠ 0)
    {θ : ℝ} (hθ : θ ∈ Icc 0 (2 * Real.pi)) :
    periodicP W (UR E b 0)
      (localConformalVekuaForwardLoad hR F hFs E b hbhalf) θ = 0 := by
  let g := localConformalVekuaForwardLoad hR F hFs E b hbhalf
  let h0 := hardyFourierTrace (normalizedHardyAverage b) 0
  have hsum := volterraOp_add_adj_boundaryL2 hΓLip hW g hθ
  have hO := localConformalVekuaForward_observationAdj_eq_cut hR F hFs hb hL hhol hinj hC hK
    e he hsource hes E hE b hbn hbhalf hΓLip hW
  have hS : cutS (W (2 * Real.pi)) (basisVec 0) =
      (2 : ℂ) • basisVec 0 + cutC (W (2 * Real.pi)) (basisVec 0) := by
    simp [cutS, cutC, two_smul]
  have hA : periodicA W (UR E b 0) g θ =
      h0 * observation W (cutS (W (2 * Real.pi)) (basisVec 0)) θ := by
    rw [hO] at hsum
    rw [periodicA, localConformalVekuaForward_trace_eq hR F hFs hb hL hhol hinj hC hK
      e he hsource hes E hE b hbn hbhalf hΓLip hW hθ, hS]
    simp only [observation, map_add, map_smul, inner_add_right, inner_smul_right] at hsum ⊢
    linear_combination (-Complex.I) * hsum - Complex.I_sq *
      (h0 * ⟪basisVec 0, W θ (cutC (W (2 * Real.pi)) (basisVec 0))⟫_ℂ)
  rw [periodicP, hA, hO, map_smul, (cutB_transport (transport_mem_unitary hΓLip hW
    ⟨Real.two_pi_pos.le, le_rfl⟩) (basisVec 0) hc).2]
  simp only [observation, map_smul, inner_smul_right]
  linear_combination Complex.I_sq *
    (h0 * ⟪basisVec 0, W θ (cutS (W (2 * Real.pi)) (basisVec 0))⟫_ℂ)

private theorem forward_half_regular_stdBasis (n : ℤ) :
    IsSobolevSeq (1 / 2 : ℝ) (stdBasisZ n : ℤ → ℂ) := by
  apply summable_of_ne_finset_zero (s := {n})
  intro k hk
  have hkn : k ≠ n := by simp_all
  simp [stdBasisZ_apply, lp.single_apply, hkn]

include hb hL hhol hinj hC hK e he hsource hes in
/-- Genuine finite Fourier density extends the bounded projected-null
identity to every normalized full Hardy input. No L2 load for those
possibly rough inputs is asserted by this extension. -/
theorem localConformalVekuaForward_projObsDual_eq_zero
    (hE : 0 ≤ E)
    {L : NNReal} (hΓLip : LipschitzWith L (physicalCircleTrace F))
    {W : ℝ → Ell2 →L[ℂ] Ell2} (hW : IsTransport (physicalCircleTrace F) E W)
    (b : L2Z) (hbn : IsNonpositiveFourierSupport b) :
    projObsDual W (NF E b) = 0 := by
  have hop : (projObsDual W).comp ((NF E).comp (1 - posProj)) = 0 := by
    apply ContinuousLinearMap.ext_on
      ((Submodule.dense_iff_topologicalClosure_eq_top).2 stdBasisZ.dense_span)
    rintro _ ⟨n, rfl⟩
    simp only [ContinuousLinearMap.comp_apply]
    by_cases hn : 0 < n
    · have hzero : (1 - posProj) (stdBasisZ n) = 0 := by
        apply lp.ext
        funext k
        by_cases hkn : k = n
        all_goals simp [posProj, hn, stdBasisZ_apply, hkn]
      simp_all
    · have hkeep : (1 - posProj) (stdBasisZ n) = stdBasisZ n := by
        apply lp.ext
        funext k
        by_cases hkn : k = n
        all_goals simp [posProj, hn, stdBasisZ_apply, hkn]
      rw [hkeep]
      apply localConformalVekuaForward_projObsDual_eq_zero_of_half_regular hR F hFs hb hL
        hhol hinj hC hK e he hsource hes E hE (stdBasisZ n) _
        (forward_half_regular_stdBasis n) hΓLip hW
      intro k hk
      have hkn : k ≠ n := by omega
      simp [stdBasisZ_apply, hkn]
  have hkeep : (1 - posProj) b = b := by
    apply lp.ext
    funext n
    by_cases hn : 0 < n
    · simp [posProj, hbn n hn]
    simp [posProj, hn]
  have h := congrArg (fun A  => A b) hop
  grind

end PhysicalCoordinates

end PolyaNeumann

end
