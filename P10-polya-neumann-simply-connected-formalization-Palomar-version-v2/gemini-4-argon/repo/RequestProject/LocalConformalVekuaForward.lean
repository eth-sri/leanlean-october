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


noncomputable section

namespace PolyaNeumann

open Set MeasureTheory Filter Metric
open scoped Topology ComplexConjugate InnerProductSpace ContDiff

local instance forwardTwoPiPos : Fact (0 < 2 * Real.pi) := ⟨Real.two_pi_pos⟩

/-- Fourier inversion for an actual L2 derivative. No absolute continuity
or differentiability of the original continuous function is assumed. -/
theorem eq_add_integral_of_L2_periodic_fourier_derivative
     (hv : Continuous v)
    (hvper : Function.Periodic v (2 * Real.pi)) (d : BoundaryL2)
    (hcoeff : ∀ n : ℤ, fourierCoeffOn Real.two_pi_pos d n =
      (Complex.I * n) * fourierCoeffOn Real.two_pi_pos v n)
     (hθ : θ ∈ Icc 0 (2 * Real.pi)) :
    v θ = v 0 + ∫ s in 0..θ, d s := by
  let P : ℝ → ℂ := fun t => ∫ s in 0..t, d s
  have hPi := intervalIntegrable_boundaryL2 d
  have hPAC : AbsolutelyContinuousOnInterval P 0 (2 * Real.pi) :=
    absolutelyContinuousOnInterval_intervalIntegral_banach hPi
      (by rw [uIcc_of_le Real.two_pi_pos.le]; exact ⟨le_rfl, Real.two_pi_pos.le⟩)
  have hPC : ContinuousOn P (Icc 0 (2 * Real.pi)) := by
    simpa [uIcc_of_le Real.two_pi_pos.le] using hPAC.continuousOn
  have hP0 : P 0 = 0 := by simp [P]
  have hPT : P (2 * Real.pi) = 0 :=
    integral_eq_zero_of_periodic_fourier_derivative hcoeff
  have hPc n : fourierCoeffOn Real.two_pi_pos d n =
      Complex.I * n * fourierCoeffOn Real.two_pi_pos P n :=
    fourierCoeffOn_of_ac_ae_hasDerivAt hPAC (Lp.memLp d) (ae_hasDerivAt_intervalIntegral_banach Real.two_pi_pos.le hPi) (hP0.trans hPT.symm) n
  have hncoeff n (hn : n ≠ 0) :
      fourierCoeffOn Real.two_pi_pos v n = fourierCoeffOn Real.two_pi_pos P n :=
    mul_left_cancel₀ (mul_ne_zero Complex.I_ne_zero (Int.cast_ne_zero.mpr hn))
      ((hcoeff n).symm.trans (hPc n))
  let f : ℝ → ℂ := fun t => v t - P t
  have hfe : f 0 = f (2 * Real.pi) := by
    dsimp only [f]
    rw [hP0, hPT, sub_zero, sub_zero]
    simpa using (hvper 0).symm
  let F : ℝ → ℂ := fun t => AddCircle.liftIco (2 * Real.pi) 0 f
    (t : AddCircle (2 * Real.pi))
  have hFc : Continuous F :=
    (AddCircle.liftIco_zero_continuous hfe (hv.continuousOn.sub hPC)).comp (AddCircle.continuous_mk' _)
  have hFf : EqOn F f (Icc 0 (2 * Real.pi)) := by
    intro t ht
    by_cases htT : t = 2 * Real.pi
    · subst t
      have hzero : AddCircle.liftIco (2 * Real.pi) 0 f
          (0 : AddCircle (2 * Real.pi)) = f 0 :=
        AddCircle.liftIco_zero_coe_apply ⟨le_rfl, Real.two_pi_pos⟩
      dsimp only [F]
      rw [AddCircle.coe_period, hzero, hfe]
    · exact AddCircle.liftIco_zero_coe_apply ⟨ht.1, lt_of_le_of_ne ht.2 htT⟩
  have hcoeffF n (hn : n ≠ 0) : fourierCoeffOn Real.two_pi_pos F n = 0 := by
    rw [fourierCoeffOn_congr_Icc hFf n, fourierCoeffOn_sub_of_continuousOn hv.continuousOn hPC n, hncoeff n hn, sub_self]
  have hconst := eq_at_zero_of_periodic_nonzero_fourier_eq_zero hFc (by
    intro t
    dsimp only [F]
    rw [AddCircle.coe_add_period]) hcoeffF θ
  rw [hFf hθ, hFf ⟨le_rfl, Real.two_pi_pos.le⟩] at hconst
  change v θ - P θ = v 0 - P 0 at hconst
  rw [hP0, sub_zero] at hconst
  simpa [add_comm] using sub_eq_iff_eq_add.mp hconst

/-- Exact shift of the genuine Fourier Sobolev weights. -/
theorem isSobolevSeq_fromL2_shift_iff s t b :
    IsSobolevSeq (s + t) (fromL2 t b) ↔ IsSobolevSeq s (b : ℤ → ℂ) := by
  have he n :
      (sobWeight n ^ (s + t) * ‖fromL2 t b n‖) ^ 2 =
        (sobWeight n ^ s * ‖b n‖) ^ 2 := by
    rw [fromL2, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.rpow_pos_of_pos (sobWeight_pos n) (-t)),
      ← mul_assoc, ← Real.rpow_add (sobWeight_pos n), show s + t + -t = s by ring]
  simp [IsSobolevSeq, he]

theorem isSobolevSeq_one_fromL2_half_of_half_regular (b : L2Z)
    (hb : IsSobolevSeq (1 / 2) b) :
    IsSobolevSeq 1 (fromL2 (1 / 2) b) := by
  simpa only [show (1 / 2 : ℝ) + 1 / 2 = 1 by norm_num] using
    (isSobolevSeq_fromL2_shift_iff (1 / 2 : ℝ) (1 / 2 : ℝ) b).mpr hb

/-- Variation of constants for actual ordinary L2 scalar forcing. The
inhomogeneous part is the genuine Duhamel construction. Uniqueness is
applied only to the homogeneous difference, whose forcing is zero. -/
theorem driven_eq_transport_add_physicalDrivenVector_boundaryL2
      (hγLip : LipschitzWith L γ)
    (hγ : ContDiff ℝ 1 γ) 
     (hW : IsTransport γ E W)
    (g : BoundaryL2)  (hy : ContinuousOn y (Icc 0 (2 * Real.pi)))
    (hyint : ∀ θ ∈ Icc 0 (2 * Real.pi),
      y θ = y 0 + ∫ s in 0..θ, transportCoeff γ E s (y s) +
        (-(Complex.I / (Real.sqrt 2 : ℂ)) * g s) • basisVec 0)
     (hθ : θ ∈ Icc 0 (2 * Real.pi)) :
    y θ = W θ (y 0) + physicalDrivenVector W (g : ℝ → ℂ) θ := by
  let Y := physicalDrivenVector W g
  let f : ℝ → Ell2 := fun s => (-(Complex.I / (Real.sqrt 2)) * g s) • basisVec 0
  have hg := intervalIntegrable_boundaryL2 g
  have hY := physicalDrivenVector_continuousOn_of_intervalIntegrable hW.1
    g hg
  have hC : Continuous (transportCoeff γ E) := by
    have hd := hγ.continuous_deriv_one
    unfold transportCoeff
    fun_prop
  have hfi : IntegrableOn f (Icc 0 (2 * Real.pi)) := by
    have hgi : IntegrableOn g (Icc 0 (2 * Real.pi)) := by
      rw [integrableOn_Icc_iff_integrableOn_Ioc]
      exact (intervalIntegrable_iff_integrableOn_Ioc_of_le Real.two_pi_pos.le).mp hg
    exact (hgi.const_mul (-(Complex.I / (Real.sqrt 2)))).smul_const _
  have hdiff t (ht : t ∈ Icc 0 (2 * Real.pi)) :
      y t - Y t = y 0 - Y 0 + ∫ s in 0..t,
        transportCoeff γ E s (y s - Y s) + 0 := by
    have hs : uIcc 0 t ⊆ Icc 0 (2 * Real.pi) := by
      rw [uIcc_of_le ht.1]
      exact Icc_subset_Icc le_rfl ht.2
    dsimp only [Y]
    rw [hyint t ht, physicalDrivenVector_integral_eq_of_intervalIntegrable hγLip hγ hW
      g hg ht]
    simp only [physicalDrivenVector_zero, sub_zero]
    rw [show (fun s => transportCoeff γ E s (y s - Y s) + 0) =
      fun s => transportCoeff γ E s (y s) + f s -
        (transportCoeff γ E s (Y s) + f s) by funext s; rw [map_sub]; abel,
      intervalIntegral.integral_sub (by
        apply intervalIntegrable_iff.mpr
        apply MeasureTheory.IntegrableOn.mono_set (((hC.continuousOn.clm_apply hy).integrableOn_Icc).add hfi)
        intro s hs'
        rw [uIoc_of_le ht.1] at hs'
        rw [uIcc_of_le ht.1] at hs
        exact hs ⟨hs'.1.le, hs'.2⟩) (by
        apply intervalIntegrable_iff.mpr
        apply MeasureTheory.IntegrableOn.mono_set (((hC.continuousOn.clm_apply hY).integrableOn_Icc).add hfi)
        intro s hs'
        rw [uIoc_of_le ht.1] at hs'
        rw [uIcc_of_le ht.1] at hs
        exact hs ⟨hs'.1.le, hs'.2⟩)]
    abel
  have hd := driven_eq_transport hγLip hW
    (continuous_const.aestronglyMeasurable : AEStronglyMeasurable (fun _ : ℝ => (0 : Ell2)) volume)
    (B := 0) (fun _ => by simp) (hy.sub hY) hdiff θ hθ
  simpa [Y, add_comm] using sub_eq_iff_eq_add.mp (show y θ - Y θ = W θ (y 0) by
    simpa [Y] using hd)

section PhysicalCoordinates

variable {R C K : ℝ} (hR : 1 < R) (F : ℂ → ℂ)
    (hFs : ContDiffOn ℝ ∞ F (ball 0 R))
    (hb : Bornology.IsBounded (F '' ball 0 1))
    (hL : IsLipschitzDomain (F '' ball 0 1))
    (hhol : DifferentiableOn ℂ F (ball 0 1))
    (hinj : InjOn F (ball 0 1))
    (hC : ∀ z ∈ ball 0 1, 1 ≤ C * ‖deriv F z‖ ^ 2)
    (hK : ∀ z ∈ ball 0 1, ‖fderiv ℝ F z 1‖ ≤ K)
    (e : OpenPartialHomeomorph ℂ ℂ) (he : ↑e = F)
    (hsource : closedBall 0 1 ⊆ e.source)
    (hes : ContDiffOn ℝ ∞ e.symm e.target)

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
    (show IsSobolevSeq (1 / 2 : ℝ) (NF E b : ℤ → ℂ) by
      have he := congrArg (fun A : L2Z →L[ℂ] L2Z => A b)
        (normalizedConormal_sub_one_eq hβF haF hgF E)
      simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply,
        ContinuousLinearMap.comp_apply] at he
      have hr : IsSobolevSeq (1 / 2 : ℝ)
          (sobolevSmoothing 1 zero_le_one (conormalRemOp (by norm_num) hβF haF hgF E b - b) : ℤ → ℂ) := by
        exact (sobNormSq_mono (by norm_num : (1 / 2 : ℝ) ≤ 1)
          (isSobolevSeq_fromL2 1 _)).1
      have heq : NF E b =
          b + sobolevSmoothing 1 zero_le_one (conormalRemOp (by norm_num) hβF haF hgF E b - b) := by
        rw [← he]
        abel
      rw [heq]
      simpa only [lp.coeFn_add] using (isSobolevSeq_add hbhalf hr))

local notation "Φ0" => localConformalVekuaForwardLoad hR F hFs

theorem localConformalVekuaForwardLoad_normalized E b
    hbhalf :
    sobolevSmoothing (1 / 2 : ℝ) (by norm_num)
      (boundaryFourier (Φ0 E b hbhalf)) = NF E b :=
  halfRegularCoordinateLoad_normalized _ _

private theorem forward_fourier_coeff_ae  (v : BoundaryL2)
    (hv : v =ᵐ[volume.restrict (Ioc 0 (2 * Real.pi))] f) n :
    boundaryFourier v n = (Real.sqrt (2 * Real.pi) : ℂ) *
      fourierCoeffOn Real.two_pi_pos f n := by
  rw [boundaryFourier_apply, fourierCoeffOn_congr_ae Real.two_pi_pos hv]

/-- Actual Fourier inversion of the exceptional zeroth row with its
genuine coordinate L2 conormal forcing. The zeroth coefficient is used. -/
local notation "Φ2" => localConformalVekuaTraceRow_continuous hR F hFs hb hL hhol hinj hC hK e he hsource hes

local notation "Φ4" => physicalCircleTrace F

local notation "Φ5" => localConformalVekua_coordinate_trace_reconstruction_ae hR F hFs hb hL hhol hinj hC hK e he hsource hes

local notation "Φ11" => Icc 0

theorem localConformalVekuaForward_zero_integral_eq
    E (b : L2Z) (hbn : IsNonpositiveFourierSupport b)
    hbhalf
     (hθ : θ ∈ Φ11 (2 * Real.pi)) :
    UR E b 0 θ = UR E b 0 0 + ∫ t in 0..θ,
      2 * (-E / 4) * deriv (Φ4) t * UR E b 1 t -
        Complex.I * Φ0 E b hbhalf t := by
  have h_inl n : fourierCoeffOn Real.two_pi_pos (((2 * (-E / 4)) • boundaryContinuousMultiplier (localConformalVelocityCircle F) (TF (VF (F 1) E (JF b))) - Complex.I • Φ0 E b hbhalf : BoundaryL2) : ℝ → ℂ) n = Complex.I * (n : ℂ) * fourierCoeffOn Real.two_pi_pos (UR E b 0) n := by
    have hb1 : IsSobolevSeq 1 (fromL2 (1 / 2) b) := by
      exact isSobolevSeq_one_fromL2_half_of_half_regular b hbhalf
    let G := boundaryContinuousMultiplier (localConformalVelocityCircle F)
      (TF (VF (F 1) E (JF b)))
    let g := Φ0 E b hbhalf
    let L : BoundaryL2 := (2 * (-E / 4)) • G - Complex.I • g
    have hNC := localConformalVekua_normalizedConormal_fourier hR F hFs hb hL hhol hinj hC hK
      e he hsource hes E b hbn hb1 n
    have hload := congrArg (fun v => v n)
      (localConformalVekuaForwardLoad_normalized hR F hFs E b hbhalf)
    change (sobWeight n ^ (-(1 / 2 : ℝ)) : ℝ) * boundaryFourier g n = NF E b n at hload
    simp only [localConformalVekuaGradientA_apply, map_smul, lp.coeFn_smul,
      Pi.smul_apply, smul_eq_mul] at hNC
    apply mul_left_cancel₀ (show (Real.sqrt (2 * Real.pi) : ℂ) ≠ 0 by
      exact_mod_cast (Real.sqrt_pos.mpr Real.two_pi_pos).ne')
    calc
      _ = _ := (boundaryFourier_apply L n).symm
      _ = Complex.I * n * boundaryFourier (TF (VF (F 1) E b)) n := by
        simp only [L, map_sub, map_smul, lp.coeFn_sub, Pi.sub_apply,
          lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]
        rw [← (mul_left_cancel₀ (show ((sobWeight n ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) ≠ 0 by
          exact_mod_cast (Real.rpow_pos_of_pos (sobWeight_pos n) (-(1 / 2 : ℝ))).ne') (hNC.symm.trans hload.symm) : -n * boundaryFourier (TF (VF (F 1) E b)) n - 2 * Complex.I * ((-E / 4) * boundaryFourier G n) = boundaryFourier g n)]
        ring_nf
        simp
      _ = _ := by rw [forward_fourier_coeff_ae _ (show TF (VF (F 1) E b) =ᵐ[volume.restrict (Ioc 0 (2 * Real.pi))] UR E b 0 by
        unfold localConformalVekuaTraceRow
        simpa using
          Φ5 E b hbn hb1)]; ring
  rw [eq_add_integral_of_L2_periodic_fourier_derivative (Φ2 E b hbn (isSobolevSeq_one_fromL2_half_of_half_regular b hbhalf) 0) (localConformalVekuaTraceRow_periodic hR F hFs hb hL hhol hinj hC hK e he hsource hes E b 0) ((2 * (-E / 4)) • boundaryContinuousMultiplier (localConformalVelocityCircle F) (TF (VF (F 1) E (JF b))) - Complex.I • Φ0 E b hbhalf) h_inl hθ]
  congr 1
  apply intervalIntegral.integral_congr_ae
  have h_inl : (((2 * (-E / 4)) • boundaryContinuousMultiplier (localConformalVelocityCircle F) (TF (VF (F 1) E (JF b))) - Complex.I • Φ0 E b hbhalf : BoundaryL2) : ℝ → ℂ) =ᵐ[volume.restrict (Ioc 0 (2 * Real.pi))] fun t => 2 * (-E / 4) * deriv (Φ4) t * UR E b 1 t - Complex.I * Φ0 E b hbhalf t := by
    let G := boundaryContinuousMultiplier (localConformalVelocityCircle F)
      (TF (VF (F 1) E (JF b)))
    let g := Φ0 E b hbhalf
    have ht1 := Φ5 E (JF b) (localConformalHardyPrimitive_nonpositive hR F hFs hhol b hbn) (by
        simpa using localConformalHardyPrimitive_pow_raw_H1 hR F hFs b (isSobolevSeq_one_fromL2_half_of_half_regular b hbhalf) 1)
    filter_upwards [Lp.coeFn_sub ((2 * (-E / 4)) • G) (Complex.I • g),
      Lp.coeFn_smul (2 * (-E / 4)) G, Lp.coeFn_smul Complex.I g,
      boundaryContinuousMultiplier_ae (localConformalVelocityCircle F)
        (TF (VF (F 1) E (JF b))), ht1] with t hsub hs ht hG htrace
    rw [hsub]
    simp
    rw [hs, ht]
    simp [G, g, hG, htrace, localConformalVelocityCircle_apply hR F hFs, localConformalVekuaTraceRow]
    ring
  filter_upwards [(ae_restrict_iff' measurableSet_Ioc).mp h_inl] with t ht hmem
  rw [uIoc_of_le hθ.1] at hmem
  exact ht ⟨hmem.1, hmem.2.trans hθ.2⟩

local notation "Φ3" => Real.sqrt 2

local notation "Φ7" => localConformalVekuaTransportVector_coord hR F hFs hb hL hhol hinj hC hK e he hsource hes

private theorem forward_zero_transportCoeff
    (E : ℝ) (hE : 0 ≤ E) (b : L2Z) (hbn : IsNonpositiveFourierSupport b)
    (hb1 : IsSobolevSeq 1 (fromL2 (1 / 2) b))
     (hθ : θ ∈ Φ11 (2 * Real.pi)) :
    2 * (-(E : ℂ) / 4) * deriv (Φ4) θ * UR (E : ℂ) b 1 θ /
        (Φ3 : ℂ) =
      (transportCoeff (Φ4) E θ (YF E b θ) : ℕ → ℂ) 0 := by
  rw [transportCoeff_coord_zero,
    Φ7 E b hbn hb1 hθ 1]
  simp [localConformalVekuaTransportCoordinate]
  change _ = physicalDrivenQ E * _
  rw [← physicalDrivenQ_sq hE]
  have hs : (Φ3 : ℂ) ^ 2 = 2 := by
    exact_mod_cast Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have hs0 : (Φ3 : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)).ne'
  field_simp [hs0]
  linear_combination -(physicalDrivenQ E ^ 2 * deriv (Φ4) θ *
    UR E b 1 θ) * hs

/-- The full actual Ell2 trace vector obeys the driven integral equation.
Positive rows come from the genuine factorial series; only the exceptional
zeroth row uses the actual L2 primitive inversion. -/
local notation "Φ1" => basisVec 0

local notation "Φ8" => localConformalVekuaTransportVector_continuousOn hR F hFs hb hL hhol hinj hC hK e he hsource hes

theorem localConformalVekuaForward_transport_integral_eq
    (E : ℝ) (hE : 0 ≤ E) (b : L2Z) (hbn : IsNonpositiveFourierSupport b)
    hbhalf
     (hθ : θ ∈ Φ11 (2 * Real.pi)) :
    YF E b θ = YF E b 0 + ∫ s in 0..θ,
      transportCoeff (Φ4) E s (YF E b s) +
        (-(Complex.I / (Φ3 : ℂ)) *
          Φ0 (E : ℂ) b hbhalf s) • Φ1 := by
  have hb1 : IsSobolevSeq 1 (fromL2 (1 / 2) b) := by
    exact isSobolevSeq_one_fromL2_half_of_half_regular b hbhalf
  let y := YF E b
  let p := localConformalVekuaPositiveTransportVector hR F hFs hb hL hhol hinj hC hK
    e he hsource hes E b
  let z : ℝ → ℂ := fun s => UR E b 0 s / Φ3
  let g := Φ0 E b hbhalf
  let Cg := fun s => transportCoeff (Φ4) E s (y s)
  let a : ℝ → ℂ := fun s =>
    (2 * (-E / 4) * deriv (Φ4) s * UR E b 1 s -
      Complex.I * g s) / Φ3
  have hy := Φ8 E b hbn hb1
  have hΓ : ContDiff ℝ 1 (Φ4) :=
    contDiff_physicalCircleTrace_of_neighborhood hR F (hFs.of_le (WithTop.coe_le_coe.mpr le_top))
  have hCg : ContinuousOn Cg (Φ11 (2 * Real.pi)) := (show Continuous (transportCoeff (Φ4) E) by
    unfold transportCoeff
    fun_prop).continuousOn.clm_apply hy
  have hsplit s (hs : s ∈ Φ11 (2 * Real.pi)) : y s = z s • Φ1 + p s :=
    localConformalVekuaTransportVector_zero_add_positive hR F hFs hb hL hhol hinj hC hK
      e he hsource hes E b hbn hb1 hs
  have hsub : Φ11 θ ⊆ Φ11 (2 * Real.pi) := Icc_subset_Icc le_rfl hθ.2
  have hpi : IntervalIntegrable (fun s => Cg s - (Cg s) 0 • Φ1)
      volume 0 θ := by
    exact ((hCg.sub ((show ContinuousOn (fun s => (Cg s) 0) (Φ11 (2 * Real.pi)) by
      convert ((innerSL ℂ (Φ1)).continuous.continuousOn.comp hCg (fun _ _ => Set.mem_univ _)) using 1
      · funext s
        simp [inner_basisVec]).smul continuousOn_const)).mono (by simpa [uIcc_of_le hθ.1] using hsub)).intervalIntegrable
  have hgi : IntervalIntegrable g volume 0 θ :=
    (intervalIntegrable_boundaryL2 g).mono_set' (by
      simp [uIoc_of_le hθ.1, uIoc_of_le Real.two_pi_pos.le]
      exact Ioc_subset_Ioc le_rfl hθ.2)
  have hai : IntervalIntegrable a volume 0 θ :=
    ((((continuous_const.mul hΓ.continuous_deriv_one).mul (Φ2 E b hbn hb1 1)).intervalIntegrable 0 θ).sub (hgi.const_mul Complex.I)).div_const _
  calc
    _ = _ := hsplit θ hθ
    _ = z 0 • Φ1 + p 0 +
        ((∫ s in 0..θ, a s) • Φ1 +
          ∫ s in 0..θ, Cg s - (Cg s) 0 • Φ1) := by
      rw [show z θ = z 0 + ∫ s in 0..θ, a s by
        simpa [z, a, g, add_div] using congrArg (fun v => v / (Φ3 : ℂ)) (localConformalVekuaForward_zero_integral_eq hR F hFs hb hL hhol hinj hC hK e he hsource hes E b hbn hbhalf hθ), sub_eq_iff_eq_add.mp (intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hθ.1 ((show ContinuousOn p (Φ11 (2 * Real.pi)) by
        apply (hy.sub (((Φ2 E b hbn hb1 0).div_const _).continuousOn.smul
          (continuousOn_const : ContinuousOn (fun _ => Φ1)
            (Φ11 (2 * Real.pi))))).congr
        intro s hs
        change p s = y s - z s • Φ1
        rw [hsplit s hs]
        abel).mono hsub) (fun s hs => (localConformalVekuaPositiveTransportVector_hasDerivAt hR F hFs hb hL hhol hinj hC hK e he hsource hes E b hbn hb1 ⟨hs.1, hs.2.trans_le hθ.2⟩).congr_deriv (localConformalVekuaPositiveTransportDerivative_tsum_eq hR F hFs hb hL hhol hinj hC hK e he hsource hes E hE b hbn hb1 ⟨hs.1.le, hs.2.le.trans hθ.2⟩)) hpi).symm, add_smul]
      abel
    _ = y 0 + ∫ s in 0..θ,
        a s • Φ1 + (Cg s - (Cg s) 0 • Φ1) := by
      rw [← hsplit 0 ⟨le_rfl, Real.two_pi_pos.le⟩,
        ← intervalIntegral.integral_smul_const,
        ← intervalIntegral.integral_add (by
          exact ⟨MeasureTheory.Integrable.smul_const hai.1 _,
            MeasureTheory.Integrable.smul_const hai.2 _⟩) hpi]
    _ = _ := by
      congr 1
      apply intervalIntegral.integral_congr
      intro s hs
      rw [uIcc_of_le hθ.1] at hs
      change a s • Φ1 + (Cg s - ((Cg s) 0) • Φ1) = _
      rw [show a s = (Cg s) 0 - (Complex.I / (Φ3)) * g s by
        dsimp only [a]
        rw [sub_div, forward_zero_transportCoeff hR F hFs hb hL hhol hinj hC hK e he hsource hes E hE b hbn hb1 ⟨hs.1, hs.2.trans hθ.2⟩]
        ring, sub_smul]
      simp
      abel

/-- The actual forward vector equals genuine homogeneous transport plus
the true L2 Duhamel vector. No forced ODE is assumed. -/
theorem localConformalVekuaForward_transport_eq
    E (hE : 0 ≤ E) (b : L2Z) (hbn : IsNonpositiveFourierSupport b)
    hbhalf
     (hΓLip : LipschitzWith L (Φ4))
     (hW : IsTransport (Φ4) E W)
     (hθ : θ ∈ Φ11 (2 * Real.pi)) :
    YF E b θ = W θ (YF E b 0) +
      physicalDrivenVector W (Φ0 (E : ℂ) b hbhalf : ℝ → ℂ) θ := by
  exact driven_eq_transport_add_physicalDrivenVector_boundaryL2 hΓLip
    (contDiff_physicalCircleTrace_of_neighborhood hR F
      (hFs.of_le (WithTop.coe_le_coe.mpr le_top))) hW
    (Φ0 E b hbhalf)
    (Φ8 E b hbn (isSobolevSeq_one_fromL2_half_of_half_regular b hbhalf))
    (fun t ht => localConformalVekuaForward_transport_integral_eq hR F hFs hb hL hhol
      hinj hC hK e he hsource hes E hE b hbn hbhalf ht) hθ

include hb hL hhol hinj hC hK e he hsource hes in
/-- The periodic endpoint of the actual trace vector determines its true
adjoint observation, with the original initial constant and sqrt(2) scale. -/
theorem localConformalVekuaForward_observationAdj_eq_cut
    E (hE : 0 ≤ E) (b : L2Z) (hbn : IsNonpositiveFourierSupport b)
    hbhalf
     (hΓLip : LipschitzWith L (Φ4))
     (hW : IsTransport (Φ4) E W) :
    observationAdj W
      (Φ0 (E : ℂ) b hbhalf : ℝ → ℂ) =
        (Complex.I * hardyFourierTrace (normalizedHardyAverage b) 0) •
          cutC (W (2 * Real.pi)) (Φ1) := by
  let y := YF E b
  let g := Φ0 E b hbhalf
  let h0 := hardyFourierTrace (normalizedHardyAverage b) 0
  let s := h0 / Φ3
  have hinit : y 0 = s • Φ1 :=
    localConformalVekuaTransportVector_origin hR F hFs hb hL hhol hinj hC hK
      e he hsource hes E b hbn (isSobolevSeq_one_fromL2_half_of_half_regular b hbhalf)
  have hT : 2 * Real.pi ∈ Φ11 (2 * Real.pi) := ⟨Real.two_pi_pos.le, le_rfl⟩
  have hform := localConformalVekuaForward_transport_eq hR F hFs hb hL hhol hinj hC hK
    e he hsource hes E hE b hbn hbhalf hΓLip hW hT
  change y (2 * Real.pi) = W (2 * Real.pi) (y 0) +
    (-(Complex.I / (Φ3))) • W (2 * Real.pi)
      (observationAdj W g) at hform
  rw [show y (2 * Real.pi) = y 0 by
    simpa using localConformalVekuaTransportVector_periodic hR F hFs
      hb hL hhol hinj hC hK e he hsource hes E b 0] at hform
  have hu : ContinuousLinearMap.adjoint (W (2 * Real.pi)) * W (2 * Real.pi) = 1 := by
    have hm := transport_mem_unitary hΓLip hW hT
    rw [Unitary.mem_iff, ContinuousLinearMap.star_eq_adjoint] at hm
    exact hm.1
  have hadj := congrArg (fun z => ContinuousLinearMap.adjoint (W (2 * Real.pi)) z) hform
  change ContinuousLinearMap.adjoint (W (2 * Real.pi)) (y 0) =
    ContinuousLinearMap.adjoint (W (2 * Real.pi))
      (W (2 * Real.pi) (y 0) +
        (-(Complex.I / (Φ3))) •
          W (2 * Real.pi) (observationAdj W g)) at hadj
  rw [map_add, map_smul, ← ContinuousLinearMap.mul_apply, hu,
    ContinuousLinearMap.one_apply, ← ContinuousLinearMap.mul_apply, hu,
    ContinuousLinearMap.one_apply] at hadj
  have hs0 : Φ3 ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)).ne'
  have hO : observationAdj W g = ((Φ3) * Complex.I) •
      (ContinuousLinearMap.adjoint (W (2 * Real.pi)) (y 0) - y 0) := by
    rw [show ContinuousLinearMap.adjoint (W (2 * Real.pi)) (y 0) - y 0 = (-(Complex.I / (Φ3))) • observationAdj W g by
      rw [hadj]
      abel, smul_smul, show Φ3 * Complex.I * -(Complex.I / (Φ3)) = 1 by
      field_simp [hs0] ; simp, one_smul]
  rw [hO, hinit, map_smul, ← smul_sub, smul_smul]
  simp [show (Φ3) * Complex.I * s = Complex.I * h0 by
    dsimp only [s]
    field_simp [hs0], h0, cutC]

include hb hL hhol hinj hC hK e he hsource hes in
/-- The projected observation annihilates the genuine normalized conormal
range on every half-regular full Hardy input, including frequency zero. -/
theorem localConformalVekuaForward_projObsDual_eq_zero_of_half_regular
    E (hE : 0 ≤ E) (b : L2Z) (hbn : IsNonpositiveFourierSupport b)
    (hbhalf : IsSobolevSeq (1 / 2) b)
     (hΓLip : LipschitzWith L (Φ4))
     (hW : IsTransport (Φ4) E W) :
    projObsDual W (NF (E : ℂ) b) = 0 := by
  have h := projObsDual_boundary_normalized hΓLip hW
    (Φ0 E b hbhalf)
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
theorem localConformalVekuaForward_periodicP_eq_zero
    E (hE : 0 ≤ E) (b : L2Z) (hbn : IsNonpositiveFourierSupport b)
    hbhalf
     (hΓLip : LipschitzWith L (Φ4))
     (hW : IsTransport (Φ4) E W)
    (hc : cutC (W (2 * Real.pi)) (Φ1) ≠ 0)
     (hθ : θ ∈ Φ11 (2 * Real.pi)) :
    periodicP W (UR (E : ℂ) b 0)
      (Φ0 (E : ℂ) b hbhalf : ℝ → ℂ) θ = 0 := by
  let g := Φ0 E b hbhalf
  let h0 := hardyFourierTrace (normalizedHardyAverage b) 0
  have hsum : volterraOp W (g : ℝ → ℂ) θ + volterraOpAdj W (g : ℝ → ℂ) θ = observation W (observationAdj W (g : ℝ → ℂ)) θ := by
    have hk s : conj (volterraKernel W s θ) = volterraKernel W θ s := by
      simp only [volterraKernel]
      rw [inner_conj_symm, ← ContinuousLinearMap.adjoint_inner_right,
        ContinuousLinearMap.adjoint_inner_left]
    have hkc : ContinuousOn (volterraKernel W θ) (Φ11 (2 * Real.pi)) :=
      ((innerSL ℂ (Φ1)).comp (W θ)).continuous.comp_continuousOn
        (continuousOn_adjoint_apply hW.1 (Φ1))
    have hg := intervalIntegrable_boundaryL2 g
    have hint : IntervalIntegrable (fun s => volterraKernel W θ s * g s)
        volume 0 (2 * Real.pi) := by
      exact hg.continuousOn_mul
        (by simpa [uIcc_of_le Real.two_pi_pos.le] using hkc)
    have hi0 : IntervalIntegrable (fun s => volterraKernel W θ s * g s) volume 0 θ :=
      hint.mono_set' (by simp [uIoc_of_le hθ.1, uIoc_of_le Real.two_pi_pos.le]
                         exact Ioc_subset_Ioc le_rfl hθ.2)
    have hi1 : IntervalIntegrable (fun s => volterraKernel W θ s * g s)
        volume θ (2 * Real.pi) :=
      hint.mono_set' (by simp [uIoc_of_le hθ.2, uIoc_of_le Real.two_pi_pos.le]
                         exact Ioc_subset_Ioc hθ.1 le_rfl)
    simp [volterraOp, volterraOpAdj, hk]
    rw [intervalIntegral.integral_add_adjacent_intervals hi0 hi1, observation, observationAdj]
    have hi : IntervalIntegrable
        (fun s => g s • ContinuousLinearMap.adjoint (W s) (Φ1))
        volume 0 (2 * Real.pi) :=
      by
        apply intervalIntegrable_iff.mpr
        simpa [IntegrableOn, uIoc_of_le Real.two_pi_pos.le] using
          integrable_boundary_observation_load hΓLip hW g
    have h := ((innerSL ℂ (Φ1)).comp (W θ)).intervalIntegral_comp_comm hi
    simp at h
    rw [← h]
    apply intervalIntegral.integral_congr
    intro s hs
    simp [volterraKernel]
    ring
  have hO := localConformalVekuaForward_observationAdj_eq_cut hR F hFs hb hL hhol hinj hC hK
    e he hsource hes E hE b hbn hbhalf hΓLip hW
  change observationAdj W g = (Complex.I * h0) •
    cutC (W (2 * Real.pi)) (Φ1) at hO
  rw [periodicP, show periodicA W (UR (E : ℂ) b 0) (g : ℝ → ℂ) θ = h0 * observation W (cutS (W (2 * Real.pi)) (Φ1)) θ by
    rw [hO] at hsum
    have h_inl : UR (E : ℂ) b 0 θ = hardyFourierTrace (normalizedHardyAverage b) 0 * observation W (Φ1) θ - Complex.I * volterraOp W (Φ0 (E : ℂ) b hbhalf : ℝ → ℂ) θ := by
      have hb1 : IsSobolevSeq 1 (fromL2 (1 / 2) b) := by
        exact isSobolevSeq_one_fromL2_half_of_half_regular b hbhalf
      let g := Φ0 E b hbhalf
      have hinner := congrArg (fun v => ⟪Φ1, v⟫_ℂ) (localConformalVekuaForward_transport_eq hR F hFs hb hL hhol hinj hC hK e he hsource hes E hE b hbn hbhalf hΓLip hW hθ)
      simp only [inner_add_right] at hinner
      have hinit : ⟪Φ1, W θ (YF E b 0)⟫_ℂ =
          hardyFourierTrace (normalizedHardyAverage b) 0 / (Φ3) *
            observation W (Φ1) θ := by
        change ⟪Φ1, W θ (YF E b 0)⟫_ℂ =
          hardyFourierTrace (normalizedHardyAverage b) 0 / (Φ3) *
            ⟪Φ1, W θ (Φ1)⟫_ℂ
        rw [localConformalVekuaTransportVector_origin hR F hFs hb hL hhol hinj hC hK
          e he hsource hes E b hbn hb1, map_smul, inner_smul_right]
      rw [show ⟪Φ1, YF E b θ⟫_ℂ = UR E b 0 θ / (Φ3) by
        simpa [inner_basisVec, localConformalVekuaTransportCoordinate] using
          Φ7 E b hbn hb1 hθ 0, hinit, show ⟪Φ1, physicalDrivenVector W g θ⟫_ℂ = -(Complex.I / (Φ3)) * volterraOp W g θ by
        rw [physicalDrivenVector, inner_smul_right, (show ⟪Φ1, W θ (∫ s in 0..θ, g s • ContinuousLinearMap.adjoint (W s) (Φ1))⟫_ℂ = volterraOp W (g : ℝ → ℂ) θ by
          have h := ((innerSL ℂ (Φ1)).comp (W θ)).intervalIntegral_comp_comm (by
            apply intervalIntegrable_iff.mpr
            apply MeasureTheory.IntegrableOn.mono_set
              (integrable_boundary_observation_load hΓLip hW g)
            rw [uIoc_of_le hθ.1]
            exact Ioc_subset_Ioc le_rfl hθ.2)
          simp at h
          rw [← h, volterraOp]
          apply intervalIntegral.integral_congr
          intro s hs
          simp [volterraKernel]
          ring)]] at hinner
      have hs0 : (Φ3 : ℂ) ≠ 0 := by
        exact_mod_cast (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)).ne'
      apply (div_left_inj' hs0).mp
      rw [hinner]
      dsimp only [g]
      ring
    rw [periodicA, h_inl, show cutS (W (2 * Real.pi)) (Φ1) = (2 : ℂ) • Φ1 + cutC (W (2 * Real.pi)) (Φ1) by
        simp [cutS, cutC]
        rw [two_smul]
        abel]
    simp only [observation, map_add, map_smul, inner_add_right, inner_smul_right] at hsum ⊢
    linear_combination (-Complex.I) * hsum - Complex.I_sq *
      (h0 * ⟪Φ1, W θ (cutC (W (2 * Real.pi)) (Φ1))⟫_ℂ), hO, map_smul, (cutB_transport (transport_mem_unitary hΓLip hW ⟨Real.two_pi_pos.le, le_rfl⟩) (Φ1) hc).2, smul_smul]
  simp only [observation, map_smul, inner_smul_right]
  linear_combination Complex.I_sq *
    (h0 * ⟪Φ1, W θ (cutS (W (2 * Real.pi)) (Φ1))⟫_ℂ)

private theorem forward_half_regular_stdBasis n :
    IsSobolevSeq (1 / 2) (stdBasisZ n : ℤ → ℂ) := by
  apply summable_of_ne_finset_zero (s := {n})
  intro k hk
  simp [stdBasisZ_apply, show k ≠ n by simpa using hk]

include hb hL hhol hinj hC hK e he hsource hes in
/-- Genuine finite Fourier density extends the bounded projected-null
identity to every normalized full Hardy input. No L2 load for those
possibly rough inputs is asserted by this extension. -/
theorem localConformalVekuaForward_projObsDual_eq_zero
    E (hE : 0 ≤ E)
     (hΓLip : LipschitzWith L (Φ4))
     (hW : IsTransport (Φ4) E W)
    (b : L2Z) (hbn : IsNonpositiveFourierSupport b) :
    projObsDual W (NF (E : ℂ) b) = 0 := by
  have hkeep : (1 - posProj) b = b := by
    apply lp.ext
    funext n
    by_cases hn : 0 < n
    · simp [posProj, hn, hbn n hn]
    · simp [posProj, hn]
  simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.zero_apply, hkeep] using (congrArg (fun A : L2Z →L[ℂ] Ell2 => A b) (show (projObsDual W).comp ((NF E).comp (1 - posProj)) = 0 by
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
          simp [posProj, diagOp_apply, stdBasisZ_apply, lp.single_apply, hn]
        · simp [posProj, diagOp_apply, stdBasisZ_apply, lp.single_apply, hkn]
      rw [hzero, map_zero, map_zero]
    · have hkeep : (1 - posProj) (stdBasisZ n) = stdBasisZ n := by
        apply lp.ext
        funext k
        by_cases hkn : k = n
        · subst k
          simp [posProj, diagOp_apply, stdBasisZ_apply, lp.single_apply, hn]
        · simp [posProj, diagOp_apply, stdBasisZ_apply, lp.single_apply, hkn]
      rw [hkeep]
      apply localConformalVekuaForward_projObsDual_eq_zero_of_half_regular hR F hFs hb hL
        hhol hinj hC hK e he hsource hes E hE (stdBasisZ n) _
        (forward_half_regular_stdBasis n) hΓLip hW
      intro k hk
      have hkn : k ≠ n := by omega
      simp [stdBasisZ_apply, hkn]))

end PhysicalCoordinates

end PolyaNeumann

end
