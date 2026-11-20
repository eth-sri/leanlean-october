module

public import RequestProject.CircleFourier
public import RequestProject.ConformalDiskCoordinates

public import RequestProject.LocalConformalVekuaTransport
public import RequestProject.ObservationLp
public import RequestProject.PeriodicFourierDerivative
public import RequestProject.PhysicalDrivenKernelRealization
public import RequestProject.ReducedForm
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

section

variable (y : L2Z) (hy : IsSobolevSeq (1 / 2 : ℝ) (y : ℤ → ℂ))
include y hy

/-- The genuine ordinary boundary L2 load represented by a half-regular
normalized Fourier vector. -/
def halfRegularCoordinateLoad  : BoundaryL2 :=
  boundaryFourier.symm (sobVec (1 / 2 : ℝ) (y : ℤ → ℂ) hy)

/-- The unitary Fourier normalization is exact, including frequency zero. -/
theorem halfRegularCoordinateLoad_normalized  :
    sobolevSmoothing (1 / 2 : ℝ) (by norm_num)
      (boundaryFourier (halfRegularCoordinateLoad y hy)) = y := by
  rw [halfRegularCoordinateLoad, boundaryFourier.apply_symm_apply]
  apply lp.ext
  funext n
  change fromL2 (1 / 2 : ℝ) (sobVec (1 / 2 : ℝ) (y : ℤ → ℂ) hy) n = y n
  rw [fromL2_sobVec]

end

/-- Fourier inversion for an actual L2 derivative. No absolute continuity
or differentiability of the original continuous function is assumed. -/
theorem eq_add_integral_of_L2_periodic_fourier_derivative
    {v : ℝ → ℂ} (hv : Continuous v)
    (hvper : Function.Periodic v (2 * Real.pi)) (d : BoundaryL2)
    (hcoeff : ∀ n : ℤ, fourierCoeffOn Real.two_pi_pos (d : ℝ → ℂ) n =
      (Complex.I * (n : ℂ)) * fourierCoeffOn Real.two_pi_pos v n)
    {θ : ℝ} (hθ : θ ∈ Icc 0 (2 * Real.pi)) :
    v θ = v 0 + ∫ s in (0 : ℝ)..θ, d s := by
  let P := fun t => ∫ s in (0 : ℝ)..t, d s
  have hPi := intervalIntegrable_boundaryL2 d
  have hPAC : AbsolutelyContinuousOnInterval P 0 (2 * Real.pi) :=
    absolutelyContinuousOnInterval_intervalIntegral_banach hPi
      (by simp)
  have hPC : ContinuousOn P (Icc 0 (2 * Real.pi)) := by
    simpa only [uIcc_of_le Real.two_pi_pos.le] using hPAC.continuousOn
  have hPD :=
    ae_hasDerivAt_intervalIntegral_banach Real.two_pi_pos.le hPi
  have hP0 : P 0 = 0 := by aesop
  have hPT : P (2 * Real.pi) = 0 :=
    integral_eq_zero_of_periodic_fourier_derivative hcoeff
  have hPc (n : ℤ) : fourierCoeffOn Real.two_pi_pos (d : ℝ → ℂ) n =
      (Complex.I * (n : ℂ)) * fourierCoeffOn Real.two_pi_pos P n :=
    fourierCoeffOn_of_ac_ae_hasDerivAt hPAC (Lp.memLp d) hPD (hP0.trans hPT.symm) n
  have hncoeff (n : ℤ) (hn : n ≠ 0) :
      fourierCoeffOn Real.two_pi_pos v n = fourierCoeffOn Real.two_pi_pos P n :=
    mul_left_cancel₀ (mul_ne_zero Complex.I_ne_zero (Int.cast_ne_zero.mpr hn))
      ((hcoeff n).symm.trans (hPc n))
  let f : ℝ → ℂ := fun t => v t - P t
  have hfc : ContinuousOn f (Icc 0 (2 * Real.pi)) := hv.continuousOn.sub hPC
  have hfe : f 0 = f (2 * Real.pi) := by
    dsimp only [f]
    rw [hP0, hPT, sub_zero, sub_zero]
    simpa only [zero_add] using (hvper 0).symm
  let F : ℝ → ℂ := fun t => AddCircle.liftIco (2 * Real.pi) 0 f
    (t : AddCircle (2 * Real.pi))
  have hFc : Continuous F :=
    (AddCircle.liftIco_zero_continuous hfe hfc).comp (AddCircle.continuous_mk' _)
  have hFp : Function.Periodic F (2 * Real.pi) := by
    intro t
    dsimp only [F]
    simp
  have hFf : EqOn F f (Icc 0 (2 * Real.pi)) := liftIco_zero_eqOn_Icc hfe
  have hcoeffF (n : ℤ) (hn : n ≠ 0) : fourierCoeffOn Real.two_pi_pos F n = 0 := by
    rw [fourierCoeffOn_congr_Icc hFf n]
    rw [fourierCoeffOn_sub_of_continuousOn hv.continuousOn hPC n, hncoeff n hn, sub_self]
  have hconst := eq_at_zero_of_periodic_nonzero_fourier_eq_zero hFc hFp hcoeffF θ
  rw [hFf hθ, hFf ⟨le_rfl, Real.two_pi_pos.le⟩] at hconst
  change v θ - P θ = v 0 - P 0 at hconst
  rw [hP0, sub_zero] at hconst
  grind

/-- The normalization changes raw order one to normalized order one half. -/
theorem isSobolevSeq_one_fromL2_half_iff (b : L2Z) :
    IsSobolevSeq 1 (fromL2 (1 / 2) b) ↔ IsSobolevSeq (1 / 2) (b : ℤ → ℂ) := by
  have he (n : ℤ) : sobWeight n ^ (1 : ℝ) * ‖fromL2 (1 / 2) b n‖ =
      sobWeight n ^ (1 / 2 : ℝ) * ‖b n‖ := by
    rw [fromL2, norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.rpow_nonneg (sobWeight_pos n).le _),
      ← mul_assoc, ← Real.rpow_add (sobWeight_pos n)]
    norm_num
  simp only [IsSobolevSeq, he]

/-- The conormal preserves one additional half derivative of the input. -/
theorem normalizedConormal_preserves_half_regular
    {β a g : ℤ → ℂ} (hβ : IsWL1 (1 / 2 : ℝ) β)
    (ha : IsWL1 (1 / 2 : ℝ) a) (hg : IsWL1 (1 / 2 : ℝ) g)
    (E : ℂ) (b : L2Z) (hb : IsSobolevSeq (1 / 2 : ℝ) (b : ℤ → ℂ)) :
    IsSobolevSeq (1 / 2 : ℝ) (normalizedConormal hβ ha hg E b : ℤ → ℂ) := by
  have he := congrArg (fun A : L2Z →L[ℂ] L2Z => A b)
    (normalizedConormal_sub_one_eq hβ ha hg E)
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply,
    ContinuousLinearMap.comp_apply] at he
  have hr : IsSobolevSeq (1 / 2 : ℝ)
      (sobolevSmoothing 1 zero_le_one (conormalRemOp (by norm_num) hβ ha hg E b - b) : ℤ → ℂ) := by
    exact (sobNormSq_mono (by norm_num : (1 / 2 : ℝ) ≤ 1)
      (isSobolevSeq_fromL2 1 _)).1
  have hsum := isSobolevSeq_add hb hr
  have heq : normalizedConormal hβ ha hg E b =
      b + sobolevSmoothing 1 zero_le_one (conormalRemOp (by norm_num) hβ ha hg E b - b) := by
    rw [← he]
    abel
  rw [heq]
  assumption

/-- The forced transport equation with an ordinary boundary `L²` load. -/
theorem driven_eq_transport_add_physicalDrivenVector_boundaryL2
    {γ : ℝ → ℂ} {L : NNReal} (hγLip : LipschitzWith L γ) {E : ℝ}
    {W : ℝ → Ell2 →L[ℂ] Ell2} (hW : IsTransport γ E W)
    (g : BoundaryL2) {y : ℝ → Ell2} (hy : ContinuousOn y (Icc 0 (2 * Real.pi)))
    (hyint : ∀ θ ∈ Icc 0 (2 * Real.pi),
      y θ = y 0 + ∫ s in (0 : ℝ)..θ, transportCoeff γ E s (y s) +
        (-(Complex.I / (Real.sqrt 2 : ℂ)) * g s) • basisVec 0)
    {θ : ℝ} (hθ : θ ∈ Icc 0 (2 * Real.pi)) :
    y θ = W θ (y 0) + physicalDrivenVector W (g : ℝ → ℂ) θ := by
  let c := -(Complex.I / (Real.sqrt 2 : ℂ))
  have hi := (intervalIntegrable_boundaryL2 g).const_mul c |>.smul_continuousOn
    (continuousOn_const (c := basisVec 0))
  rw [driven_eq_transport hγLip hW hi hy hyint θ hθ, map_add, physicalDrivenVector, ← map_smul,
    ← intervalIntegral.integral_smul]
  congr 2
  exact intervalIntegral.integral_congr fun _ _ => by simp [c, smul_smul]


section PhysicalCoordinates

variable {F : ℂ → ℂ} (coords : ConformalDiskCoordinates F)
include coords

local notation "JF" => localConformalHardyPrimitive coords.one_lt_radius F coords.smooth
local notation "VF" => localConformalVekuaH1 coords
local notation "TF" => coords.trace
local notation "UR" => localConformalVekuaTraceRow coords
local notation "YF" => localConformalVekuaTransportVector coords
local notation "hβF" => localConformalVelocityCircle_isWL1_half coords.one_lt_radius F coords.smooth
local notation "haF" => localConformalHardyPrimitiveMultiplier_isWL1 coords.one_lt_radius F coords.smooth
local notation "hgF" => localConformalCenteredCircle_isWL1_half coords.one_lt_radius F coords.smooth
local notation "NF" => normalizedConormal hβF haF hgF
section

variable (E : ℂ) (b : L2Z) (hbhalf : IsSobolevSeq (1 / 2 : ℝ) (b : ℤ → ℂ))
include E b hbhalf

/-- The ordinary coordinate load exists here as a conclusion of genuine
half-order input regularity and the proved normalized smoothing formula. -/
def localConformalVekuaForwardLoad  : BoundaryL2 :=
  halfRegularCoordinateLoad (NF E b)
    (normalizedConormal_preserves_half_regular hβF haF hgF E b hbhalf)

theorem localConformalVekuaForwardLoad_normalized  :
    sobolevSmoothing (1 / 2 : ℝ) (by norm_num)
      (boundaryFourier (localConformalVekuaForwardLoad coords E b hbhalf)) = NF E b :=
  halfRegularCoordinateLoad_normalized _ _

end

section

variable (E : ℂ) (b : L2Z) (hbn : IsNonpositiveFourierSupport b) (hbhalf : IsSobolevSeq (1 / 2 : ℝ) (b : ℤ → ℂ))
include E b hbn hbhalf

local notation "G0" => boundaryContinuousMultiplier (localConformalVelocityCircle F) (TF (VF (F 1) E (JF b)))
local notation "g0" => localConformalVekuaForwardLoad coords E b hbhalf

/-- The ordinary L² right side of the zeroth row equation. -/
def forwardZeroDerivative : BoundaryL2 := (2 * (-E / 4)) • G0 - Complex.I • g0

/-- Actual Fourier inversion of the exceptional zeroth row with its
genuine coordinate L2 conormal forcing. The zeroth coefficient is used. -/
theorem localConformalVekuaForward_zero_fourier_derivative
     (n : ℤ) :
    fourierCoeffOn Real.two_pi_pos (forwardZeroDerivative coords E b hbhalf : ℝ → ℂ) n =
      (Complex.I * (n : ℂ)) * fourierCoeffOn Real.two_pi_pos (UR E b 0) n := by
  have hb1 := (isSobolevSeq_one_fromL2_half_iff b).2 hbhalf
  have ht0 : (TF (VF (F 1) E b) : ℝ → ℂ)
      =ᵐ[volume.restrict (Ioc 0 (2 * Real.pi))] UR E b 0 := by
    simpa only [pow_zero, ContinuousLinearMap.one_apply] using
      localConformalVekuaTraceRow_ae coords E b hbn hb1 0
  have hNC := localConformalVekua_normalizedConormal_fourier coords E b hbn hb1 n
  have hload := congrArg (fun v : L2Z => v n)
    (localConformalVekuaForwardLoad_normalized coords E b hbhalf)
  change ((sobWeight n ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * boundaryFourier g0 n = NF E b n at hload
  simp only [localConformalVekuaGradientA_apply, map_smul, lp.coeFn_smul,
    Pi.smul_apply] at hNC
  have hw : (((sobWeight n ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)) ≠ 0 := by
    exact_mod_cast (Real.rpow_pos_of_pos (sobWeight_pos n) (-(1 / 2 : ℝ))).ne'
  have hn : -(n : ℂ) * boundaryFourier (TF (VF (F 1) E b)) n -
      2 * Complex.I * ((-E / 4) * boundaryFourier G0 n) = boundaryFourier g0 n :=
    mul_left_cancel₀ hw (hNC.symm.trans hload.symm)
  have hs0 : (Real.sqrt (2 * Real.pi) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr Real.two_pi_pos).ne'
  apply mul_left_cancel₀ hs0
  calc
    _ = boundaryFourier (forwardZeroDerivative coords E b hbhalf) n := (boundaryFourier_apply _ n).symm
    _ = (Complex.I * (n : ℂ)) * boundaryFourier (TF (VF (F 1) E b)) n := by
      simp only [forwardZeroDerivative, map_sub, map_smul, lp.coeFn_sub, Pi.sub_apply,
        lp.coeFn_smul, Pi.smul_apply]
      rw [← hn]
      ring_nf
      simp
    _ = _ := by rw [boundaryFourier_apply_of_ae _ ht0]; ring

private theorem forward_zero_derivative_ae :
    (forwardZeroDerivative coords E b hbhalf : ℝ → ℂ) =ᵐ[volume.restrict (Ioc 0 (2 * Real.pi))]
      fun t => 2 * (-E / 4) * deriv (physicalCircleTrace F) t * UR E b 1 t - Complex.I * g0 t := by
  have ht := localConformalVekuaTraceRow_ae coords E b hbn ((isSobolevSeq_one_fromL2_half_iff b).2 hbhalf) 1
  rw [pow_one] at ht
  filter_upwards [Lp.coeFn_sub ((2 * (-E / 4)) • G0) (Complex.I • g0),
    Lp.coeFn_smul (2 * (-E / 4)) G0, Lp.coeFn_smul Complex.I g0,
    boundaryContinuousMultiplier_ae (localConformalVelocityCircle F) (TF (VF (F 1) E (JF b))), ht]
    with t hsub hs hg hG htrace
  change (((2 * (-E / 4)) • G0 - Complex.I • g0 : BoundaryL2) : ℝ → ℂ) t = _
  simp only [hsub, Pi.sub_apply, hs, hg, Pi.smul_apply, smul_eq_mul, hG, htrace,
    localConformalVelocityCircle_apply coords.one_lt_radius F coords.smooth]
  ring

/-- The exceptional zero row has its true inhomogeneous primitive
formula, with the actual initial constant and ordinary L2 coordinate load. -/
theorem localConformalVekuaForward_zero_integral_eq
    
    {θ : ℝ} (hθ : θ ∈ Icc 0 (2 * Real.pi)) :
    UR E b 0 θ = UR E b 0 0 + ∫ t in (0 : ℝ)..θ,
      2 * (-E / 4) * deriv (physicalCircleTrace F) t * UR E b 1 t -
        Complex.I * localConformalVekuaForwardLoad coords E b hbhalf t := by
  have hb1 := (isSobolevSeq_one_fromL2_half_iff b).2 hbhalf
  rw [eq_add_integral_of_L2_periodic_fourier_derivative
    (localConformalVekuaTraceRow_continuous coords E b hbn hb1 0)
    (localConformalVekuaTraceRow_periodic coords E b 0) (forwardZeroDerivative coords E b hbhalf)
    (localConformalVekuaForward_zero_fourier_derivative coords E b hbn hbhalf) hθ]
  congr 1
  exact intervalIntegral.integral_congr_ae_restrict
    ((forward_zero_derivative_ae coords E b hbn hbhalf).filter_mono (ae_mono
      (Measure.restrict_mono (by rw [uIoc_of_le hθ.1]; exact Ioc_subset_Ioc le_rfl hθ.2) le_rfl)))

end

section

variable (E : ℝ) (hE : 0 ≤ E) (b : L2Z) (hbn : IsNonpositiveFourierSupport b)
include E hE b hbn

/-- Integrating the zeroth scalar row and the positive vector rows gives the full equation. -/
theorem localConformalVekuaForward_transport_integral_eq
    (hbhalf : IsSobolevSeq (1 / 2 : ℝ) (b : ℤ → ℂ))
    {θ : ℝ} (hθ : θ ∈ Icc 0 (2 * Real.pi)) :
    YF E b θ = YF E b 0 + ∫ s in (0 : ℝ)..θ,
      transportCoeff (physicalCircleTrace F) E s (YF E b s) +
        (-(Complex.I / (Real.sqrt 2 : ℂ)) *
          localConformalVekuaForwardLoad coords (E : ℂ) b hbhalf s) • basisVec 0 := by
  have hb1 := (isSobolevSeq_one_fromL2_half_iff b).2 hbhalf
  let y := YF E b
  let P := vekuaPositivePart
  let g := localConformalVekuaForwardLoad coords (E : ℂ) b hbhalf
  let f := fun s => transportCoeff (physicalCircleTrace F) E s (y s)
  let a := fun s => -(Complex.I / (Real.sqrt 2 : ℂ)) * g s
  have hΓ :=
    contDiff_physicalCircleTrace_of_neighborhood coords.one_lt_radius F (coords.smooth.of_le (WithTop.coe_le_coe.mpr le_top))
  have hCoeff : Continuous (transportCoeff (physicalCircleTrace F) E) := by
    have hd := hΓ.continuous_deriv_one
    have hc := Complex.continuous_conj.comp hd
    unfold transportCoeff; fun_prop
  have hf := hCoeff.clm_apply (localConformalVekuaTransportVector_continuous coords E b hb1)
  have ha : IntervalIntegrable a volume 0 θ := ((intervalIntegrable_boundaryL2 g).mono_set' (by
    simpa only [uIoc_of_le hθ.1, uIoc_of_le Real.two_pi_pos.le] using Ioc_subset_Ioc le_rfl hθ.2)).const_mul _
  let ev := lp.evalCLM ℂ (fun _ : ℕ => ℂ) 2 0
  have he (s : ℝ) : ev (y s) = UR (E : ℂ) b 0 s / (Real.sqrt 2 : ℂ) :=
    localConformalVekuaTransportVector_coord coords E hE b hbn hb1 s 0
  have hz : ev (y θ) = ev (y 0) + ∫ s in (0 : ℝ)..θ, ev (f s) + a s := by
    rw [he, he, localConformalVekuaForward_zero_integral_eq coords (E : ℂ) b hbn hbhalf hθ,
      add_div, ← intervalIntegral.integral_div]
    congr 1
    apply intervalIntegral.integral_congr
    intro s _
    change (2 * (-(E : ℂ) / 4) * deriv (physicalCircleTrace F) s * UR (E : ℂ) b 1 s -
      Complex.I * g s) / (Real.sqrt 2 : ℂ) = (f s : ℕ → ℂ) 0 + a s
    rw [sub_div, localConformalVekuaTransport_zeroCoeff coords E hE b hbn hb1]
    simp only 
    ring
  have hPc : Continuous P := by
    change Continuous (fun x : Ell2 => x - ev x • basisVec 0)
    exact continuous_id.sub (ev.continuous.smul continuous_const)
  have hpI : IntervalIntegrable (fun s => P (f s)) volume 0 θ :=
    (hPc.comp hf).intervalIntegrable 0 θ
  have hp := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun s _ => localConformalVekuaPositive_hasDerivAt coords E b hb1 s) hpI
  have hzI := ((ev.continuous.comp hf).intervalIntegrable (μ := volume) 0 θ).add ha
  have hzI' : IntervalIntegrable (fun s => (ev (f s) + a s) • basisVec 0) volume 0 θ :=
    ⟨hzI.1.smul_const _, hzI.2.smul_const _⟩
  have hsplit (x : Ell2) : ev x • basisVec 0 + P x = x := by
    change _ + (x - ev x • basisVec 0) = x
    abel
  change y θ = y 0 + ∫ s in (0 : ℝ)..θ, f s + a s • basisVec 0
  calc
    _ = ev (y θ) • basisVec 0 + P (y θ) := (hsplit _).symm
    _ = y 0 + ∫ s in (0 : ℝ)..θ, (ev (f s) + a s) • basisVec 0 + P (f s) := by
      rw [hz, add_smul, ← intervalIntegral.integral_smul_const,
        intervalIntegral.integral_add hzI' hpI, hp]
      conv_rhs => lhs; rw [← hsplit (y 0)]
      change _ = (ev (y 0) • basisVec 0 + P (y 0)) +
        ((∫ s in (0 : ℝ)..θ, (ev (f s) + a s) • basisVec 0) + (P (y θ) - P (y 0)))
      abel
    _ = _ := by
      congr 1
      apply intervalIntegral.integral_congr
      intro s _
      change (ev (f s) + a s) • basisVec 0 + P (f s) = f s + a s • basisVec 0
      rw [add_smul, add_right_comm, hsplit]

/-- The actual forward vector equals genuine homogeneous transport plus
the true L2 Duhamel vector. No forced ODE is assumed. -/
theorem localConformalVekuaForward_transport_eq
    
    (hbhalf : IsSobolevSeq (1 / 2 : ℝ) (b : ℤ → ℂ))
    {L : NNReal} (hΓLip : LipschitzWith L (physicalCircleTrace F))
    {W : ℝ → Ell2 →L[ℂ] Ell2} (hW : IsTransport (physicalCircleTrace F) E W)
    {θ : ℝ} (hθ : θ ∈ Icc 0 (2 * Real.pi)) :
    YF E b θ = W θ (YF E b 0) +
      physicalDrivenVector W (localConformalVekuaForwardLoad coords (E : ℂ) b hbhalf : ℝ → ℂ) θ := by
  have hb1 := (isSobolevSeq_one_fromL2_half_iff b).2 hbhalf
  exact driven_eq_transport_add_physicalDrivenVector_boundaryL2 hΓLip
    hW
    (localConformalVekuaForwardLoad coords (E : ℂ) b hbhalf)
    ((localConformalVekuaTransportVector_continuous coords E b hb1).continuousOn)
    (fun t ht => localConformalVekuaForward_transport_integral_eq coords E hE b hbn hbhalf ht) hθ

end

/-- The periodic endpoint of the actual trace vector determines its true
adjoint observation, with the original initial constant and sqrt(2) scale. -/
theorem localConformalVekuaForward_observationAdj_eq_cut
    (E : ℝ) (hE : 0 ≤ E) (b : L2Z) (hbn : IsNonpositiveFourierSupport b)
    (hbhalf : IsSobolevSeq (1 / 2 : ℝ) (b : ℤ → ℂ))
    {L : NNReal} (hΓLip : LipschitzWith L (physicalCircleTrace F))
    {W : ℝ → Ell2 →L[ℂ] Ell2} (hW : IsTransport (physicalCircleTrace F) E W) :
    observationAdj W
      (localConformalVekuaForwardLoad coords (E : ℂ) b hbhalf : ℝ → ℂ) =
        (Complex.I * hardyFourierTrace (normalizedHardyAverage b) 0) •
          cutC (W (2 * Real.pi)) (basisVec 0) := by
  have hb1 := (isSobolevSeq_one_fromL2_half_iff b).2 hbhalf
  let y := YF E b
  let g := localConformalVekuaForwardLoad coords (E : ℂ) b hbhalf
  let h0 := hardyFourierTrace (normalizedHardyAverage b) 0
  let s := h0 / (Real.sqrt 2 : ℂ)
  have hinit : y 0 = s • basisVec 0 :=
    localConformalVekuaTransportVector_origin coords E b
  have hper : y (2 * Real.pi) = y 0 := by
    simpa only [zero_add] using localConformalVekuaTransportVector_periodic coords E hE b hbn hb1 0
  have hT : (2 * Real.pi) ∈ Icc 0 (2 * Real.pi) := ⟨Real.two_pi_pos.le, le_rfl⟩
  have hform := localConformalVekuaForward_transport_eq coords E hE b hbn hbhalf hΓLip hW hT
  change y (2 * Real.pi) = W (2 * Real.pi) (y 0) +
    (-(Complex.I / (Real.sqrt 2 : ℂ))) • W (2 * Real.pi)
      (observationAdj W (g : ℝ → ℂ)) at hform
  rw [hper] at hform
  have hu : ContinuousLinearMap.adjoint (W (2 * Real.pi)) * W (2 * Real.pi) = 1 := by
    have hm := transport_mem_unitary hΓLip hW hT
    rw [Unitary.mem_iff, ContinuousLinearMap.star_eq_adjoint] at hm
    tauto
  have hadj := congrArg (fun z : Ell2 => ContinuousLinearMap.adjoint (W (2 * Real.pi)) z) hform
  change ContinuousLinearMap.adjoint (W (2 * Real.pi)) (y 0) =
    ContinuousLinearMap.adjoint (W (2 * Real.pi))
      (W (2 * Real.pi) (y 0) +
        (-(Complex.I / (Real.sqrt 2 : ℂ))) •
          W (2 * Real.pi) (observationAdj W (g : ℝ → ℂ))) at hadj
  rw [map_add, map_smul, ← ContinuousLinearMap.mul_apply, hu,
    ContinuousLinearMap.one_apply, ← ContinuousLinearMap.mul_apply, hu,
    ContinuousLinearMap.one_apply] at hadj
  have hsub : ContinuousLinearMap.adjoint (W (2 * Real.pi)) (y 0) - y 0 =
      (-(Complex.I / (Real.sqrt 2 : ℂ))) • observationAdj W (g : ℝ → ℂ) := by
    rw [hadj]
    abel
  have hs0 : (Real.sqrt 2 : ℂ) ≠ 0 := by
    simp
  have hcancel : (Real.sqrt 2 : ℂ) * Complex.I * -(Complex.I / (Real.sqrt 2 : ℂ)) = 1 := by
    field_simp [hs0] ; simp
  have hO : observationAdj W (g : ℝ → ℂ) = ((Real.sqrt 2 : ℂ) * Complex.I) •
      (ContinuousLinearMap.adjoint (W (2 * Real.pi)) (y 0) - y 0) := by
    rw [hsub, smul_smul, hcancel, one_smul]
  rw [hO, hinit, map_smul, ← smul_sub, smul_smul]
  have hscalar : ((Real.sqrt 2 : ℂ) * Complex.I) * s = Complex.I * h0 := by
    dsimp only [s]
    field_simp [hs0]
  tauto

/-- The projected observation annihilates the genuine normalized conormal
range on every half-regular full Hardy input, including frequency zero. -/
theorem localConformalVekuaForward_projObsDual_eq_zero_of_half_regular
    (E : ℝ) (hE : 0 ≤ E) (b : L2Z) (hbn : IsNonpositiveFourierSupport b)
    (hbhalf : IsSobolevSeq (1 / 2 : ℝ) (b : ℤ → ℂ))
    {L : NNReal} (hΓLip : LipschitzWith L (physicalCircleTrace F))
    {W : ℝ → Ell2 →L[ℂ] Ell2} (hW : IsTransport (physicalCircleTrace F) E W) :
    projObsDual W (NF (E : ℂ) b) = 0 := by
  have h := projObsDual_boundary_normalized hΓLip hW
    (localConformalVekuaForwardLoad coords (E : ℂ) b hbhalf)
  rw [localConformalVekuaForwardLoad_normalized, map_smul,
    localConformalVekuaForward_observationAdj_eq_cut coords E hE b hbn hbhalf hΓLip hW,
    map_smul, cutProj_eq_starProjection,
    Submodule.starProjection_orthogonal_apply_eq_zero (Submodule.mem_span_singleton_self _),
    smul_zero] at h
  exact (smul_eq_zero.mp h).resolve_left (by
    exact_mod_cast (Real.sqrt_pos.mpr Real.two_pi_pos).ne')

section

variable (E : ℝ) (hE : 0 ≤ E) (b : L2Z) (hbn : IsNonpositiveFourierSupport b) (hbhalf : IsSobolevSeq (1 / 2 : ℝ) (b : ℤ → ℂ)) {L : NNReal} (hΓLip : LipschitzWith L (physicalCircleTrace F)) {W : ℝ → Ell2 →L[ℂ] Ell2} (hW : IsTransport (physicalCircleTrace F) E W)
include E hE b hbn hbhalf L hΓLip W hW

/-- The actual coordinate trace obeys the true forward observation and
Volterra identity for its derived ordinary L2 conormal load. -/
theorem localConformalVekuaForward_trace_eq
    
    {θ : ℝ} (hθ : θ ∈ Icc 0 (2 * Real.pi)) :
    UR (E : ℂ) b 0 θ = hardyFourierTrace (normalizedHardyAverage b) 0 *
      observation W (basisVec 0) θ - Complex.I *
        volterraOp W (localConformalVekuaForwardLoad coords (E : ℂ) b hbhalf : ℝ → ℂ) θ := by
  have hb1 := (isSobolevSeq_one_fromL2_half_iff b).2 hbhalf
  let g := localConformalVekuaForwardLoad coords (E : ℂ) b hbhalf
  have hform := localConformalVekuaForward_transport_eq coords E hE b hbn hbhalf hΓLip hW hθ
  have hinner := congrArg (fun v : Ell2 => ⟪basisVec 0, v⟫_ℂ) hform
  simp  [inner_add_right] at hinner
  have hleft : ⟪basisVec 0, YF E b θ⟫_ℂ = UR (E : ℂ) b 0 θ / (Real.sqrt 2 : ℂ) := by
    simpa only [inner_basisVec, localConformalVekuaTransportCoordinate, if_true] using
      localConformalVekuaTransportVector_coord coords E hE b hbn hb1 θ 0
  have hinit : ⟪basisVec 0, W θ (YF E b 0)⟫_ℂ =
      (hardyFourierTrace (normalizedHardyAverage b) 0 / (Real.sqrt 2 : ℂ)) *
        observation W (basisVec 0) θ := by
    change ⟪basisVec 0, W θ (YF E b 0)⟫_ℂ =
      (hardyFourierTrace (normalizedHardyAverage b) 0 / (Real.sqrt 2 : ℂ)) *
        ⟪basisVec 0, W θ (basisVec 0)⟫_ℂ
    rw [localConformalVekuaTransportVector_origin coords E b, map_smul, inner_smul_right]
  have hforced : ⟪basisVec 0, physicalDrivenVector W (g : ℝ → ℂ) θ⟫_ℂ =
      -(Complex.I / (Real.sqrt 2 : ℂ)) * volterraOp W (g : ℝ → ℂ) θ := by
    rw [physicalDrivenVector, inner_smul_right, inner_transport_integral hW.1 θ ((intervalIntegrable_boundaryL2 g).mono_set' (by grind))
      (uIcc_subset_Icc ⟨le_rfl, Real.two_pi_pos.le⟩ hθ)]
    rfl
  rw [hleft, hinit, hforced] at hinner
  have hs0 : (Real.sqrt 2 : ℂ) ≠ 0 := by
    simp
  apply (div_left_inj' hs0).mp
  rw [hinner]
  ring

/-- The genuine periodic form vanishes on the actual forward Vekua trace
and its actual L2 load. A nonzero cut is used only by the correction B. -/
theorem localConformalVekuaForward_periodicP_eq_zero
    
    (hc : cutC (W (2 * Real.pi)) (basisVec 0) ≠ 0)
    {θ : ℝ} (hθ : θ ∈ Icc 0 (2 * Real.pi)) :
    periodicP W (UR (E : ℂ) b 0)
      (localConformalVekuaForwardLoad coords (E : ℂ) b hbhalf : ℝ → ℂ) θ = 0 := by
  let g := localConformalVekuaForwardLoad coords (E : ℂ) b hbhalf
  let h0 := hardyFourierTrace (normalizedHardyAverage b) 0
  have hsum := volterraOp_add_adj_of_intervalIntegrable hW.1 (intervalIntegrable_boundaryL2 g) hθ
  have hO := localConformalVekuaForward_observationAdj_eq_cut coords E hE b hbn hbhalf hΓLip hW
  change observationAdj W (g : ℝ → ℂ) = (Complex.I * h0) •
    cutC (W (2 * Real.pi)) (basisVec 0) at hO
  have hS : cutS (W (2 * Real.pi)) (basisVec 0) =
      (2 : ℂ) • basisVec 0 + cutC (W (2 * Real.pi)) (basisVec 0) := by
    simp  [cutS, cutC]
    rw [two_smul]
    abel
  have hA : periodicA W (UR (E : ℂ) b 0) (g : ℝ → ℂ) θ =
      h0 * observation W (cutS (W (2 * Real.pi)) (basisVec 0)) θ := by
    rw [hO] at hsum
    rw [periodicA, localConformalVekuaForward_trace_eq coords E hE b hbn hbhalf hΓLip hW hθ, hS]
    simp only [observation, map_add, map_smul, inner_add_right, inner_smul_right] at hsum ⊢
    linear_combination (-Complex.I) * hsum - Complex.I_sq *
      (h0 * ⟪basisVec 0, W θ (cutC (W (2 * Real.pi)) (basisVec 0))⟫_ℂ)
  have hBc := (cutB_transport (transport_mem_unitary hΓLip hW
    ⟨Real.two_pi_pos.le, le_rfl⟩) (basisVec 0) hc).2
  rw [periodicP, hA, hO, map_smul, hBc, smul_smul]
  simp  [observation, map_smul, inner_smul_right]
  linear_combination Complex.I_sq *
    (h0 * ⟪basisVec 0, W θ (cutS (W (2 * Real.pi)) (basisVec 0))⟫_ℂ)

end

/-- Genuine finite Fourier density extends the bounded projected-null
identity to every normalized full Hardy input. No L2 load for those
possibly rough inputs is asserted by this extension. -/
theorem localConformalVekuaForward_projObsDual_eq_zero
    (E : ℝ) (hE : 0 ≤ E)
    {L : NNReal} (hΓLip : LipschitzWith L (physicalCircleTrace F))
    {W : ℝ → Ell2 →L[ℂ] Ell2} (hW : IsTransport (physicalCircleTrace F) E W)
    (b : L2Z) (hbn : IsNonpositiveFourierSupport b) :
    projObsDual W (NF (E : ℂ) b) = 0 := by
  exact eq_zero_of_nonpositive_modes ((projObsDual W).comp (NF (E : ℂ))) (fun n hn =>
    localConformalVekuaForward_projObsDual_eq_zero_of_half_regular coords E hE (stdBasisZ n)
      (stdBasisZ_mem_nonpositive hn) (stdBasisZ_isSobolevSeq _ n) hΓLip hW) hbn

/-- The forward load of the Hardy input obtained by the inverse gauge is exactly the given load. -/
theorem conormal_eq_of_observationAdj_eq_zero
    {L : NNReal} (hLip : LipschitzWith L (physicalCircleTrace F))
    {E : ℝ} (hE : 0 < E) {W : ℝ → Ell2 →L[ℂ] Ell2}
    (hW : IsTransport (physicalCircleTrace F) E W) (g : BoundaryL2)
    (hO : observationAdj W (g : ℝ → ℂ) = 0) :
    ∃ b : L2Z, IsNonpositiveFourierSupport b ∧ NF (E : ℂ) b =
      sobolevSmoothing (1 / 2 : ℝ) (by norm_num) (boundaryFourier g) := by
  let γ := physicalCircleTrace F
  have hγ := contDiff_physicalCircleTrace_of_neighborhood coords.one_lt_radius F
    (coords.smooth.of_le (by simp))
  let b := physicalDrivenKernelInput hLip hγ hW g (Lp.memLp g) hO
  have hb := physicalDrivenKernelInput_nonpositive coords hLip hE hW g hO
  have hb1 := fromL2_physicalDrivenKernelInput_isSobolevSeq_one hLip hγ hW g (Lp.memLp g) hO
  have hbhalf :=
    (isSobolevSeq_one_fromL2_half_iff b).1 hb1
  let r := localConformalVekuaForwardLoad coords (E : ℂ) b hbhalf
  have hreg : IsSobolevSeq (0 + 1 : ℝ) (normalizedHardyAverage b) := by
    simpa only [zero_add] using (show IsSobolevSeq 1 (normalizedHardyAverage b) from
      isSobolevSeq_smul ((Real.sqrt (2 * Real.pi) : ℂ)⁻¹) hb1)
  have hc := continuous_hardyFourierTrace (sq_tsum_norm_le (s := 0) (by norm_num) hreg).1
  have hy : EqOn (YF E b) (physicalDrivenVector W (g : ℝ → ℂ)) (Icc 0 (2 * Real.pi)) := by
    apply vekuaTowerVector_eq_driven hγ hc hLip hW _ (intervalIntegrable_boundaryL2 g)
    intro t ht
    rw [hardyFourierTrace_physicalDrivenKernelInput, physicalDrivenPeriodicGauge_eqOn _ E W g hO 0 ht]
  have hd : EqOn (physicalDrivenVector W (r : ℝ → ℂ)) (physicalDrivenVector W (g : ℝ → ℂ))
      (Icc 0 (2 * Real.pi)) := by
    intro t ht
    have h := localConformalVekuaForward_transport_eq coords E hE.le b hb hbhalf hLip hW ht
    rw [hy ht, hy (show (0 : ℝ) ∈ Icc 0 (2 * Real.pi) from ⟨le_rfl, Real.two_pi_pos.le⟩),
      physicalDrivenVector_zero, map_zero, zero_add] at h
    exact h.symm
  have hr : r = g := by
    apply Lp.ext
    apply (ae_restrict_iff' measurableSet_Ioc).mpr
    have hT : ∀ᵐ t : ℝ, t ≠ 2 * Real.pi := by simp [ae_iff]
    filter_upwards [hT,
      physicalDrivenVector_ae_hasDerivAt_of_intervalIntegrable hLip hγ hW r (intervalIntegrable_boundaryL2 r),
      physicalDrivenVector_ae_hasDerivAt_of_intervalIntegrable hLip hγ hW g (intervalIntegrable_boundaryL2 g)]
      with t hT hr hg ht
    have hi : t ∈ Ioo 0 (2 * Real.pi) := ⟨ht.1, lt_of_le_of_ne ht.2 hT⟩
    have hf : physicalDrivenVector W (r : ℝ → ℂ) =ᶠ[𝓝 t] physicalDrivenVector W (g : ℝ → ℂ) :=
      Filter.Eventually.mono (Ioo_mem_nhds hi.1 hi.2) fun s hs => hd (Ioo_subset_Icc_self hs)
    have h := ((hr hi).congr_of_eventuallyEq hf.symm).unique (hg hi)
    rw [hd (Ioo_subset_Icc_self hi), add_right_inj] at h
    have h0 := congrArg (fun x : Ell2 => x 0) h
    simp only [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, basisVec_coord, if_true, mul_one] at h0
    exact mul_left_cancel₀ (by simp ) h0
  exact ⟨b, hb, hr ▸ (localConformalVekuaForwardLoad_normalized coords (E : ℂ) b hbhalf).symm⟩

/-- A nonzero boundary cut rules out the conormal kernel. Use the same
forced transport as for general inputs, with the ordinary load now zero. -/
theorem localConformalVekuaConormal_eq_zero_imp_of_cutC_ne_zero
    (E : ℝ) (hE : 0 ≤ E) (b : L2Z) (hbn : IsNonpositiveFourierSupport b)
    (hker : NF (E : ℂ) b = 0)
    {W : ℝ → Ell2 →L[ℂ] Ell2} (hW : IsTransport (physicalCircleTrace F) E W)
    (hcut : cutC (W (2 * Real.pi)) (basisVec 0) ≠ 0) : b = 0 := by
  have hb1 := localConformalVekuaConormal_kernel_raw_H1 coords.one_lt_radius F coords.smooth (E : ℂ) b hker
  have hbhalf :=
    (isSobolevSeq_one_fromL2_half_iff b).1 hb1
  let g := localConformalVekuaForwardLoad coords (E : ℂ) b hbhalf
  have hg : g = 0 := by
    apply boundaryFourier.injective
    apply sobolevSmoothing_injective (1 / 2 : ℝ) (by norm_num)
    simpa only [map_zero] using
      (localConformalVekuaForwardLoad_normalized coords (E : ℂ) b hbhalf).trans hker
  have hga :=
    (ae_restrict_iff' measurableSet_Ioc).mp (hg.symm ▸ Lp.coeFn_zero ℂ 2 (volume.restrict (Ioc 0 (2 * Real.pi))))
  have hi {t : ℝ} (ht : t ∈ Icc 0 (2 * Real.pi)) :
      (∫ s in (0 : ℝ)..t, g s • ContinuousLinearMap.adjoint (W s) (basisVec 0)) = 0 := by
    apply intervalIntegral.integral_zero_ae
    filter_upwards [hga] with s hs hmem
    rw [uIoc_of_le ht.1] at hmem
    simp [hs ⟨hmem.1, hmem.2.trans ht.2⟩]
  obtain ⟨L, hL⟩ := exists_periodic_C1_density_lipschitz (physicalCircleTrace F)
    (contDiff_physicalCircleTrace_of_neighborhood coords.one_lt_radius F
      (coords.smooth.of_le (WithTop.coe_le_coe.mpr le_top))) (physicalCircleTrace_periodic F)
  have hO : observationAdj W (g : ℝ → ℂ) = 0 := hi ⟨Real.two_pi_pos.le, le_rfl⟩
  have hobs := localConformalVekuaForward_observationAdj_eq_cut coords E hE b hbn hbhalf hL hW
  change observationAdj W (g : ℝ → ℂ) = _ at hobs
  rw [hO, eq_comm, smul_eq_zero, mul_eq_zero] at hobs
  have h0 : hardyFourierTrace (normalizedHardyAverage b) 0 = 0 := by
    grind [Complex.I_ne_zero]
  have hy {t : ℝ} (ht : t ∈ Icc 0 (2 * Real.pi)) : YF E b t = 0 := by
    rw [localConformalVekuaForward_transport_eq coords E hE b hbn hbhalf hL hW ht,
      localConformalVekuaTransportVector_origin coords E b, h0]
    change W t ((0 / (Real.sqrt 2 : ℂ)) • basisVec 0) + physicalDrivenVector W (g : ℝ → ℂ) t = 0
    simp [physicalDrivenVector, hi ht]
  have ha : IsSobolevSeq 1 (normalizedHardyAverage b) := isSobolevSeq_smul _ hb1
  have hs := (sq_tsum_norm_le (s := 0) (by norm_num) (by simpa using ha)).1
  have hzero : EqOn (hardyFourierTrace (normalizedHardyAverage b)) 0 (Icc 0 (2 * Real.pi)) :=
    fun t ht => vekuaTowerVector_eq_zero_imp
      (contDiff_physicalCircleTrace_of_neighborhood coords.one_lt_radius F
        (coords.smooth.of_le (by simp))) (continuous_hardyFourierTrace hs) t (hy ht)
  apply fromL2_injective (1 / 2 : ℝ)
  funext n
  have hn : normalizedHardyAverage b n = 0 := by
    rw [← fourierCoeffOn_hardyFourierTrace hs, fourierCoeffOn_congr_Icc hzero]
    simp [fourierCoeffOn_eq_integral]
  have hscale := Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.2 Real.two_pi_pos).ne'
  simpa [fromL2] using (mul_eq_zero.mp hn).resolve_left (inv_ne_zero hscale)

/-- Reference-energy injectivity on the original full nonpositive space,
obtained from a genuine nonzero cut, without a nonresonance premise. -/
theorem localConformalVekuaConormal_injective_on_nonpositive_of_cutC_ne_zero
    (E : ℝ) (hE : 0 ≤ E) {W : ℝ → Ell2 →L[ℂ] Ell2}
    (hW : IsTransport (physicalCircleTrace F) E W)
    (hcut : cutC (W (2 * Real.pi)) (basisVec 0) ≠ 0) :
    InjOn (NF (E : ℂ))
      {b : L2Z | IsNonpositiveFourierSupport b} := by
  intro b hb' d hd' hbd
  have hn : IsNonpositiveFourierSupport (b - d) := by
    intro n hn
    simp [hb' n hn, hd' n hn]
  have hzero : NF (E : ℂ) (b - d) = 0 := by
    rw [map_sub, hbd, sub_self]
  exact sub_eq_zero.mp
    (localConformalVekuaConormal_eq_zero_imp_of_cutC_ne_zero coords E hE (b - d) hn hzero hW hcut)

end PhysicalCoordinates

end PolyaNeumann

end
