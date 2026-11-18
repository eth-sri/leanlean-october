module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Topology.Algebra.Order.Field
public import HypoellipticAleksandrov.Parabolic.ScalarClassical
public import PDEFoundation.Sobolev.OneDimensional.SmoothTransport
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import HypoellipticAleksandrov.KineticAleksandrov.Interval.KillingComparison
import HypoellipticAleksandrov.KineticAleksandrov.SectionTwo.UniquenessMeasure
import Mathlib.Topology.Order.Compact
public import HypoellipticAleksandrov.KineticAleksandrov.Decay.SmoothTestOrder
public import HypoellipticAleksandrov.KineticAleksandrov.Interval.FourierKernels

@[expose] public noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Interval
open MeasureTheory Set Filter Topology HypoellipticAleksandrov HypoellipticAleksandrov.Parabolic HypoellipticAleksandrov.KineticAleksandrov.SectionTwo HypoellipticAleksandrov.KineticAleksandrov.Decay
open scoped MatrixOrder

/-- The source error function, using the oriented integral also for negative arguments. -/
def intervalErf (x : ℝ) : ℝ :=
  (2 / Real.sqrt Real.pi) * ∫ t in 0..x, Real.exp (-t ^ 2)

/-- The half-line heat barrier; derivative statements require positive ellipticity and time. -/
def intervalHeat (lam θ x : ℝ) : ℝ :=
  intervalErf (x / (2 * Real.sqrt (lam * θ)))

/-- The derivative of the literal error-function integral. -/
theorem hasDerivAt_intervalErf (x : ℝ) :
    HasDerivAt intervalErf ((2 / Real.sqrt Real.pi) * Real.exp (-x ^ 2)) x := by
  have hc : Continuous (fun t => Real.exp (-t ^ 2)) := by fun_prop
  exact (intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable 0 x)
    hc.stronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt).const_mul _

/-- The error function vanishes at the origin. -/
@[simp] theorem intervalErf_zero : intervalErf 0 = 0 := by
  simp [intervalErf, intervalIntegral.integral_same]

/-- The error function is smooth, with the source C-infinity order. -/
theorem contDiff_intervalErf : ContDiff ℝ (⊤ : ℕ∞) intervalErf := by
  apply contDiff_infty_iff_deriv.2
  refine ⟨fun x => (hasDerivAt_intervalErf x).differentiableAt, ?_⟩
  have heq : deriv intervalErf =
      fun x => (2 / Real.sqrt Real.pi) * Real.exp (-x ^ 2) := by
    funext x
    exact (hasDerivAt_intervalErf x).deriv
  rw [heq]
  fun_prop

/-- Strict increase of the literal error function. -/
theorem strictMono_intervalErf : StrictMono intervalErf := by
  apply strictMono_of_deriv_pos
  intro x
  rw [(hasDerivAt_intervalErf x).deriv]
  exact mul_pos (div_pos (by norm_num) (Real.sqrt_pos.2 Real.pi_pos)) (Real.exp_pos _)

/-- Nonnegativity of the error function on the nonnegative half-line. -/
theorem intervalErf_nonneg {x : ℝ} (hx : 0 ≤ x) : 0 ≤ intervalErf x := by
  simpa using strictMono_intervalErf.monotone hx

/-- Every finite nonnegative argument leaves a strictly positive Gaussian tail. -/
theorem intervalErf_lt_one {x : ℝ} (hx : 0 ≤ x) : intervalErf x < 1 := by
  have hi : Integrable (fun t => Real.exp (-t ^ 2)) := by
    simpa using integrable_exp_neg_mul_sq (by norm_num : (0:ℝ) < 1)
  have : NeZero (volume.restrict (Ioi x) : Measure ℝ) := ⟨by
    intro h
    have he := congrArg (fun ν : Measure ℝ => ν univ) h
    simp at he⟩
  have htail : 0 < ∫ t in Ioi x, Real.exp (-t ^ 2) :=
    integral_exp_pos hi.integrableOn
  have hsplit := intervalIntegral.integral_Ioi_sub_Ioi
    (hi.integrableOn (s := Ioi 0)) hx
  have hfull : (∫ t in Ioi 0, Real.exp (-t ^ 2)) = Real.sqrt Real.pi / 2 := by
    simpa using integral_gaussian_Ioi 1
  rw [hfull] at hsplit
  have hlt : (∫ t in (0:ℝ)..x, Real.exp (-t ^ 2)) < Real.sqrt Real.pi / 2 := by
    linarith only [hsplit, htail]
  have hk : 0 < 2 / Real.sqrt Real.pi := div_pos (by norm_num)
    (Real.sqrt_pos.2 Real.pi_pos)
  have hnorm : (2 / Real.sqrt Real.pi) * (Real.sqrt Real.pi / 2) = 1 := by
    field_simp
  simpa only [intervalErf, hnorm] using (mul_lt_mul_of_pos_left hlt hk)

/-- Gaussian normalization gives the error-function limit at positive infinity. -/
theorem tendsto_intervalErf_atTop :
    Filter.Tendsto intervalErf Filter.atTop (nhds (1 : ℝ)) := by
  have hi : Integrable (fun t => Real.exp (-t ^ 2)) := by
    simpa using integrable_exp_neg_mul_sq (by norm_num : (0:ℝ) < 1)
  have ht := (intervalIntegral_tendsto_integral_Ioi 0 hi.integrableOn
    Filter.tendsto_id).const_mul (2 / Real.sqrt Real.pi)
  have hfull : (∫ t in Ioi 0, Real.exp (-t ^ 2)) = Real.sqrt Real.pi / 2 := by
    simpa using integral_gaussian_Ioi 1
  rw [hfull] at ht
  have hnorm : (2 / Real.sqrt Real.pi) * (Real.sqrt Real.pi / 2) = 1 := by
    field_simp
  rwa [hnorm] at ht

/-- Spatial derivative of the heat barrier. -/
theorem hasDerivAt_intervalHeat_space (lam θ : ℝ)
    (x : ℝ) :
    HasDerivAt (intervalHeat lam θ)
      ((2 / Real.sqrt Real.pi) * Real.exp (-(x / (2 * Real.sqrt (lam * θ))) ^ 2) /
        (2 * Real.sqrt (lam * θ))) x := by
  unfold intervalHeat
  simpa only [Function.comp_def, id_eq, mul_one_div] using
    (hasDerivAt_intervalErf (x / (2 * Real.sqrt (lam * θ)))).comp x
      ((hasDerivAt_id x).div_const (2 * Real.sqrt (lam * θ)))

/-- Spatial derivative written as an equality of functions. -/
theorem deriv_intervalHeat_space (lam θ : ℝ) :
    deriv (intervalHeat lam θ) = fun x =>
      (2 / Real.sqrt Real.pi) * Real.exp (-(x / (2 * Real.sqrt (lam * θ))) ^ 2) /
        (2 * Real.sqrt (lam * θ)) := by
  funext x
  exact (hasDerivAt_intervalHeat_space lam θ x).deriv

/-- Second spatial derivative of the barrier. -/
theorem deriv2_intervalHeat_space {lam θ : ℝ} (hlam : 0 < lam) (hθ : 0 < θ)
    (x : ℝ) :
    deriv (deriv (intervalHeat lam θ)) x =
      -(2 * x * (2 / Real.sqrt Real.pi) *
        Real.exp (-(x / (2 * Real.sqrt (lam * θ))) ^ 2)) /
        (2 * Real.sqrt (lam * θ)) ^ 3 := by
  rw [deriv_intervalHeat_space lam θ]
  have h := ((((hasDerivAt_id x).div_const (2 * Real.sqrt (lam * θ))).pow 2).neg.exp
    |>.const_mul (2 / Real.sqrt Real.pi)).div_const (2 * Real.sqrt (lam * θ))
  dsimp only [id_eq, Pi.neg_apply, Pi.pow_apply] at h
  rw [h.deriv]
  simp only [Nat.reduceSub, pow_one]
  field_simp [(Real.sqrt_pos.2 (mul_pos hlam hθ)).ne']
  ring

/-- Time derivative of the barrier. -/
theorem hasDerivAt_intervalHeat_time {lam θ : ℝ} (hlam : 0 < lam) (hθ : 0 < θ)
    (x : ℝ) :
    HasDerivAt (fun t => intervalHeat lam t x)
      (-(2 * x * lam * (2 / Real.sqrt Real.pi) *
        Real.exp (-(x / (2 * Real.sqrt (lam * θ))) ^ 2)) /
        (2 * Real.sqrt (lam * θ)) ^ 3) θ := by
  have hd : 2 * Real.sqrt (lam * θ) ≠ 0 := mul_ne_zero (by norm_num) ((Real.sqrt_pos.2 (mul_pos hlam hθ)).ne')
  have h := (hasDerivAt_intervalErf (x / (2 * Real.sqrt (lam * θ)))).comp θ
    ((hasDerivAt_const θ x).div ((((hasDerivAt_id θ).const_mul lam).sqrt (mul_pos hlam hθ).ne').const_mul 2) hd)
  dsimp only [id_eq, Function.comp_def, Pi.div_apply] at h
  convert h using 1
  · rfl
  · field_simp
    ring

/-- The barrier solves the half-line heat equation with diffusivity `lam`. -/
theorem intervalHeat_heatEquation {lam θ : ℝ} (hlam : 0 < lam) (hθ : 0 < θ)
    (x : ℝ) :
    deriv (fun t => intervalHeat lam t x) θ =
      lam * deriv (deriv (intervalHeat lam θ)) x := by
  rw [(hasDerivAt_intervalHeat_time hlam hθ x).deriv,
    deriv2_intervalHeat_space hlam hθ]
  ring

/-- Concavity on the nonnegative half-line. -/
theorem intervalHeat_secondDerivative_nonpos {lam θ x : ℝ}
    (hlam : 0 < lam) (hθ : 0 < θ) (hx : 0 ≤ x) :
    deriv (deriv (intervalHeat lam θ)) x ≤ 0 := by
  rw [deriv2_intervalHeat_space hlam hθ]
  apply div_nonpos_of_nonpos_of_nonneg
  · exact neg_nonpos.2 (by positivity)
  · positivity

/-- The source supersolution inequality for any coefficient at least `lam`. -/
theorem intervalHeat_supersolution {lam θ x A : ℝ}
    (hlam : 0 < lam) (hθ : 0 < θ) (hx : 0 ≤ x) (hA : lam ≤ A) :
    deriv (fun t => intervalHeat lam t x) θ =
        lam * deriv (deriv (intervalHeat lam θ)) x ∧
      deriv (deriv (intervalHeat lam θ)) x ≤ 0 ∧
      0 ≤ deriv (fun t => intervalHeat lam t x) θ -
        A * deriv (deriv (intervalHeat lam θ)) x := by
  have heq := intervalHeat_heatEquation hlam hθ x
  have hneg := intervalHeat_secondDerivative_nonpos hlam hθ hx
  refine ⟨heq, hneg, ?_⟩
  rw [heq, ← sub_mul]
  exact mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.2 hA) hneg


/-- The heat barrier is jointly smooth wherever its time parameter is positive. -/
theorem contDiffAt_intervalHeat {lam : ℝ} (hlam : 0 < lam)
    (p : ℝ × ℝ) (hp : 0 < p.1) :
    ContDiffAt ℝ (⊤ : ℕ∞) (fun q : ℝ × ℝ => intervalHeat lam q.1 q.2) p := by
  have hs : ContDiffAt ℝ (⊤ : ℕ∞) (fun q => Real.sqrt (lam * q.1)) p :=
    (contDiffAt_const.mul contDiffAt_fst).sqrt (mul_pos hlam hp).ne'
  exact contDiff_intervalErf.contDiffAt.comp p
    (contDiffAt_snd.div (contDiffAt_const.mul hs)
      (mul_ne_zero (by norm_num) (Real.sqrt_pos.2 (mul_pos hlam hp)).ne'))

/-- Positive distance has terminal heat-barrier limit one as time decreases to zero. -/
theorem tendsto_intervalHeat_time_zero {lam x : ℝ} (hlam : 0 < lam) (hx : 0 < x) :
    Tendsto (fun θ => intervalHeat lam θ x) (nhdsWithin 0 (Ioi 0)) (𝓝 1) := by
  have hs : Tendsto (fun θ : ℝ => 2 * Real.sqrt (lam * θ))
      (nhdsWithin 0 (Ioi 0)) (𝓝 0) := by
    have ht : Tendsto (fun θ : ℝ => θ) (nhdsWithin 0 (Ioi 0)) (𝓝 0) :=
      tendsto_id.mono_left nhdsWithin_le_nhds
    have hm : Tendsto (fun θ : ℝ => lam * θ) (nhdsWithin 0 (Ioi 0)) (𝓝 0) := by
      simpa using (tendsto_const_nhds.mul ht)
    simpa using
      (tendsto_const_nhds.mul (Real.continuous_sqrt.continuousAt.tendsto.comp hm) : Tendsto (fun θ : ℝ => 2 * Real.sqrt (lam * θ))
        (nhdsWithin 0 (Ioi 0)) (𝓝 (2 * Real.sqrt 0)))
  have hsg : Tendsto (fun θ : ℝ => 2 * Real.sqrt (lam * θ))
      (nhdsWithin 0 (Ioi 0)) (nhdsWithin 0 (Ioi 0)) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨hs, ?_⟩
    filter_upwards [self_mem_nhdsWithin] with θ hθ
    exact mul_pos (by norm_num) (Real.sqrt_pos.2 (mul_pos hlam hθ))
  have he := tendsto_intervalErf_atTop.comp (hsg.inv_tendsto_nhdsGT_zero.const_mul_atTop hx)
  simpa only [intervalHeat, div_eq_mul_inv, Pi.inv_apply, Function.comp_def] using he

/-- Fixed positive-time heat barriers are increasing with spatial distance. -/
theorem intervalHeat_mono_distance {lam θ : ℝ} (hlam : 0 < lam) (hθ : 0 < θ) :
    Monotone (intervalHeat lam θ) := by
  intro x y hxy
  exact strictMono_intervalErf.monotone
    ((div_le_div_iff_of_pos_right (mul_pos (by norm_num)
      (Real.sqrt_pos.2 (mul_pos hlam hθ)))).mpr hxy)


/-- The unique native coordinate direction agrees with scalar differentiation,
including Mathlib's total derivative convention at nonsmooth points. -/
theorem scalar_deriv_eq_native (f : PDE.Vec 1 → ℝ) (v : PDE.Vec 1) :
    deriv (fun t => f (fun _ => t)) (v 0) = (fderiv ℝ f v) (PDE.basisVec 0) := by
  have he := congrArg (fun L => L 1) (PDE.scalarToVecOneContinuousLinearEquiv.comp_right_fderiv (f := f) (x := v 0))
  have h1 : (PDE.scalarToVecOneContinuousLinearEquiv : ℝ →L[ℝ] PDE.Vec 1) 1 =
      PDE.basisVec 0 := PDE.scalarToVecOneContinuousLinearEquiv_one
  have hv : PDE.scalarToVecOneContinuousLinearEquiv (v 0) = v := by
    ext i
    have hi := Fin.eq_zero i
    subst i
    rfl
  rw [ContinuousLinearMap.comp_apply, h1, hv] at he
  exact he


/-- The one-dimensional native Hessian is the iterated scalar derivative. -/
theorem scalarSpatialHessian_one (u : TimeVelocity 1 → ℝ) (p : TimeVelocity 1) :
    scalarSpatialHessian u p 0 0 =
      deriv (deriv (fun v => u (p.1, fun _ => v))) (p.2 0) := by
  let g : PDE.Vec 1 → PDE.Vec 1 :=
    fun v => scalarSpatialGradient u (p.1, v)
  have hg : (fun t => g (fun _ => t) 0) =
      deriv (fun v => u (p.1, fun _ => v)) := by
    funext t
    exact (scalar_deriv_eq_native (fun v => u (p.1, v)) (fun _ => t)).symm
  have he := scalar_deriv_eq_native (fun v => g v 0) p.2
  rw [hg] at he
  have hi : (fderiv ℝ (fun v => g v 0) p.2) (PDE.basisVec 0) =
      (fderiv ℝ g p.2 (PDE.basisVec 0)) 0 := by
    let E := PDE.scalarToVecOneContinuousLinearEquiv.symm
    change (fderiv ℝ (E ∘ g) p.2) (PDE.basisVec 0) = _
    rw [E.comp_fderiv]
    rfl
  exact hi.symm.trans he.symm

/-- Affine pullback of the scalar heat barrier has its expected first derivative. -/
theorem deriv_intervalHeat_affine (lam θ s e : ℝ) :
    deriv (fun y => intervalHeat lam θ (s * (y - e))) =
      fun y => s * deriv (intervalHeat lam θ) (s * (y - e)) := by
  funext y
  have h := (hasDerivAt_intervalHeat_space lam θ (s * (y - e))).comp y
    (((hasDerivAt_id y).sub_const e).const_mul s)
  dsimp only [Function.comp_def, id_eq] at h
  rw [h.deriv, (hasDerivAt_intervalHeat_space lam θ (s * (y - e))).deriv]
  ring

/-- Affine pullback of the scalar heat barrier has its expected second derivative. -/
theorem deriv2_intervalHeat_affine {lam θ : ℝ} (_hlam : 0 < lam) (_hθ : 0 < θ)
    (s e y : ℝ) :
    deriv (deriv (fun z => intervalHeat lam θ (s * (z - e)))) y =
      s ^ 2 * deriv (deriv (intervalHeat lam θ)) (s * (y - e)) := by
  have hd : DifferentiableAt ℝ (deriv (intervalHeat lam θ)) (s * (y - e)) := by
    rw [deriv_intervalHeat_space]
    fun_prop
  have h := (hd.hasDerivAt.comp y (((hasDerivAt_id y).sub_const e).const_mul s)).const_mul s
  dsimp only [Function.comp_def, id_eq] at h
  rw [deriv_intervalHeat_affine, h.deriv]
  ring

/-- The regularized terminal barrier based at an endpoint, with inward orientation `s`. -/
def endpointHeat (lam τ ε s e : ℝ) (p : TimeVelocity 1) : ℝ :=
  intervalHeat lam (τ - p.1 + ε) (s * (p.2 0 - e))

/-- Joint regularity of the regularized endpoint barrier. -/
theorem contDiffAt_endpointHeat {lam τ ε s e : ℝ} (hlam : 0 < lam)
    (p : TimeVelocity 1) (hp : 0 < τ - p.1 + ε) :
    ContDiffAt ℝ (⊤ : ℕ∞) (endpointHeat lam τ ε s e) p := by
  have hg : ContDiffAt ℝ (⊤ : ℕ∞)
      (fun q => (τ - q.1 + ε, s * (q.2 0 - e))) p :=
    ((contDiffAt_const.sub contDiffAt_fst).add contDiffAt_const).prodMk
      (contDiffAt_const.mul
        (((contDiff_apply ℝ ℝ 0).contDiffAt.comp p contDiffAt_snd).sub
          contDiffAt_const))
  exact (contDiffAt_intervalHeat hlam (τ - p.1 + ε, s * (p.2 0 - e)) hp).comp p
    (f := fun q => (τ - q.1 + ε, s * (q.2 0 - e))) hg

/-- The time derivative reverses the forward half-line time. -/
theorem scalarTimeDerivative_endpointHeat {lam τ ε s e : ℝ} (hlam : 0 < lam)
    (p : TimeVelocity 1) (hp : 0 < τ - p.1 + ε) :
    scalarTimeDerivative (endpointHeat lam τ ε s e) p =
      -deriv (fun θ => intervalHeat lam θ (s * (p.2 0 - e))) (τ - p.1 + ε) := by
  have h := (hasDerivAt_intervalHeat_time hlam hp (s * (p.2 0 - e))).comp p.1
    (((hasDerivAt_const p.1 τ).sub (hasDerivAt_id p.1)).add_const ε)
  dsimp only [Function.comp_def, id_eq, Pi.sub_apply] at h
  change deriv (fun r => intervalHeat lam (τ - r + ε) (s * (p.2 0 - e))) p.1 = _
  rw [h.deriv, (hasDerivAt_intervalHeat_time hlam hp (s * (p.2 0 - e))).deriv]
  ring

/-- The native Hessian is the scalar heat Hessian when the orientation has square one. -/
theorem scalarSpatialHessian_endpointHeat {lam τ ε s e : ℝ} (hlam : 0 < lam)
    (hs : s ^ 2 = 1) (p : TimeVelocity 1) (hp : 0 < τ - p.1 + ε) :
    scalarSpatialHessian (endpointHeat lam τ ε s e) p 0 0 =
      deriv (deriv (intervalHeat lam (τ - p.1 + ε))) (s * (p.2 0 - e)) := by
  rw [scalarSpatialHessian_one]
  change deriv (deriv (fun v => intervalHeat lam (τ - p.1 + ε) (s * (v - e))))
    (p.2 0) = _
  rw [deriv2_intervalHeat_affine hlam hp, hs, one_mul]

/-- The endpoint barrier is a backward supersolution under the source ellipticity bound. -/
theorem endpointHeat_operator_nonpos {lam τ ε s e : ℝ} (hlam : 0 < lam)
    (hs : s ^ 2 = 1) (B : CoefficientField 1) (p : TimeVelocity 1)
    (hp : 0 < τ - p.1 + ε) (hx : 0 ≤ s * (p.2 0 - e))
    (hB : lam ≤ B p.1 p.2 0 0) :
    scalarParabolicOperator B 0 (endpointHeat lam τ ε s e) p ≤ 0 := by
  rw [scalarParabolicOperator_apply, scalarTimeDerivative_endpointHeat hlam p hp]
  simp [matrixContraction, Fin.sum_univ_one, PDE.vecDot]
  rw [scalarSpatialHessian_endpointHeat hlam hs p hp]
  have h := (intervalHeat_supersolution hlam hp hx hB).2.2
  linarith


/-- The scalar diagonal inherits the source lower ellipticity bound. -/
theorem interval_coefficient_lower {lam Lam : ℝ} (B : CoefficientField 1)
    (hB : IsSectionTwoCoefficient lam Lam B) (r : ℝ) (v : PDE.Vec 1) :
    lam ≤ B r v 0 0 := by
  simpa [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply_eq, sub_nonneg] using (hB.2.2.2.2.1 r v).diag_nonneg (i := 0)

/-- Coordinates of the closure of an interval satisfy the closed endpoint bounds. -/
theorem interval_coordinate_closure {a c : ℝ} {v : PDE.Vec 1}
    (hv : v ∈ closure (PDE.oneDimensionalAxisBox a c)) : a ≤ v 0 ∧ v 0 ≤ c := by
  have hsub : PDE.oneDimensionalAxisBox a c ⊆ {w : PDE.Vec 1 | a ≤ w 0 ∧ w 0 ≤ c} := by
    intro w hw
    have hh := PDE.mem_oneDimensionalAxisBox_iff.mp hw
    exact ⟨hh.1.le, hh.2.le⟩
  exact closure_minimal hsub ((isClosed_le continuous_const (continuous_apply 0)).inter
    (isClosed_le (continuous_apply 0) continuous_const)) hv

/-- Positive endpoint distance on compact test support provides eventual terminal domination. -/
theorem endpointHeat_terminal_domination {lam s e κ : ℝ} (hlam : 0 < lam)
    (hκ0 : 0 ≤ κ) (hκ : κ < 1) (φ : PDE.Vec 1 → ℝ) (hφc : HasCompactSupport φ)
    (hφ : ∀ v, 0 ≤ φ v ∧ φ v ≤ 1)
    (hpos : ∀ v ∈ tsupport φ, 0 < s * (v 0 - e)) :
    ∀ᶠ ε in nhdsWithin 0 (Ioi 0),
      ∀ v ∈ tsupport φ, κ * φ v ≤ intervalHeat lam ε (s * (v 0 - e)) := by
  by_cases hempty : (tsupport φ).Nonempty
  · have hc : Continuous (fun v : PDE.Vec 1 => s * (v 0 - e)) := by fun_prop
    obtain ⟨v₀, hv₀, hmin⟩ := hφc.exists_isMinOn hempty hc.continuousOn
    have he := (tendsto_intervalHeat_time_zero hlam (hpos v₀ hv₀)).eventually (eventually_gt_nhds hκ)
    filter_upwards [he, self_mem_nhdsWithin] with ε hε hεpos v hv
    calc κ * φ v ≤ κ := by
          exact mul_le_of_le_one_right hκ0 (hφ v).2
      _ ≤ intervalHeat lam ε (s * (v₀ 0 - e)) := hε.le
      _ ≤ intervalHeat lam ε (s * (v 0 - e)) :=
        intervalHeat_mono_distance hlam hεpos (hmin hv)
  · exact Eventually.of_forall fun _ v hv => (hempty ⟨v, hv⟩).elim

/-- Smooth tests on the interval satisfy the endpoint killing estimate.
The endpoint geometry premises are discharged for both endpoints in `Killing`. -/
theorem interval_endpoint_test_bound {a c lam Lam σ τ s e : ℝ}
    (hac : a < c) (hστ : σ < τ) (hlam : 0 < lam) (hs : s ^ 2 = 1)
    (B : CoefficientField 1) (hB : IsSectionTwoCoefficient lam Lam B)
    (hJ : MeasurableSet (PDE.oneDimensionalAxisBox a c))
    (K : MovingFiberKernel (PDE.oneDimensionalAxisBox a c) stationary)
    (hpar : HasParabolicMarginalBundle (PDE.oneDimensionalAxisBox a c) stationary hJ
      (zIndependentCoefficient B) K)
    (hdpos : ∀ v ∈ PDE.oneDimensionalAxisBox a c, 0 < s * (v 0 - e))
    (hdnonneg : ∀ v ∈ closure (PDE.oneDimensionalAxisBox a c), 0 ≤ s * (v 0 - e))
    (v : PDE.Vec 1) (hv : v ∈ movingDomain (PDE.oneDimensionalAxisBox a c) stationary σ)
    (φ : PDE.Vec 1 → ℝ) (hφs : ContDiff ℝ (⊤ : ℕ∞) φ) (hφc : HasCompactSupport φ)
    (hφJ : tsupport φ ⊆ PDE.oneDimensionalAxisBox a c)
    (hφ : ∀ w, 0 ≤ φ w ∧ φ w ≤ 1) :
    (∫ w, φ w ∂P K hJ (scalarQuery σ τ hστ.le v hv)) ≤
      intervalHeat lam (τ - σ) (s * (v 0 - e)) := by
  let μ := P K hJ (scalarQuery σ τ hστ.le v hv)
  obtain ⟨Q, _hfirst, _hid, _hpos, _hsub, _hcomp, hrepr,
    _hmeas, _hend, _hkc, hsolve⟩ := hpar (fun _ _ _ _ => rfl)
  have hscaled : ∀ κ : ℝ, 0 ≤ κ → κ < 1 →
      κ * (∫ w, φ w ∂μ) ≤ intervalHeat lam (τ - σ) (s * (v 0 - e)) := by
    intro κ hκ0 hκ1
    let F : BoundedBorel (PDE.Vec 1) :=
      ⟨fun w => κ * φ w, measurable_const.mul hφs.continuous.measurable,
        ⟨1, zero_le_one, fun w => by
          rw [abs_of_nonneg (mul_nonneg hκ0 (hφ w).1)]
          exact (mul_le_of_le_one_right hκ0 (hφ w).2).trans hκ1.le⟩⟩
    have hFJ : tsupport (fun w => κ * φ w) ⊆ PDE.oneDimensionalAxisBox a c :=
      tsupport_mul_subset_right.trans hφJ
    obtain ⟨V, hV, heval, _hunique⟩ := hsolve τ F
      ⟨contDiff_const.mul hφs, hφc.mul_left, by
        simpa only [movingDomain_stationary] using hFJ⟩
    have hεbound : ∀ᶠ ε in nhdsWithin 0 (Ioi 0),
        V (σ, v) ≤ intervalHeat lam (τ - σ + ε) (s * (v 0 - e)) := by
      filter_upwards [(endpointHeat_terminal_domination hlam hκ0 hκ1 φ hφc hφ (fun w hw => hdpos w (hφJ hw))), self_mem_nhdsWithin] with ε hdomε hε
      have hε0 : 0 < ε := hε
      apply interval_terminal_comparison hac hστ hlam B hB F V
        (endpointHeat lam τ ε s e) hV
      · intro p hp
        exact (contDiffAt_endpointHeat hlam p (by linarith only [hp.1.2, hε0])).continuousAt
          |>.continuousWithinAt
      · intro p hp
        exact (contDiffAt_endpointHeat hlam p (by linarith only [hp.1.2, hε0])).of_le (by simp)
      · intro p hp
        exact endpointHeat_operator_nonpos hlam hs B p (by linarith only [hp.1.2, hε0])
          (hdpos _ hp.2).le (interval_coefficient_lower B hB _ _)
      · intro w hw
        change κ * φ w ≤ intervalHeat lam (τ - τ + ε) (s * (w 0 - e))
        rw [sub_self, zero_add]
        by_cases hwφ : w ∈ tsupport φ
        · exact hdomε w hwφ
        · rw [image_eq_zero_of_notMem_tsupport hwφ, mul_zero]
          exact intervalErf_nonneg (div_nonneg (hdnonneg w hw) (by positivity))
      · intro p hp
        exact intervalErf_nonneg (div_nonneg (hdnonneg _ (frontier_subset_closure hp.2))
          (by positivity))
      · simpa only [movingDomain_stationary] using subset_closure
          (show v ∈ PDE.oneDimensionalAxisBox a c from
            by simpa only [movingDomain_stationary] using hv)
    have hlimit : Tendsto (fun ε => intervalHeat lam (τ - σ + ε) (s * (v 0 - e)))
        (nhdsWithin 0 (Ioi 0)) (𝓝 (intervalHeat lam (τ - σ) (s * (v 0 - e)))) := by
      have ht0 : Tendsto (fun ε : ℝ => ε) (nhdsWithin 0 (Ioi 0)) (𝓝 0) :=
        tendsto_id.mono_left nhdsWithin_le_nhds
      have ht1 : Tendsto (fun ε : ℝ => τ - σ + ε) (nhdsWithin 0 (Ioi 0))
          (𝓝 (τ - σ)) := by simpa using ht0.const_add (τ - σ)
      have ht := ht1.prodMk_nhds (tendsto_const_nhds (x := s * (v 0 - e)))
      exact ((contDiffAt_intervalHeat hlam (τ - σ, s * (v 0 - e)) (sub_pos.mpr hστ)).continuousAt).tendsto.comp
        (f := fun ε : ℝ => (τ - σ + ε, s * (v 0 - e))) ht
    have he := heval σ hστ.le ⟨v, hv⟩
    rw [hrepr] at he
    have hi : (∫ w, φ w ∂μ) =
        ∫ w : EvolutionPosition (PDE.oneDimensionalAxisBox a c) stationary τ, φ w.1
          ∂parabolicMarginalKernel K hJ σ τ hστ.le ⟨v, hv⟩ := by
      exact integral_map measurable_subtype_coe.aemeasurable
        hφs.continuous.measurable.aestronglyMeasurable
    rw [hi, ← integral_const_mul]
    exact he ▸ (ge_of_tendsto hlimit hεbound)
  have ht : Tendsto (fun κ : ℝ => κ * (∫ w, φ w ∂μ)) (nhdsWithin 1 (Iio 1))
      (𝓝 (∫ w, φ w ∂μ)) := by
    have hκ : Tendsto (fun κ : ℝ => κ) (nhdsWithin 1 (Iio 1)) (𝓝 1) :=
      tendsto_id.mono_left nhdsWithin_le_nhds
    simpa using hκ.mul_const (∫ w, φ w ∂μ)
  apply le_of_tendsto ht
  filter_upwards [(eventually_gt_nhds (zero_lt_one : (0 : ℝ) < 1)).filter_mono
    nhdsWithin_le_nhds, self_mem_nhdsWithin] with κ hκ0 hκ1
  exact hscaled κ hκ0.le hκ1


/-- Smooth compact tests bounded by one determine an upper bound for supported mass. -/
theorem mass_le_of_interval_smooth_tests {U : Set (PDE.Vec 1)} (hU : IsOpen U)
    (μ : Measure (PDE.Vec 1)) [IsFiniteMeasure μ] (hμ : μ.restrict U = μ)
    {C : ℝ} (hC : 0 ≤ C)
    (htest : ∀ φ : PDE.Vec 1 → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      tsupport φ ⊆ U → (∀ w, 0 ≤ φ w ∧ φ w ≤ 1) → ∫ w, φ w ∂μ ≤ C) :
    μ.real univ ≤ C := by
  have hbound : μ U ≤ ENNReal.ofReal C := by
    rw [hU.measure_eq_iSup_isCompact μ]
    refine iSup_le fun A => iSup_le fun hAU => iSup_le fun hA => ?_
    obtain ⟨φ, hφ, hφc, hφU, hφr, hφA⟩ := exists_smooth_cutoff hA hU hAU
    have hle : μ.real A ≤ ∫ w, φ w ∂μ := by
      rw [← integral_indicator_one hA.measurableSet]
      apply integral_mono ((integrable_const 1).indicator hA.measurableSet) (hφ.continuous.integrable_of_hasCompactSupport hφc (μ := μ))
      intro w
      by_cases hw : w ∈ A
      · simp only [indicator_of_mem hw, hφA w hw, le_refl]
      · simpa only [indicator_of_notMem hw] using (hφr w).1
    rw [← ENNReal.ofReal_toReal (measure_ne_top μ A)]
    exact ENNReal.ofReal_le_ofReal (hle.trans (htest φ hφ hφc hφU hφr))
  have he : μ univ = μ U := by
    conv_lhs => rw [← hμ]
    rw [Measure.restrict_apply MeasurableSet.univ, univ_inter]
  rw [Measure.real, he]
  exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hbound).trans_eq
    (ENNReal.toReal_ofReal hC)

/-- The endpoint test bound gives the total positive parabolic mass bound. -/
theorem interval_endpoint_mass_bound {a c lam Lam σ τ s e : ℝ}
    (hac : a < c) (hστ : σ < τ) (hlam : 0 < lam) (hs : s ^ 2 = 1)
    (B : CoefficientField 1) (hB : IsSectionTwoCoefficient lam Lam B)
    (hJ : MeasurableSet (PDE.oneDimensionalAxisBox a c))
    (K : MovingFiberKernel (PDE.oneDimensionalAxisBox a c) stationary)
    (hpar : HasParabolicMarginalBundle (PDE.oneDimensionalAxisBox a c) stationary hJ
      (zIndependentCoefficient B) K)
    (hdpos : ∀ w ∈ PDE.oneDimensionalAxisBox a c, 0 < s * (w 0 - e))
    (hdnonneg : ∀ w ∈ closure (PDE.oneDimensionalAxisBox a c), 0 ≤ s * (w 0 - e))
    (v : PDE.Vec 1) (hv : v ∈ movingDomain (PDE.oneDimensionalAxisBox a c) stationary σ) :
    (P K hJ (scalarQuery σ τ hστ.le v hv)).real univ ≤
      intervalHeat lam (τ - σ) (s * (v 0 - e)) := by
  have hvJ : v ∈ PDE.oneDimensionalAxisBox a c := by
    simpa only [movingDomain_stationary] using hv
  apply mass_le_of_interval_smooth_tests
    (isOpen_of_isAdmissibleEvolutionDomain (interval_admissible hac))
    (P K hJ (scalarQuery σ τ hστ.le v hv))
  · apply Measure.restrict_eq_self_of_ae_mem
    rw [ae_iff]
    exact P_compl_eq_zero_stationary K hJ _
  · exact intervalErf_nonneg (div_nonneg (hdpos v hvJ).le (by positivity))
  · intro φ hφs hφc hφJ hφ
    exact interval_endpoint_test_bound hac hστ hlam hs B hB hJ K hpar
      hdpos hdnonneg v hv φ hφs hφc hφJ hφ


private theorem master_mass_eq_marginal_mass {d : ℕ} {Ω : Set (PDE.Vec d)}
    {γ : ℝ → PDE.Vec d} (hΩ : MeasurableSet Ω) (K : MovingFiberKernel Ω γ)
    (σ τ : ℝ) (hστ : σ ≤ τ) (v z : PDE.Vec d) (hv : v ∈ movingDomain Ω γ σ)
    (hfirst : (parabolicMarginalKernel K hΩ σ τ hστ) ⟨v, hv⟩ =
      (K.fiberFirstMarginal hΩ σ τ hστ) (evolutionStateOfPosition Ω γ σ ⟨v, hv⟩ z)) :
    (parabolicMarginalKernel K hΩ σ τ hστ ⟨v, hv⟩) univ =
      K.master (movingQuery σ τ hστ v z hv) univ := by
  have hmap := K.map_fiberFirstMarginal_eq_firstMarginal hΩ σ τ hστ
    (evolutionStateOfPosition Ω γ σ ⟨v, hv⟩ z)
  rw [← hfirst] at hmap
  have hq : evolutionQueryOfState Ω γ σ τ hστ
      (evolutionStateOfPosition Ω γ σ ⟨v, hv⟩ z) = movingQuery σ τ hστ v z hv := rfl
  rw [hq] at hmap
  have h := congrArg (fun μ : Measure (PDE.Vec d) => μ univ) hmap
  rw [Measure.map_apply measurable_subtype_coe MeasurableSet.univ,
    MovingFiberKernel.firstMarginal, ProbabilityTheory.Kernel.fst_apply,
    Measure.map_apply measurable_fst MeasurableSet.univ] at h
  simpa only [preimage_univ] using h


/-- Scalar marginal mass equals the ambient master mass of the same query. -/
theorem interval_parabolic_mass_eq_master {a c : ℝ}
    (hJ : MeasurableSet (PDE.oneDimensionalAxisBox a c))
    (K : MovingFiberKernel (PDE.oneDimensionalAxisBox a c) stationary)
    (B : CoefficientField 1)
    (hp : HasParabolicMarginalBundle (PDE.oneDimensionalAxisBox a c) stationary hJ
      (zIndependentCoefficient B) K)
    (σ τ : ℝ) (hστ : σ ≤ τ) (v z : PDE.Vec 1)
    (hv : v ∈ movingDomain (PDE.oneDimensionalAxisBox a c) stationary σ) :
    P K hJ (scalarQuery σ τ hστ v hv) univ =
      K.master (movingQuery σ τ hστ v z hv) univ := by
  obtain ⟨Q, hfirst, _⟩ := hp (fun _ _ _ _ => rfl)
  unfold P parabolicMarginalAmbientMeasure
  rw [Measure.map_apply measurable_subtype_coe MeasurableSet.univ, preimage_univ]
  exact master_mass_eq_marginal_mass hJ K σ τ hστ v z hv (hfirst σ τ hστ ⟨v, hv⟩ z)

/-- The positive marginal is bounded by the half-line barrier at the nearer endpoint. -/
theorem interval_killing
    (hH : HormanderHypoellipticityStatement)
    (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam m Lb a c : ℝ} (hac : a < c)
    (B : CoefficientField 1) (b : PDE.Vec 1 → PDE.Vec 1)
    (hsetting : SourceSetting lam Lam m Lb (PDE.oneDimensionalAxisBox a c) B b)
    (hJ : MeasurableSet (PDE.oneDimensionalAxisBox a c))
    (S : TerminalOperatorFamily (PDE.oneDimensionalAxisBox a c) stationary)
    (K : MovingFiberKernel (PDE.oneDimensionalAxisBox a c) stationary)
    (hr : RealizesTerminalEvolution (PDE.oneDimensionalAxisBox a c) stationary hJ
      (zIndependentCoefficient B) b S K)
    (σ τ : ℝ) (hστ : σ < τ) (v : PDE.Vec 1)
    (hv : v ∈ movingDomain (PDE.oneDimensionalAxisBox a c) stationary σ) :
    (P K hJ (scalarQuery σ τ hστ.le v hv)).real univ ≤
      intervalErf (min (v 0 - a) (c - v 0) / (2 * Real.sqrt (lam * (τ - σ)))) := by
  have hp := (interval_evolution_clauses hH hLE hac B b hsetting hJ S K hr).2.1
  have hleft := interval_endpoint_mass_bound hac hστ hsetting.1.1
    (s := 1) (e := a) (by norm_num) B hsetting.1 hJ K hp
    (fun w hw => by
      have h := PDE.mem_oneDimensionalAxisBox_iff.mp hw
      simpa [PDE.vecOneCoordinate] using sub_pos.mpr h.1)
    (fun w hw => by
      simpa using sub_nonneg.mpr (interval_coordinate_closure hw).1) v hv
  have hright := interval_endpoint_mass_bound hac hστ hsetting.1.1
    (s := -1) (e := c) (by norm_num) B hsetting.1 hJ K hp
    (fun w hw => by
      have h := PDE.mem_oneDimensionalAxisBox_iff.mp hw
      change 0 < -1 * (w 0 - c)
      have hc : w 0 < c := h.2
      linarith)
    (fun w hw => by
      have h := (interval_coordinate_closure hw).2
      linarith) v hv
  rcases le_total (v 0 - a) (c - v 0) with hl | hr
  · rw [min_eq_left hl]
    simpa [intervalHeat] using hleft
  · rw [min_eq_right hr]
    convert hright using 1
    unfold intervalHeat
    congr 2
    ring

/-- Fourier total variation is bounded by scalar marginal mass on the same kernel. -/
theorem interval_fourier_tv_le_mass {a c : ℝ}
    (hJ : MeasurableSet (PDE.oneDimensionalAxisBox a c))
    (K : MovingFiberKernel (PDE.oneDimensionalAxisBox a c) stationary)
    (B : CoefficientField 1)
    (hp : HasParabolicMarginalBundle (PDE.oneDimensionalAxisBox a c) stationary hJ
      (zIndependentCoefficient B) K)
    (σ τ : ℝ) (hστ : σ ≤ τ) (v z ξ : PDE.Vec 1)
    (hv : v ∈ movingDomain (PDE.oneDimensionalAxisBox a c) stationary σ)
    (ν : ComplexMeasure (PDE.Vec 1))
    (hν : IsFourierProjection K (movingQuery σ τ hστ v z hv) ξ ν) :
    TV ν ≤ (P K hJ (scalarQuery σ τ hστ v hv)).real univ := by
  have h := (Measure.le_iff.mp (fourierProjection_variation_le K _ ξ ν hν))
    univ MeasurableSet.univ
  have hm : K.firstMarginal (movingQuery σ τ hστ v z hv) univ =
      K.master (movingQuery σ τ hστ v z hv) univ := by
    rw [MovingFiberKernel.firstMarginal, ProbabilityTheory.Kernel.fst_apply,
      Measure.map_apply measurable_fst MeasurableSet.univ, preimage_univ]
  rw [hm, ← interval_parabolic_mass_eq_master hJ K B hp σ τ hστ v z hv] at h
  exact ENNReal.toReal_mono (measure_ne_top _ _) h

end HypoellipticAleksandrov.KineticAleksandrov.Interval

