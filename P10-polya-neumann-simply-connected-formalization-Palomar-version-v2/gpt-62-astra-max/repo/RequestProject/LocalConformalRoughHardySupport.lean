module

public import RequestProject.CircleAnalysisNotation

public import RequestProject.DiskCoordinates

public import RequestProject.PhysicalMomentHardyCriterion
public import RequestProject.PhysicalDrivenHardyRegularity
public import RequestProject.BoundaryFourierMultiplier
public import RequestProject.LocalConformalArcReparam
public import RequestProject.ObservationDual
public import RequestProject.PhysicalHardyWeights
public import RequestProject.PlanarNotation

/-!
# Actual Hardy support from L² physical moments

The density is only an actual L² function on the angular interval. Its first
weighted primitive is genuinely absolutely continuous, has an L² derivative,
and has zero endpoints by the zeroth physical moment. Integration by parts
transfers every physical moment to its continuous periodic representative.
The existing continuous physical moment criterion applies to that first
primitive, using its own second primitive. No continuity of the original
density, or point evaluation of an H^{1/2} function, is required.

The derivative of the first primitive has strictly negative Fourier support,
including a genuinely zero average. The original density is recovered by
multiplication by i z conjugate(1/F'). The actual boundary Fourier multiplier
identity and its convergent convolution give nonpositive support, retaining
the original density's full zero mode. Variable speed of the conformal circle
is preserved throughout.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open scoped ContDiff

namespace PolyaNeumann

open MeasureTheory Set Metric Filter
open AbsolutelyContinuousOnInterval
open scoped Topology ComplexConjugate

theorem rough_memLp_continuous_mul {a H : ℝ → ℂ}
    (ha : Continuous a) (hH : MemLp H 2 angleMeasure) :
    MemLp (fun θ => a θ * H θ) 2 angleMeasure := by
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn
    ha.continuousOn
  apply hH.of_le_mul (c := C) (ha.aestronglyMeasurable.restrict.mul hH.aestronglyMeasurable)
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with θ hθ
  simpa using (mul_le_mul_of_nonneg_right (hC θ ⟨hθ.1.le, hθ.2⟩) (norm_nonneg _))

section

variable (γ : ℝ → ℂ) (F : ℂ → ℂ) (Φ : SmoothDiskMap) (hb : Bornology.IsBounded Φ.domain)
    (hL : IsLipschitzDomain Φ.domain) (hhol : DifferentiableOn ℂ Φ.map unitDisk)
    (hnz : ∀ z ∈ closedDisk, fderiv ℝ Φ.map z 1 ≠ 0) (e : OpenPartialHomeomorph ℂ ℂ)
    (he : (e : ℂ → ℂ) = Φ.map) (hsource : closedDisk ⊆ e.source)
    (hes : ContDiffOn ℝ ∞ e.symm e.target) (H : ℝ → ℂ) (hγ : ContDiff ℝ 1 γ) (θ : ℝ)
    (hH : MemLp H 2 angleMeasure) (hmom0 : (∫ₚ θ, conj (deriv γ θ) * H θ) = 0)
    (hmom : ∀ m : ℕ, (∫ₚ θ, (conj (deriv γ θ) * H θ) * (conj (γ θ) - conj (γ 0)) ^ m) = 0)
    (m : ℕ)

include hH hγ in
/-- The true weighted derivative density is in L². -/
theorem physicalMomentDensity_memLp :
    MemLp (fun θ => conj (deriv γ θ) * H θ) 2
      angleMeasure :=
  rough_memLp_continuous_mul
    (Complex.continuous_conj.comp hγ.continuous_deriv_one) hH

private theorem rough_memLp_intervalIntegrable {f : ℝ → ℂ}
    (hf : MemLp f 2 angleMeasure) :
    IntervalIntegrable f volume 0 anglePeriod :=
  (intervalIntegrable_iff_integrableOn_Ioc_of_le Real.two_pi_pos.le).mpr
    (hf.integrable (by norm_num))

include hH hγ in
/-- The first physical primitive is actual AC, rather than an assumed trace. -/
theorem physicalMomentPrimitive_absolutelyContinuous :
    AbsolutelyContinuousOnInterval (physicalMomentPrimitive γ H) 0 anglePeriod := absolutelyContinuousOnInterval_intervalIntegral_banach
    (rough_memLp_intervalIntegrable (physicalMomentDensity_memLp γ H hγ hH))
    (by simp)

include hH hγ in
/-- The genuine almost-everywhere first derivative, without a continuous load. -/
theorem physicalMomentPrimitive_ae_hasDerivAt :
    ∀ᵐ θ, θ ∈ angleInterior →
      HasDerivAt (physicalMomentPrimitive γ H) (conj (deriv γ θ) * H θ) θ :=
  ae_hasDerivAt_intervalIntegral_banach Real.two_pi_pos.le
    (rough_memLp_intervalIntegrable (physicalMomentDensity_memLp γ H hγ hH))

include H γ θ in
/-- Periodization of the actual continuous first primitive, with no density
value at the chosen boundary origin. -/
def physicalMomentPeriodicPrimitive : ℂ :=
  AddCircle.liftIco anglePeriod 0 (physicalMomentPrimitive γ H)
    (θ : ParamCircle)

theorem physicalMomentPeriodicPrimitive_periodic :
    Function.Periodic (physicalMomentPeriodicPrimitive γ H) anglePeriod := by
  simp [physicalMomentPeriodicPrimitive]

include hmom0 in
theorem physicalMomentPeriodicPrimitive_eqOn :
    EqOn (physicalMomentPeriodicPrimitive γ H) (physicalMomentPrimitive γ H)
      angleInterval := by
  intro θ hθ
  by_cases hθL : θ = anglePeriod
  · subst θ
    have hlift : AddCircle.liftIco anglePeriod 0 (physicalMomentPrimitive γ H)
        (0 : ParamCircle) = physicalMomentPrimitive γ H 0 :=
      AddCircle.liftIco_zero_coe_apply ⟨le_rfl, Real.two_pi_pos⟩
    unfold physicalMomentPeriodicPrimitive
    rw [AddCircle.coe_period, hlift, physicalMomentPrimitive_zero,
      physicalMomentPrimitive_endpoint γ H hmom0]
  · exact AddCircle.liftIco_zero_coe_apply (by grind)

include hH hmom0 hγ in
theorem physicalMomentPeriodicPrimitive_continuous :
    Continuous (physicalMomentPeriodicPrimitive γ H) := by
  have hc : ContinuousOn (physicalMomentPrimitive γ H) angleInterval := by
    simpa only [uIcc_of_le Real.two_pi_pos.le] using
      (physicalMomentPrimitive_absolutelyContinuous γ H hγ hH).continuousOn
  exact (AddCircle.liftIco_zero_continuous
    (by rw [physicalMomentPrimitive_zero, physicalMomentPrimitive_endpoint γ H hmom0])
    hc).comp (AddCircle.continuous_mk' _)

include hH hmom hγ in
/-- AC integration by parts transfers the original (m+1)-st moment to the
m-th moment of the first primitive. The original density remains only L². -/
theorem physicalMomentPrimitive_moments_of_memLp :
    (∫ₚ θ,
      (conj (deriv γ θ) * physicalMomentPrimitive γ H θ) *
        (conj (γ θ) - conj (γ 0)) ^ m) = 0 := by
  let a  := fun θ => conj (deriv γ θ)
  let z  := fun θ => conj (γ θ) - conj (γ 0)
  let K := physicalMomentPrimitive γ H
  let ν  := fun θ => a θ * H θ
  let c : ℂ := (m + 1 : ℕ)
  have ha  := Complex.continuous_conj.comp hγ.continuous_deriv_one
  have hγconj := Complex.conjCLE.contDiff.comp hγ
  have hz : ContDiff ℝ 1 z := by
    exact hγconj.sub (contDiff_const (c := conj (γ 0)))
  have dz (θ : ℝ) := ((hγ.differentiable_one θ).hasDerivAt.star).sub_const (conj (γ 0))
  have dv (θ : ℝ) : HasDerivAt (fun s => z s ^ (m + 1))
      (c * z θ ^ m * a θ) θ := by
    exact (dz θ).pow (m + 1)
  have hKAC  :=
    physicalMomentPrimitive_absolutelyContinuous γ H hγ hH
  have hKC : ContinuousOn K angleInterval := by
    simpa only [uIcc_of_le Real.two_pi_pos.le] using hKAC.continuousOn
  have hνI : IntegrableOn ν angleInterval := by
    rw [integrableOn_Icc_iff_integrableOn_Ioc]
    exact (physicalMomentDensity_memLp γ H hγ hH).integrable
      (by norm_num)
  have hfirst : IntegrableOn (fun θ => ν θ * z θ ^ (m + 1)) angleInterval :=
    hνI.mul_continuousOn (hz.continuous.pow (m + 1)).continuousOn isCompact_Icc
  have hsecond : IntegrableOn (fun θ => (a θ * K θ) * z θ ^ m)
      angleInterval :=
    ((ha.continuousOn.mul hKC).mul (hz.continuous.pow m).continuousOn).integrableOn_Icc
  
  have hprodD : ∀ᵐ θ, θ ∈ angleInterior →
      HasDerivAt (fun θ => K θ * z θ ^ (m + 1))
        (ν θ * z θ ^ (m + 1) + c * ((a θ * K θ) * z θ ^ m)) θ := by
    filter_upwards [physicalMomentPrimitive_ae_hasDerivAt γ H hγ hH] with θ hθ hmem
    convert (hθ hmem).mul (dv θ) using 1
    ring
  
  have hFTC := eq_add_intervalIntegral_of_ac_ae_hasDerivAt Real.two_pi_pos.le
    (by
      exact hKAC.smul (driven_c1_absolutelyContinuous (hz.pow (m + 1)))) (hfirst.add (hsecond.const_mul c)) hprodD anglePeriod ⟨Real.two_pi_pos.le, le_rfl⟩
  have hK0 : K 0 = 0 := physicalMomentPrimitive_zero γ H
  have hKL : K anglePeriod = 0 := physicalMomentPrimitive_endpoint γ H
    (by simpa only [pow_zero, mul_one] using hmom 0)
  rw [hK0, hKL, zero_mul, zero_mul, zero_add] at hFTC
  simp at hFTC
  
  
  
  
  rw [intervalIntegral.integral_add (IntegrableOn.intervalIntegrable
    (by simpa only [uIcc_of_le Real.two_pi_pos.le] using hfirst)) ((IntegrableOn.intervalIntegrable (by simpa only [uIcc_of_le Real.two_pi_pos.le] using hsecond)).const_mul c),
    intervalIntegral.integral_const_mul, (hmom (m + 1)), zero_add] at hFTC
  
  apply (mul_eq_zero.mp hFTC.symm).resolve_left
  dsimp [c]
  intro hc
  have hre := congrArg Complex.re hc
  norm_num at hre
  linarith

include hH hmom hγ in
theorem physicalMomentPeriodicPrimitive_moments_of_memLp :
    (∫ₚ θ,
      (conj (deriv γ θ) * physicalMomentPeriodicPrimitive γ H θ) *
        (conj (γ θ) - conj (γ 0)) ^ m) = 0 := by
  have heq := physicalMomentPeriodicPrimitive_eqOn γ H
    (by simpa only [pow_zero, mul_one] using hmom 0)
  rw [show (∫ₚ θ,
      (conj (deriv γ θ) * physicalMomentPeriodicPrimitive γ H θ) *
        (conj (γ θ) - conj (γ 0)) ^ m) =
      (∫ₚ θ,
      (conj (deriv γ θ) * physicalMomentPrimitive γ H θ) *
        (conj (γ θ) - conj (γ 0)) ^ m) from by
    apply intervalIntegral.integral_congr
    intro θ hθ
    rw [uIcc_of_le Real.two_pi_pos.le] at hθ
    simp [heq hθ]]
  exact physicalMomentPrimitive_moments_of_memLp γ H hγ hH hmom m

/-- The existing continuous criterion is applied to the actual first
primitive; the original rough density has not been made continuous. -/
theorem localConformal_physicalMomentPeriodicPrimitive_nonpositive {Ω : Set ℂ}
    (hb : Bornology.IsBounded Ω) (hΩ : IsLipschitzDomain Ω) (Φ : SmoothDiskMap)
    (hhol : DifferentiableOn ℂ Φ.map unitDisk) (hinj : InjOn Φ.map closedDisk)
    (hnz : ∀ z ∈ closedDisk, fderiv ℝ Φ.map z 1 ≠ 0) (himage : Φ.domain = Ω) (H : ℝ → ℂ)
    (hH : MemLp H 2 angleMeasure)
    (hmom : ∀ m : ℕ, (∫ₚ θ,
      (conj (deriv Φ.boundary θ) * H θ) *
        (conj (Φ.boundary θ) - conj (Φ.boundary 0)) ^ m) = 0) :
    IsNonpositiveFourierSupport (angleCoeff
      (physicalMomentPeriodicPrimitive Φ.boundary H)) := by
  have hγ  :=
    Φ.boundaryC1
  exact localConformal_physicalMoments_nonpositive hb hΩ Φ hhol hinj hnz himage
    (physicalMomentPeriodicPrimitive Φ.boundary H)
    (physicalMomentPeriodicPrimitive_continuous _ H hγ hH
      (by simpa only [pow_zero, mul_one] using hmom 0))
    (physicalMomentPeriodicPrimitive_periodic _ H)
    (physicalMomentPeriodicPrimitive_moments_of_memLp _ H hγ hH hmom)

include hH hmom0 hγ in
/-- The a.e. derivative has strictly negative support, with zero frequency
proved by the endpoint identity rather than discarded. -/
theorem physicalMomentDensity_strictNegative_of_primitive_support
    (hK : IsNonpositiveFourierSupport (angleCoeff
      (physicalMomentPeriodicPrimitive γ H))) :
    IsStrictNegativeFourierSupport (angleCoeff
      (fun θ => conj (deriv γ θ) * H θ)) := by
  
  intro n hn
  rw [fourierCoeffOn_of_ac_ae_hasDerivAt
    (physicalMomentPrimitive_absolutelyContinuous γ H hγ hH)
    (physicalMomentDensity_memLp γ H hγ hH)
    (physicalMomentPrimitive_ae_hasDerivAt γ H hγ hH) (by
      rw [physicalMomentPrimitive_zero, physicalMomentPrimitive_endpoint γ H hmom0]) n]
  by_cases hn0 : n = 0
  · simp [*]
  · rw [← fourierCoeffOn_congr_Icc (physicalMomentPeriodicPrimitive_eqOn γ H hmom0) n,
      hK n (by omega), mul_zero]

private theorem rough_fourierCoeffOn_circle_mul (f : ℝ → ℂ) (n : ℤ) :
    angleCoeff (fun θ => unitCirclePt θ * f θ) n =
      angleCoeff f (n - 1) := by
  rw [fourierCoeffOn_eq_integral, fourierCoeffOn_eq_integral]
  simp only [sub_zero, Complex.real_smul, smul_eq_mul]
  congr 1
  apply intervalIntegral.integral_congr
  intro θ _
  
  have hrough :
      fourier  1 (θ : AddCircle (anglePeriod - 0)) =
        unitCirclePt θ := by
    rw [fourier_coe_apply, circleMap_zero]
    norm_num [Real.pi_ne_zero]
    field_simp [Real.pi_ne_zero]
  have hcalc :
      fourier  (-n) (θ : AddCircle (anglePeriod - 0)) *
          (unitCirclePt θ * f θ) =
        fourier  (-(n - 1)) (θ : AddCircle (anglePeriod - 0)) * f θ := by
    rw [← hrough]
    calc
      _ =
          (fourier  (-n) (θ : AddCircle (anglePeriod - 0)) *
            fourier  1 (θ : AddCircle (anglePeriod - 0))) * f θ := by ring
      _ = fourier  (-n + 1) (θ : AddCircle (anglePeriod - 0)) * f θ := by
        rw [fourier_add]
      _ = _ := by
        rw [show -n + 1 = -(n - 1) by omega]
  exact hcalc

private theorem rough_c1_fourier_summable {f : ℝ → ℂ}
    (hf : ContDiff ℝ 1 f) (hp : Function.Periodic f anglePeriod) :
    Summable (angleCoeff f) := by
  have hreg := isSobolevSeq_one_fourierCoeffOn_of_ac_ae_hasDerivAt
    (driven_c1_absolutelyContinuous hf)
    (memLp_angle_of_continuousOn hf.continuous_deriv_one.continuousOn)
    (Eventually.of_forall fun θ _ => (hf.differentiable_one θ).hasDerivAt)
    (by simpa only [zero_add] using (hp 0).symm)
  exact Summable.of_norm ((sq_tsum_norm_le (s := 0) (by norm_num)
    (by simpa only [zero_add] using hreg)).1)

include F θ in
/-- The actual reciprocal coordinate coefficient used to recover the rough
density from its weighted derivative. -/
def physicalMomentRecoveryCoefficient : ℂ :=
  Complex.I * (unitCirclePt θ * conj (physicalCircleTrace (physicalMomentQuotient F 0) θ))

theorem physicalMomentRecoveryCoefficient_periodic :
    Function.Periodic (physicalMomentRecoveryCoefficient F) anglePeriod := by
  intro θ
  unfold physicalMomentRecoveryCoefficient
  rw [(periodic_circleMap 0 1) θ, (physicalCircleTrace_periodic (physicalMomentQuotient F 0)) θ]

include hnz in
theorem physicalMomentRecoveryCoefficient_contDiff :
    ContDiff ℝ 1 (physicalMomentRecoveryCoefficient Φ.map) := by
  have hq := physicalMomentQuotient_circle_contDiff Φ hnz 0
  have hqconj := Complex.conjCLE.contDiff.comp hq
  exact contDiff_const.mul ((contDiff_circleMap 0 1).mul hqconj)

include hnz in
/-- The actual continuous circle coefficient, descended from its equal endpoints. -/
def physicalMomentRecoveryCircle :
    C(ParamCircle, ℂ) :=
  ⟨AddCircle.liftIoc anglePeriod 0 (physicalMomentRecoveryCoefficient Φ.map),
    AddCircle.liftIoc_zero_continuous
      (by simpa only [zero_add] using (physicalMomentRecoveryCoefficient_periodic Φ.map 0).symm)
      (physicalMomentRecoveryCoefficient_contDiff Φ hnz).continuous.continuousOn⟩

theorem physicalMomentRecoveryCircle_apply {θ : ℝ} (hθ : θ ∈ angleIoc) :
    physicalMomentRecoveryCircle Φ hnz (θ : ParamCircle) =
      physicalMomentRecoveryCoefficient Φ.map θ := by
  change AddCircle.liftIoc anglePeriod 0 (physicalMomentRecoveryCoefficient Φ.map)
    (θ : ParamCircle) = physicalMomentRecoveryCoefficient Φ.map θ
  exact AddCircle.liftIoc_zero_coe_apply hθ

theorem physicalMomentRecoveryCircle_summable :
    Summable (fourierCoeff (physicalMomentRecoveryCircle Φ hnz)) := by
  have heq : fourierCoeff (physicalMomentRecoveryCircle Φ hnz) =
      angleCoeff (physicalMomentRecoveryCoefficient Φ.map) := by
    funext n
    simp [physicalMomentRecoveryCircle, fourierCoeff_liftIoc_eq]
  rw [heq]
  exact rough_c1_fourier_summable (physicalMomentRecoveryCoefficient_contDiff Φ hnz)
    (physicalMomentRecoveryCoefficient_periodic Φ.map)

include hhol in
/-- The recovery multiplier has no Fourier frequencies above one. This
comes from the genuine holomorphic reciprocal differential, not an assumed
Hardy multiplier property. -/
theorem physicalMomentRecoveryCircle_coeff_eq_zero_of_one_lt
    {n : ℤ} (hn : 1 < n) :
    fourierCoeff (physicalMomentRecoveryCircle Φ hnz) n = 0 := by
  have hq : DiffContOnCl ℂ (physicalMomentQuotient Φ.map 0) unitDisk := by
    apply DiffContOnCl.mk_ball (physicalMomentQuotient_holomorphic Φ.map hhol hnz 0)
    intro z hz
    exact (physicalMomentQuotient_contDiffAt_closedDisk Φ hnz 0 hz).continuousAt.continuousWithinAt
  simp only [physicalMomentRecoveryCircle, ContinuousMap.coe_mk, fourierCoeff_liftIoc_eq,
    zero_add]
  change angleCoeff
    (fun θ => Complex.I * (unitCirclePt θ * conj
      (physicalCircleTrace (physicalMomentQuotient Φ.map 0) θ))) n = 0
  rw [fourierCoeffOn.const_mul, rough_fourierCoeffOn_circle_mul, physicalWeights_fourierCoeffOn_conj,
    physicalCircleTrace_fourierCoeffOn_eq_zero_of_neg (physicalMomentQuotient Φ.map 0) hq
      (by omega), map_zero, mul_zero]

include hhol hnz in
/-- Exact pointwise recovery from the true angular derivative, valid even
for an arbitrary measurable representative of the original density. -/
theorem physicalMomentRecoveryCoefficient_mul_density :
    physicalMomentRecoveryCoefficient Φ.map θ * (conj (deriv Φ.boundary θ) * H θ) =
      H θ := by
  let z := unitCirclePt θ
  let D := fderiv ℝ Φ.map z 1
  have hD  := hnz z (circleMap_mem_closedBall 0 (by norm_num) θ)
  have hz : z * conj z = 1 := by
    rw [Complex.mul_conj]
    have hnorm : ‖z‖ = 1 := by simp [z, norm_circleMap_zero]
    simp [Complex.normSq_eq_norm_sq, hnorm]
  rw [physicalMomentRecoveryCoefficient, localConformal_circleTrace_deriv Φ hhol]
  change (Complex.I * (z * conj (1 / D))) * (conj (D * (z * Complex.I)) * H θ) = H θ
  simp only [map_div₀, map_one, map_mul, Complex.conj_I]
  have hcD : conj D ≠ 0 := by
    simpa only [starRingEnd_apply] using (star_ne_zero.mpr hD)
  calc
    _ = ((Complex.I * -Complex.I) * (z * conj z) * (conj D / conj D)) * H θ := by ring
    _ = _ := by simp [*]

private theorem rough_seqConv_upper_one_strictNegative {a h : ℤ → ℂ}
    (ha : ∀ n : ℤ, 1 < n → a n = 0) (hh : IsStrictNegativeFourierSupport h)
    {n : ℤ} (hn : 0 < n) : seqConv a h n = 0 := by
  
  calc
    _ = ∑' _ : ℤ, (0 : ℂ) := by
      apply tsum_congr
      intro k
      by_cases hk : 1 < k
      · simp [*]
      · rw [hh (n - k) (by omega), mul_zero]
    _ = 0 := tsum_zero

/-- Genuine L² physical moment criterion for the original density. The
all-input multiplication is the actual boundary Fourier CLM identity. -/
theorem localConformal_physicalMoments_nonpositive_of_memLp {Ω : Set ℂ}
    (hb : Bornology.IsBounded Ω) (hΩ : IsLipschitzDomain Ω) (Φ : SmoothDiskMap)
    (hhol : DifferentiableOn ℂ Φ.map unitDisk) (hinj : InjOn Φ.map closedDisk)
    (hnz : ∀ z ∈ closedDisk, fderiv ℝ Φ.map z 1 ≠ 0) (himage : Φ.domain = Ω) (H : ℝ → ℂ)
    (hH : MemLp H 2 angleMeasure)
    (hmom : ∀ m : ℕ, (∫ₚ θ,
      (conj (deriv Φ.boundary θ) * H θ) *
        (conj (Φ.boundary θ) - conj (Φ.boundary 0)) ^ m) = 0) :
    IsNonpositiveFourierSupport (angleCoeff H) := by
  have hγ  :=
    Φ.boundaryC1
  have hK := localConformal_physicalMomentPeriodicPrimitive_nonpositive
    hb hΩ Φ hhol hinj hnz himage H hH hmom
  have hνsupport := physicalMomentDensity_strictNegative_of_primitive_support
    Φ.boundary H hγ hH
    (by simpa only [pow_zero, mul_one] using hmom 0) hK
  let ν  := fun θ => conj (deriv Φ.boundary θ) * H θ
  have hν  :=
    physicalMomentDensity_memLp _ H hγ hH
  let v  := hν.toLp ν
  let A := physicalMomentRecoveryCircle Φ hnz
  have hrecover : boundaryContinuousMultiplier A v = hH.toLp H := by
    apply Lp.ext
    filter_upwards [boundaryContinuousMultiplier_ae A v, hν.coeFn_toLp, hH.coeFn_toLp,
      ae_restrict_mem measurableSet_Ioc] with θ hmul hv hHθ hθ
    rw [hmul, hv, hHθ, physicalMomentRecoveryCircle_apply Φ hnz hθ]
    exact physicalMomentRecoveryCoefficient_mul_density Φ hhol hnz H θ
  have hνBF : IsStrictNegativeFourierSupport (boundaryFourier v) := by
    intro n hn
    rw [boundaryFourier_apply, fourierCoeffOn_congr_ae Real.two_pi_pos hν.coeFn_toLp,
      hνsupport n hn, mul_zero]
  have hsA  := physicalMomentRecoveryCircle_summable Φ hnz
  have hBF : IsNonpositiveFourierSupport (boundaryFourier (hH.toLp H)) := by
    intro n hn
    rw [← hrecover, boundaryFourier_continuousMultiplier A hsA]
    exact rough_seqConv_upper_one_strictNegative
      (fun k hk => physicalMomentRecoveryCircle_coeff_eq_zero_of_one_lt Φ hhol hnz hk)
      hνBF hn
  intro n hn
  have hnBF := hBF n hn
  rw [boundaryFourier_apply, fourierCoeffOn_congr_ae Real.two_pi_pos hH.coeFn_toLp] at hnBF
  have hs : fourierScale ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr Real.two_pi_pos).ne'
  exact (mul_eq_zero.mp hnBF).resolve_left hs

include hH hL hb he hes hhol hsource in
/-- Full supplied-coordinate version of the rough physical moment
criterion. Closed injectivity and the boundary reciprocal are derived from
the actual smooth inverse. The original L² density need not be periodic as
a pointwise representative. -/
theorem localConformal_physicalMoments_nonpositive_of_memLp_of_smoothInverse
    (hmom : ∀ m : ℕ, (∫ₚ θ,
      (conj (deriv Φ.boundary θ) * H θ) *
        (conj (Φ.boundary θ) - conj (Φ.boundary 0)) ^ m) = 0) :
    IsNonpositiveFourierSupport (angleCoeff H) := by
  have hinj : InjOn Φ.map closedDisk := by
    rw [← he]
    exact e.injOn.mono hsource
  have hnz := SmoothDiskMap.closedDifferential_ne_zero
    Φ e he hsource hes
  exact localConformal_physicalMoments_nonpositive_of_memLp
    hb hL Φ hhol hinj hnz rfl H hH hmom

end

end PolyaNeumann

end
