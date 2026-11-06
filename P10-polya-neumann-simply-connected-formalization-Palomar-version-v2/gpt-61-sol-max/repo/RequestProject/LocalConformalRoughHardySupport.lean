module

public import RequestProject.KernelRows
public import RequestProject.LocalConformalRoughGaugeRegularity
public import RequestProject.PhysicalDrivenIntegrable


public import RequestProject.PlanarTypes
public import RequestProject.CirclePeriod

public import RequestProject.PlanarGeometry

public import RequestProject.PhysicalMomentHardyCriterion
public import RequestProject.PhysicalDrivenHardyRegularity
public import RequestProject.BoundaryFourierMultiplier
public import RequestProject.LocalConformalArcReparam
public import RequestProject.ObservationDual

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

open scoped ContDiff


noncomputable section

namespace PolyaNeumann

open MeasureTheory Set Metric Filter
open AbsolutelyContinuousOnInterval
open scoped ComplexConjugate



section
variable (γ H : ComplexCurve) (hγ : ContDiff ℝ 1 γ) (hH : MemLp H 2 (volume.restrict boundaryHalfOpenInterval))

include γ H hγ hH in
/-- The true weighted derivative density is in L². -/
theorem physicalMomentDensity_memLp :
    MemLp (fun θ => conj (deriv γ θ) * H θ) 2
      (volume.restrict boundaryHalfOpenInterval) :=
  common_roughGauge_continuous_mul_memLp
    (Complex.continuous_conj.comp hγ.continuous_deriv_one) hH

section
include γ H hγ hH

/-- The first physical primitive is actual AC, rather than an assumed trace. -/
theorem physicalMomentPrimitive_absolutelyContinuous :
    AbsolutelyContinuousOnInterval (physicalMomentPrimitive γ H) 0 circlePeriod := absolutelyContinuousOnInterval_intervalIntegral_banach
    (intervalIntegrable_boundary_of_memLp _ (physicalMomentDensity_memLp γ H hγ hH))
    (by simp_all)

/-- The genuine almost-everywhere first derivative, without a continuous load. -/
theorem physicalMomentPrimitive_ae_hasDerivAt :
    ∀ᵐ θ, θ ∈ Ioo 0 circlePeriod →
      HasDerivAt (physicalMomentPrimitive γ H) (conj (deriv γ θ) * H θ) θ :=
  ae_hasDerivAt_intervalIntegral_banach Real.two_pi_pos.le
    (intervalIntegrable_boundary_of_memLp _ (physicalMomentDensity_memLp γ H hγ hH))

end


/-- Periodization of the actual continuous first primitive, with no density
value at the chosen boundary origin. -/
def physicalMomentPeriodicPrimitive γ H (θ : ℝ)  :=
  AddCircle.liftIco circlePeriod 0 (physicalMomentPrimitive γ H)
    (θ : AddCircle circlePeriod)

theorem physicalMomentPeriodicPrimitive_periodic γ H :
    Function.Periodic (physicalMomentPeriodicPrimitive γ H) circlePeriod := by
  simp_all [physicalMomentPeriodicPrimitive]

theorem physicalMomentPeriodicPrimitive_eqOn γ H
    (hmom0 : (∫ θ in (0 : ℝ)..circlePeriod, conj (deriv γ θ) * H θ) = 0) :
    EqOn (physicalMomentPeriodicPrimitive γ H) (physicalMomentPrimitive γ H)
      boundaryInterval := by
  intro θ hθ
  by_cases hθL : θ = 2 * Real.pi
  · subst θ
    have hlift : AddCircle.liftIco circlePeriod 0 (physicalMomentPrimitive γ H)
        (0 : AddCircle circlePeriod) = physicalMomentPrimitive γ H 0 :=
      AddCircle.liftIco_zero_coe_apply ⟨le_rfl, Real.two_pi_pos⟩
    unfold physicalMomentPeriodicPrimitive
    rw [AddCircle.coe_period, hlift, physicalMomentPrimitive_zero,
      physicalMomentPrimitive_endpoint γ H hmom0]
  · exact AddCircle.liftIco_zero_coe_apply ⟨hθ.1, lt_of_le_of_ne hθ.2 hθL⟩

include γ H hγ hH in
theorem physicalMomentPeriodicPrimitive_continuous
    (hmom0 : (∫ θ in (0 : ℝ)..circlePeriod, conj (deriv γ θ) * H θ) = 0) :
    Continuous (physicalMomentPeriodicPrimitive γ H) := by
  have hc : ContinuousOn (physicalMomentPrimitive γ H) boundaryInterval := by
    simpa  [uIcc_of_le Real.two_pi_pos.le] using
      (physicalMomentPrimitive_absolutelyContinuous γ H hγ hH).continuousOn
  exact (AddCircle.liftIco_zero_continuous
    (by rw [physicalMomentPrimitive_zero, physicalMomentPrimitive_endpoint γ H hmom0])
    hc).comp (AddCircle.continuous_mk' _)

end


section
variable (γ H : ComplexCurve) (hγ : ContDiff ℝ 1 γ) (hH : MemLp H 2 (volume.restrict boundaryHalfOpenInterval)) (hmom : ∀ m : ℕ, (∫ θ in (0 : ℝ)..circlePeriod,
      (conj (deriv γ θ) * H θ) * (conj (γ θ) - conj (γ 0)) ^ m) = 0) (m : ℕ)
include γ H hγ hH hmom m

/-- AC integration by parts transfers the original (m+1)-st moment to the
m-th moment of the first primitive. The original density remains only L². -/
theorem physicalMomentPrimitive_moments_of_memLp :
    (∫ θ in (0 : ℝ)..circlePeriod,
      (conj (deriv γ θ) * physicalMomentPrimitive γ H θ) *
        (conj (γ θ) - conj (γ 0)) ^ m) = 0 := by
  let a  := fun θ => conj (deriv γ θ)
  let z  := fun θ => conj (γ θ) - conj (γ 0)
  let K := physicalMomentPrimitive γ H
  let ν  := fun θ => a θ * H θ
  let c : ℂ := (m + 1 : ℕ)
  have ha  := Complex.continuous_conj.comp hγ.continuous_deriv_one
  have hγconj : ContDiff ℝ 1 (fun θ => conj (γ θ)) := by
    simpa only [Function.comp_def, Complex.conjCLE_apply] using Complex.conjCLE.contDiff.comp hγ
  have hz : ContDiff ℝ 1 z := by
    fun_prop
  have dz (θ : ℝ) : HasDerivAt z (a θ) θ := by
    simpa only [Complex.star_def] using
      ((hγ.differentiable_one θ).hasDerivAt.star).sub_const (conj (γ 0))
  have dv (θ : ℝ) : HasDerivAt (fun s => z s ^ (m + 1))
      (c * z θ ^ m * a θ) θ := by
    exact (dz θ).pow (m + 1)
  have hKAC  :=
    physicalMomentPrimitive_absolutelyContinuous γ H hγ hH
  have hKC : ContinuousOn K boundaryInterval := by
    simpa only [uIcc_of_le Real.two_pi_pos.le] using hKAC.continuousOn
  have hνI : IntegrableOn ν boundaryInterval := by
    rw [integrableOn_Icc_iff_integrableOn_Ioc]
    exact (physicalMomentDensity_memLp γ H hγ hH).integrable
      (by norm_num)
  have hfirst : IntegrableOn (fun θ => ν θ * z θ ^ (m + 1)) boundaryInterval :=
    hνI.mul_continuousOn (hz.continuous.pow (m + 1)).continuousOn isCompact_Icc
  have hsecond : IntegrableOn (fun θ => (a θ * K θ) * z θ ^ m)
      boundaryInterval :=
    ((ha.continuousOn.mul hKC).mul (hz.continuous.pow m).continuousOn).integrableOn_Icc
  have hprodAC : AbsolutelyContinuousOnInterval (fun θ => K θ * z θ ^ (m + 1))
      0 circlePeriod := by
    exact hKAC.smul (common_driven_c1_absolutelyContinuous (hz.pow (m + 1)))
  have hprodD : ∀ᵐ θ, θ ∈ Ioo 0 circlePeriod →
      HasDerivAt (fun θ => K θ * z θ ^ (m + 1))
        (ν θ * z θ ^ (m + 1) + c * ((a θ * K θ) * z θ ^ m)) θ := by
    filter_upwards [physicalMomentPrimitive_ae_hasDerivAt γ H hγ hH] with θ hθ hmem
    convert (hθ hmem).mul (dv θ) using 1
    ring
  have hprodI := hfirst.add (hsecond.const_mul c)
  have hFTC := eq_add_intervalIntegral_of_ac_ae_hasDerivAt Real.two_pi_pos.le
    hprodAC hprodI hprodD circlePeriod ⟨Real.two_pi_pos.le, le_rfl⟩
  have hK0 : K 0 = 0 := physicalMomentPrimitive_zero γ H
  have hKL : K circlePeriod = 0 := physicalMomentPrimitive_endpoint γ H
    (by simpa only [pow_zero, mul_one] using hmom 0)
  rw [hK0, hKL, zero_mul, zero_mul, zero_add] at hFTC
  have hi₁ : IntervalIntegrable (fun θ => ν θ * z θ ^ (m + 1)) volume 0 circlePeriod :=
    IntegrableOn.intervalIntegrable
      (by simpa only [uIcc_of_le Real.two_pi_pos.le] using hfirst)
  have hi₂ : IntervalIntegrable (fun θ => (a θ * K θ) * z θ ^ m) volume 0 circlePeriod :=
    IntegrableOn.intervalIntegrable (by simpa only [uIcc_of_le Real.two_pi_pos.le] using hsecond)
  have hiMoment  :=
    hmom (m + 1)
  change 0 = ∫ θ in (0)..circlePeriod,
    (ν θ * z θ ^ (m + 1) + c * ((a θ * K θ) * z θ ^ m)) at hFTC
  rw [intervalIntegral.integral_add hi₁ (hi₂.const_mul c),
    intervalIntegral.integral_const_mul, hiMoment, zero_add] at hFTC
  have hc : c ≠ 0 := by
    dsimp [c]
    intro hc
    have hre := congrArg Complex.re hc
    norm_num at hre
    linarith
  exact (mul_eq_zero.mp hFTC.symm).resolve_left hc

theorem physicalMomentPeriodicPrimitive_moments_of_memLp :
    (∫ θ in (0 : ℝ)..circlePeriod,
      (conj (deriv γ θ) * physicalMomentPeriodicPrimitive γ H θ) *
        (conj (γ θ) - conj (γ 0)) ^ m) = 0 := by
  have heq := physicalMomentPeriodicPrimitive_eqOn γ H
    (by simpa   using hmom 0)
  rw [show (∫ θ in (0 : ℝ)..circlePeriod,
      (conj (deriv γ θ) * physicalMomentPeriodicPrimitive γ H θ) *
        (conj (γ θ) - conj (γ 0)) ^ m) =
      (∫ θ in (0 : ℝ)..circlePeriod,
      (conj (deriv γ θ) * physicalMomentPrimitive γ H θ) *
        (conj (γ θ) - conj (γ 0)) ^ m) from by
    apply intervalIntegral.integral_congr
    intro θ hθ
    rw [uIcc_of_le Real.two_pi_pos.le] at hθ
    simp only [heq hθ]]
  simp_all [physicalMomentPrimitive_moments_of_memLp]

end


section
variable {Ω } (hb : Bornology.IsBounded Ω) (hΩ : IsLipschitzDomain Ω) {R } (hR : 1 < R) (F ) (hFs : RealSmoothOnBall F R) (hhol : DifferentiableOn ℂ F unitDisk) (hinj : InjOn F closedUnitDisk) (hnz : ∀ z ∈ closedUnitDisk, fderiv ℝ F z 1 ≠ 0) (himage : F '' unitDisk = Ω) (H ) (hH : MemLp H 2 (volume.restrict boundaryHalfOpenInterval)) (hmom : ∀ m : ℕ, (∫ θ in (0 : ℝ)..circlePeriod,
      (conj (deriv (physicalCircleTrace F) θ) * H θ) *
        (conj (physicalCircleTrace F θ) - conj (physicalCircleTrace F 0)) ^ m) = 0)

include Ω hb hΩ R hR F hFs hhol hinj hnz himage H hH hmom in
/-- The existing continuous criterion is applied to the actual first
primitive; the original rough density has not been made continuous. -/
theorem localConformal_physicalMomentPeriodicPrimitive_nonpositive :
    IsNonpositiveFourierSupport (fourierCoeffOn Real.two_pi_pos
      (physicalMomentPeriodicPrimitive (physicalCircleTrace F) H)) := by
  have hγ  :=
    contDiff_physicalCircleTrace_of_neighborhood hR F (hFs.of_le (WithTop.coe_le_coe.mpr le_top))
  exact localConformal_physicalMoments_nonpositive hb hΩ hR F hFs hhol hinj hnz himage
    (physicalMomentPeriodicPrimitive (physicalCircleTrace F) H)
    (physicalMomentPeriodicPrimitive_continuous _ H hγ hH
      (by simpa   using hmom 0))
    (physicalMomentPeriodicPrimitive_periodic _ H)
    (physicalMomentPeriodicPrimitive_moments_of_memLp _ H hγ hH hmom)

/-- The a.e. derivative has strictly negative support, with zero frequency
proved by the endpoint identity rather than discarded. -/
theorem physicalMomentDensity_strictNegative_of_primitive_support γ H
    (hγ : ContDiff ℝ 1 γ)
    (hH : MemLp H 2 (volume.restrict boundaryHalfOpenInterval))
    (hmom0 : (∫ θ in (0 : ℝ)..circlePeriod, conj (deriv γ θ) * H θ) = 0)
    (hK : IsNonpositiveFourierSupport (fourierCoeffOn Real.two_pi_pos
      (physicalMomentPeriodicPrimitive γ H))) :
    IsStrictNegativeFourierSupport (fourierCoeffOn Real.two_pi_pos
      (fun θ => conj (deriv γ θ) * H θ)) := by
  have hp : physicalMomentPrimitive γ H 0 = physicalMomentPrimitive γ H circlePeriod := by
    rw [physicalMomentPrimitive_zero, physicalMomentPrimitive_endpoint γ H hmom0]
  intro n hn
  rw [fourierCoeffOn_of_ac_ae_hasDerivAt
    (physicalMomentPrimitive_absolutelyContinuous γ H hγ hH)
    (physicalMomentDensity_memLp γ H hγ hH)
    (physicalMomentPrimitive_ae_hasDerivAt γ H hγ hH) hp n]
  by_cases hn0 : n = 0
  · subst n
    norm_num
  · rw [← fourierCoeffOn_congr_Icc (physicalMomentPeriodicPrimitive_eqOn γ H hmom0) n,
      hK n (by omega), mul_zero]

private theorem rough_fourierCoeffOn_circle_mul f n :
    fourierCoeffOn Real.two_pi_pos (fun θ => unitCircleMap θ * f θ) n =
      fourierCoeffOn Real.two_pi_pos f (n - 1) := by
  rw [fourierCoeffOn_eq_integral, fourierCoeffOn_eq_integral]
  congr 1
  apply intervalIntegral.integral_congr
  intro θ _
  have hrough :
      fourier (T := 2 * Real.pi - 0) 1 (θ : AddCircle (2 * Real.pi - 0)) =
        unitCircleMap θ := by
    rw [fourier_coe_apply, circleMap_zero]
    norm_num
    field_simp
  have hcalc :
      fourier (T := 2 * Real.pi - 0) (-n) (θ : AddCircle (2 * Real.pi - 0)) *
          (unitCircleMap θ * f θ) =
        fourier (T := 2 * Real.pi - 0) (-(n - 1)) (θ : AddCircle (2 * Real.pi - 0)) * f θ := by
    rw [← hrough]
    calc
      fourier (T := 2 * Real.pi - 0) (-n) θ *
            (fourier (T := 2 * Real.pi - 0) 1 θ * f θ) =
          (fourier (T := 2 * Real.pi - 0) (-n) θ *
            fourier (T := 2 * Real.pi - 0) 1 θ) * f θ := by ring
      _ = fourier (T := 2 * Real.pi - 0) (-n + 1) θ * f θ := by
        rw [fourier_add]
      _ = fourier (T := 2 * Real.pi - 0) (-(n - 1)) θ * f θ := by
        rw [show -n + 1 = -(n - 1) by omega]
  exact hcalc

private theorem rough_c1_fourier_summable {f : ComplexCurve}
    (hf : ContDiff ℝ 1 f) (hp : Function.Periodic f circlePeriod) :
    Summable (fourierCoeffOn Real.two_pi_pos f) := by
  have hreg := isSobolevSeq_one_fourierCoeffOn_of_ac_ae_hasDerivAt
    (common_driven_c1_absolutelyContinuous hf)
    (driven_realization_continuousOn_memLp hf.continuous_deriv_one.continuousOn)
    (Eventually.of_forall fun θ _ => (hf.differentiable_one θ).hasDerivAt)
    (by simpa   using (hp 0).symm)
  exact Summable.of_norm ((sq_tsum_norm_le (s := 0) (by norm_num)
    (by simpa   using hreg)).1)

/-- The actual reciprocal coordinate coefficient used to recover the rough
density from its weighted derivative. -/
def physicalMomentRecoveryCoefficient F θ  :=
  Complex.I * (unitCircleMap θ * conj (physicalCircleTrace (physicalMomentQuotient F 0) θ))

theorem physicalMomentRecoveryCoefficient_periodic F :
    Function.Periodic (physicalMomentRecoveryCoefficient F) circlePeriod := by
  intro θ
  unfold physicalMomentRecoveryCoefficient
  rw [(periodic_circleMap 0 1) θ, (physicalCircleTrace_periodic (physicalMomentQuotient F 0)) θ]

theorem physicalMomentRecoveryCoefficient_contDiff  (hR : 1 < R) F
    (hFs : RealSmoothOnBall F R)
    (hnz : ∀ z ∈ closedUnitDisk, fderiv ℝ F z 1 ≠ 0) :
    ContDiff ℝ 1 (physicalMomentRecoveryCoefficient F) := (ContDiff.mul contDiff_const (ContDiff.mul (contDiff_circleMap 0 1) (ContDiff.comp (ContinuousLinearEquiv.contDiff Complex.conjCLE) (physicalMomentQuotient_circle_contDiff hR F hFs hnz 0))))

/-- The actual continuous circle coefficient, descended from its equal endpoints. -/
def physicalMomentRecoveryCircle {R : ℝ} (hR : 1 < R) (F : PlaneMap)
    (hFs : RealSmoothOnBall F R)
    (hnz : ∀ z ∈ closedUnitDisk, fderiv ℝ F z 1 ≠ 0) :
    C(AddCircle circlePeriod, ℂ) :=
  ⟨AddCircle.liftIoc circlePeriod 0 (physicalMomentRecoveryCoefficient F),
    AddCircle.liftIoc_zero_continuous
      (by simpa   using (physicalMomentRecoveryCoefficient_periodic F 0).symm)
      (physicalMomentRecoveryCoefficient_contDiff hR F hFs hnz).continuous.continuousOn⟩

theorem physicalMomentRecoveryCircle_apply  hR F
    (hFs : RealSmoothOnBall F R)
    hnz
     (hθ : θ ∈ boundaryHalfOpenInterval) :
    physicalMomentRecoveryCircle hR F hFs hnz (θ : AddCircle circlePeriod) =
      physicalMomentRecoveryCoefficient F θ := by
  change AddCircle.liftIoc circlePeriod 0 (physicalMomentRecoveryCoefficient F)
    θ = physicalMomentRecoveryCoefficient F θ
  exact AddCircle.liftIoc_zero_coe_apply hθ

theorem physicalMomentRecoveryCircle_summable  hR F
    (hFs : RealSmoothOnBall F R)
    hnz :
    Summable (fourierCoeff (physicalMomentRecoveryCircle hR F hFs hnz)) := by
  have heq : fourierCoeff (physicalMomentRecoveryCircle hR F hFs hnz) =
      fourierCoeffOn Real.two_pi_pos (physicalMomentRecoveryCoefficient F) := by
    funext n
    simp  [physicalMomentRecoveryCircle, fourierCoeff_liftIoc_eq]
  grind only [rough_c1_fourier_summable, physicalMomentRecoveryCoefficient_contDiff, physicalMomentRecoveryCoefficient_periodic]

/-- The recovery multiplier has no Fourier frequencies above one. This
comes from the genuine holomorphic reciprocal differential, not an assumed
Hardy multiplier property. -/
theorem physicalMomentRecoveryCircle_coeff_eq_zero_of_one_lt
     hR F
    (hFs : RealSmoothOnBall F R)
    (hhol : DifferentiableOn ℂ F unitDisk)
    hnz
     (hn : 1 < n) :
    fourierCoeff (physicalMomentRecoveryCircle hR F hFs hnz) n = 0 := by
  have hq : DiffContOnCl ℂ (physicalMomentQuotient F 0) unitDisk := by
    apply DiffContOnCl.mk_ball (physicalMomentQuotient_holomorphic F hhol hnz 0)
    intro z hz
    exact (physicalMomentQuotient_contDiffAt_closedDisk hR F hFs hnz 0 hz).continuousAt.continuousWithinAt
  simp  [physicalMomentRecoveryCircle, fourierCoeff_liftIoc_eq]
  change fourierCoeffOn Real.two_pi_pos
    (fun θ => Complex.I * (unitCircleMap θ * conj
      (physicalCircleTrace (physicalMomentQuotient F 0) θ))) n = 0
  rw [fourierCoeffOn.const_mul, rough_fourierCoeffOn_circle_mul, fourierCoeffOn_conj,
    physicalCircleTrace_fourierCoeffOn_eq_zero_of_neg (physicalMomentQuotient F 0) hq
      (by omega), map_zero, mul_zero]

/-- Exact pointwise recovery from the true angular derivative, valid even
for an arbitrary measurable representative of the original density. -/
theorem physicalMomentRecoveryCoefficient_mul_density  (hR : 1 < R) F
    (hFs : RealSmoothOnBall F R)
    (hhol : DifferentiableOn ℂ F unitDisk)
    (hnz : ∀ z ∈ closedUnitDisk, fderiv ℝ F z 1 ≠ 0)
    (H : ComplexCurve) θ :
    physicalMomentRecoveryCoefficient F θ * (conj (deriv (physicalCircleTrace F) θ) * H θ) =
      H θ := by
  let z := unitCircleMap θ
  let D := fderiv ℝ F z 1
  have hD : D ≠ 0 := hnz z (circleMap_mem_closedBall 0 (by norm_num) θ)
  have hz : z * conj z = 1 := by
    rw [Complex.mul_conj]
    have hnorm : ‖z‖ = 1 := by simp [z]
    rw [Complex.normSq_eq_norm_sq, hnorm]
    norm_num
  rw [physicalMomentRecoveryCoefficient, localConformal_circleTrace_deriv hR F hFs hhol]
  change (Complex.I * (z * conj (1 / D))) * (conj (D * (z * Complex.I)) * H θ) = H θ
  simp  
  have hcD : conj D ≠ 0 := by
    simp_all
  calc
    _ = ((Complex.I * -Complex.I) * (z * conj z) * (conj D / conj D)) * H θ := by ring
    _ = H θ := by rw [hz, div_self hcD]; simp

private theorem rough_seqConv_upper_one_strictNegative 
    (ha : ∀ n : ℤ, 1 < n → a n = 0) (hh : IsStrictNegativeFourierSupport h)
     (hn : 0 < n) : seqConv a h n = 0 := by
  calc
    _ = ∑' _ : ℤ, (0 : ℂ) := by
      apply tsum_congr
      intro k
      by_cases hk : 1 < k
      · rw [ha k hk, zero_mul]
      · rw [hh (n - k) (by omega), mul_zero]
    _ = 0 := tsum_zero

include Ω hb hΩ R hR F hFs hhol hinj hnz himage H hH hmom in
/-- Genuine L² physical moment criterion for the original density. The
all-input multiplication is the actual boundary Fourier CLM identity. -/
theorem localConformal_physicalMoments_nonpositive_of_memLp :
    IsNonpositiveFourierSupport (fourierCoeffOn Real.two_pi_pos H) := by
  have hγ  :=
    contDiff_physicalCircleTrace_of_neighborhood hR F (hFs.of_le (WithTop.coe_le_coe.mpr le_top))
  have hK := localConformal_physicalMomentPeriodicPrimitive_nonpositive
    hb hΩ hR F hFs hhol hinj hnz himage H hH hmom
  have hνsupport := physicalMomentDensity_strictNegative_of_primitive_support
    (physicalCircleTrace F) H hγ hH
    (by simpa only [pow_zero, mul_one] using hmom 0) hK
  let ν  := fun θ => conj (deriv (physicalCircleTrace F) θ) * H θ
  have hν  :=
    physicalMomentDensity_memLp _ H hγ hH
  let v  := hν.toLp ν
  let A := physicalMomentRecoveryCircle hR F hFs hnz
  have hrecover : boundaryContinuousMultiplier A v = hH.toLp H := by
    apply Lp.ext
    filter_upwards [boundaryContinuousMultiplier_ae A v, hν.coeFn_toLp, hH.coeFn_toLp,
      ae_restrict_mem measurableSet_Ioc] with θ hmul hv hHθ hθ
    rw [hmul, hv, hHθ, physicalMomentRecoveryCircle_apply hR F hFs hnz hθ]
    exact physicalMomentRecoveryCoefficient_mul_density hR F hFs hhol hnz H θ
  have hνBF : IsStrictNegativeFourierSupport (boundaryFourier v) := by
    intro n hn
    rw [boundaryFourier_apply, fourierCoeffOn_congr_ae Real.two_pi_pos hν.coeFn_toLp,
      hνsupport n hn, mul_zero]
  have hsA  := physicalMomentRecoveryCircle_summable hR F hFs hnz
  have hBF : IsNonpositiveFourierSupport (boundaryFourier (hH.toLp H)) := by
    intro n hn
    rw [← hrecover, boundaryFourier_continuousMultiplier A hsA]
    exact rough_seqConv_upper_one_strictNegative
      (fun k hk => physicalMomentRecoveryCircle_coeff_eq_zero_of_one_lt hR F hFs hhol hnz hk)
      hνBF hn
  intro n hn
  have hnBF := hBF n hn
  rw [boundaryFourier_apply, fourierCoeffOn_congr_ae Real.two_pi_pos hH.coeFn_toLp] at hnBF
  have hs : (Real.sqrt circlePeriod : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr Real.two_pi_pos).ne'
  simp_all

end


section
variable {R } (hR : 1 < R) (F : PlaneMap) (hFs : RealSmoothOnBall F R)
include R hR F hFs

/-- Closed-disk differential nonvanishing follows from the actual local
inverse and its genuine real smoothness. No extra boundary regularity or
nonvanishing assumption is imposed on the supplied coordinate tuple. -/
theorem localConformal_closedDifferential_ne_zero_of_smoothInverse
    (e : OpenPartialHomeomorph ℂ ℂ) (he : (e : PlaneMap) = F)
    (hsource : closedUnitDisk ⊆ e.source)
    (hes : RealSmoothOn e.symm e.target) :
    ∀ z ∈ closedUnitDisk, fderiv ℝ F z 1 ≠ 0 := by
  intro z hz
  have hzs := hsource hz
  have hzt : F z ∈ e.target := by
    rw [← he]
    exact e.mapsTo hzs
  have hdF := ((hFs.contDiffAt (isOpen_ball.mem_nhds (closedBall_subset_ball hR hz))).differentiableAt (by simp)).hasFDerivAt
  have hdG := ((hes.contDiffAt (e.open_target.mem_nhds hzt)).differentiableAt
    (by simp)).hasFDerivAt
  have hcomp := hdG.comp z hdF
  have hid : HasFDerivAt id
      ((fderiv ℝ e.symm (F z)).comp (fderiv ℝ F z)) z := by
    apply hcomp.congr_of_eventuallyEq
    filter_upwards [e.open_source.mem_nhds hzs] with x hx
    measurability
  have hlin := hid.unique (hasFDerivAt_id z)
  have hval := congrArg (fun A : ℂ →L[ℝ] ℂ => A 1) hlin
  change fderiv ℝ e.symm (F z) (fderiv ℝ F z 1) = 1 at hval
  measurability

/-- Full supplied-coordinate version of the rough physical moment
criterion. Closed injectivity and the boundary reciprocal are derived from
the actual smooth inverse. The original L² density need not be periodic as
a pointwise representative. -/
theorem localConformal_physicalMoments_nonpositive_of_memLp_of_smoothInverse
    (hb : Bornology.IsBounded (F '' unitDisk))
    (hL : IsLipschitzDomain (F '' unitDisk))
    (hhol : DifferentiableOn ℂ F unitDisk)
    (e : OpenPartialHomeomorph ℂ ℂ) (he : (e : PlaneMap) = F)
    (hsource : closedUnitDisk ⊆ e.source)
    (hes : RealSmoothOn e.symm e.target) H
    (hH : MemLp H 2 (volume.restrict boundaryHalfOpenInterval))
    (hmom : ∀ m : ℕ, (∫ θ in (0 : ℝ)..circlePeriod,
      (conj (deriv (physicalCircleTrace F) θ) * H θ) *
        (conj (physicalCircleTrace F θ) - conj (physicalCircleTrace F 0)) ^ m) = 0) :
    IsNonpositiveFourierSupport (fourierCoeffOn Real.two_pi_pos H) := by
  have hinj : InjOn F closedUnitDisk := by
    rw [← he]
    exact e.injOn.mono hsource
  have hnz := localConformal_closedDifferential_ne_zero_of_smoothInverse
    hR F hFs e he hsource hes
  exact localConformal_physicalMoments_nonpositive_of_memLp
    hb hL hR F hFs hhol hinj hnz rfl H hH hmom

end


end PolyaNeumann

end
