module

public import RequestProject.PhysicalHardySupport


public import RequestProject.PlanarTypes

public import RequestProject.CirclePeriod

public import RequestProject.PlanarGeometry

public import RequestProject.PhysicalCauchyBoundaryExtension
public import Mathlib.Analysis.Calculus.ContDiff.Comp
public import Mathlib.Analysis.Calculus.FDeriv.RestrictScalars
public import Mathlib.Analysis.Calculus.Deriv.Star
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-!
# The actual physical moment Hardy criterion for the original density

The continuous holomorphic extension of the conjugated physical primitive
does not by itself assert support of the original density.  Here the genuine
boundary equation `conj K' = γ' * conj H` is combined with the actual quotient
`q(z) = z^m / (fderiv ℝ F z 1)`.  Real smoothness near the closed disk gives
continuous `q` and its real differential there.  Complex linearity extends
from the open disk by continuity, so the actual boundary derivative of q
is available without boundary derivative regularity of the reconstructed
extension.

Boundary integration by parts and Cauchy--Goursat prove every full complex
circle moment of `conj H`.  Consequently all positive averaged Fourier
coefficients of the original H vanish.  Initial supplied-coordinate existence
remains separate; no Hardy support or elliptic regularity is assumed.
-/

@[expose] public section

open scoped ContDiff


noncomputable section

namespace PolyaNeumann

open MeasureTheory Set Metric
open scoped ComplexConjugate



/-- The actual complex-linear coefficient of the supplied real differential. -/
def physicalMomentDifferential (F : PlaneMap) z  := fderiv ℝ F z 1

/-- The genuine quotient used to test the original physical density. -/
def physicalMomentQuotient F m z  :=
  z ^ m / physicalMomentDifferential F z

/-- The actual real differential of the quotient evaluated on 1. -/
def physicalMomentQuotientPrime F m z  :=
  fderiv ℝ (physicalMomentQuotient F m) z 1

private theorem realDifferential_eq_complex_deriv
     (hf : DifferentiableOn ℂ f unitDisk)
     (hz : z ∈ unitDisk) v :
    fderiv ℝ f z v = deriv f z * v := by
  rw [(hf.differentiableAt (isOpen_ball.mem_nhds hz)).fderiv_restrictScalars ℝ]
  exact fderiv_eq_deriv_mul

/-- Pointwise real smoothness at the closed disk suffices to extend actual
complex linearity of the differential from its open interior. -/
private theorem realDifferential_complex_linear_closedDisk
    f (hf : DifferentiableOn ℂ f unitDisk)
    (hs : ∀ z ∈ closedUnitDisk, RealSmoothAt f z)
     (hz : z ∈ closedUnitDisk) v :
    fderiv ℝ f z v = fderiv ℝ f z 1 * v := by
  have hc a : ContinuousOn (fun w => fderiv ℝ f w a) closedUnitDisk := by
    intro w hw
    exact (((hs w hw).continuousAt_fderiv (by simp)).clm_apply continuousAt_const).continuousWithinAt
  have heq : EqOn (fun w => fderiv ℝ f w v)
      (fun w => fderiv ℝ f w 1 * v) unitDisk := by
    intro w hw
    simp_all [realDifferential_eq_complex_deriv]
  exact heq.of_subset_closure (hc v) ((hc 1).mul continuousOn_const)
    ball_subset_closedBall
    (by simpa  [closure_ball (0 : ℂ) (by norm_num : (1 : ℝ) ≠ 0)] using
      subset_rfl) hz

theorem physicalMomentDifferential_contDiffOn  F
    (hFs : RealSmoothOnBall F R) :
    RealSmoothOn (physicalMomentDifferential F) (ball (0 : ℂ) R) :=
  (hFs.fderiv_of_isOpen isOpen_ball (by simp)).clm_apply contDiffOn_const

theorem physicalMomentDifferential_holomorphic F
    (hhol : DifferentiableOn ℂ F unitDisk) :
    DifferentiableOn ℂ (physicalMomentDifferential F) unitDisk := by
  apply (hhol.deriv isOpen_ball).congr
  simp_all [physicalMomentDifferential, realDifferential_eq_complex_deriv]

section
variable {R } (hR : 1 < R) (F : PlaneMap) (hFs : RealSmoothOnBall F R)

include R hR F hFs in
/-- Nonzero closed-disk differential gives actual local smoothness of each
quotient at every closed-disk point; no collar nonvanishing premise is added. -/
theorem physicalMomentQuotient_contDiffAt_closedDisk
    (hnz : ∀ z ∈ closedUnitDisk, fderiv ℝ F z 1 ≠ 0) m 
    (hz : z ∈ closedUnitDisk) :
    RealSmoothAt (physicalMomentQuotient F m) z := by
  have hD := (physicalMomentDifferential_contDiffOn F hFs).contDiffAt
    (isOpen_ball.mem_nhds (closedBall_subset_ball hR hz))
  have hp : RealSmoothAt (((id ^ m))) z := contDiffAt_id.pow m
  have h := hp.mul (hD.inv (hnz z hz))
  assumption

theorem physicalMomentQuotient_holomorphic F
    (hhol : DifferentiableOn ℂ F unitDisk)
    (hnz : ∀ z ∈ closedUnitDisk, fderiv ℝ F z 1 ≠ 0) m :
    DifferentiableOn ℂ (physicalMomentQuotient F m) unitDisk :=
  (differentiableOn_id.pow m).div (physicalMomentDifferential_holomorphic F hhol)
    (fun z hz => hnz z (ball_subset_closedBall hz))

section
variable (hhol : DifferentiableOn ℂ F unitDisk) (hnz : ∀ z ∈ closedUnitDisk, fderiv ℝ F z 1 ≠ 0) (m : ℕ)

section
include R hR F hFs

include hhol hnz m in
/-- q and its genuine differentiated coefficient q' are holomorphic in the
open disk and continuous on its closure, proved from actual coordinate data. -/
theorem physicalMomentQuotientPrime_diffContOnCl :
    DiffContOnCl ℂ (physicalMomentQuotientPrime F m) unitDisk := by
  have hq := physicalMomentQuotient_holomorphic F hhol hnz m
  have hs z (hz : z ∈ closedUnitDisk)  :=
    physicalMomentQuotient_contDiffAt_closedDisk hR F hFs hnz m hz
  apply DiffContOnCl.mk_ball
  · apply (hq.deriv isOpen_ball).congr
    grind only [physicalMomentQuotientPrime, realDifferential_eq_complex_deriv]
  · intro z hz
    exact (((hs z hz).continuousAt_fderiv (by simp)).clm_apply continuousAt_const).continuousWithinAt

theorem physicalMomentQuotient_circle_contDiff
    (hnz : ∀ z ∈ closedUnitDisk, fderiv ℝ F z 1 ≠ 0) m :
    ContDiff ℝ 1 (physicalCircleTrace (physicalMomentQuotient F m)) := by
  apply contDiff_iff_contDiffAt.mpr
  intro θ
  have hz : unitCircleMap θ ∈ closedUnitDisk :=
    circleMap_mem_closedBall 0 (by norm_num) θ
  exact ((physicalMomentQuotient_contDiffAt_closedDisk hR F hFs hnz m hz).of_le
    (WithTop.coe_le_coe.mpr le_top)).comp θ (contDiff_circleMap 0 1).contDiffAt

include hhol hnz m in
/-- Actual differentiated angular quotient, including every boundary point. -/
theorem physicalMomentQuotient_circle_hasDerivAt θ :
    HasDerivAt (physicalCircleTrace (physicalMomentQuotient F m))
      (physicalMomentQuotientPrime F m (unitCircleMap θ) *
        (unitCircleMap θ * Complex.I)) θ := by
  have hz : unitCircleMap θ ∈ closedUnitDisk :=
    circleMap_mem_closedBall 0 (by norm_num) θ
  have hs := physicalMomentQuotient_contDiffAt_closedDisk hR F hFs hnz m hz
  have hfd := (hs.differentiableAt (by simp)).hasFDerivAt
  have hd := hfd.comp_hasDerivAt θ (hasDerivAt_circleMap 0 1 θ)
  rw [realDifferential_complex_linear_closedDisk (physicalMomentQuotient F m)
    (physicalMomentQuotient_holomorphic F hhol hnz m)
    (fun z hz => physicalMomentQuotient_contDiffAt_closedDisk hR F hFs hnz m hz) hz] at hd
  exact hd

end


end


end


section
variable {R } (hR : 1 < R) (F ) (hFs : RealSmoothOnBall F R) (hhol : DifferentiableOn ℂ F unitDisk) (hnz : ∀ z ∈ closedUnitDisk, fderiv ℝ F z 1 ≠ 0) (H ) (hH : Continuous H) (hmom0 : (∫ θ in (0 : ℝ)..circlePeriod,
      conj (deriv (physicalCircleTrace F) θ) * H θ) = 0) (P ) (hP : DiffContOnCl ℂ P unitDisk) (htrace : ∀ θ ∈ boundaryInterval,
      P (unitCircleMap θ) = conj (physicalMomentPrimitive (physicalCircleTrace F) H θ))

include R hR F hFs hhol hnz H hH hmom0 P hP htrace in
/-- Boundary integration by parts tests the original density against every
positive circle power.  The disk extension is required only to be holomorphic
inside and continuous on the closure; its boundary derivative is not assumed. -/
theorem physicalMomentDensity_circle_moment_eq_zero_of_primitive_extension
    m :
    (∫ θ in (0 : ℝ)..circlePeriod, conj (H θ) * (unitCircleMap θ) ^ (m + 1)) = 0 := by
  let γ := physicalCircleTrace F
  let K := physicalMomentPrimitive γ H
  let u  := fun θ => conj (K θ)
  let u'  := fun θ => deriv γ θ * conj (H θ)
  let q := physicalMomentQuotient F m
  let v := physicalCircleTrace q
  let v'  := fun θ => physicalMomentQuotientPrime F m (unitCircleMap θ) *
    (unitCircleMap θ * Complex.I)
  have hγ  :=
    contDiff_physicalCircleTrace_of_neighborhood hR F
      (hFs.of_le (WithTop.coe_le_coe.mpr le_top))
  have hK  := contDiff_physicalMomentPrimitive γ H hγ hH
  have hu : Continuous u := Complex.continuous_conj.comp hK.continuous
  have hu'  :=
    hγ.continuous_deriv_one.mul (Complex.continuous_conj.comp hH)
  have hdu θ : HasDerivAt u (u' θ) θ := by
    simpa only [u', Complex.star_def, map_mul, Complex.conj_conj] using
      (physicalMomentPrimitive_hasDerivAt γ H hγ hH θ).star
  have hv  := physicalMomentQuotient_circle_contDiff hR F hFs hnz m
  have hdv (θ : ℝ) : HasDerivAt v (v' θ) θ :=
    physicalMomentQuotient_circle_hasDerivAt hR F hFs hhol hnz m θ
  have hveq : deriv v = v' := by
    funext θ
    exact (hdv θ).deriv
  have hv' : Continuous v' := by
    rw [← hveq]
    exact hv.continuous_deriv_one
  have hu0 : u 0 = 0 := by measurability
  have huL : u circlePeriod = 0 := by
    measurability
  have hcauchy : circleIntegral (fun z => P z * physicalMomentQuotientPrime F m z) 0 1 = 0 :=
    DiffContOnCl.circleIntegral_eq_zero (by norm_num)
      ⟨hP.differentiableOn.mul
          (physicalMomentQuotientPrime_diffContOnCl hR F hFs hhol hnz m).differentiableOn,
        hP.continuousOn.mul
          (physicalMomentQuotientPrime_diffContOnCl hR F hFs hhol hnz m).continuousOn⟩
  have hceq : circleIntegral (fun z => P z * physicalMomentQuotientPrime F m z) 0 1 =
      ∫ θ in (0 : ℝ)..circlePeriod, u θ * v' θ := by
    rw [circleIntegral]
    apply intervalIntegral.integral_congr
    intro θ hθ
    rw [uIcc_of_le Real.two_pi_pos.le] at hθ
    simp only [deriv_circleMap, smul_eq_mul]
    grind
  rw [hceq] at hcauchy
  have hi := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
    hu.continuousOn hv.continuous.continuousOn (fun θ _ => hdu θ) (fun θ _ => hdv θ)
    (hu'.intervalIntegrable 0 circlePeriod) (hv'.intervalIntegrable 0 circlePeriod)
  simp only [hcauchy, huL, hu0, zero_mul, sub_self, zero_sub] at hi
  have hJ  := neg_eq_zero.mp hi.symm
  have heq : (fun θ => u' θ * v θ) =
      (fun θ => Complex.I * (conj (H θ) * (unitCircleMap θ) ^ (m + 1))) := by
    funext θ
    change (deriv (physicalCircleTrace F) θ * conj (H θ)) *
      ((unitCircleMap θ) ^ m / fderiv ℝ F (unitCircleMap θ) 1) =
        Complex.I * (conj (H θ) * (unitCircleMap θ) ^ (m + 1))
    rw [localConformal_circleTrace_deriv hR F hFs hhol, pow_succ]
    have hD := hnz (unitCircleMap θ) (circleMap_mem_closedBall 0 (by norm_num) θ)
    field_simp [hD]
  rw [heq, intervalIntegral.integral_const_mul] at hJ
  exact (mul_eq_zero.mp hJ).resolve_left Complex.I_ne_zero

include R hR F hFs hhol hnz H hH hmom0 P hP htrace in
/-- The actual primitive extension implies support of the original density,
through the proved physical quotient and boundary integration by parts. -/
theorem physicalMomentDensity_nonpositive_of_primitive_extension :
    IsNonpositiveFourierSupport (fourierCoeffOn Real.two_pi_pos H) := by
  have hneg m : fourierCoeffOn Real.two_pi_pos (fun θ => conj (H θ))
      (-((m + 1 : ℕ) : ℤ)) = 0 := by
    have hm := physicalMomentDensity_circle_moment_eq_zero_of_primitive_extension
      hR F hFs hhol hnz H hH hmom0 P hP htrace m
    have hi : (∫ θ in (0 : ℝ)..circlePeriod,
        fourier (T := 2 * Real.pi) ((m + 1 : ℕ) : ℤ)
          (θ : AddCircle circlePeriod) * conj (H θ)) = 0 := by
      calc
        _ = ∫ θ in (0)..circlePeriod, conj (H θ) * (unitCircleMap θ) ^ (m + 1) := by
          apply intervalIntegral.integral_congr
          intro θ _
          change fourier (T := 2 * Real.pi) ((m + 1 : ℕ))
            θ * conj (H θ) =
              conj (H θ) * (unitCircleMap θ) ^ (m + 1)
          rw [common_physicalHardy_fourier_natCast]
          ring
        _ = 0 := hm
    rw [fourierCoeffOn_eq_integral]
    simp_all
  intro n hn
  cases n with
  | negSucc m => omega
  | ofNat k =>
      cases k with
      | zero => simp_all
      | succ m =>
          simp_all [common_physicalHardy_fourierCoeffOn_conj]

end


/-- The actual full physical antiholomorphic moments imply nonpositive
Fourier support of the ORIGINAL density H in the supplied conformal
coordinate.  The primitive extension is constructed, not assumed; the
quotient uses only the actual nonzero closed-disk coordinate differential. -/
theorem localConformal_physicalMoments_nonpositive
     (hb : Bornology.IsBounded Ω) (hΩ : IsLipschitzDomain Ω)
     (hR : 1 < R) F
    (hFs : RealSmoothOnBall F R)
    (hhol : DifferentiableOn ℂ F unitDisk)
    (hinj : InjOn F closedUnitDisk)
    (hnz : ∀ z ∈ closedUnitDisk, fderiv ℝ F z 1 ≠ 0)
    (himage : F '' unitDisk = Ω)
    H (hH : Continuous H)
    (hpH : Function.Periodic H circlePeriod)
    (hmom : ∀ m : ℕ, (∫ θ in (0 : ℝ)..circlePeriod,
      (conj (deriv (physicalCircleTrace F) θ) * H θ) *
        (conj (physicalCircleTrace F θ) - conj (physicalCircleTrace F 0)) ^ m) = 0) :
    IsNonpositiveFourierSupport (fourierCoeffOn Real.two_pi_pos H) := by
  obtain ⟨G, hG, htrace⟩ := exists_localConformal_physicalMomentPrimitive_extension
    hb hΩ hR F hFs hhol hinj hnz himage H hH hpH hmom
  have hF  :=
    DiffContOnCl.mk_ball hhol (hFs.continuousOn.mono (closedBall_subset_ball hR))
  have hmaps : MapsTo F unitDisk Ω := by
    intro z hz
    grind
  apply physicalMomentDensity_nonpositive_of_primitive_extension hR F hFs hhol hnz H hH
    (by simpa   using hmom 0)
    (G ∘ F) (hG.comp hF hmaps)
  exact htrace

end PolyaNeumann

end
