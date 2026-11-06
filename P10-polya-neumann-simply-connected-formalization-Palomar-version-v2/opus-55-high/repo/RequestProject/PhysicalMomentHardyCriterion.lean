module

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

set_option autoImplicit false

noncomputable section

namespace PolyaNeumann

open MeasureTheory Set Metric
open scoped ComplexConjugate Topology


/-- The actual complex-linear coefficient of the supplied real differential. -/
def physicalMomentDifferential (F : ℂ → ℂ) (z : ℂ) : ℂ := fderiv ℝ F z 1

/-- The genuine quotient used to test the original physical density. -/
def physicalMomentQuotient (F : ℂ → ℂ) (m : ℕ) (z : ℂ) : ℂ :=
  z ^ m / physicalMomentDifferential F z

/-- The actual real differential of the quotient evaluated on 1. -/
def physicalMomentQuotientPrime (F : ℂ → ℂ) (m : ℕ) (z : ℂ) : ℂ :=
  fderiv ℝ (physicalMomentQuotient F m) z 1

variable {R : ℝ} (F : ℂ → ℂ)

private theorem realDifferential_eq_complex_deriv
    {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f (ball (0 : ℂ) 1))
    {z : ℂ} (hz : z ∈ ball (0 : ℂ) 1) (v : ℂ) :
    fderiv ℝ f z v = deriv f z * v := by
  rw [(hf.differentiableAt (isOpen_ball.mem_nhds hz)).fderiv_restrictScalars ℝ]
  change fderiv ℂ f z v = _
  exact fderiv_eq_deriv_mul

/-- Pointwise real smoothness at the closed disk suffices to extend actual
complex linearity of the differential from its open interior. -/
private theorem realDifferential_complex_linear_closedDisk
    (f : ℂ → ℂ) (hf : DifferentiableOn ℂ f (ball (0 : ℂ) 1))
    (hs : ∀ z ∈ closedBall (0 : ℂ) 1, ContDiffAt ℝ (⊤ : ℕ∞) f z)
    {z : ℂ} (hz : z ∈ closedBall (0 : ℂ) 1) (v : ℂ) :
    fderiv ℝ f z v = fderiv ℝ f z 1 * v := by
  have hc (a : ℂ) : ContinuousOn (fun w => fderiv ℝ f w a) (closedBall (0 : ℂ) 1) := by
    intro w hw
    exact (((hs w hw).continuousAt_fderiv (by simp)).clm_apply continuousAt_const).continuousWithinAt
  have heq : EqOn (fun w => fderiv ℝ f w v)
      (fun w => fderiv ℝ f w 1 * v) (ball (0 : ℂ) 1) := by
    intro w hw
    simp [realDifferential_eq_complex_deriv hf hw v, realDifferential_eq_complex_deriv hf hw 1, mul_one]
  exact heq.of_subset_closure (hc v) ((hc 1).mul continuousOn_const)
    ball_subset_closedBall
    (by simp [closure_ball (0 : ℂ) (by norm_num : (1 : ℝ) ≠ 0)]) hz

theorem physicalMomentDifferential_contDiffOn (hFs : ContDiffOn ℝ (⊤ : ℕ∞) F (ball 0 R)) :
    ContDiffOn ℝ (⊤ : ℕ∞) (physicalMomentDifferential F) (ball 0 R) :=
  (hFs.fderiv_of_isOpen isOpen_ball (by simp)).clm_apply contDiffOn_const

theorem physicalMomentDifferential_holomorphic (F : ℂ → ℂ)
    (hhol : DifferentiableOn ℂ F (ball 0 1)) :
    DifferentiableOn ℂ (physicalMomentDifferential F) (ball 0 1) := by
  apply (hhol.deriv isOpen_ball).congr
  intro z hz
  simpa only [physicalMomentDifferential, mul_one] using
    realDifferential_eq_complex_deriv hhol hz 1

/-- Nonzero closed-disk differential gives actual local smoothness of each
quotient at every closed-disk point; no collar nonvanishing premise is added. -/
theorem physicalMomentQuotient_contDiffAt_closedDisk (hR : 1 < R) (F : ℂ → ℂ)
    (hFs : ContDiffOn ℝ (⊤ : ℕ∞) F (ball 0 R))
    (hnz : ∀ z ∈ closedBall 0 1, fderiv ℝ F z 1 ≠ 0) (m : ℕ) {z : ℂ}
    (hz : z ∈ closedBall 0 1) :
    ContDiffAt ℝ (⊤ : ℕ∞) (physicalMomentQuotient F m) z := by
  have h := (contDiffAt_id.pow m).mul (((physicalMomentDifferential_contDiffOn F hFs).contDiffAt
    (isOpen_ball.mem_nhds (closedBall_subset_ball hR hz))).inv (hnz z hz))
  assumption

theorem physicalMomentQuotient_holomorphic (hhol : DifferentiableOn ℂ F (ball 0 1))
    (hnz : ∀ z ∈ closedBall 0 1, fderiv ℝ F z 1 ≠ 0) (m : ℕ) :
    DifferentiableOn ℂ (physicalMomentQuotient F m) (ball 0 1) :=
  (differentiableOn_id.pow m).div (physicalMomentDifferential_holomorphic F hhol)
    (fun z hz => hnz z (ball_subset_closedBall hz))

/-- q and its genuine differentiated coefficient q' are holomorphic in the
open disk and continuous on its closure, proved from actual coordinate data. -/
theorem physicalMomentQuotientPrime_diffContOnCl {R : ℝ} (hR : 1 < R) (F : ℂ → ℂ)
    (hFs : ContDiffOn ℝ (⊤ : ℕ∞) F (ball 0 R))
    (hhol : DifferentiableOn ℂ F (ball 0 1))
    (hnz : ∀ z ∈ closedBall 0 1, fderiv ℝ F z 1 ≠ 0) (m : ℕ) :
    DiffContOnCl ℂ (physicalMomentQuotientPrime F m) (ball 0 1) := by
  have hq := physicalMomentQuotient_holomorphic F hhol hnz m
  have hs (z : ℂ) (hz : z ∈ closedBall 0 1) :
      ContDiffAt ℝ (⊤ : ℕ∞) (physicalMomentQuotient F m) z :=
    physicalMomentQuotient_contDiffAt_closedDisk hR F hFs hnz m hz
  apply DiffContOnCl.mk_ball
  · apply (hq.deriv isOpen_ball).congr
    intro z hz
    simpa only [physicalMomentQuotientPrime, mul_one] using
      realDifferential_eq_complex_deriv hq hz 1
  · intro z hz
    exact (((hs z hz).continuousAt_fderiv (by simp)).clm_apply continuousAt_const).continuousWithinAt

theorem physicalMomentQuotient_circle_contDiff (hR : 1 < R) (F : ℂ → ℂ)
    (hFs : ContDiffOn ℝ (⊤ : ℕ∞) F (ball 0 R))
    (hnz : ∀ z ∈ closedBall 0 1, fderiv ℝ F z 1 ≠ 0) (m : ℕ) :
    ContDiff ℝ 1 (physicalCircleTrace (physicalMomentQuotient F m)) := by
  apply contDiff_iff_contDiffAt.mpr
  intro θ
  exact ((physicalMomentQuotient_contDiffAt_closedDisk hR F hFs hnz m (circleMap_mem_closedBall 0 (by norm_num) θ)).of_le
    (WithTop.coe_le_coe.mpr le_top)).comp θ (contDiff_circleMap 0 1).contDiffAt

/-- Actual differentiated angular quotient, including every boundary point. -/
theorem physicalMomentQuotient_circle_hasDerivAt (hR : 1 < R) (F : ℂ → ℂ)
    (hFs : ContDiffOn ℝ (⊤ : ℕ∞) F (ball 0 R))
    (hhol : DifferentiableOn ℂ F (ball 0 1))
    (hnz : ∀ z ∈ closedBall 0 1, fderiv ℝ F z 1 ≠ 0) (m : ℕ) (θ : ℝ) :
    HasDerivAt (physicalCircleTrace (physicalMomentQuotient F m))
      (physicalMomentQuotientPrime F m (circleMap 0 1 θ) *
        (circleMap 0 1 θ * Complex.I)) θ := by
  have hz : circleMap 0 1 θ ∈ closedBall 0 1 :=
    circleMap_mem_closedBall 0 (by norm_num) θ
  have hd := ((physicalMomentQuotient_contDiffAt_closedDisk hR F hFs hnz m hz).differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt θ (hasDerivAt_circleMap 0 1 θ)
  rwa [realDifferential_complex_linear_closedDisk (physicalMomentQuotient F m)
    (physicalMomentQuotient_holomorphic F hhol hnz m)
    (fun z hz => physicalMomentQuotient_contDiffAt_closedDisk hR F hFs hnz m hz) hz] at hd

/-- Boundary integration by parts tests the original density against every
positive circle power.  The disk extension is required only to be holomorphic
inside and continuous on the closure; its boundary derivative is not assumed. -/
theorem physicalMomentDensity_circle_moment_eq_zero_of_primitive_extension
    (hR : 1 < R) (F : ℂ → ℂ)
    (hFs : ContDiffOn ℝ (⊤ : ℕ∞) F (ball 0 R))
    (hhol : DifferentiableOn ℂ F (ball 0 1))
    (hnz : ∀ z ∈ closedBall 0 1, fderiv ℝ F z 1 ≠ 0)
    (H : ℝ → ℂ) (hH : Continuous H)
    (hmom0 : (∫ θ in 0..(2 * Real.pi),
      conj (deriv (physicalCircleTrace F) θ) * H θ) = 0)
    (P : ℂ → ℂ) (hP : DiffContOnCl ℂ P (ball 0 1))
    (htrace : ∀ θ ∈ Icc 0 (2 * Real.pi),
      P (circleMap 0 1 θ) = conj (physicalMomentPrimitive (physicalCircleTrace F) H θ))
    (m : ℕ) :
    (∫ θ in 0..(2 * Real.pi), conj (H θ) * (circleMap 0 1 θ) ^ (m + 1)) = 0 := by
  let γ := physicalCircleTrace F
  let K := physicalMomentPrimitive γ H
  let u  := fun θ => conj (K θ)
  let u'  := fun θ => deriv γ θ * conj (H θ)
  let q := physicalMomentQuotient F m
  let v := physicalCircleTrace q
  let v'  := fun θ => physicalMomentQuotientPrime F m (circleMap 0 1 θ) *
    (circleMap 0 1 θ * Complex.I)
  have hγ  :=
    contDiff_physicalCircleTrace_of_neighborhood hR F
      (hFs.of_le (WithTop.coe_le_coe.mpr le_top))
  have hu : Continuous u := Complex.continuous_conj.comp (contDiff_physicalMomentPrimitive γ H hγ hH).continuous
  have hdu (θ : ℝ) : HasDerivAt u (u' θ) θ := by
    simpa only [Complex.star_def, map_mul, Complex.conj_conj] using
      (physicalMomentPrimitive_hasDerivAt γ H hγ hH θ).star
  have hv  := physicalMomentQuotient_circle_contDiff hR F hFs hnz m
  have hdv (θ : ℝ) : HasDerivAt v (v' θ) θ :=
    physicalMomentQuotient_circle_hasDerivAt hR F hFs hhol hnz m θ
  have hveq : deriv v = v' := by
    funext θ
    exact (hdv θ).deriv
  have hv' : Continuous v' := by
    rw [← hveq]
    fun_prop
  have hu0 : u 0 = 0 := by simp [u, K]
  have huL : u (2 * Real.pi) = 0 := by
    simp [u, K, physicalMomentPrimitive_endpoint γ H hmom0]
  have hcauchy : circleIntegral (fun z => P z * physicalMomentQuotientPrime F m z) 0 1 = 0 :=
    DiffContOnCl.circleIntegral_eq_zero (by norm_num)
      ⟨hP.differentiableOn.mul
          (physicalMomentQuotientPrime_diffContOnCl hR F hFs hhol hnz m).differentiableOn,
        hP.continuousOn.mul
          (physicalMomentQuotientPrime_diffContOnCl hR F hFs hhol hnz m).continuousOn⟩
  have hceq : circleIntegral (fun z => P z * physicalMomentQuotientPrime F m z) 0 1 =
      ∫ θ in 0..(2 * Real.pi), u θ * v' θ := by
    apply intervalIntegral.integral_congr
    intro θ hθ
    rw [uIcc_of_le Real.two_pi_pos.le] at hθ
    simp 
    grind
  rw [hceq] at hcauchy
  have hi := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
    hu.continuousOn hv.continuous.continuousOn (fun θ _ => hdu θ) (fun θ _ => hdv θ)
    ((hγ.continuous_deriv_one.mul (Complex.continuous_conj.comp hH)).intervalIntegrable 0 (2 * Real.pi)) (hv'.intervalIntegrable 0 (2 * Real.pi))
  simp only [hcauchy, huL, hu0, zero_mul, sub_self, zero_sub] at hi
  have hJ  := neg_eq_zero.mp hi.symm
  have heq : (fun θ => u' θ * v θ) =
      (fun θ => Complex.I * (conj (H θ) * (circleMap 0 1 θ) ^ (m + 1))) := by
    funext θ
    change (deriv (physicalCircleTrace F) θ * conj (H θ)) *
      ((circleMap 0 1 θ) ^ m / fderiv ℝ F (circleMap 0 1 θ) 1) =
        Complex.I * (conj (H θ) * (circleMap 0 1 θ) ^ (m + 1))
    rw [localConformal_circleTrace_deriv hR F hFs hhol, pow_succ]
    have hD := hnz (circleMap 0 1 θ) (circleMap_mem_closedBall 0 (by norm_num) θ)
    field_simp 
  rw [heq] at hJ
  simp_all

private theorem physicalMomentCriterion_fourier_natCast (m : ℕ) (θ : ℝ) :
    fourier (T := 2 * Real.pi) (m : ℤ) (θ : AddCircle (2 * Real.pi)) =
      (circleMap 0 1 θ) ^ m := by
  rw [fourier_coe_apply, circleMap_zero_pow]
  simp only [one_pow, circleMap_zero, Complex.ofReal_one, one_mul]
  congr 1
  push_cast
  field_simp

private theorem physicalMomentCriterion_fourierCoeffOn_conj (H : ℝ → ℂ) (n : ℤ) :
    fourierCoeffOn Real.two_pi_pos (fun θ => conj (H θ)) n =
      conj (fourierCoeffOn Real.two_pi_pos H (-n)) := by
  rw [fourierCoeffOn_eq_integral, fourierCoeffOn_eq_integral]
  simp only [sub_zero, Complex.real_smul, map_mul, Complex.conj_ofReal]
  simp [← intervalIntegral_conj]

/-- The actual primitive extension implies support of the original density,
through the proved physical quotient and boundary integration by parts. -/
theorem physicalMomentDensity_nonpositive_of_primitive_extension
    (hR : 1 < R) (F : ℂ → ℂ)
    (hFs : ContDiffOn ℝ (⊤ : ℕ∞) F (ball 0 R))
    (hhol : DifferentiableOn ℂ F (ball 0 1))
    (hnz : ∀ z ∈ closedBall 0 1, fderiv ℝ F z 1 ≠ 0)
    (H : ℝ → ℂ) (hH : Continuous H)
    (hmom0 : (∫ θ in 0..(2 * Real.pi),
      conj (deriv (physicalCircleTrace F) θ) * H θ) = 0)
    (P : ℂ → ℂ) (hP : DiffContOnCl ℂ P (ball 0 1))
    (htrace : ∀ θ ∈ Icc 0 (2 * Real.pi),
      P (circleMap 0 1 θ) = conj (physicalMomentPrimitive (physicalCircleTrace F) H θ)) :
    IsNonpositiveFourierSupport (fourierCoeffOn Real.two_pi_pos H) := by
  have hneg (m : ℕ) : fourierCoeffOn Real.two_pi_pos (fun θ => conj (H θ))
      (-(m + 1)) = 0 := by
    have hi : (∫ θ in 0..(2 * Real.pi),
        fourier (T := 2 * Real.pi) (m + 1)
          θ * conj (H θ)) = 0 := by
      calc
        _ = ∫ θ in 0..(2 * Real.pi), conj (H θ) * (circleMap 0 1 θ) ^ (m + 1) := by
          apply intervalIntegral.integral_congr
          intro θ _
          change fourier  (m + 1 : ℕ)
            θ * conj (H θ) =
              conj (H θ) * (circleMap 0 1 θ) ^ (m + 1)
          rw [physicalMomentCriterion_fourier_natCast]
          ring
        _ = 0 := (physicalMomentDensity_circle_moment_eq_zero_of_primitive_extension
      hR F hFs hhol hnz H hH hmom0 P hP htrace m)
    simp_all [fourierCoeffOn_eq_integral]
  intro n hn
  cases n with
  | negSucc m => omega
  | ofNat k =>
      cases k with
      | zero => trivial
      | succ m =>
          simp_all [physicalMomentCriterion_fourierCoeffOn_conj]

/-- The actual full physical antiholomorphic moments imply nonpositive
Fourier support of the ORIGINAL density H in the supplied conformal
coordinate.  The primitive extension is constructed, not assumed; the
quotient uses only the actual nonzero closed-disk coordinate differential. -/
theorem localConformal_physicalMoments_nonpositive
    {Ω : Set ℂ} (hb : Bornology.IsBounded Ω) (hΩ : IsLipschitzDomain Ω)
    {R : ℝ} (hR : 1 < R) (F : ℂ → ℂ)
    (hFs : ContDiffOn ℝ (⊤ : ℕ∞) F (ball 0 R))
    (hhol : DifferentiableOn ℂ F (ball 0 1))
    (hinj : InjOn F (closedBall 0 1))
    (hnz : ∀ z ∈ closedBall 0 1, fderiv ℝ F z 1 ≠ 0)
    (himage : F '' ball 0 1 = Ω)
    (H : ℝ → ℂ) (hH : Continuous H)
    (hpH : Function.Periodic H (2 * Real.pi))
    (hmom : ∀ m : ℕ, (∫ θ in 0..(2 * Real.pi),
      (conj (deriv (physicalCircleTrace F) θ) * H θ) *
        (conj (physicalCircleTrace F θ) - conj (physicalCircleTrace F 0)) ^ m) = 0) :
    IsNonpositiveFourierSupport (fourierCoeffOn Real.two_pi_pos H) := by
  obtain ⟨G, hG, htrace⟩ := exists_localConformal_physicalMomentPrimitive_extension
    hb hΩ hR F hFs hhol hinj hnz himage H hH hpH hmom
  apply physicalMomentDensity_nonpositive_of_primitive_extension hR F hFs hhol hnz H hH
    (by simpa only [pow_zero, mul_one] using hmom 0)
    (G ∘ F) (hG.comp (DiffContOnCl.mk_ball hhol (hFs.continuousOn.mono (closedBall_subset_ball hR))) (by
    intro z hz
    grind))
  assumption

end PolyaNeumann

end
