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


noncomputable section

namespace PolyaNeumann

open MeasureTheory Set Metric
open scoped ComplexConjugate Topology ContDiff


/-- The actual complex-linear coefficient of the supplied real differential. -/
def physicalMomentDifferential (F : ℂ → ℂ) (z : ℂ) : ℂ := fderiv ℝ F z 1

/-- The genuine quotient used to test the original physical density. -/
def physicalMomentQuotient (F : ℂ → ℂ) (m : ℕ) (z : ℂ) : ℂ :=
  z ^ m / physicalMomentDifferential F z

/-- The actual real differential of the quotient evaluated on 1. -/
def physicalMomentQuotientPrime (F : ℂ → ℂ) (m : ℕ) (z : ℂ) : ℂ :=
  fderiv ℝ (physicalMomentQuotient F m) z 1

local notation "Φ2" => ball 0 1

private theorem realDifferential_eq_complex_deriv
     (hf : DifferentiableOn ℂ f (Φ2))
     (hz : z ∈ ball (0 : ℂ) 1) v :
    fderiv ℝ f z v = deriv f z * v := by
  rw [(hf.differentiableAt (isOpen_ball.mem_nhds hz)).fderiv_restrictScalars ℝ]
  exact fderiv_eq_deriv_mul

/-- Pointwise real smoothness at the closed disk suffices to extend actual
complex linearity of the differential from its open interior. -/
local notation "Φ1" => closedBall 0 1

private theorem realDifferential_complex_linear_closedDisk
    f (hf : DifferentiableOn ℂ f (Φ2))
    (hs : ∀ z ∈ closedBall (0 : ℂ) 1, ContDiffAt ℝ ∞ f z)
     (hz : z ∈ closedBall (0 : ℂ) 1) v :
    fderiv ℝ f z v = fderiv ℝ f z 1 * v := by
  have hc a : ContinuousOn (fun w => fderiv ℝ f w a) (Φ1) := by
    intro w hw
    exact (((hs w hw).continuousAt_fderiv (by simp)).clm_apply continuousAt_const).continuousWithinAt
  exact (show EqOn (fun w => fderiv ℝ f w v) (fun w => fderiv ℝ f w 1 * v) (Φ2) by
    intro w hw
    change fderiv ℝ f w v = fderiv ℝ f w 1 * v
    rw [realDifferential_eq_complex_deriv hf hw v,
      realDifferential_eq_complex_deriv hf hw 1, mul_one]).of_subset_closure (hc v) ((hc 1).mul continuousOn_const)
    ball_subset_closedBall
    (by simpa [closure_ball (0 : ℂ) (by norm_num : (1 : ℝ) ≠ 0)] using
      (subset_rfl : closedBall (0 : ℂ) 1 ⊆ closedBall (0 : ℂ) 1)) hz

/-- Nonzero closed-disk differential gives actual local smoothness of each
quotient at every closed-disk point; no collar nonvanishing premise is added. -/
theorem physicalMomentQuotient_contDiffAt_closedDisk  (hR : 1 < R) F
    (hFs : ContDiffOn ℝ ∞ F (ball 0 R))
    (hnz : ∀ z ∈ Φ1, fderiv ℝ F z 1 ≠ 0) m 
    (hz : z ∈ Φ1) :
    ContDiffAt ℝ ∞ (physicalMomentQuotient F m) z := by
  have h := (contDiffAt_id.pow m).mul ((((hFs.fderiv_of_isOpen isOpen_ball (by simp)).clm_apply contDiffOn_const : ContDiffOn ℝ ∞ (physicalMomentDifferential F) (ball 0 R)).contDiffAt (isOpen_ball.mem_nhds (closedBall_subset_ball hR hz))).inv (hnz z hz))
  show ContDiffAt ℝ ∞ (fun w => w ^ m / physicalMomentDifferential F w) z
  simp [div_eq_mul_inv]
  exact h

theorem physicalMomentQuotient_holomorphic F
    (hhol : DifferentiableOn ℂ F (Φ2))
    (hnz : ∀ z ∈ Φ1, fderiv ℝ F z 1 ≠ 0) m :
    DifferentiableOn ℂ (physicalMomentQuotient F m) (Φ2) :=
  (differentiableOn_id.pow m).div (show DifferentiableOn ℂ (physicalMomentDifferential F) (ball (0 : ℂ) 1) by
    apply (hhol.deriv isOpen_ball).congr
    intro z hz
    simpa [physicalMomentDifferential] using
      realDifferential_eq_complex_deriv hhol hz 1)
    (fun z hz => hnz z (ball_subset_closedBall hz))

/-- q and its genuine differentiated coefficient q' are holomorphic in the
open disk and continuous on its closure, proved from actual coordinate data. -/
theorem physicalMomentQuotientPrime_diffContOnCl  (hR : 1 < R) F
    (hFs : ContDiffOn ℝ ∞ F (ball 0 R))
    (hhol : DifferentiableOn ℂ F (Φ2))
    (hnz : ∀ z ∈ Φ1, fderiv ℝ F z 1 ≠ 0) m :
    DiffContOnCl ℂ (physicalMomentQuotientPrime F m) (Φ2) := by
  have hq := physicalMomentQuotient_holomorphic F hhol hnz m
  have hs z (hz : z ∈ Φ1) :
      ContDiffAt ℝ (⊤ : ℕ∞) (physicalMomentQuotient F m) z :=
    physicalMomentQuotient_contDiffAt_closedDisk hR F hFs hnz m hz
  apply DiffContOnCl.mk_ball
  · apply (hq.deriv isOpen_ball).congr
    intro z hz
    simpa [physicalMomentQuotientPrime] using
      realDifferential_eq_complex_deriv hq hz 1
  · intro z hz
    exact (((hs z hz).continuousAt_fderiv (by simp)).clm_apply continuousAt_const).continuousWithinAt

theorem physicalMomentQuotient_circle_contDiff  (hR : 1 < R) F
    (hFs : ContDiffOn ℝ ∞ F (ball 0 R))
    (hnz : ∀ z ∈ Φ1, fderiv ℝ F z 1 ≠ 0) m :
    ContDiff ℝ 1 (physicalCircleTrace (physicalMomentQuotient F m)) := by
  apply contDiff_iff_contDiffAt.mpr
  intro θ
  exact ((physicalMomentQuotient_contDiffAt_closedDisk hR F hFs hnz m (circleMap_mem_closedBall 0 (by norm_num) θ)).of_le
    (WithTop.coe_le_coe.mpr le_top)).comp θ (contDiff_circleMap 0 1).contDiffAt

local notation "Φ0" => circleMap 0 1

private theorem physicalMomentCriterion_fourier_natCast (m : ℕ) (θ : ℝ) :
    fourier (T := 2 * Real.pi) (m : ℤ) (θ : AddCircle (2 * Real.pi)) =
      (Φ0 θ) ^ m := by
  rw [fourier_coe_apply, circleMap_zero_pow]
  simp [circleMap_zero]
  congr 1
  push_cast
  field_simp [Real.pi_ne_zero]

private theorem physicalMomentCriterion_fourierCoeffOn_conj (H : ℝ → ℂ) n :
    fourierCoeffOn Real.two_pi_pos (fun θ => conj (H θ)) n =
      conj (fourierCoeffOn Real.two_pi_pos H (-n)) := by
  rw [fourierCoeffOn_eq_integral, fourierCoeffOn_eq_integral]
  simp only [sub_zero, Complex.real_smul, map_mul, Complex.conj_ofReal]
  congr 1
  rw [← intervalIntegral_conj]
  apply intervalIntegral.integral_congr
  intro θ _
  simp only [smul_eq_mul, map_mul, neg_neg]
  congr 1
  simpa only [fourier_coe_apply, sub_zero] using
    fourier_neg (n := n) (x := (θ : AddCircle (2 * Real.pi)))

/-- The actual primitive extension implies support of the original density,
through the proved physical quotient and boundary integration by parts. -/
theorem physicalMomentDensity_nonpositive_of_primitive_extension
     (hR : 1 < R) (F : ℂ → ℂ)
    (hFs : ContDiffOn ℝ ∞ F (ball 0 R))
    (hhol : DifferentiableOn ℂ F (Φ2))
    (hnz : ∀ z ∈ Φ1, fderiv ℝ F z 1 ≠ 0)
    (H : ℝ → ℂ) (hH : Continuous H)
    (hmom0 : (∫ θ in 0..(2 * Real.pi),
      conj (deriv (physicalCircleTrace F) θ) * H θ) = 0)
    P (hP : DiffContOnCl ℂ P (Φ2))
    (htrace : ∀ θ ∈ Icc 0 (2 * Real.pi),
      P (Φ0 θ) = conj (physicalMomentPrimitive (physicalCircleTrace F) H θ)) :
    IsNonpositiveFourierSupport (fourierCoeffOn Real.two_pi_pos H) := by
  have hneg m : fourierCoeffOn Real.two_pi_pos (fun θ => conj (H θ))
      (-(m + 1 : ℕ)) = 0 := by
    rw [fourierCoeffOn_eq_integral]
    simp
    simpa [fourier_coe_apply] using
      congrArg (fun z => (1 / (2 * Real.pi)) • z) (show (∫ θ in 0..(2 * Real.pi), fourier (T := 2 * Real.pi) (m + 1 : ℕ) (θ : AddCircle (2 * Real.pi)) * conj (H θ)) = 0 by
        calc
          _ = ∫ θ in 0..(2 * Real.pi), conj (H θ) * (Φ0 θ) ^ (m + 1) := by
            apply intervalIntegral.integral_congr
            intro θ _
            change fourier (T := 2 * Real.pi) (m + 1 : ℕ)
              (θ : AddCircle (2 * Real.pi)) * conj (H θ) = _
            rw [physicalMomentCriterion_fourier_natCast]
            ring
          _ = 0 := (show (∫ θ in 0..(2 * Real.pi), conj (H θ) * (Φ0 θ) ^ (m + 1)) = 0 by
            let γ := physicalCircleTrace F
            let K := physicalMomentPrimitive γ H
            let u : ℝ → ℂ := fun θ => conj (K θ)
            let u' : ℝ → ℂ := fun θ => deriv γ θ * conj (H θ)
            let v := physicalCircleTrace (physicalMomentQuotient F m)
            let v' : ℝ → ℂ := fun θ => physicalMomentQuotientPrime F m (Φ0 θ) *
              (Φ0 θ * Complex.I)
            have hγ :=
              contDiff_physicalCircleTrace_of_neighborhood hR F
                (hFs.of_le (WithTop.coe_le_coe.mpr le_top))
            have hu : Continuous u := Complex.continuous_conj.comp (contDiff_physicalMomentPrimitive γ H hγ hH).continuous
            have hdu θ : HasDerivAt u (u' θ) θ := by
              simpa [u, u'] using
                (physicalMomentPrimitive_hasDerivAt γ H hγ hH θ).star
            have hv : ContDiff ℝ 1 v := physicalMomentQuotient_circle_contDiff hR F hFs hnz m
            have hdv θ : HasDerivAt v (v' θ) θ :=
              show HasDerivAt (physicalCircleTrace (physicalMomentQuotient F m)) (physicalMomentQuotientPrime F m (Φ0 θ) * (Φ0 θ * Complex.I)) θ by
                have hz : Φ0 θ ∈ Φ1 :=
                  circleMap_mem_closedBall 0 (by norm_num) θ
                have hfd := ((physicalMomentQuotient_contDiffAt_closedDisk hR F hFs hnz m hz).differentiableAt (by simp)).hasFDerivAt
                have hd := hfd.comp_hasDerivAt θ (hasDerivAt_circleMap 0 1 θ)
                rw [realDifferential_complex_linear_closedDisk (physicalMomentQuotient F m)
                  (physicalMomentQuotient_holomorphic F hhol hnz m)
                  (fun z hz => physicalMomentQuotient_contDiffAt_closedDisk hR F hFs hnz m hz) hz] at hd
                exact hd
            have hveq : deriv v = v' := by
              funext θ
              exact (hdv θ).deriv
            have hv' : Continuous v' := by
              rw [← hveq]
              exact hv.continuous_deriv_one
            have hu0 : u 0 = 0 := by simp [u, K]
            have huL : u (2 * Real.pi) = 0 := by
              dsimp only [u, K]
              rw [physicalMomentPrimitive_endpoint γ H hmom0, map_zero]
            have hcauchy : circleIntegral (fun z => P z * physicalMomentQuotientPrime F m z) 0 1 = 0 :=
              DiffContOnCl.circleIntegral_eq_zero (by norm_num)
                ⟨hP.differentiableOn.mul
                    (physicalMomentQuotientPrime_diffContOnCl hR F hFs hhol hnz m).differentiableOn,
                  hP.continuousOn.mul
                    (physicalMomentQuotientPrime_diffContOnCl hR F hFs hhol hnz m).continuousOn⟩
            have hceq : circleIntegral (fun z => P z * physicalMomentQuotientPrime F m z) 0 1 =
                ∫ θ in 0..(2 * Real.pi), u θ * v' θ := by
              rw [circleIntegral]
              apply intervalIntegral.integral_congr
              intro θ hθ
              rw [uIcc_of_le Real.two_pi_pos.le] at hθ
              simp
              rw [htrace θ hθ]
              dsimp only [u, v', K, γ]
              ring
            rw [hceq] at hcauchy
            have hi := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
              hu.continuousOn hv.continuous.continuousOn (fun θ _ => hdu θ) (fun θ _ => hdv θ)
              ((hγ.continuous_deriv_one.mul (Complex.continuous_conj.comp hH)).intervalIntegrable 0 (2 * Real.pi)) (hv'.intervalIntegrable 0 (2 * Real.pi))
            simp only [hcauchy, huL, hu0, zero_mul, sub_self, zero_sub] at hi
            have hJ : (∫ θ in 0..(2 * Real.pi), u' θ * v θ) = 0 := neg_eq_zero.mp hi.symm
            rw [show (fun θ => u' θ * v θ) = (fun θ => Complex.I * (conj (H θ) * (Φ0 θ) ^ (m + 1))) by
              funext θ
              change deriv (physicalCircleTrace F) θ * conj (H θ) *
                ((Φ0 θ) ^ m / fderiv ℝ F (Φ0 θ) 1) = _
              rw [localConformal_circleTrace_deriv hR F hFs hhol, pow_succ]
              field_simp [hnz (Φ0 θ) (circleMap_mem_closedBall 0 (by norm_num) θ)], intervalIntegral.integral_const_mul] at hJ
            exact (mul_eq_zero.mp hJ).resolve_left Complex.I_ne_zero))
  intro n hn
  cases n with
  | negSucc m => omega
  | ofNat k =>
      cases k with
      | zero => exact False.elim ((lt_irrefl 0) hn)
      | succ m =>
          have hz := hneg m
          rw [physicalMomentCriterion_fourierCoeffOn_conj, neg_neg] at hz
          simpa
            using congrArg conj hz

/-- The actual full physical antiholomorphic moments imply nonpositive
Fourier support of the ORIGINAL density H in the supplied conformal
coordinate.  The primitive extension is constructed, not assumed; the
quotient uses only the actual nonzero closed-disk coordinate differential. -/
theorem localConformal_physicalMoments_nonpositive
     (hb : Bornology.IsBounded Ω) (hΩ : IsLipschitzDomain Ω)
     (hR : 1 < R) F
    (hFs : ContDiffOn ℝ ∞ F (ball 0 R))
    (hhol : DifferentiableOn ℂ F (Φ2))
    (hinj : InjOn F (Φ1))
    (hnz : ∀ z ∈ Φ1, fderiv ℝ F z 1 ≠ 0)
    (himage : F '' Φ2 = Ω)
    H (hH : Continuous H)
    (hpH : Function.Periodic H (2 * Real.pi))
    (hmom : ∀ m : ℕ, (∫ θ in 0..(2 * Real.pi),
      (conj (deriv (physicalCircleTrace F) θ) * H θ) *
        (conj (physicalCircleTrace F θ) - conj (physicalCircleTrace F 0)) ^ m) = 0) :
    IsNonpositiveFourierSupport (fourierCoeffOn Real.two_pi_pos H) := by
  obtain ⟨G, hG, htrace⟩ := exists_localConformal_physicalMomentPrimitive_extension
    hb hΩ hR F hFs hhol hinj hnz himage H hH hpH hmom
  apply physicalMomentDensity_nonpositive_of_primitive_extension hR F hFs hhol hnz H hH
    (by simpa using hmom 0)
    (G ∘ F) (hG.comp (DiffContOnCl.mk_ball hhol (hFs.continuousOn.mono (closedBall_subset_ball hR))) (by
      intro z hz
      rw [← himage]
      exact mem_image_of_mem F hz))
  exact htrace

end PolyaNeumann

end
