module

public import RequestProject.CircleAnalysisNotation

public import RequestProject.DiskCoordinates

public import RequestProject.PhysicalCauchyBoundaryExtension
public import Mathlib.Analysis.Calculus.ContDiff.Comp
public import Mathlib.Analysis.Calculus.FDeriv.RestrictScalars
public import Mathlib.Analysis.Calculus.Deriv.Star
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
public import RequestProject.PlanarNotation

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

open scoped ContDiff

namespace PolyaNeumann

open MeasureTheory Set Metric
open scoped ComplexConjugate Topology

section

variable (Φ : SmoothDiskMap) (hhol : DifferentiableOn ℂ Φ.map unitDisk)
    (hnz : ∀ z ∈ closedDisk, fderiv ℝ Φ.map z 1 ≠ 0) (H : ℝ → ℂ) (hH : Continuous H)
    (hmom0 : (∫ₚ θ, conj (deriv Φ.boundary θ) * H θ) = 0) (P : ℂ → ℂ)
    (hP : DiffContOnCl ℂ P unitDisk)
    (htrace : ∀ θ ∈ angleInterval, P (unitCirclePt θ) = conj (physicalMomentPrimitive Φ.boundary H θ))
    (F : ℂ → ℂ) (m : ℕ) (z : ℂ)

include F z in
/-- The actual complex-linear coefficient of the supplied real differential. -/
def physicalMomentDifferential : ℂ := fderiv ℝ F z 1

include F m z in
/-- The genuine quotient used to test the original physical density. -/
def physicalMomentQuotient : ℂ :=
  z ^ m / physicalMomentDifferential F z

include F m z in
/-- The actual real differential of the quotient evaluated on 1. -/
def physicalMomentQuotientPrime : ℂ :=
  fderiv ℝ (physicalMomentQuotient F m) z 1

private theorem realDifferential_eq_complex_deriv
    {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f unitDisk)
    {z : ℂ} (hz : z ∈ unitDisk) (v : ℂ) :
    fderiv ℝ f z v = deriv f z * v := by
  rw [(hf.differentiableAt (isOpen_ball.mem_nhds hz)).fderiv_restrictScalars ℝ]
  exact fderiv_eq_deriv_mul

/-- Pointwise real smoothness at the closed disk suffices to extend actual
complex linearity of the differential from its open interior. -/
private theorem realDifferential_complex_linear_closedDisk
    (f : ℂ → ℂ) (hf : DifferentiableOn ℂ f unitDisk)
    (hs : ∀ z ∈ closedDisk, ContDiffAt ℝ ∞ f z)
    {z : ℂ} (hz : z ∈ closedDisk) (v : ℂ) :
    fderiv ℝ f z v = fderiv ℝ f z 1 * v := by
  have hc (a : ℂ) : ContinuousOn (fun w => fderiv ℝ f w a) closedDisk := by
    intro w hw
    exact (((hs w hw).continuousAt_fderiv (by simp)).clm_apply continuousAt_const).continuousWithinAt
  have heq : EqOn (fun w => fderiv ℝ f w v)
      (fun w => fderiv ℝ f w 1 * v) unitDisk := by
    intro w hw
    change fderiv ℝ f w v = fderiv ℝ f w 1 * v
    rw [realDifferential_eq_complex_deriv hf hw v,
      realDifferential_eq_complex_deriv hf hw 1, mul_one]
  exact heq.of_subset_closure (hc v) ((by fun_prop))
    ball_subset_closedBall
    (by simpa only [closure_ball (0 : ℂ) (by norm_num : (1 : ℝ) ≠ 0)] using
      (subset_rfl : closedDisk ⊆ closedDisk)) hz

theorem physicalMomentDifferential_contDiffOn {R : ℝ} (F : ℂ → ℂ)
    (hFs : ContDiffOn ℝ ∞ F (ball (0 : ℂ) R)) :
    ContDiffOn ℝ ∞ (physicalMomentDifferential F) (ball (0 : ℂ) R) :=
  (hFs.fderiv_of_isOpen isOpen_ball (by simp)).clm_apply contDiffOn_const

theorem physicalMomentDifferential_holomorphic
    (hhol : DifferentiableOn ℂ F unitDisk) :
    DifferentiableOn ℂ (physicalMomentDifferential F) unitDisk := by
  apply (hhol.deriv isOpen_ball).congr
  intro z hz
  simpa [physicalMomentDifferential] using realDifferential_eq_complex_deriv hhol hz 1

include hnz in
/-- Nonzero closed-disk differential gives actual local smoothness of each
quotient at every closed-disk point; no collar nonvanishing premise is added. -/
theorem physicalMomentQuotient_contDiffAt_closedDisk {z : ℂ} (hz : z ∈ closedDisk) :
    ContDiffAt ℝ ∞ (physicalMomentQuotient Φ.map m) z := by
  have hD := (physicalMomentDifferential_contDiffOn Φ.map Φ.smooth).contDiffAt
    (isOpen_ball.mem_nhds (closedBall_subset_ball Φ.one_lt_radius hz))
  have hp : ContDiffAt ℝ ∞ (fun w : ℂ => w ^ m) z := contDiffAt_id.pow m
  have h := hp.mul (hD.inv (hnz z hz))
  exact h

theorem physicalMomentQuotient_holomorphic
    (hhol : DifferentiableOn ℂ F unitDisk)
    (hnz : ∀ z ∈ closedDisk, fderiv ℝ F z 1 ≠ 0) (m : ℕ) :
    DifferentiableOn ℂ (physicalMomentQuotient F m) unitDisk :=
  (differentiableOn_id.pow m).div (physicalMomentDifferential_holomorphic F hhol)
    (fun z hz => hnz z (ball_subset_closedBall hz))

include hhol hnz in
/-- q and its genuine differentiated coefficient q' are holomorphic in the
open disk and continuous on its closure, proved from actual coordinate data. -/
theorem physicalMomentQuotientPrime_diffContOnCl :
    DiffContOnCl ℂ (physicalMomentQuotientPrime Φ.map m) unitDisk := by
  have hq := physicalMomentQuotient_holomorphic Φ.map hhol hnz m
  have hs (z : ℂ) (hz : z ∈ closedDisk)  :=
    physicalMomentQuotient_contDiffAt_closedDisk Φ hnz m hz
  apply DiffContOnCl.mk_ball
  · apply (hq.deriv isOpen_ball).congr
    intro z hz
    simpa [physicalMomentQuotientPrime] using realDifferential_eq_complex_deriv hq hz 1
  · intro z hz
    exact (((hs z hz).continuousAt_fderiv (by simp)).clm_apply continuousAt_const).continuousWithinAt

include hnz in
theorem physicalMomentQuotient_circle_contDiff :
    ContDiff ℝ 1 (physicalCircleTrace (physicalMomentQuotient Φ.map m)) := by
  apply contDiff_iff_contDiffAt.mpr
  intro θ
  have hz : unitCirclePt θ ∈ closedDisk :=
    circleMap_mem_closedBall 0 (by norm_num) θ
  exact ((physicalMomentQuotient_contDiffAt_closedDisk Φ hnz m hz).of_le
    (WithTop.coe_le_coe.mpr le_top)).comp θ (contDiff_circleMap 0 1).contDiffAt

include hhol hnz in
/-- Actual differentiated angular quotient, including every boundary point. -/
theorem physicalMomentQuotient_circle_hasDerivAt (θ : ℝ) :
    HasDerivAt (physicalCircleTrace (physicalMomentQuotient Φ.map m))
      (physicalMomentQuotientPrime Φ.map m (unitCirclePt θ) *
        (unitCirclePt θ * Complex.I)) θ := by
  have hz : unitCirclePt θ ∈ closedDisk :=
    circleMap_mem_closedBall 0 (by norm_num) θ
  have hs := physicalMomentQuotient_contDiffAt_closedDisk Φ hnz m hz
  have hfd := (hs.differentiableAt (by simp)).hasFDerivAt
  have hd := hfd.comp_hasDerivAt θ (hasDerivAt_circleMap 0 1 θ)
  rw [realDifferential_complex_linear_closedDisk (physicalMomentQuotient Φ.map m)
    (physicalMomentQuotient_holomorphic Φ.map hhol hnz m)
    (fun z hz => physicalMomentQuotient_contDiffAt_closedDisk Φ hnz m hz) hz] at hd
  exact hd

include hH hP hhol hmom0 hnz htrace in
/-- Boundary integration by parts tests the original density against every
positive circle power.  The disk extension is required only to be holomorphic
inside and continuous on the closure; its boundary derivative is not assumed. -/
theorem physicalMomentDensity_circle_moment_eq_zero_of_primitive_extension :
    (∫ₚ θ, conj (H θ) * (unitCirclePt θ) ^ (m + 1)) = 0 := by
  let γ := Φ.boundary
  let K := physicalMomentPrimitive γ H
  let u  := fun θ => conj (K θ)
  let u'  := fun θ => deriv γ θ * conj (H θ)
  let q := physicalMomentQuotient Φ.map m
  let v := physicalCircleTrace q
  let v'  := fun θ => physicalMomentQuotientPrime Φ.map m (unitCirclePt θ) *
    (unitCirclePt θ * Complex.I)
  have hγ  :=
    Φ.boundaryC1
  have hK  := contDiff_physicalMomentPrimitive γ H hγ hH
  have hu : Continuous u := Complex.continuous_conj.comp hK.continuous
  have hu'  :=
    hγ.continuous_deriv_one.mul (Complex.continuous_conj.comp hH)
  have hdu (θ : ℝ) : HasDerivAt u (u' θ) θ := by
    simpa only [u, u', Complex.star_def, map_mul, Complex.conj_conj] using
      (physicalMomentPrimitive_hasDerivAt γ H hγ hH θ).star
  have hv  := physicalMomentQuotient_circle_contDiff Φ hnz m
  have hdv (θ : ℝ) : HasDerivAt v (v' θ) θ :=
    physicalMomentQuotient_circle_hasDerivAt Φ hhol hnz m θ
  have hveq : deriv v = v' := by
    funext θ
    exact (hdv θ).deriv
  have hv' : Continuous v' := by
    rw [← hveq]
    exact hv.continuous_deriv_one
  have hu0 : u 0 = 0 := by simp [u, K, physicalMomentPrimitive_zero, map_zero]
  have huL : u anglePeriod = 0 := by
    dsimp only [u, K]
    rw [physicalMomentPrimitive_endpoint γ H hmom0, map_zero]
  have hcauchy : circleIntegral (fun z => P z * physicalMomentQuotientPrime Φ.map m z) 0 1 = 0 :=
    DiffContOnCl.circleIntegral_eq_zero (by norm_num)
      ⟨hP.differentiableOn.mul
          (physicalMomentQuotientPrime_diffContOnCl Φ hhol hnz m).differentiableOn,
        hP.continuousOn.mul
          (physicalMomentQuotientPrime_diffContOnCl Φ hhol hnz m).continuousOn⟩
  have hceq : circleIntegral (fun z => P z * physicalMomentQuotientPrime Φ.map m z) 0 1 =
      ∫ₚ θ, u θ * v' θ := by
    rw [circleIntegral]
    apply intervalIntegral.integral_congr
    intro θ hθ
    rw [uIcc_of_le Real.two_pi_pos.le] at hθ
    simp
    rw [htrace θ hθ]
    ring
  rw [hceq] at hcauchy
  have hi := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
    hu.continuousOn hv.continuous.continuousOn (fun θ _ => hdu θ) (fun θ _ => hdv θ)
    (hu'.intervalIntegrable 0 anglePeriod) (hv'.intervalIntegrable 0 anglePeriod)
  simp only [hcauchy, huL, hu0, zero_mul, sub_self, zero_sub] at hi
  have hJ  := neg_eq_zero.mp hi.symm
  have heq : (fun θ => u' θ * v θ) =
      (fun θ => Complex.I * (conj (H θ) * (unitCirclePt θ) ^ (m + 1))) := by
    funext θ
    change (deriv Φ.boundary θ * conj (H θ)) *
      ((unitCirclePt θ) ^ m / fderiv ℝ Φ.map (unitCirclePt θ) 1) =
        Complex.I * (conj (H θ) * (unitCirclePt θ) ^ (m + 1))
    rw [localConformal_circleTrace_deriv Φ hhol, pow_succ]
    have hD := hnz (unitCirclePt θ) (circleMap_mem_closedBall 0 (by norm_num) θ)
    field_simp [hD]
  rw [heq, intervalIntegral.integral_const_mul] at hJ
  exact (mul_eq_zero.mp hJ).resolve_left Complex.I_ne_zero

include hH hP hhol hmom0 hnz htrace in
/-- The actual primitive extension implies support of the original density,
through the proved physical quotient and boundary integration by parts. -/
theorem physicalMomentDensity_nonpositive_of_primitive_extension :
    IsNonpositiveFourierSupport (angleCoeff H) := by
  have hneg (m : ℕ) : angleCoeff (fun θ => conj (H θ))
      (-((m + 1 : ℕ) : ℤ)) = 0 := by
    have hm := physicalMomentDensity_circle_moment_eq_zero_of_primitive_extension
      Φ hhol hnz H hH hmom0 P hP htrace m
    have hi : (∫ₚ θ,
        fourier  ((m + 1 : ℕ) : ℤ)
          (θ : ParamCircle) * conj (H θ)) = 0 := by
      calc
        _ = ∫ₚ θ, conj (H θ) * (unitCirclePt θ) ^ (m + 1) := by
          apply intervalIntegral.integral_congr
          intro θ _
          change fourier (T := anglePeriod) ((m + 1 : ℕ) : ℤ)
            (θ : ParamCircle) * conj (H θ) =
              conj (H θ) * (unitCirclePt θ) ^ (m + 1)
          rw [fourier_natCast_eq_pow]
          ring
        _ = 0 := hm
    rw [fourierCoeffOn_eq_integral]
    simp only [sub_zero, neg_neg, smul_eq_mul]
    simpa only [fourier_coe_apply, sub_zero, smul_zero] using
      congrArg (fun z : ℂ => (1 / anglePeriod : ℝ) • z) hi
  intro n hn
  cases n with
  | negSucc m => omega
  | ofNat k =>
      cases k with
      | zero => exact False.elim ((lt_irrefl (0 : ℤ)) hn)
      | succ m =>
          have hz := hneg m
          rw [fourierCoeffOn_conj_volume, neg_neg] at hz
          have hz' := congrArg conj hz
          simpa using hz'

end

/-- The actual full physical antiholomorphic moments imply nonpositive
Fourier support of the ORIGINAL density H in the supplied conformal
coordinate.  The primitive extension is constructed, not assumed; the
quotient uses only the actual nonzero closed-disk coordinate differential. -/
theorem localConformal_physicalMoments_nonpositive {Ω : Set ℂ}
    (hb : Bornology.IsBounded Ω) (hΩ : IsLipschitzDomain Ω) (Φ : SmoothDiskMap)
    (hhol : DifferentiableOn ℂ Φ.map unitDisk) (hinj : InjOn Φ.map closedDisk)
    (hnz : ∀ z ∈ closedDisk, fderiv ℝ Φ.map z 1 ≠ 0) (himage : Φ.domain = Ω) (H : ℝ → ℂ)
    (hH : Continuous H) (hpH : Function.Periodic H anglePeriod)
    (hmom : ∀ m : ℕ, (∫ₚ θ,
      (conj (deriv Φ.boundary θ) * H θ) *
        (conj (Φ.boundary θ) - conj (Φ.boundary 0)) ^ m) = 0) :
    IsNonpositiveFourierSupport (angleCoeff H) := by
  obtain ⟨G, hG, htrace⟩ := exists_localConformal_physicalMomentPrimitive_extension
    hb hΩ Φ hhol hinj hnz himage H hH hpH hmom
  have hF  :=
    DiffContOnCl.mk_ball hhol (Φ.smooth.continuousOn.mono (closedBall_subset_ball Φ.one_lt_radius))
  have hmaps : MapsTo Φ.map unitDisk Ω := by
    intro z hz
    rw [← himage]
    exact mem_image_of_mem Φ.map hz
  apply physicalMomentDensity_nonpositive_of_primitive_extension Φ hhol hnz H hH
    (by simpa only [pow_zero, mul_one] using hmom 0)
    (G ∘ Φ.map) (hG.comp hF hmaps)
  exact htrace

end PolyaNeumann

end
