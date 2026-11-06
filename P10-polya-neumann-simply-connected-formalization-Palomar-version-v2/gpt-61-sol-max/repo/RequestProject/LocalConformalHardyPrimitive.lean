module

public import RequestProject.DiskHardyExtension


public import RequestProject.PlanarTypes
public import RequestProject.CirclePeriod

public import RequestProject.PlanarGeometry

public import RequestProject.ConormalNormalization
public import RequestProject.PhysicalHardyWeights
public import RequestProject.HardyPrimitiveTrace
public import RequestProject.DiskHardyDerivative
public import RequestProject.LocalConformalHardyExtension
public import RequestProject.NeumannH1SmoothMultiplier
public import RequestProject.LocalConformalArcReparam
public import RequestProject.BoundaryFourierMultiplier
public import RequestProject.NeumannHardyTraceInjective
public import RequestProject.LocalConformalGradientComponents

/-!
# Actual Hardy multiplication and the normalized primitive

The primitive on normalized half-trace data is constructed from the proved
half-order sequence bound. Its gain of one order factors through the genuine
circle smoothing operator, so its disk extension has an actual L² derivative.

Multiplication of the actual disk Hardy extension by a compact smooth
coefficient has the proved weak product rule and the actual boundary trace
product rule. The coefficient conjugate to the conformal derivative is an
explicit derivative of a genuine smooth cutoff; its antiholomorphic CR
identity follows from interior holomorphicity of the supplied map.
-/

@[expose] public section

open scoped ContDiff


noncomputable section

namespace PolyaNeumann

open MeasureTheory Set Metric Filter
open scoped Topology ComplexConjugate



/-- Averaged coefficients of an actual half-trace vector. -/
def normalizedHardyAverage b n  :=
  (Real.sqrt circlePeriod : ℂ)⁻¹ * fromL2 (1 / 2 : ℝ) b n

/-- Bounded multiplication on normalized half-order Fourier coordinates.
The multiplier coefficients use the averaged convention. -/
def normalizedHardyMultiplier c (hc : IsWL1 (1 / 2 : ℝ) c)  :=
  (seqOpBound_seqConv (by norm_num : (0 : ℝ) ≤ 1 / 2) hc).toCLM

theorem normalizedHardyMultiplier_apply c
    hc b n :
    normalizedHardyMultiplier c hc b n =
      ((sobWeight n ^ (1 / 2 : ℝ) : ℝ) : ℂ) * seqConv c (fromL2 (1 / 2 : ℝ) b) n :=
  common_multiplier_toCLM_apply _ b n

/-- The primitive in the stronger normalized coordinates of order 3/2. -/
def normalizedHardyPrimitiveGain a (ha : IsWL1 (1 / 2 : ℝ) a)  :=
  (seqOpBound_antiPrim (by norm_num : (0 : ℝ) ≤ 1 / 2) ha).toCLM

section
variable (a ) (ha : IsWL1 (1 / 2 : ℝ) a)

include a ha in
theorem normalizedHardyPrimitiveGain_apply b n :
    normalizedHardyPrimitiveGain a ha b n =
      ((sobWeight n ^ ((1 / 2 : ℝ) + 1) : ℝ) : ℂ) *
        antiPrim a (fromL2 (1 / 2 : ℝ) b) n :=
  common_multiplier_toCLM_apply _ b n

/-- The actual normalized primitive at order 1/2, retaining the constant
chosen by `antiPrim` at the same boundary origin. -/
def normalizedHardyPrimitive a ha  :=
  (sobolevSmoothing 1 (by norm_num)).comp (normalizedHardyPrimitiveGain a ha)

section
include a ha

theorem normalizedHardyPrimitive_apply b n :
    normalizedHardyPrimitive a ha b n =
      ((sobWeight n ^ (1 / 2 : ℝ) : ℝ) : ℂ) * antiPrim a (fromL2 (1 / 2 : ℝ) b) n := by
  change sobolevSmoothing 1 (by norm_num) (normalizedHardyPrimitiveGain a ha b) n = _
  simp  [sobolevSmoothing, normalizedHardyPrimitiveGain_apply]
  rw [← mul_assoc, ← Complex.ofReal_mul, ← Real.rpow_add (sobWeight_pos n)]
  simp_all

theorem normalizedHardyPrimitive_nonpositive (han : IsStrictNegativeFourierSupport a)
    (b : L2Z) (hbn : IsNonpositiveFourierSupport b) :
    IsNonpositiveFourierSupport (normalizedHardyPrimitive a ha b) := by
  have hb : IsNonpositiveFourierSupport (fromL2 (1 / 2 : ℝ) b) := by
    simp_all [fromL2, PolyaNeumann.IsNonpositiveFourierSupport]
  intro n hn
  rw [normalizedHardyPrimitive_apply, antiPrim_nonpositive han hb n hn, mul_zero]

/-- Actual L² derivative of the completed disk primitive. This identifies
the derivative with the completed derivative data, before a product is
identified using the genuine Hardy trace uniqueness theorem. -/
theorem diskHardyExtension_normalizedPrimitive_gradient b :
    h1Gradient unitDisk 0 (diskHardyExtension (normalizedHardyPrimitive a ha b)) =
      h1Value unitDisk
        (diskHardyExtension (diskHardyDerivativeData (normalizedHardyPrimitiveGain a ha b))) :=
  diskHardyExtension_smoothing_gradient (normalizedHardyPrimitiveGain a ha b)

end


end


/-- Genuine disk H¹ multiplication of the actual completed Hardy extension. -/
def diskHardySmoothProduct (a : SmoothH1Coefficient) :
    L2Z →L[ℂ] NeumannH1 unitDisk :=
  (neumannH1SmoothMultiplier unitDisk a).comp diskHardyExtension

theorem h1Value_diskHardySmoothProduct a b :
    h1Value unitDisk (diskHardySmoothProduct a b) =
      h1SmoothCoefficientL2 unitDisk a
        (h1Value unitDisk (diskHardyExtension b)) :=
  h1Value_neumannH1SmoothMultiplier _ a _

theorem h1Gradient_diskHardySmoothProduct a b i :
    h1Gradient unitDisk i (diskHardySmoothProduct a b) =
      h1SmoothCoefficientL2 unitDisk a
          (h1Gradient unitDisk i (diskHardyExtension b)) +
        h1SmoothCoefficientDerivativeL2 unitDisk a i
          (h1Value unitDisk (diskHardyExtension b)) :=
  h1Gradient_neumannH1SmoothMultiplier _ a _ i

section
variable (a : SmoothH1Coefficient) (hCR : ∀ z ∈ unitDisk,
      fderiv ℝ (a : PlaneMap) z 1 = Complex.I * fderiv ℝ (a : PlaneMap) z Complex.I)

include a hCR in
private theorem hardy_coefficient_derivative_CR
    u :
    h1SmoothCoefficientDerivativeL2 unitDisk a 0 u =
      Complex.I • h1SmoothCoefficientDerivativeL2 unitDisk a 1 u := by
  apply Lp.ext
  filter_upwards [h1SmoothCoefficientDerivativeL2_ae (ball 0 1) a 0 u,
    h1SmoothCoefficientDerivativeL2_ae (ball 0 1) a 1 u,
    Lp.coeFn_smul Complex.I (h1SmoothCoefficientDerivativeL2 (ball 0 1) a 1 u),
    ae_restrict_mem measurableSet_ball] with z hx hy hs hz
  rw [hx, hs]
  simp_all [ PolyaNeumann.coordDir, PolyaNeumann.L2] <;> ring

include a hCR in
/-- An actual smooth antiholomorphic coefficient preserves the genuine
weak CR equation of the completed disk Hardy extension. -/
theorem diskHardySmoothProduct_cauchyRiemann
    b :
    h1Gradient unitDisk 0 (diskHardySmoothProduct a b) =
      Complex.I • h1Gradient unitDisk 1 (diskHardySmoothProduct a b) := by
  rw [h1Gradient_diskHardySmoothProduct, h1Gradient_diskHardySmoothProduct,
    diskHardyExtension_cauchyRiemann, map_smul,
    hardy_coefficient_derivative_CR a hCR, smul_add]

/-- The actual compact coefficient conjugate to the supplied conformal
derivative. It is smooth globally because the actual F is cut off first. -/
def localConformalHardyDerivativeTest {R : ℝ} (hR : 1 < R) (F : PlaneMap)
    (hFs : RealSmoothOnBall F R) : smoothTraceTests :=
  ⟨fun z => conj (dirD (smoothDiskCutoff R hR F) 1 z),
    ((smoothDiskCutoff_testFunction hR hFs).dirD 1).conj⟩

def localConformalHardyDerivativeCoefficient {R : ℝ} (hR : 1 < R) (F : PlaneMap)
    (hFs : RealSmoothOnBall F R) : SmoothH1Coefficient :=
  smoothTraceTestsH1Coefficient (localConformalHardyDerivativeTest hR F hFs)

section
variable {R } (hR : 1 < R) (F : PlaneMap) (hFs : RealSmoothOnBall F R)

include R hR F hFs in
theorem localConformalHardyDerivativeCoefficient_closedDisk
     (hz : z ∈ closedUnitDisk) :
    localConformalHardyDerivativeCoefficient hR F hFs z = conj (fderiv ℝ F z 1) := by
  change conj (fderiv ℝ (smoothDiskCutoff R hR F) z 1) = _
  rw [fderiv_smoothDiskCutoff_eq hR F hz]

private theorem hardy_real_derivative_of_holomorphic {U } (hU : IsOpen U)
    {F } (hF : DifferentiableOn ℂ F U) {z } (hz : z ∈ U) (v : ℂ) :
    fderiv ℝ F z v = deriv F z * v := by
  rw [(hF.differentiableAt (hU.mem_nhds hz)).fderiv_restrictScalars ℝ]
  exact fderiv_eq_deriv_mul

section
include R hR F hFs

/-- The actual cutoff coefficient has the derivative of conj(F′) in the
interior, derived from holomorphic F′ and its real chain rule. -/
theorem localConformalHardyDerivativeCoefficient_fderiv
    (hhol : DifferentiableOn ℂ F unitDisk)
     (hz : z ∈ unitDisk) v :
    fderiv ℝ (localConformalHardyDerivativeCoefficient hR F hFs : PlaneMap) z v =
      conj (deriv (deriv F) z * v) := by
  have he : (localConformalHardyDerivativeCoefficient hR F hFs : PlaneMap)
      =ᶠ[𝓝 z] fun w => conj (deriv F w) := by
    filter_upwards [isOpen_ball.mem_nhds hz] with w hw
    rw [localConformalHardyDerivativeCoefficient_closedDisk hR F hFs (ball_subset_closedBall hw),
      hardy_real_derivative_of_holomorphic isOpen_ball hhol hw 1, mul_one]
  rw [he.fderiv_eq (𝕜 := ℝ)]
  have hd := (hhol.deriv isOpen_ball).differentiableAt (isOpen_ball.mem_nhds hz)
  have h := (Complex.conjCLE.hasFDerivAt.comp z (hd.restrictScalars ℝ).hasFDerivAt).fderiv
  rw [show (fun w => conj (deriv F w)) = Complex.conjCLE ∘ deriv F from rfl, h]
  change conj (fderiv ℝ (deriv F) z v) = _
  rw [hardy_real_derivative_of_holomorphic isOpen_ball (hhol.deriv isOpen_ball) hz v]

theorem localConformalHardyDerivativeCoefficient_cauchyRiemann
    (hhol : DifferentiableOn ℂ F unitDisk)  (hz : z ∈ unitDisk) :
    fderiv ℝ (localConformalHardyDerivativeCoefficient hR F hFs : PlaneMap) z 1 =
      Complex.I * fderiv ℝ
        (localConformalHardyDerivativeCoefficient hR F hFs : PlaneMap) z Complex.I := by
  rw [localConformalHardyDerivativeCoefficient_fderiv hR F hFs hhol hz 1,
    localConformalHardyDerivativeCoefficient_fderiv hR F hFs hhol hz Complex.I]
  simp  
  calc
    conj (deriv (deriv F) z) = -(Complex.I * Complex.I) * conj (deriv (deriv F) z) := by
      simp
    _ = _ := by ring

end


/-- The genuine disk product needed for the interior physical primitive. -/
def localConformalHardyDerivativeProduct {R : ℝ} (hR : 1 < R) (F : PlaneMap)
    (hFs : RealSmoothOnBall F R) :
    L2Z →L[ℂ] NeumannH1 unitDisk :=
  diskHardySmoothProduct (localConformalHardyDerivativeCoefficient hR F hFs)

/-- Actual angular-velocity multiplier data for the primitive. -/
def localConformalHardyPrimitiveMultiplier F  :=
  fourierCoeffOn Real.two_pi_pos (fun θ => conj (deriv (physicalCircleTrace F) θ))

section
include R hR F hFs

theorem localConformalHardyPrimitiveMultiplier_isWL1 :
    IsWL1 (1 / 2 : ℝ) (localConformalHardyPrimitiveMultiplier F) := by
  have h1 := (physicalCircleTrace_fourier_weights_of_smooth_neighborhood hR F hFs).1
  refine h1.of_nonneg_of_le (fun n => ?_) (fun n => ?_)
  · exact mul_nonneg (Real.rpow_nonneg (sobWeight_pos n).le _) (norm_nonneg _)
  · exact mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow_of_exponent_le (one_le_sobWeight n) (by norm_num)) (norm_nonneg _)

theorem localConformalHardyPrimitiveMultiplier_strictNegative
    (hhol : DifferentiableOn ℂ F unitDisk) :
    IsStrictNegativeFourierSupport (localConformalHardyPrimitiveMultiplier F) :=
  physicalCircleTrace_conj_deriv_strictNegative_of_neighborhood hR F
    (hFs.of_le (by simp)) hhol

end


/-- The actual supplied-coordinate primitive on normalized half-trace data. -/
def localConformalHardyPrimitive {R : ℝ} (hR : 1 < R) (F : PlaneMap)
    (hFs : RealSmoothOnBall F R) : L2Z →L[ℂ] L2Z :=
  normalizedHardyPrimitive (localConformalHardyPrimitiveMultiplier F)
    (localConformalHardyPrimitiveMultiplier_isWL1 hR F hFs)

private theorem hardy_fourier_one_circle (θ : ℝ) :
    fourier (T := 2 * Real.pi) 1 (θ : AddCircle circlePeriod) = unitCircleMap θ := by
  rw [fourier_coe_two_pi, circleMap_zero]
  norm_num

/-- The actual boundary coefficient as a continuous circle function. -/
def diskSmoothCoefficientCircle (a : SmoothH1Coefficient) :
    C(AddCircle circlePeriod, ℂ) :=
  ⟨fun q => a (fourier (T := 2 * Real.pi) 1 q),
    a.smooth.continuous.comp (fourier (T := 2 * Real.pi) 1).continuous⟩

theorem diskSmoothCoefficientCircle_apply a (θ : ℝ) :
    diskSmoothCoefficientCircle a (θ : AddCircle circlePeriod) = a (unitCircleMap θ) := by
  change a (fourier (T := 2 * Real.pi) 1 θ) = _
  rw [hardy_fourier_one_circle]

private theorem hardy_fourierCoeffOn_circle (A : C(AddCircle circlePeriod, ℂ)) n :
    fourierCoeffOn Real.two_pi_pos (fun θ : ℝ => A (θ : AddCircle circlePeriod)) n =
      fourierCoeff A n := by
  have he : AddCircle.liftIoc circlePeriod 0
      (fun θ : ℝ => A (θ : AddCircle circlePeriod)) = (A : AddCircle circlePeriod → ℂ) := by
    funext q
    change A ((AddCircle.equivIoc circlePeriod 0 q)) = A q
    simp_all
  have h := fourierCoeff_liftIoc_eq (T := 2 * Real.pi) (a := 0)
    (fun θ : ℝ => A θ) n
  simp_all

theorem diskSmoothCoefficientCircle_coeff a n :
    fourierCoeff (diskSmoothCoefficientCircle a) n =
      fourierCoeffOn Real.two_pi_pos (fun θ => a (unitCircleMap θ)) n := by
  grind only [hardy_fourierCoeffOn_circle, diskSmoothCoefficientCircle_apply]

theorem diskSmoothCoefficientCircle_isWL1 a :
    IsWL1 (1 / 2 : ℝ) (fourierCoeff (diskSmoothCoefficientCircle a)) := by
  have hf : ContDiff ℝ 4 (fun θ : ℝ => a (unitCircleMap θ)) :=
    (a.smooth.of_le (WithTop.coe_le_coe.mpr le_top)).comp (contDiff_circleMap 0 1)
  have hp  :=
    (periodic_circleMap 0 1).comp a
  have h2 := (periodic_contDiff_four_fourier_weights hf hp).2
  change Summable (fun n => sobWeight n ^ (1 / 2) *
    ‖fourierCoeff (diskSmoothCoefficientCircle a) n‖)
  simp_rw [diskSmoothCoefficientCircle_coeff]
  refine h2.of_nonneg_of_le (fun n => ?_) (fun n => ?_)
  · exact mul_nonneg (Real.rpow_nonneg (sobWeight_pos n).le _) (norm_nonneg _)
  · exact mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow_of_exponent_le (one_le_sobWeight n) (by norm_num)) (norm_nonneg _)

private theorem hardy_fourierCoeff_shift (C : C(AddCircle circlePeriod, ℂ)) n :
    fourierCoeff (fun q => fourier (T := 2 * Real.pi) (-1) q * C q) n =
      fourierCoeff C (n + 1) := by
  apply integral_congr_ae
  exact Eventually.of_forall (fun q => by
    change fourier (T := 2 * Real.pi) (-n) q *
      (fourier (T := 2 * Real.pi) (-1) q * C q) =
        fourier (T := 2 * Real.pi) (-(n + 1)) q * C q
    rw [← mul_assoc, ← fourier_add]
    ring)

section
include R hR F hFs

/-- The conjugated angular velocity has precisely the shifted coefficient
of conj(F′), including its phase -i. -/
theorem localConformalHardyPrimitiveMultiplier_shift
    (hhol : DifferentiableOn ℂ F unitDisk) n :
    localConformalHardyPrimitiveMultiplier F n = (-Complex.I) *
      fourierCoeff (diskSmoothCoefficientCircle
        (localConformalHardyDerivativeCoefficient hR F hFs)) (n + 1) := by
  let C := diskSmoothCoefficientCircle (localConformalHardyDerivativeCoefficient hR F hFs)
  let B  := (-Complex.I) •
    ((fourier (T := 2 * Real.pi) (-1)) * C)
  have he (θ : ℝ) : conj (deriv (physicalCircleTrace F) θ) =
      B (θ : AddCircle circlePeriod) := by
    rw [localConformal_circleTrace_deriv hR F hFs hhol]
    simp  
    simp only [B, ContinuousMap.smul_apply, ContinuousMap.mul_apply]
    rw [fourier_neg, hardy_fourier_one_circle, diskSmoothCoefficientCircle_apply,
      localConformalHardyDerivativeCoefficient_closedDisk hR F hFs
        (circleMap_mem_closedBall 0 (by norm_num) θ)]
    ring
  change fourierCoeffOn Real.two_pi_pos
    (fun θ => conj (deriv (physicalCircleTrace F) θ)) n = _
  rw [(funext he),
    hardy_fourierCoeffOn_circle]
  change fourierCoeff ((-Complex.I) •
    (fun q => fourier (T := 2 * Real.pi) (-1) q * C q)) n = _
  rw [fourierCoeff.const_smul]
  simp only [smul_eq_mul]
  rw [hardy_fourierCoeff_shift]

theorem localConformalHardyDerivativeCoefficient_nonpositive
    (hhol : DifferentiableOn ℂ F unitDisk) :
    IsNonpositiveFourierSupport (fourierCoeff (diskSmoothCoefficientCircle
      (localConformalHardyDerivativeCoefficient hR F hFs))) := by
  intro n hn
  have ha := localConformalHardyPrimitiveMultiplier_strictNegative hR F hFs hhol
    (n - 1) (by omega)
  rw [localConformalHardyPrimitiveMultiplier_shift hR F hFs hhol,
    sub_add_cancel] at ha
  simp_all

end


end


private theorem hardy_seqConv_nonpositive 
    (hc : IsNonpositiveFourierSupport c) (hh : IsNonpositiveFourierSupport h) :
    IsNonpositiveFourierSupport (seqConv c h) := by
  intro n hn
  unfold seqConv
  have he : (fun k => c k * h (n - k)) = (fun _ : ℤ => (0 : ℂ)) := by
    funext k
    by_cases hk : 0 < k
    · rw [hc k hk, zero_mul]
    · rw [hh (n - k) (by omega), mul_zero]
  rw [he, tsum_zero]

private theorem hardy_seqConv_shift {a c }
    (hshift : ∀ n : ℤ, a n = (-Complex.I) * c (n + 1)) h n :
    seqConv a h (n - 1) = (-Complex.I) * seqConv c h n := by
  unfold seqConv
  calc
    _ = (-Complex.I) * ∑' k : ℤ, c (k + 1) * h (n - (k + 1)) := by
      rw [← tsum_mul_left]
      grind
    _ = _ := congrArg (fun x : ℂ => (-Complex.I) * x)
      ((Equiv.addRight 1).tsum_eq (fun k => c k * h (n - k)))

private theorem hardy_primitive_derivative_scalar x y sx sy
    (hx : x ≠ 0) (hy : y ≠ 0) (hsy : sy ≠ 0) :
    (x / y * (sx / sy)) * ((sy * y) / (Complex.I * (-x))) * (-Complex.I) = sx := by
  field_simp 

private theorem hardy_primitive_derivative_scale k :
    (diskHardyDerivativeWeight k : ℂ) *
        (((sobWeight (-((k + 1 : ℕ) : ℤ)) ^ ((1 / 2 : ℝ) + 1) : ℝ) : ℂ) /
          (Complex.I * (-((k + 1 : ℕ) : ℂ)))) * (-Complex.I) =
      ((sobWeight (-(k : ℤ)) ^ (1 / 2 : ℝ) : ℝ) : ℂ) := by
  rw [common_hardy_sobWeight_neg_nat, common_hardy_sobWeight_neg_nat]
  have hy : (((k + 1 + 1 : ℕ) : ℝ) ^ ((1 / 2 : ℝ) + 1)) =
      Real.sqrt ((k + 2 : ℕ) : ℝ) * ((k + 2 : ℕ) : ℝ) := by
    have hi : k + 1 + 1 = k + 2 := by omega
    rw [hi, Real.rpow_add (by positivity), Real.rpow_one, ← Real.sqrt_eq_rpow]
  rw [hy, ← Real.sqrt_eq_rpow]
  simp only [diskHardyDerivativeWeight, Real.sqrt_div (by positivity : (0 : ℝ) ≤ ((k + 1 : ℕ) : ℝ))]
  have hx : ((k + 1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (by omega : k + 1 ≠ 0)
  have hy0 : ((k + 2 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (by omega : k + 2 ≠ 0)
  have hsy : (Real.sqrt ((k + 2 : ℕ) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr (by positivity)).ne'
  simpa   using
    hardy_primitive_derivative_scalar ((k + 1 : ℕ)) ((k + 2 : ℕ))
      (Real.sqrt ((k + 1 : ℕ))) (Real.sqrt ((k + 2 : ℕ)))
      hx hy0 hsy

/-- The actual derivative-data operator on a normalized primitive is the
actual normalized product data. The input and product retain frequency zero. -/
theorem diskHardyDerivativeData_normalizedPrimitiveGain
    a c ha hc
    (hshift : ∀ n : ℤ, a n = (-Complex.I) * c (n + 1))
    (hcn : IsNonpositiveFourierSupport c) (b : L2Z)
    (hbn : IsNonpositiveFourierSupport b) :
    diskHardyDerivativeData (normalizedHardyPrimitiveGain a ha b) =
      normalizedHardyMultiplier c hc b := by
  have hb : IsNonpositiveFourierSupport (fromL2 (1 / 2 : ℝ) b) := by
    simp_all [fromL2, PolyaNeumann.IsNonpositiveFourierSupport]
  ext n
  by_cases hn : 0 < n
  · rw [diskHardyDerivativeData_apply_pos _ hn, normalizedHardyMultiplier_apply,
      hardy_seqConv_nonpositive hcn hb n hn, mul_zero]
  · let k  := Int.toNat (-n)
    have hnk : n = -(k : ℤ) := by omega
    rw [hnk, diskHardyDerivativeData_apply_neg, normalizedHardyPrimitiveGain_apply,
      normalizedHardyMultiplier_apply]
    have hne : -((k + 1 : ℕ) : ℤ) ≠ 0 := by omega
    rw [antiPrim, if_neg hne, primSeq]
    have hi : -(k : ℤ) - 1 = -((k + 1 : ℕ) : ℤ) := by omega
    have hconv := hardy_seqConv_shift hshift (fromL2 (1 / 2) b) (-k)
    rw [hi] at hconv
    rw [hconv]
    simp only [Int.cast_neg, Int.cast_natCast]
    grind only [diskHardyDerivativeWeight, sobWeight, seqConv, fromL2, hardy_primitive_derivative_scale, PolyaNeumann.diskHardyDerivativeWeight, PolyaNeumann.sobWeight, PolyaNeumann.seqConv]

theorem normalizedHardyMultiplier_nonpositive c
    hc (hcn : IsNonpositiveFourierSupport c)
    (b : L2Z) (hbn : IsNonpositiveFourierSupport b) :
    IsNonpositiveFourierSupport (normalizedHardyMultiplier c hc b) := by
  have hb : IsNonpositiveFourierSupport (fromL2 (1 / 2 : ℝ) b) := by
    simp_all [fromL2, PolyaNeumann.IsNonpositiveFourierSupport]
  intro n hn
  rw [normalizedHardyMultiplier_apply, hardy_seqConv_nonpositive hcn hb n hn, mul_zero]

private theorem hardy_trace_eq_of_halfTrace_eq
    u v (h : diskHalfTrace u = diskHalfTrace v) :
    diskH1Trace u = diskH1Trace v := by
  apply boundaryFourier.injective
  apply lp.ext
  rw [← fromL2_half_diskHalfTrace, ← fromL2_half_diskHalfTrace, h]

include a hCR in
/-- The actual completed antiholomorphic product is identified with its
completed Fourier extension by the proved weak CR trace uniqueness theorem. -/
theorem diskHardySmoothProduct_eq_extension
    (hcn : IsNonpositiveFourierSupport (fourierCoeff (diskSmoothCoefficientCircle a)))
    (b : L2Z) (hbn : IsNonpositiveFourierSupport b) :
    diskHardySmoothProduct a b = diskHardyExtension
      (normalizedHardyMultiplier (fourierCoeff (diskSmoothCoefficientCircle a))
        (diskSmoothCoefficientCircle_isWL1 a) b) := by
  apply neumannH1_eq_of_antiholomorphic_same_trace unitDisk_bounded
    isLipschitzDomain_unitDisk unitCircle_isBoundaryParam
  · exact diskHardySmoothProduct_cauchyRiemann a hCR b
  · exact diskHardyExtension_cauchyRiemann _
  · apply hardy_trace_eq_of_halfTrace_eq
    have hp := diskHalfTrace_smoothMultiplier a (diskSmoothCoefficientCircle a)
      (diskSmoothCoefficientCircle_apply a) (diskSmoothCoefficientCircle_isWL1 a)
      (diskHardyExtension b)
    rw [diskHalfTrace_diskHardyExtension_eq_of_nonpositive b hbn] at hp
    rw [diskHalfTrace_diskHardyExtension_eq_of_nonpositive _
      (normalizedHardyMultiplier_nonpositive _ _ hcn b hbn)]
    exact hp

end


section
variable {R } (hR : 1 < R) (F : PlaneMap) (hFs : RealSmoothOnBall F R) (hhol : DifferentiableOn ℂ F unitDisk) (b : L2Z) (hbn : IsNonpositiveFourierSupport b)
include R hR F hFs hhol b hbn

theorem localConformalHardyDerivativeProduct_eq_extension :
    localConformalHardyDerivativeProduct hR F hFs b = diskHardyExtension
      (normalizedHardyMultiplier
        (fourierCoeff (diskSmoothCoefficientCircle
          (localConformalHardyDerivativeCoefficient hR F hFs)))
        (diskSmoothCoefficientCircle_isWL1
          (localConformalHardyDerivativeCoefficient hR F hFs)) b) :=
  diskHardySmoothProduct_eq_extension _
    (fun _ hz => localConformalHardyDerivativeCoefficient_cauchyRiemann hR F hFs hhol hz)
    (localConformalHardyDerivativeCoefficient_nonpositive hR F hFs hhol) b hbn

/-- Actual disk x derivative of the normalized physical primitive. The
derivative multiplier is the compact smooth representative of conj(F′). -/
theorem diskHardyExtension_localConformalPrimitive_gradient :
    h1Gradient unitDisk 0
        (diskHardyExtension (localConformalHardyPrimitive hR F hFs b)) =
      h1SmoothCoefficientL2 unitDisk
        (localConformalHardyDerivativeCoefficient hR F hFs)
          (h1Value unitDisk (diskHardyExtension b)) := by
  change h1Gradient (ball 0 1) 0 (diskHardyExtension
    (normalizedHardyPrimitive (localConformalHardyPrimitiveMultiplier F)
      (localConformalHardyPrimitiveMultiplier_isWL1 hR F hFs) b)) = _
  rw [diskHardyExtension_normalizedPrimitive_gradient,
    diskHardyDerivativeData_normalizedPrimitiveGain _ _ _
      (diskSmoothCoefficientCircle_isWL1 (localConformalHardyDerivativeCoefficient hR F hFs))
      (localConformalHardyPrimitiveMultiplier_shift hR F hFs hhol)
      (localConformalHardyDerivativeCoefficient_nonpositive hR F hFs hhol) b hbn,
    ← localConformalHardyDerivativeProduct_eq_extension hR F hFs hhol b hbn]
  exact h1Value_diskHardySmoothProduct _ b

/-- The normalized primitive preserves the entire Hardy subspace. -/
theorem localConformalHardyPrimitive_nonpositive :
    IsNonpositiveFourierSupport (localConformalHardyPrimitive hR F hFs b) :=
  normalizedHardyPrimitive_nonpositive _ _
    (localConformalHardyPrimitiveMultiplier_strictNegative hR F hFs hhol) b hbn

end


section
variable (a ) (ha : IsWL1 (1 / 2 : ℝ) a) (b : L2Z)
include a ha b

theorem fromL2_normalizedHardyPrimitive :
    fromL2 (1 / 2 : ℝ) (normalizedHardyPrimitive a ha b) =
      antiPrim a (fromL2 (1 / 2 : ℝ) b) := by
  funext n
  rw [fromL2, normalizedHardyPrimitive_apply, ← mul_assoc, ← Complex.ofReal_mul,
    mul_comm (sobWeight n ^ (-(1 / 2))), sobWeight_rpow_mul_neg, Complex.ofReal_one,
    one_mul]

/-- Averaged coefficients of the normalized primitive are the same `antiPrim`
coefficients, including its prescribed zero coefficient. -/
theorem normalizedHardyAverage_primitive :
    normalizedHardyAverage (normalizedHardyPrimitive a ha b) =
      antiPrim a (normalizedHardyAverage b) := by
  change (Real.sqrt circlePeriod : ℂ)⁻¹ •
      fromL2 (1 / 2) (normalizedHardyPrimitive a ha b) =
    antiPrim a ((Real.sqrt circlePeriod : ℂ)⁻¹ • fromL2 (1 / 2) b)
  rw [fromL2_normalizedHardyPrimitive,
    (seqOpBound_antiPrim (by norm_num) ha).map_smul _ _
      (isSobolevSeq_fromL2 (1 / 2) b)]

end


private theorem hardy_phase_mul_massDensity  F
    (hhol : DifferentiableOn ℂ F unitDisk)
    (hC : DiskInverseJacobianBound F C)
     (hz : z ∈ unitDisk) :
    localConformalAntiholomorphicPhase F z * localConformalMassDensity F z =
      conj (fderiv ℝ F z 1) := by
  have hd : deriv F z ≠ 0 := by
    intro he
    have h := hC z hz
    rw [he, norm_zero] at h
    norm_num at h
  have hs : (‖fderiv ℝ F z 1‖ : ℂ) ≠ 0 := by
    apply Complex.ofReal_ne_zero.mpr
    rw [hardy_real_derivative_of_holomorphic isOpen_ball hhol hz 1, mul_one]
    exact norm_ne_zero_iff.mpr hd
  exact div_mul_cancel₀ _ hs

/-- Multiplication by actual conj(F′) on pullback values equals the actual
Jacobian phase times the genuine weighted L² pullback of physical values. -/
theorem localConformalHardyDerivativeCoefficient_pullback_value 
    hR F
    (hFs : RealSmoothOnBall F R)
    (hb : Bornology.IsBounded (F '' unitDisk))
    hL
    (hhol : DifferentiableOn ℂ F unitDisk)
    (hinj : InjOn F unitDisk)
    (hC : DiskInverseJacobianBound F C)
    (hK : DiskDerivativeBound F K)
    u :
    h1SmoothCoefficientL2 unitDisk
      (localConformalHardyDerivativeCoefficient hR F hFs)
        (h1Value unitDisk (localConformalH1Pullback hR F hFs hL u)) =
      localConformalAntiholomorphicPhaseMultiplier F
        (localConformalWeightedL2Pullback hR F hFs hL hK
          (h1Value (F '' unitDisk) u)) := by
  rw [localConformalWeightedL2Pullback_h1Value hR F hFs hb hL hhol hinj hC hK,
    localConformalMassPullback_apply]
  apply Lp.ext
  filter_upwards [h1SmoothCoefficientL2_ae (ball 0 1)
    (localConformalHardyDerivativeCoefficient hR F hFs)
    (h1Value (ball 0 1) (localConformalH1Pullback hR F hFs hL u)),
    localConformalAntiholomorphicPhaseMultiplier_ae F
      (lpBoundedMultiplier (localConformalMassDensity F)
        (localConformalMassDensity_aemeasurable hR F hFs)
        (localConformalMassDensity_ae_bound F hK)
        (h1Value (ball 0 1) (localConformalH1Pullback hR F hFs hL u))),
    lpBoundedMultiplier_ae (localConformalMassDensity F)
      (localConformalMassDensity_aemeasurable hR F hFs)
      (localConformalMassDensity_ae_bound F hK)
      (h1Value (ball 0 1) (localConformalH1Pullback hR F hFs hL u)),
    ae_restrict_mem measurableSet_ball] with z ha hp hm hz
  rw [ha, hp, hm,
    localConformalHardyDerivativeCoefficient_closedDisk hR F hFs (ball_subset_closedBall hz),
    ← mul_assoc, hardy_phase_mul_massDensity F hhol hC hz]

section PhysicalPrimitive

variable {R C K } (hR : 1 < R) (F )
    (hFs : RealSmoothOnBall F R)
    (hb : Bornology.IsBounded (F '' unitDisk))
    (hL : IsLipschitzDomain (F '' unitDisk))
    (hhol : DifferentiableOn ℂ F unitDisk)
    (hinj : InjOn F unitDisk)
    (hC : DiskInverseJacobianBound F C)
    (hK : DiskDerivativeBound F K)
    (e : OpenPartialHomeomorph ℂ ℂ) (he : (e : PlaneMap) = F)
    (hsource : closedUnitDisk ⊆ e.source)
    (hes : RealSmoothOn e.symm e.target)
local notation "hardyH1ExtensionFixed" => localConformalHardyH1Extension hR F hFs hb hL hhol hinj hC hK e he hsource hes


/-- The primitive has the actual physical x derivative U(b), proved from
the disk derivative identity and cancellation of the genuine Jacobian phase
and the norm-preserving physical L² pullback. -/
theorem localConformalHardyH1Extension_primitive_gradient (b : L2Z)
    (hbn : IsNonpositiveFourierSupport b) :
    h1Gradient (F '' unitDisk) 0
      (hardyH1ExtensionFixed
        (localConformalHardyPrimitive hR F hFs b)) =
      h1Value (F '' unitDisk)
        (hardyH1ExtensionFixed b) := by
  apply localConformalWeightedL2Pullback_injective hR F hFs hb hL hhol hinj hC hK
  apply localConformalAntiholomorphicPhaseMultiplier_injective F hhol hC
  calc
    _ = h1Gradient (ball 0 1) 0 (localConformalH1Pullback hR F hFs hL
      (hardyH1ExtensionFixed
        (localConformalHardyPrimitive hR F hFs b))) :=
      (localConformalH1Pullback_gradient_antiholomorphic hR F hFs hb hL hhol hinj hC hK _
        (localConformalHardyH1Extension_cauchyRiemann hR F hFs hb hL hhol hinj hC hK
          e he hsource hes _)).symm
    _ = h1Gradient (ball 0 1) 0
      (diskHardyExtension (localConformalHardyPrimitive hR F hFs b)) := by
        norm_num
    _ = h1SmoothCoefficientL2 (ball 0 1)
      (localConformalHardyDerivativeCoefficient hR F hFs)
        (h1Value (ball 0 1) (diskHardyExtension b)) :=
      diskHardyExtension_localConformalPrimitive_gradient hR F hFs hhol b hbn
    _ = _ := by
      have h := localConformalHardyDerivativeCoefficient_pullback_value hR F hFs hb hL
        hhol hinj hC hK
        (hardyH1ExtensionFixed b)
      simp_all

/-- The physical y derivative has the true antiholomorphic sign. -/
theorem localConformalHardyH1Extension_primitive_gradient_y (b : L2Z)
    (hbn : IsNonpositiveFourierSupport b) :
    h1Gradient (F '' unitDisk) 1
      (hardyH1ExtensionFixed
        (localConformalHardyPrimitive hR F hFs b)) =
      (-Complex.I) • h1Value (F '' unitDisk)
        (hardyH1ExtensionFixed b) := by
  calc
    _ = (-Complex.I) • h1Gradient (F '' ball 0 1) 0
      (hardyH1ExtensionFixed
        (localConformalHardyPrimitive hR F hFs b)) := by
      rw [localConformalHardyH1Extension_cauchyRiemann, smul_smul]
      simp
    _ = _ := by simp_all [localConformalHardyH1Extension_primitive_gradient]

end PhysicalPrimitive

end PolyaNeumann

end
