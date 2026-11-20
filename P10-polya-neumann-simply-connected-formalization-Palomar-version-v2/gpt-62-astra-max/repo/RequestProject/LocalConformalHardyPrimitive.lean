module

public import RequestProject.CircleAnalysisNotation

public import RequestProject.DiskCoordinates

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
public import RequestProject.PlanarNotation

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

set_option autoImplicit false

noncomputable section

open scoped ContDiff

namespace PolyaNeumann

open MeasureTheory Set Metric Filter
open scoped Topology ComplexConjugate

section

variable (c a : ℤ → ℂ) (hc : IsWL1 halfOrder c) (ha : IsWL1 halfOrder a)
    (han : IsStrictNegativeFourierSupport a) (b : L2Z) (n : ℤ)

include b n in
/-- Averaged coefficients of an actual half-trace vector. -/
def normalizedHardyAverage : ℂ :=
  fourierScale⁻¹ * fromL2 halfOrder b n

include hc in
/-- Bounded multiplication on normalized half-order Fourier coordinates.
The multiplier coefficients use the averaged convention. -/
def normalizedHardyMultiplier :
    FourierOp :=
  (seqOpBound_seqConv (by norm_num : (0 : ℝ) ≤ 1 / 2) hc).toCLM

theorem normalizedHardyMultiplier_apply :
    normalizedHardyMultiplier c hc b n =
      ((sobWeight n ^ halfOrder : ℝ) : ℂ) * seqConv c (fromL2 halfOrder b) n :=
  multiplier_toCLM_apply _ b n

include ha in
/-- The primitive in the stronger normalized coordinates of order 3/2. -/
def normalizedHardyPrimitiveGain :
    FourierOp :=
  (seqOpBound_antiPrim (by norm_num : (0 : ℝ) ≤ 1 / 2) ha).toCLM

theorem normalizedHardyPrimitiveGain_apply :
    normalizedHardyPrimitiveGain a ha b n =
      ((sobWeight n ^ (halfOrder + 1) : ℝ) : ℂ) *
        antiPrim a (fromL2 halfOrder b) n :=
  multiplier_toCLM_apply _ b n

include ha in
/-- The actual normalized primitive at order 1/2, retaining the constant
chosen by `antiPrim` at the same boundary origin. -/
def normalizedHardyPrimitive :
    FourierOp :=
  (sobolevSmoothing 1 (by norm_num)).comp (normalizedHardyPrimitiveGain a ha)

theorem normalizedHardyPrimitive_apply :
    normalizedHardyPrimitive a ha b n =
      ((sobWeight n ^ halfOrder : ℝ) : ℂ) * antiPrim a (fromL2 halfOrder b) n := by
  change sobolevSmoothing 1 (by norm_num) (normalizedHardyPrimitiveGain a ha b) n = _
  simp only [sobolevSmoothing, diagOp_apply, normalizedHardyPrimitiveGain_apply]
  rw [← mul_assoc, ← Complex.ofReal_mul, ← Real.rpow_add (sobWeight_pos n)]
  simp

include han in
theorem normalizedHardyPrimitive_nonpositive (hbn : IsNonpositiveFourierSupport b) :
    IsNonpositiveFourierSupport (normalizedHardyPrimitive a ha b) := by
  
  intro n hn
  rw [normalizedHardyPrimitive_apply, antiPrim_nonpositive han (by
    intro n hn
    simp [fromL2, hbn n hn]) n hn, mul_zero]

/-- Actual L² derivative of the completed disk primitive. This identifies
the derivative with the completed derivative data, before a product is
identified using the genuine Hardy trace uniqueness theorem. -/
theorem diskHardyExtension_normalizedPrimitive_gradient :
    h1Gradient unitDisk 0 (diskHardyExtension (normalizedHardyPrimitive a ha b)) =
      h1Value unitDisk
        (diskHardyExtension (diskHardyDerivativeData (normalizedHardyPrimitiveGain a ha b))) :=
  diskHardyExtension_smoothing_gradient _

end

section

variable (a : SmoothH1Coefficient) (Φ : SmoothDiskMap) (C : C(ParamCircle, ℂ))
    (hCR : ∀ z ∈ unitDisk, fderiv ℝ (a : ℂ → ℂ) z 1 = Complex.I * fderiv ℝ (a : ℂ → ℂ) z Complex.I)
    (θ : ℝ) (hhol : DifferentiableOn ℂ Φ.map unitDisk) (b : L2Z) (n : ℤ)

include a in
/-- Genuine disk H¹ multiplication of the actual completed Hardy extension. -/
def diskHardySmoothProduct :
    L2Z →L[ℂ] NeumannH1 unitDisk :=
  (neumannH1SmoothMultiplier unitDisk a).comp diskHardyExtension

theorem h1Value_diskHardySmoothProduct :
    h1Value unitDisk (diskHardySmoothProduct a b) =
      h1SmoothCoefficientL2 unitDisk a
        (h1Value unitDisk (diskHardyExtension b)) :=
  h1Value_neumannH1SmoothMultiplier _ a _

theorem h1Gradient_diskHardySmoothProduct (i : Fin 2) :
    h1Gradient unitDisk i (diskHardySmoothProduct a b) =
      h1SmoothCoefficientL2 unitDisk a
          (h1Gradient unitDisk i (diskHardyExtension b)) +
        h1SmoothCoefficientDerivativeL2 unitDisk a i
          (h1Value unitDisk (diskHardyExtension b)) :=
  h1Gradient_neumannH1SmoothMultiplier _ a _ i

include hCR in
private theorem hardy_coefficient_derivative_CR
    (u : L2 unitDisk) :
    h1SmoothCoefficientDerivativeL2 unitDisk a 0 u =
      Complex.I • h1SmoothCoefficientDerivativeL2 unitDisk a 1 u := by
  apply Lp.ext
  filter_upwards [h1SmoothCoefficientDerivativeL2_ae unitDisk a 0 u,
    h1SmoothCoefficientDerivativeL2_ae unitDisk a 1 u,
    Lp.coeFn_smul Complex.I (h1SmoothCoefficientDerivativeL2 unitDisk a 1 u),
    ae_restrict_mem measurableSet_ball] with z hx hy hs hz
  simp [hx, hs]
  rw [hy]
  change fderiv ℝ (a : ℂ → ℂ) z 1 * u z =
    Complex.I * (fderiv ℝ (a : ℂ → ℂ) z Complex.I * u z)
  rw [hCR z hz]
  ring

include hCR in
/-- An actual smooth antiholomorphic coefficient preserves the genuine
weak CR equation of the completed disk Hardy extension. -/
theorem diskHardySmoothProduct_cauchyRiemann :
    h1Gradient unitDisk 0 (diskHardySmoothProduct a b) =
      Complex.I • h1Gradient unitDisk 1 (diskHardySmoothProduct a b) := by
  rw [h1Gradient_diskHardySmoothProduct, h1Gradient_diskHardySmoothProduct,
    diskHardyExtension_cauchyRiemann, map_smul,
    hardy_coefficient_derivative_CR a hCR, smul_add]

include Φ in
/-- The actual compact coefficient conjugate to the supplied conformal
derivative. It is smooth globally because the actual F is cut off first. -/
def SmoothDiskMap.hardyDerivativeTest : smoothTraceTests :=
  ⟨fun z => conj (dirD (smoothDiskCutoff Φ.radius Φ.one_lt_radius Φ.map) 1 z),
    ((smoothDiskCutoff_testFunction Φ.one_lt_radius Φ.smooth).dirD 1).conj⟩

include Φ in
def SmoothDiskMap.hardyDerivativeCoefficient : SmoothH1Coefficient :=
  smoothTraceTestsH1Coefficient Φ.hardyDerivativeTest

theorem localConformalHardyDerivativeCoefficient_closedDisk {z : ℂ}
    (hz : z ∈ closedDisk) :
    Φ.hardyDerivativeCoefficient z = conj (fderiv ℝ Φ.map z 1) := by
  change conj (fderiv ℝ (smoothDiskCutoff Φ.radius Φ.one_lt_radius Φ.map) z 1) = _
  rw [fderiv_smoothDiskCutoff_eq Φ.one_lt_radius Φ.map hz]

private theorem hardy_real_derivative_of_holomorphic {U : Set ℂ} (hU : IsOpen U)
    {F : ℂ → ℂ} (hF : DifferentiableOn ℂ F U) {z : ℂ} (hz : z ∈ U) (v : ℂ) :
    fderiv ℝ F z v = deriv F z * v := by
  rw [(hF.differentiableAt (hU.mem_nhds hz)).fderiv_restrictScalars ℝ]
  exact fderiv_eq_deriv_mul

include hhol in
/-- The actual cutoff coefficient has the derivative of conj(F′) in the
interior, derived from holomorphic F′ and its real chain rule. -/
theorem localConformalHardyDerivativeCoefficient_fderiv {z : ℂ} (hz : z ∈ unitDisk) (v : ℂ) :
    fderiv ℝ (Φ.hardyDerivativeCoefficient : ℂ → ℂ) z v =
      conj (deriv (deriv Φ.map) z * v) := by
  have he : Φ.hardyDerivativeCoefficient
      =ᶠ[𝓝 z] fun w => conj (deriv Φ.map w) := by
    filter_upwards [isOpen_ball.mem_nhds hz] with w hw
    rw [localConformalHardyDerivativeCoefficient_closedDisk Φ (ball_subset_closedBall hw),
      hardy_real_derivative_of_holomorphic isOpen_ball hhol hw 1, mul_one]
  rw [he.fderiv_eq ]
  
  have h := (Complex.conjCLE.hasFDerivAt.comp z (((hhol.deriv isOpen_ball).differentiableAt (isOpen_ball.mem_nhds hz)).restrictScalars ℝ).hasFDerivAt).fderiv
  rw [show (fun w => conj (deriv Φ.map w)) = Complex.conjCLE ∘ deriv Φ.map from rfl, h]
  change conj (fderiv ℝ (deriv Φ.map) z v) = _
  rw [hardy_real_derivative_of_holomorphic isOpen_ball (hhol.deriv isOpen_ball) hz v]

include hhol in
theorem localConformalHardyDerivativeCoefficient_cauchyRiemann {z : ℂ} (hz : z ∈ unitDisk) :
    fderiv ℝ (Φ.hardyDerivativeCoefficient : ℂ → ℂ) z 1 =
      Complex.I * fderiv ℝ
        (Φ.hardyDerivativeCoefficient : ℂ → ℂ) z Complex.I := by
  rw [localConformalHardyDerivativeCoefficient_fderiv Φ hhol hz 1,
    localConformalHardyDerivativeCoefficient_fderiv Φ hhol hz Complex.I]
  simp only [mul_one, map_mul, Complex.conj_I]
  calc
    _ = -(Complex.I * Complex.I) * conj (deriv (deriv Φ.map) z) := by
      simp
    _ = _ := by ring

include Φ in
/-- The genuine disk product needed for the interior physical primitive. -/
def SmoothDiskMap.hardyDerivativeProduct :
    L2Z →L[ℂ] NeumannH1 unitDisk :=
  diskHardySmoothProduct Φ.hardyDerivativeCoefficient

/-- Actual angular-velocity multiplier data for the primitive. -/
def localConformalHardyPrimitiveMultiplier (F : ℂ → ℂ) : ℤ → ℂ :=
  angleCoeff (fun θ => conj (deriv (physicalCircleTrace F) θ))

theorem localConformalHardyPrimitiveMultiplier_isWL1 :
    IsWL1 halfOrder (localConformalHardyPrimitiveMultiplier Φ.map) := by
  
  refine ((physicalCircleTrace_fourier_weights_of_smooth_neighborhood Φ).1).of_nonneg_of_le (fun n => ?_) (fun n => ?_)
  · exact mul_nonneg (Real.rpow_nonneg (sobWeight_pos n).le _) (norm_nonneg _)
  · exact mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow_of_exponent_le (one_le_sobWeight n) (by norm_num)) (norm_nonneg _)

include hhol in
theorem localConformalHardyPrimitiveMultiplier_strictNegative :
    IsStrictNegativeFourierSupport (localConformalHardyPrimitiveMultiplier Φ.map) :=
  physicalCircleTrace_conj_deriv_strictNegative_of_neighborhood Φ.one_lt_radius Φ.map
    (Φ.smooth.of_le (by simp)) hhol

include Φ in
/-- The actual supplied-coordinate primitive on normalized half-trace data. -/
def SmoothDiskMap.hardyPrimitive : FourierOp :=
  normalizedHardyPrimitive (localConformalHardyPrimitiveMultiplier Φ.map)
    (localConformalHardyPrimitiveMultiplier_isWL1 Φ)

private theorem hardy_fourier_one_circle :
    fourier  1 (θ : ParamCircle) = unitCirclePt θ := by
  rw [hardy_fourier_exp, circleMap_zero]
  simp

include a in
/-- The actual boundary coefficient as a continuous circle function. -/
def diskSmoothCoefficientCircle :
    C(ParamCircle, ℂ) :=
  ⟨fun q => a (fourier  1 q),
    a.smooth.continuous.comp (fourier  1).continuous⟩

theorem diskSmoothCoefficientCircle_apply :
    diskSmoothCoefficientCircle a (θ : ParamCircle) = a (unitCirclePt θ) := by
  change a (fourier (T := anglePeriod) 1 (θ : ParamCircle)) = _
  rw [hardy_fourier_one_circle]

/-- Fourier coefficients of a function on the parameter circle are its interval coefficients. -/
theorem circle_fourierCoeff_eq (A : ParamCircle → ℂ) :
    fourierCoeff A = angleCoeff (fun θ : ℝ => A (θ : ParamCircle)) := by
  funext n
  simp only [fourierCoeff_eq_intervalIntegral A n 0, fourierCoeffOn_eq_integral, fourier_coe_apply, zero_add, sub_zero]

theorem diskSmoothCoefficientCircle_coeff :
    fourierCoeff (diskSmoothCoefficientCircle a) n =
      angleCoeff (fun θ => a (unitCirclePt θ)) n := by
  rw [circle_fourierCoeff_eq]
  congr 1
  funext θ
  exact diskSmoothCoefficientCircle_apply a θ

theorem diskSmoothCoefficientCircle_isWL1 :
    IsWL1 halfOrder (fourierCoeff (diskSmoothCoefficientCircle a)) := by
  
  have hp  :=
    (periodic_circleMap 0 1).comp a
  have h2 := (periodic_contDiff_four_fourier_weights ((a.smooth.of_le (WithTop.coe_le_coe.mpr le_top)).comp (contDiff_circleMap 0 1)) hp).2
  change Summable (fun n => sobWeight n ^ halfOrder *
    ‖fourierCoeff (diskSmoothCoefficientCircle a) n‖)
  simp_rw [diskSmoothCoefficientCircle_coeff]
  refine h2.of_nonneg_of_le (fun n => ?_) (fun n => ?_)
  · exact mul_nonneg (Real.rpow_nonneg (sobWeight_pos n).le _) (norm_nonneg _)
  · exact mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow_of_exponent_le (one_le_sobWeight n) (by norm_num)) (norm_nonneg _)

private theorem hardy_fourierCoeff_shift :
    fourierCoeff (fun q => fourier  (-1) q * C q) n =
      fourierCoeff C (n + 1) := by
  
  apply integral_congr_ae
  exact Eventually.of_forall (fun q => by
    simp [*] <;> ring)

include hhol in
/-- The conjugated angular velocity has precisely the shifted coefficient
of conj(F′), including its phase -i. -/
theorem localConformalHardyPrimitiveMultiplier_shift :
    localConformalHardyPrimitiveMultiplier Φ.map n = (-Complex.I) *
      fourierCoeff (diskSmoothCoefficientCircle
        Φ.hardyDerivativeCoefficient) (n + 1) := by
  let C := diskSmoothCoefficientCircle Φ.hardyDerivativeCoefficient
  let B  := (-Complex.I) •
    ((fourier  (-1)) * C)
  have he (θ : ℝ) : conj (deriv Φ.boundary θ) =
      B θ := by
    rw [localConformal_circleTrace_deriv Φ hhol]
    simp only [map_mul, Complex.conj_I]
    simp only [B, ContinuousMap.smul_apply, ContinuousMap.mul_apply, smul_eq_mul]
    rw [fourier_neg, hardy_fourier_one_circle, diskSmoothCoefficientCircle_apply,
      localConformalHardyDerivativeCoefficient_closedDisk Φ (circleMap_mem_closedBall 0 (by norm_num) θ)]
    ring
  change angleCoeff
    (fun θ => conj (deriv Φ.boundary θ)) n = _
  rw [show (fun θ => conj (deriv Φ.boundary θ)) =
      (fun θ : ℝ => B θ) from funext he,
    ← circle_fourierCoeff_eq]
  change fourierCoeff ((-Complex.I) •
    (fun q => fourier (T := anglePeriod) (-1) q * C q)) n = _
  rw [fourierCoeff.const_smul]
  simp only [smul_eq_mul]
  rw [hardy_fourierCoeff_shift]

end

section

variable (a c : ℤ → ℂ) (ha : IsWL1 halfOrder a) (hc : IsWL1 halfOrder c)
    (hshift : ∀ n : ℤ, a n = (-Complex.I) * c (n + 1)) (hcn : IsNonpositiveFourierSupport c)
    (Φ : SmoothDiskMap) (hhol : DifferentiableOn ℂ Φ.map unitDisk) (b : L2Z)
    (hbn : IsNonpositiveFourierSupport b)

include hhol in
theorem localConformalHardyDerivativeCoefficient_nonpositive :
    IsNonpositiveFourierSupport (fourierCoeff (diskSmoothCoefficientCircle
      Φ.hardyDerivativeCoefficient)) := by
  intro n hn
  have ha := localConformalHardyPrimitiveMultiplier_strictNegative Φ hhol
    (n - 1) (by omega)
  rw [localConformalHardyPrimitiveMultiplier_shift Φ hhol,
    sub_add_cancel] at ha
  aesop

private theorem hardy_seqConv_nonpositive {c h : ℤ → ℂ}
    (hc : IsNonpositiveFourierSupport c) (hh : IsNonpositiveFourierSupport h) :
    IsNonpositiveFourierSupport (seqConv c h) := by
  intro n hn
  unfold seqConv
  have he : (fun k => c k * h (n - k)) = (fun _ : ℤ => 0) := by
    funext k
    by_cases hk : 0 < k
    · rw [hc k hk, zero_mul]
    · rw [hh (n - k) (by omega), mul_zero]
  simp [*]

private theorem hardy_seqConv_shift {a c : ℤ → ℂ}
    (hshift : ∀ n : ℤ, a n = (-Complex.I) * c (n + 1)) (h : ℤ → ℂ) (n : ℤ) :
    seqConv a h (n - 1) = (-Complex.I) * seqConv c h n := by
  unfold seqConv
  calc
    _ = (-Complex.I) * ∑' k : ℤ, c (k + 1) * h (n - (k + 1)) := by
      rw [← tsum_mul_left]
      grind
    _ = _ := congrArg _
      ((Equiv.addRight 1).tsum_eq (fun k => c k * h (n - k)))

private theorem hardy_primitive_derivative_scalar (x y sx sy : ℂ)
    (hx : x ≠ 0) (hy : y ≠ 0) (hsy : sy ≠ 0) :
    (x / y * (sx / sy)) * ((sy * y) / (Complex.I * (-x))) * (-Complex.I) = sx := by
  field_simp <;> ring

private theorem hardy_primitive_derivative_scale (k : ℕ) :
    (diskHardyDerivativeWeight k : ℂ) *
        (((sobWeight (-((k + 1 : ℕ) : ℤ)) ^ (halfOrder + 1) : ℝ) : ℂ) /
          (Complex.I * (-((k + 1 : ℕ) : ℂ)))) * (-Complex.I) =
      ((sobWeight (-(k : ℤ)) ^ halfOrder : ℝ) : ℂ) := by
  rw [sobWeight_neg_nat, sobWeight_neg_nat]
  have hy : ((k + 1 + 1 : ℕ) ^ (halfOrder + 1)) =
      Real.sqrt (k + 2 : ℕ) * (k + 2 : ℕ) := by
    have hi : k + 1 + 1 = k + 2 := by omega
    rw [hi, Real.rpow_add (by positivity), Real.rpow_one, ← Real.sqrt_eq_rpow]
  rw [hy, ← Real.sqrt_eq_rpow]
  simp only [diskHardyDerivativeWeight, Real.sqrt_div (by positivity : 0 ≤ ((k + 1 : ℕ) : ℝ))]
  
  
  
  simpa only [Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_natCast] using
    hardy_primitive_derivative_scalar (k + 1 : ℕ) (k + 2 : ℕ)
      (Real.sqrt (k + 1 : ℕ)) (Real.sqrt (k + 2 : ℕ))
      (by exact_mod_cast (by omega : k + 1 ≠ 0)) (by exact_mod_cast (by omega : k + 2 ≠ 0)) (by
          exact_mod_cast (by positivity))

include hbn hcn hshift in
/-- The actual derivative-data operator on a normalized primitive is the
actual normalized product data. The input and product retain frequency zero. -/
theorem diskHardyDerivativeData_normalizedPrimitiveGain :
    diskHardyDerivativeData (normalizedHardyPrimitiveGain a ha b) =
      normalizedHardyMultiplier c hc b := by
  
  ext n
  by_cases hn : 0 < n
  · rw [diskHardyDerivativeData_apply_pos _ hn, normalizedHardyMultiplier_apply,
      hardy_seqConv_nonpositive hcn (by
        intro n hn
        simp [fromL2, hbn n hn]) n hn, mul_zero]
  · let k  := Int.toNat (-n)
    have hnk : n = -k := by omega
    rw [hnk, diskHardyDerivativeData_apply_neg, normalizedHardyPrimitiveGain_apply,
      normalizedHardyMultiplier_apply, antiPrim, if_neg (by omega), primSeq]
    have hi : -k - 1 = -((k + 1 : ℕ) : ℤ) := by omega
    have hconv := hardy_seqConv_shift hshift (fromL2 (1 / 2) b) (-k)
    rw [hi] at hconv
    rw [hconv]
    simp only [Int.cast_neg, Int.cast_natCast]
    calc
      _ = ((diskHardyDerivativeWeight k) *
          (((sobWeight _ ^ (halfOrder + 1) : ℝ) : ℂ) /
            (Complex.I * (-(k + 1 : ℕ)))) * (-Complex.I)) *
              seqConv c _ _ := by ring
      _ = _ := by rw [hardy_primitive_derivative_scale]

include hbn hcn in
theorem normalizedHardyMultiplier_nonpositive :
    IsNonpositiveFourierSupport (normalizedHardyMultiplier c hc b) := by
  
  intro n hn
  rw [normalizedHardyMultiplier_apply, hardy_seqConv_nonpositive hcn (by
    intro n hn
    simp [fromL2, hbn n hn]) n hn, mul_zero]

private theorem hardy_trace_eq_of_halfTrace_eq
    (u v : NeumannH1 unitDisk) (h : diskHalfTrace u = diskHalfTrace v) :
    diskH1Trace u = diskH1Trace v := by
  apply boundaryFourier.injective
  apply lp.ext
  rw [← fromL2_half_diskHalfTrace, ← fromL2_half_diskHalfTrace, h]

/-- The actual completed antiholomorphic product is identified with its
completed Fourier extension by the proved weak CR trace uniqueness theorem. -/
theorem diskHardySmoothProduct_eq_extension (a : SmoothH1Coefficient)
    (hCR : ∀ z ∈ unitDisk,
      fderiv ℝ (a : ℂ → ℂ) z 1 = Complex.I * fderiv ℝ (a : ℂ → ℂ) z Complex.I)
    (hcn : IsNonpositiveFourierSupport (fourierCoeff (diskSmoothCoefficientCircle a)))
    (b : L2Z) (hbn : IsNonpositiveFourierSupport b) :
    diskHardySmoothProduct a b = diskHardyExtension
      (normalizedHardyMultiplier (fourierCoeff (diskSmoothCoefficientCircle a))
        (diskSmoothCoefficientCircle_isWL1 a) b) := by
  apply neumannH1_eq_of_antiholomorphic_same_trace unitDisk_bounded
    isLipschitzDomain_unitDisk unitCircle_isBoundaryParam
  · exact diskHardySmoothProduct_cauchyRiemann a hCR b
  · exact diskHardyExtension_cauchyRiemann _
  · 
    apply hardy_trace_eq_of_halfTrace_eq
    have hp := diskHalfTrace_smoothMultiplier a (diskSmoothCoefficientCircle a)
      (diskSmoothCoefficientCircle_apply a) (diskSmoothCoefficientCircle_isWL1 a)
      (diskHardyExtension b)
    rw [diskHalfTrace_diskHardyExtension_eq_of_nonpositive b hbn] at hp
    rw [diskHalfTrace_diskHardyExtension_eq_of_nonpositive _
      (normalizedHardyMultiplier_nonpositive _ _ hcn b hbn)]
    exact hp

include hbn hhol in
theorem localConformalHardyDerivativeProduct_eq_extension :
    Φ.hardyDerivativeProduct b = diskHardyExtension
      (normalizedHardyMultiplier
        (fourierCoeff (diskSmoothCoefficientCircle
          Φ.hardyDerivativeCoefficient))
        (diskSmoothCoefficientCircle_isWL1
          Φ.hardyDerivativeCoefficient) b) :=
  diskHardySmoothProduct_eq_extension _
    (fun _ hz => localConformalHardyDerivativeCoefficient_cauchyRiemann Φ hhol hz)
    (localConformalHardyDerivativeCoefficient_nonpositive Φ hhol) b hbn

include hbn hhol in
/-- Actual disk x derivative of the normalized physical primitive. The
derivative multiplier is the compact smooth representative of conj(F′). -/
theorem diskHardyExtension_localConformalPrimitive_gradient :
    h1Gradient unitDisk 0
        (diskHardyExtension (Φ.hardyPrimitive b)) =
      h1SmoothCoefficientL2 unitDisk
        Φ.hardyDerivativeCoefficient
          (h1Value unitDisk (diskHardyExtension b)) := by
  change h1Gradient unitDisk 0 (diskHardyExtension
    (normalizedHardyPrimitive (localConformalHardyPrimitiveMultiplier Φ.map)
      (localConformalHardyPrimitiveMultiplier_isWL1 Φ) b)) = _
  rw [diskHardyExtension_normalizedPrimitive_gradient,
    diskHardyDerivativeData_normalizedPrimitiveGain _ _ _
      (diskSmoothCoefficientCircle_isWL1 Φ.hardyDerivativeCoefficient)
      (localConformalHardyPrimitiveMultiplier_shift Φ hhol)
      (localConformalHardyDerivativeCoefficient_nonpositive Φ hhol) b hbn,
    ← localConformalHardyDerivativeProduct_eq_extension Φ hhol b hbn]
  exact h1Value_diskHardySmoothProduct _ b

include hbn hhol in
/-- The normalized primitive preserves the entire Hardy subspace. -/
theorem localConformalHardyPrimitive_nonpositive :
    IsNonpositiveFourierSupport (Φ.hardyPrimitive b) :=
  normalizedHardyPrimitive_nonpositive _ _
    (localConformalHardyPrimitiveMultiplier_strictNegative Φ hhol) b hbn

theorem fromL2_normalizedHardyPrimitive :
    fromL2 halfOrder (normalizedHardyPrimitive a ha b) =
      antiPrim a (fromL2 halfOrder b) := by
  funext n
  rw [fromL2, normalizedHardyPrimitive_apply, ← mul_assoc, ← Complex.ofReal_mul,
    mul_comm (sobWeight n ^ (-halfOrder)), sobWeight_rpow_mul_neg, Complex.ofReal_one,
    one_mul]

/-- Averaged coefficients of the normalized primitive are the same `antiPrim`
coefficients, including its prescribed zero coefficient. -/
theorem normalizedHardyAverage_primitive :
    normalizedHardyAverage (normalizedHardyPrimitive a ha b) =
      antiPrim a (normalizedHardyAverage b) := by
  change fourierScale⁻¹ •
      fromL2 halfOrder (normalizedHardyPrimitive a ha b) =
    antiPrim a (fourierScale⁻¹ • fromL2 halfOrder b)
  rw [fromL2_normalizedHardyPrimitive,
    (seqOpBound_antiPrim (by positivity) ha).map_smul _ _
      (isSobolevSeq_fromL2 _ b)]

end

private theorem hardy_phase_mul_massDensity {C : ℝ} (F : ℂ → ℂ)
    (hhol : DifferentiableOn ℂ F unitDisk)
    (hC : ∀ z ∈ unitDisk, 1 ≤ C * ‖deriv F z‖ ^ 2)
    {z : ℂ} (hz : z ∈ unitDisk) :
    localConformalAntiholomorphicPhase F z * localConformalMassDensity F z =
      conj (fderiv ℝ F z 1) := by
  
  
  apply div_mul_cancel₀ _
  apply Complex.ofReal_ne_zero.mpr
  rw [hardy_real_derivative_of_holomorphic isOpen_ball hhol hz 1, mul_one]
  apply norm_ne_zero_iff.mpr
  intro he
  have h := hC z hz
  rw [he, norm_zero] at h
  norm_num at h

/-- Multiplication by actual conj(F′) on pullback values equals the actual
Jacobian phase times the genuine weighted L² pullback of physical values. -/
theorem localConformalHardyDerivativeCoefficient_pullback_value (Φ : ControlledDiskMap)
    (u : NeumannH1 Φ.domain) :
    h1SmoothCoefficientL2 unitDisk
      Φ.hardyDerivativeCoefficient
        (h1Value unitDisk (Φ.h1Pullback Φ.lipschitzDomain u)) =
      localConformalAntiholomorphicPhaseMultiplier Φ.map
        (Φ.weightedL2Pullback Φ.lipschitzDomain Φ.deriv_upper
          (h1Value Φ.domain u)) := by
  rw [localConformalWeightedL2Pullback_h1Value Φ,
    localConformalMassPullback_apply]
  apply Lp.ext
  filter_upwards [h1SmoothCoefficientL2_ae unitDisk
    Φ.hardyDerivativeCoefficient
    _,
    localConformalAntiholomorphicPhaseMultiplier_ae Φ.map
      _,
    lpBoundedMultiplier_ae (localConformalMassDensity Φ.map)
      (localConformalMassDensity_aemeasurable Φ)
      _
      _,
    ae_restrict_mem measurableSet_ball] with z ha hp hm hz
  rw [ha, hp, hm,
    localConformalHardyDerivativeCoefficient_closedDisk Φ (ball_subset_closedBall hz),
    ← mul_assoc, hardy_phase_mul_massDensity Φ.map Φ.holomorphic Φ.deriv_lower hz]

section PhysicalPrimitive

section

variable (Φ : DiskCoordinates) (b : L2Z) (hbn : IsNonpositiveFourierSupport b)
include hbn

/-- The primitive has the actual physical x derivative U(b), proved from
the disk derivative identity and cancellation of the genuine Jacobian phase
and the norm-preserving physical L² pullback. -/
theorem localConformalHardyH1Extension_primitive_gradient :
    h1Gradient Φ.domain 0
      (Φ.hardyH1Extension (Φ.hardyPrimitive b)) =
      h1Value Φ.domain
        (Φ.hardyH1Extension b) := by
  apply localConformalWeightedL2Pullback_injective Φ
  apply localConformalAntiholomorphicPhaseMultiplier_injective Φ.map Φ.holomorphic Φ.deriv_lower
  calc
    _ = _ :=
      (localConformalH1Pullback_gradient_antiholomorphic Φ _
        (localConformalHardyH1Extension_cauchyRiemann Φ _)).symm
    _ = h1Gradient unitDisk 0
      _ := by
        rw [localConformalH1Pullback_hardyExtension]
    _ = _ :=
      diskHardyExtension_localConformalPrimitive_gradient Φ Φ.holomorphic b hbn
    _ = _ := by
      simpa using localConformalHardyDerivativeCoefficient_pullback_value Φ (Φ.hardyH1Extension b)

/-- The physical y derivative has the true antiholomorphic sign. -/
theorem localConformalHardyH1Extension_primitive_gradient_y :
    h1Gradient Φ.domain 1
      (Φ.hardyH1Extension (Φ.hardyPrimitive b)) =
      (-Complex.I) • h1Value Φ.domain
        (Φ.hardyH1Extension b) := calc
    _ = (-Complex.I) • h1Gradient Φ.domain 0
      (Φ.hardyH1Extension (Φ.hardyPrimitive b)) := by
      simp [localConformalHardyH1Extension_cauchyRiemann, smul_smul]
    _ = _ := by rw [localConformalHardyH1Extension_primitive_gradient Φ b hbn]

end

end PhysicalPrimitive

end PolyaNeumann

end
