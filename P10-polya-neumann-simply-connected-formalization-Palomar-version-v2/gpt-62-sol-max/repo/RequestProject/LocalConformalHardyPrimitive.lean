module

public import RequestProject.CircleFourier
public import RequestProject.ConformalDiskCoordinates

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

set_option autoImplicit false

noncomputable section

namespace PolyaNeumann

open MeasureTheory Set Metric Filter
open scoped Topology ComplexConjugate

/-- Averaged coefficients of an actual half-trace vector. -/
def normalizedHardyAverage (b : L2Z) (n : ℤ) : ℂ :=
  (Real.sqrt (2 * Real.pi) : ℂ)⁻¹ * fromL2 (1 / 2 : ℝ) b n

section

variable (c : ℤ → ℂ) (hc : IsWL1 (1 / 2 : ℝ) c)
include c hc

/-- Bounded multiplication on normalized half-order Fourier coordinates.
The multiplier coefficients use the averaged convention. -/
def normalizedHardyMultiplier  :
    L2Z →L[ℂ] L2Z :=
  (seqOpBound_seqConv (by norm_num : (0 : ℝ) ≤ 1 / 2) hc).toCLM

theorem normalizedHardyMultiplier_apply  (b : L2Z) (n : ℤ) :
    normalizedHardyMultiplier c hc b n =
      ((sobWeight n ^ (1 / 2 : ℝ) : ℝ) : ℂ) * seqConv c (fromL2 (1 / 2 : ℝ) b) n :=
  SeqOpBound.toCLM_apply _ b n

theorem fromL2_normalizedHardyMultiplier (b : L2Z) :
    fromL2 (1 / 2) (normalizedHardyMultiplier c hc b) = seqConv c (fromL2 (1 / 2) b) :=
  SeqOpBound.fromL2_toCLM _ b

end

section

variable (a : ℤ → ℂ) (ha : IsWL1 (1 / 2 : ℝ) a)
include a ha

/-- The primitive in the stronger normalized coordinates of order 3/2. -/
def normalizedHardyPrimitiveGain  :
    L2Z →L[ℂ] L2Z :=
  (seqOpBound_antiPrim (by norm_num : (0 : ℝ) ≤ 1 / 2) ha).toCLM

theorem normalizedHardyPrimitiveGain_apply  (b : L2Z) (n : ℤ) :
    normalizedHardyPrimitiveGain a ha b n =
      ((sobWeight n ^ ((1 / 2 : ℝ) + 1) : ℝ) : ℂ) *
        antiPrim a (fromL2 (1 / 2 : ℝ) b) n :=
  SeqOpBound.toCLM_apply _ b n

/-- The actual normalized primitive at order 1/2, retaining the constant
chosen by `antiPrim` at the same boundary origin. -/
def normalizedHardyPrimitive  :
    L2Z →L[ℂ] L2Z :=
  (sobolevSmoothing 1 (by norm_num)).comp (normalizedHardyPrimitiveGain a ha)

theorem normalizedHardyPrimitive_apply  (b : L2Z) (n : ℤ) :
    normalizedHardyPrimitive a ha b n =
      ((sobWeight n ^ (1 / 2 : ℝ) : ℝ) : ℂ) * antiPrim a (fromL2 (1 / 2 : ℝ) b) n := by
  change sobolevSmoothing 1 (by norm_num) (normalizedHardyPrimitiveGain a ha b) n = _
  simp only [sobolevSmoothing, diagOp_apply, normalizedHardyPrimitiveGain_apply]
  rw [← mul_assoc, ← Complex.ofReal_mul, ← Real.rpow_add (sobWeight_pos n)]
  simp

theorem normalizedHardyPrimitive_nonpositive  (han : IsStrictNegativeFourierSupport a)
    (b : L2Z) (hbn : IsNonpositiveFourierSupport b) :
    IsNonpositiveFourierSupport (normalizedHardyPrimitive a ha b) := by
  have hb : IsNonpositiveFourierSupport (fromL2 (1 / 2 : ℝ) b) := by
    intro n hn
    simp  [fromL2, hbn n hn, mul_zero]
  intro n hn
  rw [normalizedHardyPrimitive_apply, antiPrim_nonpositive han hb n hn, mul_zero]

/-- Actual L² derivative of the completed disk primitive. This identifies
the derivative with the completed derivative data, before a product is
identified using the genuine Hardy trace uniqueness theorem. -/
theorem diskHardyExtension_normalizedPrimitive_gradient  (b : L2Z) :
    h1Gradient (ball (0 : ℂ) 1) 0 (diskHardyExtension (normalizedHardyPrimitive a ha b)) =
      h1Value (ball (0 : ℂ) 1)
        (diskHardyExtension (diskHardyDerivativeData (normalizedHardyPrimitiveGain a ha b))) :=
  diskHardyExtension_smoothing_gradient (normalizedHardyPrimitiveGain a ha b)

end

section

variable (a : SmoothH1Coefficient)
include a

/-- Genuine disk H¹ multiplication of the actual completed Hardy extension. -/
def diskHardySmoothProduct  :
    L2Z →L[ℂ] NeumannH1 (ball (0 : ℂ) 1) :=
  (neumannH1SmoothMultiplier (ball (0 : ℂ) 1) a).comp diskHardyExtension


theorem h1Gradient_diskHardySmoothProduct  (b : L2Z) (i : Fin 2) :
    h1Gradient (ball (0 : ℂ) 1) i (diskHardySmoothProduct a b) =
      h1SmoothCoefficientL2 (ball (0 : ℂ) 1) a
          (h1Gradient (ball (0 : ℂ) 1) i (diskHardyExtension b)) +
        h1SmoothCoefficientDerivativeL2 (ball (0 : ℂ) 1) a i
          (h1Value (ball (0 : ℂ) 1) (diskHardyExtension b)) :=
  h1Gradient_neumannH1SmoothMultiplier _ a _ i

private theorem hardy_coefficient_derivative_CR 
    (hCR : ∀ z ∈ ball (0 : ℂ) 1,
      fderiv ℝ (a : ℂ → ℂ) z 1 = Complex.I * fderiv ℝ (a : ℂ → ℂ) z Complex.I)
    (u : L2 (ball (0 : ℂ) 1)) :
    h1SmoothCoefficientDerivativeL2 (ball (0 : ℂ) 1) a 0 u =
      Complex.I • h1SmoothCoefficientDerivativeL2 (ball (0 : ℂ) 1) a 1 u := by
  apply Lp.ext
  filter_upwards [h1SmoothCoefficientDerivativeL2_ae (ball (0 : ℂ) 1) a 0 u,
    h1SmoothCoefficientDerivativeL2_ae (ball (0 : ℂ) 1) a 1 u,
    Lp.coeFn_smul Complex.I (h1SmoothCoefficientDerivativeL2 (ball (0 : ℂ) 1) a 1 u),
    ae_restrict_mem measurableSet_ball] with z hx hy hs hz
  rw [hx, hs]
  simp only [Pi.smul_apply]
  rw [hy]
  change fderiv ℝ (a : ℂ → ℂ) z 1 * u z =
    Complex.I * (fderiv ℝ (a : ℂ → ℂ) z Complex.I * u z)
  rw [hCR z hz]
  ring

/-- An actual smooth antiholomorphic coefficient preserves the genuine
weak CR equation of the completed disk Hardy extension. -/
theorem diskHardySmoothProduct_cauchyRiemann 
    (hCR : ∀ z ∈ ball (0 : ℂ) 1,
      fderiv ℝ (a : ℂ → ℂ) z 1 = Complex.I * fderiv ℝ (a : ℂ → ℂ) z Complex.I)
    (b : L2Z) :
    h1Gradient (ball (0 : ℂ) 1) 0 (diskHardySmoothProduct a b) =
      Complex.I • h1Gradient (ball (0 : ℂ) 1) 1 (diskHardySmoothProduct a b) := by
  rw [h1Gradient_diskHardySmoothProduct, h1Gradient_diskHardySmoothProduct,
    diskHardyExtension_cauchyRiemann, map_smul,
    hardy_coefficient_derivative_CR a hCR, smul_add]

end

section

variable {R : ℝ} (hR : 1 < R) (F : ℂ → ℂ) (hFs : ContDiffOn ℝ (⊤ : ℕ∞) F (ball (0 : ℂ) R))
include R hR F hFs

/-- The actual compact coefficient conjugate to the supplied conformal
derivative. It is smooth globally because the actual F is cut off first. -/
def localConformalHardyDerivativeTest  : smoothTraceTests :=
  ⟨fun z => conj (dirD (smoothDiskCutoff R hR F) 1 z),
    ((smoothDiskCutoff_testFunction hR hFs).dirD 1).conj⟩

def localConformalHardyDerivativeCoefficient  : SmoothH1Coefficient :=
  smoothTraceTestsH1Coefficient (localConformalHardyDerivativeTest hR F hFs)

theorem localConformalHardyDerivativeCoefficient_closedDisk 
    {z : ℂ} (hz : z ∈ closedBall (0 : ℂ) 1) :
    localConformalHardyDerivativeCoefficient hR F hFs z = conj (fderiv ℝ F z 1) := by
  change conj (fderiv ℝ (smoothDiskCutoff R hR F) z 1) = _
  rw [fderiv_smoothDiskCutoff_eq hR F hz]

end

private theorem hardy_real_derivative_of_holomorphic {U : Set ℂ} (hU : IsOpen U)
    {F : ℂ → ℂ} (hF : DifferentiableOn ℂ F U) {z : ℂ} (hz : z ∈ U) (v : ℂ) :
    fderiv ℝ F z v = deriv F z * v := by
  rw [(hF.differentiableAt (hU.mem_nhds hz)).fderiv_restrictScalars ℝ]
  exact id fderiv_eq_deriv_mul

section

variable {R : ℝ} (hR : 1 < R) (F : ℂ → ℂ) (hFs : ContDiffOn ℝ (⊤ : ℕ∞) F (ball (0 : ℂ) R))
include R hR F hFs

/-- The actual cutoff coefficient has the derivative of conj(F′) in the
interior, derived from holomorphic F′ and its real chain rule. -/
theorem localConformalHardyDerivativeCoefficient_fderiv 
    (hhol : DifferentiableOn ℂ F (ball (0 : ℂ) 1))
    {z : ℂ} (hz : z ∈ ball (0 : ℂ) 1) (v : ℂ) :
    fderiv ℝ (localConformalHardyDerivativeCoefficient hR F hFs : ℂ → ℂ) z v =
      conj (deriv (deriv F) z * v) := by
  have he : (localConformalHardyDerivativeCoefficient hR F hFs : ℂ → ℂ)
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
    (hhol : DifferentiableOn ℂ F (ball (0 : ℂ) 1)) {z : ℂ} (hz : z ∈ ball (0 : ℂ) 1) :
    fderiv ℝ (localConformalHardyDerivativeCoefficient hR F hFs : ℂ → ℂ) z 1 =
      Complex.I * fderiv ℝ
        (localConformalHardyDerivativeCoefficient hR F hFs : ℂ → ℂ) z Complex.I := by
  rw [localConformalHardyDerivativeCoefficient_fderiv hR F hFs hhol hz 1,
    localConformalHardyDerivativeCoefficient_fderiv hR F hFs hhol hz Complex.I]
  grind [mul_one, map_mul, Complex.conj_I, Complex.I_mul_I]

/-- The genuine disk product needed for the interior physical primitive. -/
def localConformalHardyDerivativeProduct  :
    L2Z →L[ℂ] NeumannH1 (ball (0 : ℂ) 1) :=
  diskHardySmoothProduct (localConformalHardyDerivativeCoefficient hR F hFs)

end

/-- Actual angular-velocity multiplier data for the primitive. -/
def localConformalHardyPrimitiveMultiplier (F : ℂ → ℂ) : ℤ → ℂ :=
  fourierCoeffOn Real.two_pi_pos (fun θ => conj (deriv (physicalCircleTrace F) θ))

section

variable {R : ℝ} (hR : 1 < R) (F : ℂ → ℂ) (hFs : ContDiffOn ℝ (⊤ : ℕ∞) F (ball (0 : ℂ) R))
include R hR F hFs

theorem localConformalHardyPrimitiveMultiplier_isWL1  :
    IsWL1 (1 / 2 : ℝ) (localConformalHardyPrimitiveMultiplier F) := by
  have h1 := (physicalCircleTrace_fourier_weights_of_smooth_neighborhood hR F hFs).1
  refine h1.of_nonneg_of_le (fun n => ?_) (fun n => ?_)
  exact mul_nonneg (Real.rpow_nonneg (sobWeight_pos n).le _) (norm_nonneg _)
  · exact mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow_of_exponent_le (one_le_sobWeight n) (by norm_num)) (norm_nonneg _)

theorem localConformalHardyPrimitiveMultiplier_strictNegative 
    (hhol : DifferentiableOn ℂ F (ball (0 : ℂ) 1)) :
    IsStrictNegativeFourierSupport (localConformalHardyPrimitiveMultiplier F) :=
  physicalCircleTrace_conj_deriv_strictNegative_of_neighborhood hR F
    (hFs.of_le (by simp)) hhol

/-- The actual supplied-coordinate primitive on normalized half-trace data. -/
def localConformalHardyPrimitive  : L2Z →L[ℂ] L2Z :=
  normalizedHardyPrimitive (localConformalHardyPrimitiveMultiplier F)
    (localConformalHardyPrimitiveMultiplier_isWL1 hR F hFs)

end

private theorem hardy_fourier_one_circle (θ : ℝ) :
    fourier (T := 2 * Real.pi) 1 (θ : AddCircle (2 * Real.pi)) = circleMap 0 1 θ := by
  rw [fourier_coe_two_pi, circleMap_zero]
  simp

/-- The actual boundary coefficient as a continuous circle function. -/
def diskSmoothCoefficientCircle (a : SmoothH1Coefficient) :
    C(AddCircle (2 * Real.pi), ℂ) :=
  ⟨fun q => a (fourier (T := 2 * Real.pi) 1 q),
    a.smooth.continuous.comp (fourier (T := 2 * Real.pi) 1).continuous⟩

theorem diskSmoothCoefficientCircle_apply (a : SmoothH1Coefficient) (θ : ℝ) :
    diskSmoothCoefficientCircle a (θ : AddCircle (2 * Real.pi)) = a (circleMap 0 1 θ) := by
  change a (fourier (T := 2 * Real.pi) 1 (θ : AddCircle (2 * Real.pi))) = _
  rw [hardy_fourier_one_circle]

private theorem hardy_fourierCoeffOn_circle (A : C(AddCircle (2 * Real.pi), ℂ)) (n : ℤ) :
    fourierCoeffOn Real.two_pi_pos (fun θ : ℝ => A (θ : AddCircle (2 * Real.pi))) n =
      fourierCoeff A n := by
  have he : AddCircle.liftIoc (2 * Real.pi) 0
      (fun θ : ℝ => A (θ : AddCircle (2 * Real.pi))) = (A : AddCircle (2 * Real.pi) → ℂ) := by
    funext q
    change A ((AddCircle.equivIoc (2 * Real.pi) 0 q : ℝ) : AddCircle (2 * Real.pi)) = A q
    simp
  have h := fourierCoeff_liftIoc_eq (T := 2 * Real.pi) (a := 0)
    (fun θ : ℝ => A (θ : AddCircle (2 * Real.pi))) n
  simp_all

theorem diskSmoothCoefficientCircle_coeff (a : SmoothH1Coefficient) (n : ℤ) :
    fourierCoeff (diskSmoothCoefficientCircle a) n =
      fourierCoeffOn Real.two_pi_pos (fun θ => a (circleMap 0 1 θ)) n := by
  rw [← hardy_fourierCoeffOn_circle]
  congr 1
  funext θ
  exact diskSmoothCoefficientCircle_apply a θ

theorem diskSmoothCoefficientCircle_isWL1 (a : SmoothH1Coefficient) :
    IsWL1 (1 / 2 : ℝ) (fourierCoeff (diskSmoothCoefficientCircle a)) := by
  have hf : ContDiff ℝ 4 (fun θ : ℝ => a (circleMap 0 1 θ)) :=
    (a.smooth.of_le (WithTop.coe_le_coe.mpr le_top)).comp (contDiff_circleMap 0 1)
  have hp :=
    (periodic_circleMap 0 1).comp (a : ℂ → ℂ)
  have h2 := (periodic_contDiff_four_fourier_weights hf hp).2
  change Summable (fun n => sobWeight n ^ (1 / 2 : ℝ) *
    ‖fourierCoeff (diskSmoothCoefficientCircle a) n‖)
  simp_rw [diskSmoothCoefficientCircle_coeff]
  refine h2.of_nonneg_of_le (fun n => ?_) (fun n => ?_)
  exact mul_nonneg (Real.rpow_nonneg (sobWeight_pos n).le _) (norm_nonneg _)
  · exact mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow_of_exponent_le (one_le_sobWeight n) (by norm_num)) (norm_nonneg _)

private theorem hardy_fourierCoeff_shift (C : C(AddCircle (2 * Real.pi), ℂ)) (n : ℤ) :
    fourierCoeff (fun q => fourier (T := 2 * Real.pi) (-1) q * C q) n =
      fourierCoeff C (n + 1) := by
  simp only [fourierCoeff]
  apply integral_congr_ae
  exact Eventually.of_forall (fun q => by simp [mul_assoc] <;> ring)

section

variable {R : ℝ} (hR : 1 < R) (F : ℂ → ℂ) (hFs : ContDiffOn ℝ (⊤ : ℕ∞) F (ball (0 : ℂ) R)) (hhol : DifferentiableOn ℂ F (ball (0 : ℂ) 1))
include R hR F hFs hhol

/-- The conjugated angular velocity has precisely the shifted coefficient
of conj(F′), including its phase -i. -/
theorem localConformalHardyPrimitiveMultiplier_shift  (n : ℤ) :
    localConformalHardyPrimitiveMultiplier F n = (-Complex.I) *
      fourierCoeff (diskSmoothCoefficientCircle
        (localConformalHardyDerivativeCoefficient hR F hFs)) (n + 1) := by
  let C := diskSmoothCoefficientCircle (localConformalHardyDerivativeCoefficient hR F hFs)
  let B : C(AddCircle (2 * Real.pi), ℂ) := (-Complex.I) •
    ((fourier (T := 2 * Real.pi) (-1)) * C)
  have he (θ : ℝ) : conj (deriv (physicalCircleTrace F) θ) =
      B (θ : AddCircle (2 * Real.pi)) := by
    rw [localConformal_circleTrace_deriv hR F hFs hhol]
    simp only [map_mul, Complex.conj_I]
    simp only [B, ContinuousMap.smul_apply, ContinuousMap.mul_apply]
    rw [fourier_neg, hardy_fourier_one_circle, diskSmoothCoefficientCircle_apply,
      localConformalHardyDerivativeCoefficient_closedDisk hR F hFs
        (circleMap_mem_closedBall 0 (by norm_num) θ)]
    ring
  change fourierCoeffOn Real.two_pi_pos
    (fun θ => conj (deriv (physicalCircleTrace F) θ)) n = _
  rw [show (fun θ => conj (deriv (physicalCircleTrace F) θ)) =
      (fun θ : ℝ => B (θ : AddCircle (2 * Real.pi))) from funext he,
    hardy_fourierCoeffOn_circle]
  change fourierCoeff ((-Complex.I) •
    (fun q => fourier (T := 2 * Real.pi) (-1) q * C q)) n = _
  grind [fourierCoeff.const_smul, smul_eq_mul, hardy_fourierCoeff_shift]

theorem localConformalHardyDerivativeCoefficient_nonpositive  :
    IsNonpositiveFourierSupport (fourierCoeff (diskSmoothCoefficientCircle
      (localConformalHardyDerivativeCoefficient hR F hFs))) := by
  intro n hn
  have ha := localConformalHardyPrimitiveMultiplier_strictNegative hR F hFs hhol
    (n - 1) (by omega)
  rw [localConformalHardyPrimitiveMultiplier_shift hR F hFs hhol,
    sub_add_cancel] at ha
  simp_all

end

private theorem hardy_seqConv_nonpositive {c h : ℤ → ℂ}
    (hc : IsNonpositiveFourierSupport c) (hh : IsNonpositiveFourierSupport h) :
    IsNonpositiveFourierSupport (seqConv c h) := by
  intro n hn
  unfold seqConv
  have he : (fun k => c k * h (n - k)) = (fun _ : ℤ => (0 : ℂ)) := by
    funext k
    by_cases hk : 0 < k
    aesop
    · rw [hh (n - k) (by omega), mul_zero]
  simp_all

private theorem hardy_seqConv_shift {a c : ℤ → ℂ}
    (hshift : ∀ n : ℤ, a n = (-Complex.I) * c (n + 1)) (h : ℤ → ℂ) (n : ℤ) :
    seqConv a h (n - 1) = (-Complex.I) * seqConv c h n := by
  unfold seqConv
  calc
    _ = (-Complex.I) * ∑' k : ℤ, c (k + 1) * h (n - (k + 1)) := by grind [tsum_mul_left]
    _ = _ := congrArg (fun x : ℂ => (-Complex.I) * x)
      ((Equiv.addRight (1 : ℤ)).tsum_eq (fun k => c k * h (n - k)))

private theorem hardy_primitive_derivative_scalar (x y sx sy : ℂ)
    (hx : x ≠ 0) (hy : y ≠ 0) (hsy : sy ≠ 0) :
    (x / y * (sx / sy)) * ((sy * y) / (Complex.I * (-x))) * (-Complex.I) = sx := by
  field_simp [hx, hy, hsy, Complex.I_ne_zero]

private theorem hardy_primitive_derivative_scale (k : ℕ) :
    (diskHardyDerivativeWeight k : ℂ) *
        (((sobWeight (-((k + 1 : ℕ) : ℤ)) ^ ((1 / 2 : ℝ) + 1) : ℝ) : ℂ) /
          (Complex.I * (-((k + 1 : ℕ) : ℂ)))) * (-Complex.I) =
      ((sobWeight (-(k : ℤ)) ^ (1 / 2 : ℝ) : ℝ) : ℂ) := by
  rw [sobWeight_neg_nat, sobWeight_neg_nat]
  have hy : (((k + 1 + 1 : ℕ) : ℝ) ^ ((1 / 2 : ℝ) + 1)) =
      Real.sqrt ((k + 2 : ℕ) : ℝ) * ((k + 2 : ℕ) : ℝ) := by
    have hi : k + 1 + 1 = k + 2 := by omega
    rw [Real.rpow_add (by positivity), Real.rpow_one, ← Real.sqrt_eq_rpow]
  rw [hy, ← Real.sqrt_eq_rpow]
  simp only [diskHardyDerivativeWeight, Real.sqrt_div (by positivity : (0 : ℝ) ≤ ((k + 1 : ℕ) : ℝ))]
  have hx : ((k + 1 : ℕ) : ℂ) ≠ 0 := by norm_cast
  have hy0 : ((k + 2 : ℕ) : ℂ) ≠ 0 := by norm_cast
  have hsy : (Real.sqrt ((k + 2 : ℕ) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr (by positivity : (0 : ℝ) < ((k + 2 : ℕ) : ℝ))).ne'
  simpa using hardy_primitive_derivative_scalar (↑(k + 1)) (↑(k + 2)) (↑√↑(k + 1)) (↑√↑(k + 2)) hx hy0 hsy

/-- The actual derivative-data operator on a normalized primitive is the
actual normalized product data. The input and product retain frequency zero. -/
theorem diskHardyDerivativeData_normalizedPrimitiveGain
    (a c : ℤ → ℂ) (ha : IsWL1 (1 / 2 : ℝ) a) (hc : IsWL1 (1 / 2 : ℝ) c)
    (hshift : ∀ n : ℤ, a n = (-Complex.I) * c (n + 1))
    (hcn : IsNonpositiveFourierSupport c) (b : L2Z)
    (hbn : IsNonpositiveFourierSupport b) :
    diskHardyDerivativeData (normalizedHardyPrimitiveGain a ha b) =
      normalizedHardyMultiplier c hc b := by
  have hb : IsNonpositiveFourierSupport (fromL2 (1 / 2 : ℝ) b) := by
    intro n hn
    simp only [fromL2, hbn n hn, mul_zero]
  ext n
  by_cases hn : 0 < n
  · rw [diskHardyDerivativeData_apply_pos _ hn, normalizedHardyMultiplier_apply,
      hardy_seqConv_nonpositive hcn hb n hn, mul_zero]
  · let k : ℕ := Int.toNat (-n)
    have hnk : n = -(k : ℤ) := by omega
    rw [hnk, diskHardyDerivativeData_apply_neg, normalizedHardyPrimitiveGain_apply,
      normalizedHardyMultiplier_apply]
    have hne : -((k + 1 : ℕ) : ℤ) ≠ 0 := by omega
    rw [antiPrim, if_neg hne, primSeq]
    have hi : -(k : ℤ) - 1 = -((k + 1 : ℕ) : ℤ) := by omega
    have hconv := hardy_seqConv_shift hshift (fromL2 (1 / 2 : ℝ) b) (-(k : ℤ))
    rw [hi] at hconv
    rw [hconv]
    simp only [Int.cast_neg, Int.cast_natCast]
    calc
      _ = ((diskHardyDerivativeWeight k : ℂ) *
          (((sobWeight (-((k + 1 : ℕ) : ℤ)) ^ ((1 / 2 : ℝ) + 1) : ℝ) : ℂ) /
            (Complex.I * (-((k + 1 : ℕ) : ℂ)))) * (-Complex.I)) *
              seqConv c (fromL2 (1 / 2 : ℝ) b) (-(k : ℤ)) := by ring
      _ = _ := by rw [hardy_primitive_derivative_scale]

theorem normalizedHardyMultiplier_nonpositive (c : ℤ → ℂ)
    (hc : IsWL1 (1 / 2 : ℝ) c) (hcn : IsNonpositiveFourierSupport c)
    (b : L2Z) (hbn : IsNonpositiveFourierSupport b) :
    IsNonpositiveFourierSupport (normalizedHardyMultiplier c hc b) := by
  have hb : IsNonpositiveFourierSupport (fromL2 (1 / 2 : ℝ) b) := by
    intro n hn
    simp  [fromL2, hbn n hn]
  intro n hn
  rw [normalizedHardyMultiplier_apply, hardy_seqConv_nonpositive hcn hb n hn, mul_zero]

private theorem hardy_trace_eq_of_halfTrace_eq
    (u v : NeumannH1 (ball (0 : ℂ) 1)) (h : diskHalfTrace u = diskHalfTrace v) :
    diskH1Trace u = diskH1Trace v := by
  apply boundaryFourier.injective
  apply lp.ext
  rw [← fromL2_half_diskHalfTrace, ← fromL2_half_diskHalfTrace, h]

/-- The actual completed antiholomorphic product is identified with its
completed Fourier extension by the proved weak CR trace uniqueness theorem. -/
theorem diskHardySmoothProduct_eq_extension (a : SmoothH1Coefficient)
    (hCR : ∀ z ∈ ball (0 : ℂ) 1,
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
  · change diskH1Trace (diskHardySmoothProduct a b) =
      diskH1Trace (diskHardyExtension
        (normalizedHardyMultiplier (fourierCoeff (diskSmoothCoefficientCircle a))
          (diskSmoothCoefficientCircle_isWL1 a) b))
    apply hardy_trace_eq_of_halfTrace_eq
    have hp := diskHalfTrace_smoothMultiplier a (diskSmoothCoefficientCircle a)
      (diskSmoothCoefficientCircle_apply a) (diskSmoothCoefficientCircle_isWL1 a)
      (diskHardyExtension b)
    rw [diskHalfTrace_diskHardyExtension_eq_of_nonpositive b hbn] at hp
    rw [diskHalfTrace_diskHardyExtension_eq_of_nonpositive _
      (normalizedHardyMultiplier_nonpositive _ _ hcn b hbn)]
    assumption

section

variable {R : ℝ} (hR : 1 < R) (F : ℂ → ℂ) (hFs : ContDiffOn ℝ (⊤ : ℕ∞) F (ball (0 : ℂ) R)) (hhol : DifferentiableOn ℂ F (ball (0 : ℂ) 1)) (b : L2Z) (hbn : IsNonpositiveFourierSupport b)
include R hR F hFs hhol b hbn

theorem localConformalHardyDerivativeProduct_eq_extension  :
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
theorem diskHardyExtension_localConformalPrimitive_gradient  :
    h1Gradient (ball (0 : ℂ) 1) 0
        (diskHardyExtension (localConformalHardyPrimitive hR F hFs b)) =
      h1SmoothCoefficientL2 (ball (0 : ℂ) 1)
        (localConformalHardyDerivativeCoefficient hR F hFs)
          (h1Value (ball (0 : ℂ) 1) (diskHardyExtension b)) := by
  change h1Gradient (ball (0 : ℂ) 1) 0 (diskHardyExtension
    (normalizedHardyPrimitive (localConformalHardyPrimitiveMultiplier F)
      (localConformalHardyPrimitiveMultiplier_isWL1 hR F hFs) b)) = _
  rw [diskHardyExtension_normalizedPrimitive_gradient,
    diskHardyDerivativeData_normalizedPrimitiveGain _ _ _
      (diskSmoothCoefficientCircle_isWL1 (localConformalHardyDerivativeCoefficient hR F hFs))
      (localConformalHardyPrimitiveMultiplier_shift hR F hFs hhol)
      (localConformalHardyDerivativeCoefficient_nonpositive hR F hFs hhol) b hbn,
    ← localConformalHardyDerivativeProduct_eq_extension hR F hFs hhol b hbn]
  rfl

/-- The normalized primitive preserves the entire Hardy subspace. -/
theorem localConformalHardyPrimitive_nonpositive  :
    IsNonpositiveFourierSupport (localConformalHardyPrimitive hR F hFs b) :=
  normalizedHardyPrimitive_nonpositive _ _
    (localConformalHardyPrimitiveMultiplier_strictNegative hR F hFs hhol) b hbn

end

section

variable (a : ℤ → ℂ) (ha : IsWL1 (1 / 2 : ℝ) a) (b : L2Z)
include a ha b

theorem fromL2_normalizedHardyPrimitive  :
    fromL2 (1 / 2 : ℝ) (normalizedHardyPrimitive a ha b) =
      antiPrim a (fromL2 (1 / 2 : ℝ) b) := by
  funext n
  rw [fromL2, normalizedHardyPrimitive_apply, ← mul_assoc, ← Complex.ofReal_mul,
    mul_comm (sobWeight n ^ (-(1 / 2 : ℝ))), sobWeight_rpow_mul_neg, Complex.ofReal_one,
    one_mul]

/-- Averaged coefficients of the normalized primitive are the same `antiPrim`
coefficients, including its prescribed zero coefficient. -/
theorem normalizedHardyAverage_primitive  :
    normalizedHardyAverage (normalizedHardyPrimitive a ha b) =
      antiPrim a (normalizedHardyAverage b) := by
  change (Real.sqrt (2 * Real.pi) : ℂ)⁻¹ •
      fromL2 (1 / 2 : ℝ) (normalizedHardyPrimitive a ha b) =
    antiPrim a ((Real.sqrt (2 * Real.pi) : ℂ)⁻¹ • fromL2 (1 / 2 : ℝ) b)
  rw [fromL2_normalizedHardyPrimitive,
    (seqOpBound_antiPrim (by norm_num : (0 : ℝ) ≤ 1 / 2) ha).map_smul _ _
      (isSobolevSeq_fromL2 (1 / 2 : ℝ) b)]

end

/-- Multiplication by actual conj(F′) on pullback values equals the actual
Jacobian phase times the genuine weighted L² pullback of physical values. -/
theorem localConformalHardyDerivativeCoefficient_pullback_value {F : ℂ → ℂ}
    (coords : ConformalDiskCoordinates F)
    (u : NeumannH1 (F '' ball (0 : ℂ) 1)) :
    h1SmoothCoefficientL2 (ball (0 : ℂ) 1)
      (localConformalHardyDerivativeCoefficient coords.one_lt_radius F coords.smooth)
        (h1Value (ball (0 : ℂ) 1) (coords.pullback u)) =
      localConformalPhaseMultiplier F true
        (localConformalWeightedL2Pullback coords
          (h1Value (F '' ball (0 : ℂ) 1) u)) := by
  rw [localConformalWeightedL2Pullback_h1Value coords]
  let v := h1Value (ball (0 : ℂ) 1) (coords.pullback u)
  change h1SmoothCoefficientL2 _ _ v = localConformalPhaseMultiplier F true
    (localConformalMassMultiplier coords v)
  apply Lp.ext
  filter_upwards [h1SmoothCoefficientL2_ae _ (localConformalHardyDerivativeCoefficient coords.one_lt_radius F coords.smooth) v,
    localConformalPhaseMultiplier_ae F true (localConformalMassMultiplier coords v),
    localConformalMassMultiplier_ae coords v, ae_restrict_mem measurableSet_ball] with z ha hp hm hz
  rw [ha, hp, hm,
    localConformalHardyDerivativeCoefficient_closedDisk coords.one_lt_radius F coords.smooth (ball_subset_closedBall hz),
    ← mul_assoc, localConformalPhase_mul_massDensity coords true hz]
  rfl

section PhysicalPrimitive

variable {F : ℂ → ℂ} (coords : ConformalDiskCoordinates F)
include coords

section

variable (b : L2Z) (hbn : IsNonpositiveFourierSupport b)
include b hbn

/-- The primitive has the actual physical x derivative U(b), proved from
the disk derivative identity and cancellation of the genuine Jacobian phase
and the norm-preserving physical L² pullback. -/
theorem localConformalHardyH1Extension_primitive_gradient  :
    h1Gradient (F '' ball (0 : ℂ) 1) 0
      (localConformalHardyH1Extension coords
        (localConformalHardyPrimitive coords.one_lt_radius F coords.smooth b)) =
      h1Value (F '' ball (0 : ℂ) 1)
        (localConformalHardyH1Extension coords b) := by
  apply localConformalWeightedL2Pullback_injective coords
  apply localConformalPhaseMultiplier_injective coords true
  calc
    _ = h1Gradient (ball (0 : ℂ) 1) 0 (coords.pullback
      (localConformalHardyH1Extension coords
        (localConformalHardyPrimitive coords.one_lt_radius F coords.smooth b))) :=
      (localConformalH1Pullback_gradient_antiholomorphic coords _
        (localConformalHardyH1Extension_cauchyRiemann coords _)).symm
    _ = h1Gradient (ball (0 : ℂ) 1) 0
      (diskHardyExtension (localConformalHardyPrimitive coords.one_lt_radius F coords.smooth b)) := by simp
    _ = h1SmoothCoefficientL2 (ball (0 : ℂ) 1)
      (localConformalHardyDerivativeCoefficient coords.one_lt_radius F coords.smooth)
        (h1Value (ball (0 : ℂ) 1) (diskHardyExtension b)) :=
      diskHardyExtension_localConformalPrimitive_gradient coords.one_lt_radius F coords.smooth coords.holomorphic b hbn
    _ = _ := by
      have h := localConformalHardyDerivativeCoefficient_pullback_value coords
        (localConformalHardyH1Extension coords b)
      simp_all

/-- The physical y derivative has the true antiholomorphic sign. -/
theorem localConformalHardyH1Extension_primitive_gradient_y  :
    h1Gradient (F '' ball (0 : ℂ) 1) 1
      (localConformalHardyH1Extension coords
        (localConformalHardyPrimitive coords.one_lt_radius F coords.smooth b)) =
      (-Complex.I) • h1Value (F '' ball (0 : ℂ) 1)
        (localConformalHardyH1Extension coords b) := by
  calc
    _ = (-Complex.I) • h1Gradient (F '' ball (0 : ℂ) 1) 0
      (localConformalHardyH1Extension coords
        (localConformalHardyPrimitive coords.one_lt_radius F coords.smooth b)) := by
      rw [localConformalHardyH1Extension_cauchyRiemann, smul_smul]
      simp
    _ = _ := by rw [localConformalHardyH1Extension_primitive_gradient coords b hbn]

end

end PhysicalPrimitive

end PolyaNeumann

end
