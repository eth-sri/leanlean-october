module

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


noncomputable section

namespace PolyaNeumann

open MeasureTheory Set Metric Filter
open scoped Topology ComplexConjugate ContDiff

variable {R : ℝ} {z : ℂ}

local instance hardyPrimitiveCircleTwoPiPos : Fact (0 < 2 * Real.pi) := ⟨Real.two_pi_pos⟩

/-- Averaged coefficients of an actual half-trace vector. -/
def normalizedHardyAverage (b : L2Z) (n : ℤ) : ℂ :=
  (Real.sqrt (2 * Real.pi) : ℂ)⁻¹ * fromL2 (1 / 2 : ℝ) b n

private theorem hardy_toCLM_apply {s t C : ℝ}
     (H : SeqOpBound s t C Φ) b n :
    H.toCLM b n = ((sobWeight n ^ t : ℝ) : ℂ) * Φ (fromL2 s b) n := rfl

/-- Bounded multiplication on normalized half-order Fourier coordinates.
The multiplier coefficients use the averaged convention. -/
def normalizedHardyMultiplier (c : ℤ → ℂ) (hc : IsWL1 (1 / 2 : ℝ) c) :
    L2Z →L[ℂ] L2Z :=
  (seqOpBound_seqConv (by norm_num : (0 : ℝ) ≤ 1 / 2) hc).toCLM

theorem normalizedHardyMultiplier_apply c
    (hc : IsWL1 (1 / 2 : ℝ) c) b n :
    normalizedHardyMultiplier c hc b n =
      ((sobWeight n ^ (1 / 2 : ℝ) : ℝ) : ℂ) * seqConv c (fromL2 (1 / 2 : ℝ) b) n :=
  hardy_toCLM_apply _ b n

/-- The primitive in the stronger normalized coordinates of order 3/2. -/
def normalizedHardyPrimitiveGain (a : ℤ → ℂ) (ha : IsWL1 (1 / 2 : ℝ) a) :
    L2Z →L[ℂ] L2Z :=
  (seqOpBound_antiPrim (by norm_num : (0 : ℝ) ≤ 1 / 2) ha).toCLM

theorem normalizedHardyPrimitiveGain_apply a
    (ha : IsWL1 (1 / 2 : ℝ) a) b n :
    normalizedHardyPrimitiveGain a ha b n =
      ((sobWeight n ^ ((1 / 2 : ℝ) + 1) : ℝ) : ℂ) *
        antiPrim a (fromL2 (1 / 2 : ℝ) b) n :=
  hardy_toCLM_apply _ b n

/-- The actual normalized primitive at order 1/2, retaining the constant
chosen by `antiPrim` at the same boundary origin. -/
def normalizedHardyPrimitive (a : ℤ → ℂ) (ha : IsWL1 (1 / 2 : ℝ) a) :
    L2Z →L[ℂ] L2Z :=
  (sobolevSmoothing 1 (by norm_num)).comp (normalizedHardyPrimitiveGain a ha)

theorem normalizedHardyPrimitive_apply a
    ha b n :
    normalizedHardyPrimitive a ha b n =
      ((sobWeight n ^ (1 / 2 : ℝ) : ℝ) : ℂ) * antiPrim a (fromL2 (1 / 2) b) n := by
  change sobolevSmoothing 1 (by norm_num) (normalizedHardyPrimitiveGain a ha b) n = _
  simp only [sobolevSmoothing, diagOp_apply, normalizedHardyPrimitiveGain_apply]
  rw [← mul_assoc, ← Complex.ofReal_mul, ← Real.rpow_add (sobWeight_pos n), show -1 + ((1 / 2 : ℝ) + 1) = 1 / 2 by ring]

/-- Actual L² derivative of the completed disk primitive. This identifies
the derivative with the completed derivative data, before a product is
identified using the genuine Hardy trace uniqueness theorem. -/
local notation "Φ1" => ball 0 1

theorem diskHardyExtension_normalizedPrimitive_gradient a
    ha b :
    h1Gradient (Φ1) 0 (diskHardyExtension (normalizedHardyPrimitive a ha b)) =
      h1Value (Φ1)
        (diskHardyExtension (diskHardyDerivativeData (normalizedHardyPrimitiveGain a ha b))) :=
  diskHardyExtension_smoothing_gradient (normalizedHardyPrimitiveGain a ha b)

/-- Genuine disk H¹ multiplication of the actual completed Hardy extension. -/
def diskHardySmoothProduct (a : SmoothH1Coefficient) :
    L2Z →L[ℂ] NeumannH1 (Φ1) :=
  (neumannH1SmoothMultiplier (Φ1) a).comp diskHardyExtension

theorem h1Gradient_diskHardySmoothProduct a b i :
    h1Gradient (Φ1) i (diskHardySmoothProduct a b) =
      h1SmoothCoefficientL2 (Φ1) a
          (h1Gradient (Φ1) i (diskHardyExtension b)) +
        h1SmoothCoefficientDerivativeL2 (Φ1) a i
          (h1Value (Φ1) (diskHardyExtension b)) :=
  h1Gradient_neumannH1SmoothMultiplier _ a _ i

local notation "Φ3" => ball 0 R

def localConformalHardyDerivativeCoefficient  (hR : 1 < R) (F : ℂ → ℂ)
    (hFs : ContDiffOn ℝ ∞ F (Φ3)) : SmoothH1Coefficient :=
  smoothTraceTestsH1Coefficient ⟨fun z => conj (dirD (smoothDiskCutoff R hR F) 1 z), ((smoothDiskCutoff_testFunction hR hFs).dirD 1).conj⟩

theorem localConformalHardyDerivativeCoefficient_closedDisk  (hR : 1 < R)
    F (hFs : ContDiffOn ℝ ∞ F (Φ3))
     (hz : z ∈ closedBall 0 1) :
    localConformalHardyDerivativeCoefficient hR F hFs z = conj (fderiv ℝ F z 1) := by
  change conj (fderiv ℝ (smoothDiskCutoff R hR F) z 1) = _
  rw [fderiv_smoothDiskCutoff_eq hR F hz]

private theorem hardy_real_derivative_of_holomorphic  (hU : IsOpen U)
    {F : ℂ → ℂ} (hF : DifferentiableOn ℂ F U)  (hz : z ∈ U) v :
    fderiv ℝ F z v = deriv F z * v := by
  rw [(hF.differentiableAt (hU.mem_nhds hz)).fderiv_restrictScalars ℝ]
  exact fderiv_eq_deriv_mul

/-- The actual cutoff coefficient has the derivative of conj(F′) in the
interior, derived from holomorphic F′ and its real chain rule. -/
theorem localConformalHardyDerivativeCoefficient_fderiv  (hR : 1 < R)
    F hFs
    (hhol : DifferentiableOn ℂ F (Φ1))
     (hz : z ∈ Φ1) v :
    fderiv ℝ (localConformalHardyDerivativeCoefficient hR F hFs : ℂ → ℂ) z v =
      conj (deriv (deriv F) z * v) := by
  have he : localConformalHardyDerivativeCoefficient hR F hFs
      =ᶠ[𝓝 z] fun w => conj (deriv F w) := by
    filter_upwards [isOpen_ball.mem_nhds hz] with w hw
    rw [localConformalHardyDerivativeCoefficient_closedDisk hR F hFs (ball_subset_closedBall hw),
      hardy_real_derivative_of_holomorphic isOpen_ball hhol hw 1, mul_one]
  rw [he.fderiv_eq (𝕜 := ℝ), show (fun w => conj (deriv F w)) = Complex.conjCLE ∘ deriv F from rfl, (Complex.conjCLE.hasFDerivAt.comp z (((hhol.deriv isOpen_ball).differentiableAt (isOpen_ball.mem_nhds hz)).restrictScalars ℝ).hasFDerivAt).fderiv]
  change conj (fderiv ℝ (deriv F) z v) = _
  rw [hardy_real_derivative_of_holomorphic isOpen_ball (hhol.deriv isOpen_ball) hz v]

theorem localConformalHardyDerivativeCoefficient_cauchyRiemann  (hR : 1 < R)
    F (hFs : ContDiffOn ℝ ∞ F (Φ3))
    (hhol : DifferentiableOn ℂ F (Φ1))  (hz : z ∈ Φ1) :
    fderiv ℝ (localConformalHardyDerivativeCoefficient hR F hFs : ℂ → ℂ) z 1 =
      Complex.I * fderiv ℝ
        (localConformalHardyDerivativeCoefficient hR F hFs : ℂ → ℂ) z Complex.I := by
  rw [localConformalHardyDerivativeCoefficient_fderiv hR F hFs hhol hz 1,
    localConformalHardyDerivativeCoefficient_fderiv hR F hFs hhol hz Complex.I]
  simp
  calc
    _ = -(Complex.I * Complex.I) * conj (deriv (deriv F) z) := by
      rw [Complex.I_mul_I]
      simp
    _ = _ := by ring

/-- Actual angular-velocity multiplier data for the primitive. -/
def localConformalHardyPrimitiveMultiplier (F : ℂ → ℂ) : ℤ → ℂ :=
  fourierCoeffOn Real.two_pi_pos (fun θ => conj (deriv (physicalCircleTrace F) θ))

theorem localConformalHardyPrimitiveMultiplier_isWL1  (hR : 1 < R)
    F (hFs : ContDiffOn ℝ ∞ F (Φ3)) :
    IsWL1 (1 / 2) (localConformalHardyPrimitiveMultiplier F) := by
  refine ((physicalCircleTrace_fourier_weights_of_smooth_neighborhood hR F hFs).1).of_nonneg_of_le (fun n => ?_) (fun n => ?_)
  · exact mul_nonneg (Real.rpow_nonneg (sobWeight_pos n).le _) (norm_nonneg _)
  · exact mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow_of_exponent_le (one_le_sobWeight n) (by norm_num)) (norm_nonneg _)

theorem localConformalHardyPrimitiveMultiplier_strictNegative  (hR : 1 < R)
    F (hFs : ContDiffOn ℝ ∞ F (Φ3))
    (hhol : DifferentiableOn ℂ F (Φ1)) :
    IsStrictNegativeFourierSupport (localConformalHardyPrimitiveMultiplier F) :=
  physicalCircleTrace_conj_deriv_strictNegative_of_neighborhood hR F
    (hFs.of_le (by simp)) hhol

/-- The actual supplied-coordinate primitive on normalized half-trace data. -/
def localConformalHardyPrimitive  (hR : 1 < R) (F : ℂ → ℂ)
    (hFs : ContDiffOn ℝ ∞ F (Φ3)) : L2Z →L[ℂ] L2Z :=
  normalizedHardyPrimitive (localConformalHardyPrimitiveMultiplier F)
    (localConformalHardyPrimitiveMultiplier_isWL1 hR F hFs)

private theorem hardy_fourier_one_circle (θ : ℝ) :
    fourier (T := 2 * Real.pi) 1 (θ : AddCircle (2 * Real.pi)) = circleMap 0 1 θ := by
  rw [fourier_coe_two_pi, circleMap_zero]
  simp

/-- The actual boundary coefficient as a continuous circle function. -/
def diskSmoothCoefficientCircle (a : SmoothH1Coefficient) :
    C(AddCircle (2 * Real.pi), ℂ) :=
  ⟨fun q => a (fourier (T := 2 * Real.pi) 1 q),
    a.smooth.continuous.comp (fourier (T := 2 * Real.pi) 1).continuous⟩

theorem diskSmoothCoefficientCircle_apply a (θ : ℝ) :
    diskSmoothCoefficientCircle a (θ : AddCircle (2 * Real.pi)) = a (circleMap 0 1 θ) := by
  change a (fourier (T := 2 * Real.pi) 1 (θ : AddCircle (2 * Real.pi))) = _
  rw [hardy_fourier_one_circle]

private theorem hardy_fourierCoeffOn_circle (A : C(AddCircle (2 * Real.pi), ℂ)) n :
    fourierCoeffOn Real.two_pi_pos (fun θ => A (θ : AddCircle (2 * Real.pi))) n =
      fourierCoeff A n := by
  have he : AddCircle.liftIoc (2 * Real.pi) 0
      (fun θ => A (θ : AddCircle (2 * Real.pi))) = (A : AddCircle (2 * Real.pi) → ℂ) := by
    funext q
    change A (AddCircle.equivIoc (2 * Real.pi) 0 q : ℝ) = _
    have hrep : ((AddCircle.equivIoc (2 * Real.pi) 0 q) :
        AddCircle (2 * Real.pi)) = q :=
      (AddCircle.equivIoc (2 * Real.pi) 0).symm_apply_apply q
    rw [hrep]
  have h := fourierCoeff_liftIoc_eq (T := 2 * Real.pi) (a := 0)
    (fun θ => A (θ : AddCircle (2 * Real.pi))) n
  rw [he] at h
  simpa using h.symm

theorem diskSmoothCoefficientCircle_coeff (a : SmoothH1Coefficient) n :
    fourierCoeff (diskSmoothCoefficientCircle a) n =
      fourierCoeffOn Real.two_pi_pos (fun θ => a (circleMap 0 1 θ)) n := by
  rw [← hardy_fourierCoeffOn_circle]
  congr 1
  funext θ
  exact diskSmoothCoefficientCircle_apply a θ

theorem diskSmoothCoefficientCircle_isWL1 a :
    IsWL1 (1 / 2) (fourierCoeff (diskSmoothCoefficientCircle a)) := by
  change Summable (fun n => sobWeight n ^ (1 / 2) *
    ‖fourierCoeff (diskSmoothCoefficientCircle a) n‖)
  simp_rw [diskSmoothCoefficientCircle_coeff]
  refine ((periodic_contDiff_four_fourier_weights ((a.smooth.of_le (WithTop.coe_le_coe.mpr le_top)).comp (contDiff_circleMap 0 1)) ((periodic_circleMap 0 1).comp a)).2).of_nonneg_of_le (fun n => ?_) (fun n => ?_)
  · exact mul_nonneg (Real.rpow_nonneg (sobWeight_pos n).le _) (norm_nonneg _)
  · exact mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow_of_exponent_le (one_le_sobWeight n) (by norm_num)) (norm_nonneg _)

theorem localConformalHardyPrimitiveMultiplier_shift  (hR : 1 < R)
    F (hFs : ContDiffOn ℝ ∞ F (Φ3))
    (hhol : DifferentiableOn ℂ F (ball (0 : ℂ) 1)) (n : ℤ) :
    localConformalHardyPrimitiveMultiplier F n = (-Complex.I) *
      fourierCoeff (diskSmoothCoefficientCircle
        (localConformalHardyDerivativeCoefficient hR F hFs)) (n + 1) := by
  let C := diskSmoothCoefficientCircle (localConformalHardyDerivativeCoefficient hR F hFs)
  let B : C(AddCircle (2 * Real.pi), ℂ) := (-Complex.I) •
    ((fourier (T := 2 * Real.pi) (-1)) * C)
  have he θ : conj (deriv (physicalCircleTrace F) θ) =
      B (θ : AddCircle (2 * Real.pi)) := by
    rw [localConformal_circleTrace_deriv hR F hFs hhol]
    simp
    simp only [B, ContinuousMap.smul_apply, ContinuousMap.mul_apply, smul_eq_mul]
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
  rw [fourierCoeff.const_smul]
  simp only [smul_eq_mul]
  have h_inl C n : fourierCoeff (fun q => fourier (T := 2 * Real.pi) (-1) q * C q) n = fourierCoeff C (n + 1) := by
    simp only [fourierCoeff, smul_eq_mul]
    apply integral_congr_ae
    exact Eventually.of_forall (fun q => by
      change fourier (T := 2 * Real.pi) (-n) q *
        (fourier (T := 2 * Real.pi) (-1) q * C q) = _
      rw [← mul_assoc, ← fourier_add]
      rw [show -n + (-1) = -(n + 1) by omega])
  rw [h_inl]

theorem localConformalHardyDerivativeCoefficient_nonpositive  (hR : 1 < R)
    (F : ℂ → ℂ) (hFs : ContDiffOn ℝ ∞ F (Φ3))
    (hhol : DifferentiableOn ℂ F (Φ1)) :
    IsNonpositiveFourierSupport (fourierCoeff (diskSmoothCoefficientCircle
      (localConformalHardyDerivativeCoefficient hR F hFs))) := by
  intro n hn
  have ha := localConformalHardyPrimitiveMultiplier_strictNegative hR F hFs hhol
    (n - 1) (by omega)
  rw [localConformalHardyPrimitiveMultiplier_shift hR F hFs hhol,
    sub_add_cancel] at ha
  exact (mul_eq_zero.mp ha).resolve_left (neg_ne_zero.mpr Complex.I_ne_zero)

private theorem hardy_seqConv_nonpositive 
    (hc : IsNonpositiveFourierSupport c) (hh : IsNonpositiveFourierSupport h) :
    IsNonpositiveFourierSupport (seqConv c h) := by
  intro n hn
  unfold seqConv
  have he : (fun k => c k * h (n - k)) = (fun _ => 0) := by
    funext k
    by_cases hk : 0 < k
    · rw [hc k hk, zero_mul]
    · rw [hh (n - k) (by omega), mul_zero]
  rw [he, tsum_zero]

private theorem hardy_seqConv_shift 
    (hshift : ∀ n : ℤ, a n = (-Complex.I) * c (n + 1)) h n :
    seqConv a h (n - 1) = (-Complex.I) * seqConv c h n := by
  unfold seqConv
  calc
    _ = (-Complex.I) * ∑' k : ℤ, c (k + 1) * h (n - (k + 1)) := by
      rw [← tsum_mul_left]
      apply tsum_congr
      intro k
      rw [hshift k, show n - 1 - k = n - (k + 1) by omega]
      ring
    _ = _ := congrArg (fun x => (-Complex.I) * x)
      ((Equiv.addRight 1).tsum_eq (fun k => c k * h (n - k)))

private theorem hardy_sobWeight_neg_nat (k : ℕ) :
    sobWeight (-(k : ℤ)) = ((k + 1 : ℕ) : ℝ) := by
  simp [sobWeight, abs_of_nonneg (show (0 : ℝ) ≤ k from Nat.cast_nonneg k)]
  ring

private theorem hardy_primitive_derivative_scalar (x y sx sy : ℂ)
    (hx : x ≠ 0) (hy : y ≠ 0) (hsy : sy ≠ 0) :
    x / y * (sx / sy) * ((sy * y) / (Complex.I * (-x))) * (-Complex.I) = sx := by
  field_simp [hx, hy, hsy, Complex.I_ne_zero]

private theorem hardy_primitive_derivative_scale k :
    (diskHardyDerivativeWeight k : ℂ) *
        (((sobWeight (-((k + 1 : ℕ) : ℤ)) ^ ((1 / 2 : ℝ) + 1) : ℝ) : ℂ) /
          (Complex.I * (-((k + 1 : ℕ) : ℂ)))) * (-Complex.I) =
      ((sobWeight (-(k : ℤ)) ^ (1 / 2 : ℝ) : ℝ) : ℂ) := by
  rw [hardy_sobWeight_neg_nat, hardy_sobWeight_neg_nat]
  rw [show ((k + 1 + 1 : ℕ) : ℝ) ^ ((1 / 2 : ℝ) + 1) = Real.sqrt ((k + 2 : ℕ) : ℝ) * ((k + 2 : ℕ) : ℝ) by
    rw [show k + 1 + 1 = k + 2 by omega, Real.rpow_add (by positivity), Real.rpow_one, ← Real.sqrt_eq_rpow], ← Real.sqrt_eq_rpow]
  simp only [diskHardyDerivativeWeight, Real.sqrt_div (by positivity : 0 ≤ ((k + 1 : ℕ) : ℝ))]
  simpa only [Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_natCast] using
    hardy_primitive_derivative_scalar (k + 1 : ℕ) (k + 2 : ℕ)
      (Real.sqrt ((k + 1 : ℕ) : ℝ)) (Real.sqrt ((k + 2 : ℕ) : ℝ))
      (by exact_mod_cast (by omega : k + 1 ≠ 0)) (by exact_mod_cast (by omega : k + 2 ≠ 0)) (by
        exact_mod_cast (Real.sqrt_pos.mpr (by positivity : 0 < ((k + 2 : ℕ) : ℝ))).ne')

private theorem hardy_trace_eq_of_halfTrace_eq
    u v (h : diskHalfTrace u = diskHalfTrace v) :
    diskH1Trace u = diskH1Trace v := by
  apply boundaryFourier.injective
  apply lp.ext
  rw [← fromL2_half_diskHalfTrace, ← fromL2_half_diskHalfTrace, h]

/-- The actual completed antiholomorphic product is identified with its
completed Fourier extension by the proved weak CR trace uniqueness theorem. -/
theorem diskHardySmoothProduct_eq_extension (a : SmoothH1Coefficient)
    (hCR : ∀ z ∈ Φ1,
      fderiv ℝ a z 1 = Complex.I * fderiv ℝ a z Complex.I)
    (hcn : IsNonpositiveFourierSupport (fourierCoeff (diskSmoothCoefficientCircle a)))
    (b : L2Z) (hbn : IsNonpositiveFourierSupport b) :
    diskHardySmoothProduct a b = diskHardyExtension
      (normalizedHardyMultiplier (fourierCoeff (diskSmoothCoefficientCircle a))
        (diskSmoothCoefficientCircle_isWL1 a) b) := by
  apply neumannH1_eq_of_antiholomorphic_same_trace unitDisk_bounded
    isLipschitzDomain_unitDisk unitCircle_isBoundaryParam
  · exact (by
    rw [h1Gradient_diskHardySmoothProduct, h1Gradient_diskHardySmoothProduct,
      diskHardyExtension_cauchyRiemann, map_smul,
      have h_inl u : h1SmoothCoefficientDerivativeL2 (Φ1) a 0 u = Complex.I • h1SmoothCoefficientDerivativeL2 (Φ1) a 1 u := by
        apply Lp.ext
        filter_upwards [h1SmoothCoefficientDerivativeL2_ae (Φ1) a 0 u,
          h1SmoothCoefficientDerivativeL2_ae (Φ1) a 1 u,
          Lp.coeFn_smul Complex.I (h1SmoothCoefficientDerivativeL2 (Φ1) a 1 u),
          ae_restrict_mem measurableSet_ball] with z hx hy hs hz
        rw [hx, hs]
        simp
        rw [hy]
        change fderiv ℝ a z 1 * u z =
          Complex.I * (fderiv ℝ a z Complex.I * u z)
        rw [hCR z hz]
        ring
      h_inl, smul_add])
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
      (by
        intro n hn
        rw [normalizedHardyMultiplier_apply, hardy_seqConv_nonpositive hcn (by
          intro n hn
          simp [fromL2, hbn n hn]) n hn, mul_zero])]
    exact hp

/-- The normalized primitive preserves the entire Hardy subspace. -/
theorem localConformalHardyPrimitive_nonpositive  (hR : 1 < R)
    F hFs
    (hhol : DifferentiableOn ℂ F (Φ1))
    (b : L2Z) (hbn : IsNonpositiveFourierSupport b) :
    IsNonpositiveFourierSupport (localConformalHardyPrimitive hR F hFs b) :=
  (show IsNonpositiveFourierSupport (normalizedHardyPrimitive _ _ b) by
    intro n hn
    rw [normalizedHardyPrimitive_apply, antiPrim_nonpositive (localConformalHardyPrimitiveMultiplier_strictNegative hR F hFs hhol) (show IsNonpositiveFourierSupport (fromL2 (1 / 2 : ℝ) b) by
      intro n hn
      simp [fromL2, hbn n hn]) n hn, mul_zero])

theorem fromL2_normalizedHardyPrimitive a
    ha b :
    fromL2 (1 / 2) (normalizedHardyPrimitive a ha b) =
      antiPrim a (fromL2 (1 / 2 : ℝ) b) := by
  funext n
  rw [fromL2, normalizedHardyPrimitive_apply, ← mul_assoc, ← Complex.ofReal_mul,
    mul_comm (sobWeight n ^ (-(1 / 2 : ℝ))), sobWeight_rpow_mul_neg, Complex.ofReal_one,
    one_mul]

/-- Averaged coefficients of the normalized primitive are the same `antiPrim`
coefficients, including its prescribed zero coefficient. -/
theorem normalizedHardyAverage_primitive a
    ha b :
    normalizedHardyAverage (normalizedHardyPrimitive a ha b) =
      antiPrim a (normalizedHardyAverage b) := by
  change (Real.sqrt (2 * Real.pi) : ℂ)⁻¹ •
      fromL2 (1 / 2 : ℝ) (normalizedHardyPrimitive a ha b) =
    antiPrim a ((Real.sqrt (2 * Real.pi) : ℂ)⁻¹ • fromL2 (1 / 2 : ℝ) b)
  rw [fromL2_normalizedHardyPrimitive,
    (seqOpBound_antiPrim (by norm_num : (0 : ℝ) ≤ 1 / 2) ha).map_smul _ _
      (isSobolevSeq_fromL2 (1 / 2 : ℝ) b)]

section PhysicalPrimitive

variable {R C K : ℝ} (hR : 1 < R) (F : ℂ → ℂ)
    (hFs : ContDiffOn ℝ ∞ F (ball 0 R))
    (hb : Bornology.IsBounded (F '' ball 0 1))
    (hL : IsLipschitzDomain (F '' ball 0 1))
    (hhol : DifferentiableOn ℂ F (ball 0 1))
    (hinj : InjOn F (ball 0 1))
    (hC : ∀ z ∈ ball 0 1, 1 ≤ C * ‖deriv F z‖ ^ 2)
    (hK : ∀ z ∈ ball 0 1, ‖fderiv ℝ F z 1‖ ≤ K)
    (e : OpenPartialHomeomorph ℂ ℂ) (he : ↑e = F)
    (hsource : closedBall 0 1 ⊆ e.source)
    (hes : ContDiffOn ℝ ∞ e.symm e.target)

/-- The primitive has the actual physical x derivative U(b), proved from
the disk derivative identity and cancellation of the genuine Jacobian phase
and the norm-preserving physical L² pullback. -/
local notation "Φ0" => localConformalHardyH1Extension hR F hFs hb hL hhol hinj hC hK e he hsource hes

local notation "Φ2" => ball 0 1

local notation "Φ4" => localConformalH1Pullback hR F hFs hL

theorem localConformalHardyH1Extension_primitive_gradient (b : L2Z)
    (hbn : IsNonpositiveFourierSupport b) :
    h1Gradient (F '' Φ2) 0
      (Φ0
        (localConformalHardyPrimitive hR F hFs b)) =
      h1Value (F '' Φ2)
        (Φ0 b) := by
  apply localConformalWeightedL2Pullback_injective hR F hFs hb hL hhol hinj hC hK
  apply localConformalAntiholomorphicPhaseMultiplier_injective F hhol hC
  calc
    _ = _ :=
      (localConformalH1Pullback_gradient_antiholomorphic hR F hFs hb hL hhol hinj hC hK _
        (localConformalHardyH1Extension_cauchyRiemann hR F hFs hb hL hhol hinj hC hK
          e he hsource hes _)).symm
    _ = _ := by
        rw [localConformalH1Pullback_hardyExtension]
    _ = _ :=
      (show h1Gradient (Φ2) 0 (diskHardyExtension (localConformalHardyPrimitive hR F hFs b)) = h1SmoothCoefficientL2 (Φ2) (localConformalHardyDerivativeCoefficient hR F hFs) (h1Value (Φ2) (diskHardyExtension b)) by
        change h1Gradient (Φ2) 0 (diskHardyExtension
          (normalizedHardyPrimitive (localConformalHardyPrimitiveMultiplier F)
            (localConformalHardyPrimitiveMultiplier_isWL1 hR F hFs) b)) = _
        rw [diskHardyExtension_normalizedPrimitive_gradient,
          show diskHardyDerivativeData (normalizedHardyPrimitiveGain _ _ b) = normalizedHardyMultiplier _ (diskSmoothCoefficientCircle_isWL1 (localConformalHardyDerivativeCoefficient hR F hFs)) b by
            ext n
            by_cases hn : 0 < n
            · rw [diskHardyDerivativeData_apply_pos _ hn, normalizedHardyMultiplier_apply,
                hardy_seqConv_nonpositive (localConformalHardyDerivativeCoefficient_nonpositive hR F hFs hhol) (by
                  intro n hn
                  simp [fromL2, hbn n hn]) n hn, mul_zero]
            · let k := Int.toNat (-n)
              rw [show n = -k by dsimp [k]; omega, diskHardyDerivativeData_apply_neg, normalizedHardyPrimitiveGain_apply,
                normalizedHardyMultiplier_apply]
              rw [antiPrim, if_neg (by omega), primSeq]
              have hconv := hardy_seqConv_shift (localConformalHardyPrimitiveMultiplier_shift hR F hFs hhol) (fromL2 (1 / 2 : ℝ) b) (-k)
              rw [show -k - 1 = -((k + 1 : ℕ) : ℤ) by omega] at hconv
              rw [hconv]
              simp only [Int.cast_neg, Int.cast_natCast]
              calc
                _ = ((diskHardyDerivativeWeight k : ℂ) *
                    (((sobWeight (-((k + 1 : ℕ) : ℤ)) ^ ((1 / 2 : ℝ) + 1) : ℝ) : ℂ) /
                      (Complex.I * (-((k + 1 : ℕ) : ℂ)))) * (-Complex.I)) *
                        seqConv _ (fromL2 (1 / 2 : ℝ) b) (-k) := by ring
                _ = _ := by rw [hardy_primitive_derivative_scale],
          ← diskHardySmoothProduct_eq_extension _ (fun _ hz => localConformalHardyDerivativeCoefficient_cauchyRiemann hR F hFs hhol hz) (localConformalHardyDerivativeCoefficient_nonpositive hR F hFs hhol) b hbn]
        exact (h1Value_neumannH1SmoothMultiplier _ _ _))
    _ = _ := by
      have h : h1SmoothCoefficientL2 (Φ2) (localConformalHardyDerivativeCoefficient hR F hFs) (h1Value (Φ2) (Φ4 (Φ0 b))) = localConformalAntiholomorphicPhaseMultiplier F (localConformalWeightedL2Pullback hR F hFs hL hK (h1Value (F '' Φ2) (Φ0 b))) := by
        rw [localConformalWeightedL2Pullback_h1Value hR F hFs hb hL hhol hinj hC hK,
          localConformalMassPullback_apply]
        apply Lp.ext
        filter_upwards [h1SmoothCoefficientL2_ae (Φ2)
          (localConformalHardyDerivativeCoefficient hR F hFs)
          (h1Value (Φ2) (Φ4 (Φ0 b))),
          localConformalAntiholomorphicPhaseMultiplier_ae F
            (lpBoundedMultiplier (localConformalMassDensity F)
              (localConformalMassDensity_aemeasurable hR F hFs)
              (localConformalMassDensity_ae_bound F hK)
              (h1Value (Φ2) (Φ4 (Φ0 b)))),
          lpBoundedMultiplier_ae (localConformalMassDensity F)
            (localConformalMassDensity_aemeasurable hR F hFs)
            (localConformalMassDensity_ae_bound F hK)
            (h1Value (Φ2) (Φ4 (Φ0 b))),
          ae_restrict_mem measurableSet_ball] with z ha hp hm hz
        rw [ha, hp, hm,
          localConformalHardyDerivativeCoefficient_closedDisk hR F hFs (ball_subset_closedBall hz),
          ← mul_assoc, show localConformalAntiholomorphicPhase F z * localConformalMassDensity F z = conj (fderiv ℝ F z 1) by
            exact div_mul_cancel₀ _ (by
              apply Complex.ofReal_ne_zero.mpr
              rw [hardy_real_derivative_of_holomorphic isOpen_ball hhol hz 1, mul_one]
              exact norm_ne_zero_iff.mpr (by
                intro he
                have h := hC z hz
                rw [he, norm_zero] at h
                norm_num at h))]
      rw [localConformalH1Pullback_hardyExtension] at h
      exact h

/-- The physical y derivative has the true antiholomorphic sign. -/
theorem localConformalHardyH1Extension_primitive_gradient_y (b : L2Z)
    (hbn : IsNonpositiveFourierSupport b) :
    h1Gradient (F '' Φ2) 1
      (Φ0
        (localConformalHardyPrimitive hR F hFs b)) =
      (-Complex.I) • h1Value (F '' Φ2)
        (Φ0 b) := by
  calc
    _ = (-Complex.I) • h1Gradient (F '' Φ2) 0
      (Φ0
        (localConformalHardyPrimitive hR F hFs b)) := by
      rw [localConformalHardyH1Extension_cauchyRiemann, smul_smul]
      simp
    _ = _ := by rw [localConformalHardyH1Extension_primitive_gradient hR F hFs hb hL
      hhol hinj hC hK e he hsource hes b hbn]

end PhysicalPrimitive

end PolyaNeumann

end
