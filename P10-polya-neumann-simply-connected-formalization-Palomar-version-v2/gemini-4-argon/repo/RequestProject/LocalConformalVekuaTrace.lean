module

public import RequestProject.LocalConformalVekuaSeries
public import RequestProject.HardyVolterraBridge
public import RequestProject.VolterraUniqueness

/-!
# The actual Vekua trace at the angular boundary origin

The affine product rule for the actual coordinate trace is proved on dense
smooth restrictions and extended by continuity. Consequently the H¹ Vekua
series has precisely the normalized boundary Fourier series, with the
averaged coefficients used by `vekuaBdryTerm`. The center is F(1), the same
boundary point as the origin used to choose the constant in `antiPrim`.

Zero trace yields one derivative of gain on the input. Bounded synthesis of
the stronger remainder gives a genuine pointwise Volterra equation; its
integral norm bound and Gronwall prove trace injectivity on all nonpositive
normalized inputs, including the constant mode.

This file uses supplied genuine conformal coordinates and their local inverse.
It does not assert the existence of those coordinates for every smooth domain.
-/

@[expose] public section


noncomputable section

namespace PolyaNeumann

open MeasureTheory Set Metric Filter
open scoped Topology ComplexConjugate ContDiff

variable {R : ℝ}

local instance vekuaTraceTwoPiPos : Fact (0 < 2 * Real.pi) := ⟨Real.two_pi_pos⟩

private def vekuaAffineTraceTest (p : ℂ) (f : smoothTraceTests) : smoothTraceTests :=
  ⟨fun z => (z - p) * f z,
    ⟨(contDiff_id.sub contDiff_const).mul f.property.1,
      f.property.2.1.mul_left, subset_univ _⟩⟩

private theorem vekuaAffineMultiplier_smooth 
    hb (hΩ : IsOpen Ω) p f :
    neumannH1AffineMultiplier hb p (smoothTraceH1 Ω f) =
      smoothTraceH1 Ω (vekuaAffineTraceTest p f) := by
  apply h1Value_injective hΩ
  rw [h1Value_neumannH1AffineMultiplier, h1Value_smoothTraceH1,
    h1Value_smoothTraceH1]
  apply Lp.ext
  filter_upwards [neumannAffineL2Multiplier_ae p (neumannH1AffineBound_spec hb p)
      ((smoothTraceTests_memLp Ω f).toLp f),
    (smoothTraceTests_memLp Ω f).coeFn_toLp,
    (smoothTraceTests_memLp Ω (vekuaAffineTraceTest p f)).coeFn_toLp]
    with z hm hf hp
  rw [hm]
  change (z - p) * ((smoothTraceTests_memLp Ω f).toLp f) z =
    ((smoothTraceTests_memLp Ω (vekuaAffineTraceTest p f)).toLp
      (vekuaAffineTraceTest p f)) z
  rw [hf, hp]
  rfl

/-- Actual continuous centered boundary coordinate, without an arclength premise. -/
local notation "Φ14" => ball 0 R

def localConformalCenteredCircle  (hR : 1 < R) (F : ℂ → ℂ)
    (hFs : ContDiffOn ℝ ∞ F (Φ14)) :
    C(AddCircle (2 * Real.pi), ℂ) :=
  diskSmoothCoefficientCircle
    (smoothTraceTestsH1Coefficient ⟨smoothDiskCutoff R hR (fun z => F z - F 1), smoothDiskCutoff_testFunction hR (hFs.sub contDiffOn_const)⟩)

theorem localConformalCenteredCircle_apply  (hR : 1 < R) F
    hFs (θ : ℝ) :
    localConformalCenteredCircle hR F hFs (θ : AddCircle (2 * Real.pi)) =
      F (circleMap 0 1 θ) - F 1 := by
  rw [localConformalCenteredCircle, diskSmoothCoefficientCircle_apply]
  change smoothDiskCutoff R hR (fun z => F z - F 1) (circleMap 0 1 θ) = _
  exact smoothDiskCutoff_eq_closedDisk hR _
    (sphere_subset_closedBall (circleMap_mem_sphere 0 (by norm_num) θ))

theorem localConformalCenteredCircle_coeff  (hR : 1 < R) F
    hFs :
    fourierCoeff (localConformalCenteredCircle hR F hFs) =
      fourierCoeffOn Real.two_pi_pos
        (fun θ => physicalCircleTrace F θ - physicalCircleTrace F 0) := by
  funext n
  rw [localConformalCenteredCircle, diskSmoothCoefficientCircle_coeff]
  congr 1
  funext θ
  change smoothDiskCutoff R hR (fun z => F z - F 1) (circleMap 0 1 θ) = _
  rw [smoothDiskCutoff_eq_closedDisk hR _
    (sphere_subset_closedBall (circleMap_mem_sphere 0 (by norm_num) θ))]
  simp [physicalCircleTrace, circleMap_zero]

theorem localConformalCenteredCircle_isWL1_two  (hR : 1 < R) F
    hFs :
    IsWL1 2 (fourierCoeff (localConformalCenteredCircle hR F hFs)) := by
  rw [localConformalCenteredCircle_coeff]
  exact (physicalCircleTrace_fourier_weights_of_smooth_neighborhood hR F hFs).2

private theorem vekua_isWL1_mono {s t : ℝ} (hst : s ≤ t) 
    (hc : IsWL1 t c) : IsWL1 s c := by
  refine hc.of_nonneg_of_le (fun n => ?_) (fun n => ?_)
  · exact mul_nonneg (Real.rpow_nonneg (sobWeight_pos n).le _) (norm_nonneg _)
  · exact mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow_of_exponent_le (one_le_sobWeight n) hst) (norm_nonneg _)

theorem localConformalCenteredCircle_isWL1_half  (hR : 1 < R) F
    (hFs : ContDiffOn ℝ ∞ F (Φ14)) :
    IsWL1 (1 / 2 : ℝ) (fourierCoeff (localConformalCenteredCircle hR F hFs)) :=
  vekua_isWL1_mono (by norm_num) (localConformalCenteredCircle_isWL1_two hR F hFs)

private theorem vekua_summable_coeff {s : ℝ} (hs : 0 ≤ s) 
    (hc : IsWL1 s c) : Summable c := by
  apply Summable.of_norm
  exact hc.of_nonneg_of_le (fun n => norm_nonneg _) (fun n =>
    le_mul_of_one_le_left (norm_nonneg _) (Real.one_le_rpow (one_le_sobWeight n) hs))

private theorem vekua_boundaryMultiplier_pow A
    j g :
    ((boundaryContinuousMultiplier A) ^ j) g = boundaryContinuousMultiplier (A ^ j) g := by
  induction j with
  | zero =>
    apply Lp.ext
    filter_upwards [boundaryContinuousMultiplier_ae (A ^ 0) g] with θ hθ
    simpa
      using hθ.symm
  | succ j ih =>
    rw [pow_succ', ContinuousLinearMap.mul_apply, ih]
    apply Lp.ext
    filter_upwards [boundaryContinuousMultiplier_ae A (boundaryContinuousMultiplier (A ^ j) g),
      boundaryContinuousMultiplier_ae (A ^ j) g,
      boundaryContinuousMultiplier_ae (A ^ (j + 1)) g] with θ ha hj hs
    rw [ha, hj, hs]
    simp [pow_succ']
    ring

private theorem vekua_circle_coeff_pow (A : C(AddCircle (2 * Real.pi), ℂ))
    (hA : Summable (fourierCoeff A)) (j : ℕ) :
    fourierCoeff (A ^ j) = seqConvPow (fourierCoeff A) j := by
  induction j with
  | zero =>
    funext n
    change fourierCoeff (fun _ : AddCircle (2 * Real.pi) => 1) n = seqDelta n
    have he : (fun _ : AddCircle (2 * Real.pi) => 1) =
        fourier (T := 2 * Real.pi) 0 := by
      funext q
      simp
    rw [he, fourierCoeff_fourier]
    simp [seqDelta, Pi.single_apply]
  | succ j ih =>
    rw [pow_succ']
    change fourierCoeff (fun q => A q * (A q) ^ j) =
      seqConv (fourierCoeff A) (seqConvPow (fourierCoeff A) j)
    simpa only [ContinuousMap.pow_apply, ih] using fourierCoeff_mul_eq_seqConv A hA ((A ^ j).continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))

private theorem vekua_fromL2_multiplier c hc
    b :
    fromL2 (1 / 2) (normalizedHardyMultiplier c hc b) =
      seqConv c (fromL2 (1 / 2) b) := by
  funext n
  rw [fromL2, normalizedHardyMultiplier_apply, ← mul_assoc, ← Complex.ofReal_mul,
    mul_comm (sobWeight n ^ (-(1 / 2))), sobWeight_rpow_mul_neg,
    Complex.ofReal_one, one_mul]

private theorem vekua_fromL2_injective s : Function.Injective (fromL2 s) := by
  intro b d hbd
  apply lp.ext
  funext n
  have hn := congrFun hbd n
  change (sobWeight n ^ (-s) : ℝ) * b n =
    (sobWeight n ^ (-s) : ℝ) * d n at hn
  exact mul_left_cancel₀ (by
    exact_mod_cast (Real.rpow_pos_of_pos (sobWeight_pos n) (-s)).ne') hn

private theorem vekua_summable_circle_terms {c : ℤ → ℂ}
    (hc : Summable (fun n => ‖c n‖)) :
    Summable (fun n => c n • fourier (T := 2 * Real.pi) n) := by
  apply Summable.of_norm
  simpa only [norm_smul, fourier_norm, mul_one] using hc

theorem vekua_reconstruction_add {c d : ℤ → ℂ}
    (hc : Summable (fun n => ‖c n‖)) (hd : Summable (fun n => ‖d n‖)) :
    hardyCircleReconstruction (c + d) = hardyCircleReconstruction c + hardyCircleReconstruction d := by
  unfold hardyCircleReconstruction
  simp [add_smul]
  exact (vekua_summable_circle_terms hc).tsum_add (vekua_summable_circle_terms hd)

theorem vekua_reconstruction_smul (a : ℂ) c :
    hardyCircleReconstruction (a • c) = a • hardyCircleReconstruction c := by
  unfold hardyCircleReconstruction
  simp [← smul_smul]
  exact tsum_const_smul'' a

def vekuaStrongReconstructionLin : L2Z →ₗ[ℂ] C(AddCircle (2 * Real.pi), ℂ) where
  toFun b := hardyCircleReconstruction (fromL2 ((1 / 2 : ℝ) + 1) b)
  map_add' b d := by
    rw [fromL2_add]
    exact vekua_reconstruction_add
      (sq_tsum_norm_le (by norm_num : (0 : ℝ) ≤ 1 / 2) (isSobolevSeq_fromL2 _ b)).1
      (sq_tsum_norm_le (by norm_num : (0 : ℝ) ≤ 1 / 2) (isSobolevSeq_fromL2 _ d)).1
  map_smul' a b := by
    rw [fromL2_smul]
    exact vekua_reconstruction_smul a _

theorem vekuaStrongReconstructionLin_norm_le b :
    ‖vekuaStrongReconstructionLin b‖ ≤ Real.sqrt evalConst * ‖b‖ := by
  have hp := isSobolevSeq_fromL2 ((1 / 2) + 1) b
  obtain ⟨hs, hsq⟩ := sq_tsum_norm_le (by norm_num : (0 : ℝ) ≤ 1 / 2) hp
  have he : 0 ≤ evalConst := tsum_nonneg (fun n => by
    have hn := sobWeight_pos n
    positivity)
  have hn := norm_sobVec ((1 / 2) + 1) _ hp
  rw [sobVec_fromL2] at hn
  calc
    _ ≤ _ := by
      change ‖∑' n : ℤ, fromL2 ((1 / 2) + 1) b n •
        fourier (T := 2 * Real.pi) n‖ ≤ _
      simpa only [norm_smul, fourier_norm, mul_one] using norm_tsum_le_tsum_norm (show Summable (fun n => ‖fromL2 ((1 / 2) + 1) b n • fourier (T := 2 * Real.pi) n‖) by
        simpa only [norm_smul, fourier_norm, mul_one] using hs)
    _ = _ :=
      (Real.sqrt_sq (tsum_nonneg (fun n => norm_nonneg _))).symm
    _ ≤ _ :=
      Real.sqrt_le_sqrt hsq
    _ = _ := by rw [Real.sqrt_mul he, ← hn]

/-- Genuine bounded synthesis into continuous circle functions for normalized
order-3/2 data. This permits passing the stronger remainder series pointwise. -/
def vekuaStrongCircleReconstruction : L2Z →L[ℂ] C(AddCircle (2 * Real.pi), ℂ) :=
  vekuaStrongReconstructionLin.mkContinuous (Real.sqrt evalConst)
    vekuaStrongReconstructionLin_norm_le

theorem vekuaStrongCircleReconstruction_apply b :
    vekuaStrongCircleReconstruction b =
      hardyCircleReconstruction (fromL2 ((1 / 2 : ℝ) + 1) b) := rfl

theorem vekuaStrongCircleReconstruction_sobVec c
    hc :
    vekuaStrongCircleReconstruction (sobVec ((1 / 2) + 1) c hc) =
      hardyCircleReconstruction c := by
  rw [vekuaStrongCircleReconstruction_apply, fromL2_sobVec]

private theorem vekua_raw_trace_smul (a : ℂ) 
    (hc : Summable (fun n => ‖c n‖)) (θ : ℝ) :
    hardyFourierTrace (a • c) θ = a * hardyFourierTrace c θ := by
  rw [← hardyCircleReconstruction_coe (by
    simpa using hc.mul_left ‖a‖), vekua_reconstruction_smul,
    ContinuousMap.smul_apply, smul_eq_mul, hardyCircleReconstruction_coe hc]

theorem fromL2_half_localConformalDiskHalfTrace  (hR : 1 < R) F
    (hFs : ContDiffOn ℝ ∞ F (Φ14))
    hL
    u :
    fromL2 (1 / 2 : ℝ) (localConformalDiskHalfTrace hR F hFs hL u) =
      boundaryFourier (localConformalDiskH1Trace hR F hFs hL u) :=
  fromL2_half_diskHalfTrace (localConformalH1Pullback hR F hFs hL u)

section TraceCoordinates

variable {R C : ℝ} (hR : 1 < R) (F : ℂ → ℂ)
    (hFs : ContDiffOn ℝ ∞ F (ball 0 R))
    (hb : Bornology.IsBounded (F '' ball 0 1))
    (hL : IsLipschitzDomain (F '' ball 0 1))
    (hhol : DifferentiableOn ℂ F (ball 0 1))
    (hinj : InjOn F (ball 0 1))
    (hC : ∀ z ∈ ball 0 1, 1 ≤ C * ‖deriv F z‖ ^ 2)

include hhol hinj hC in
/-- The actual affine H¹ product has the actual centered coordinate trace. -/
theorem localConformalDiskH1Trace_affineMultiplier
    u :
    localConformalDiskH1Trace hR F hFs hL (neumannH1AffineMultiplier hb (F 1) u) =
      boundaryContinuousMultiplier (localConformalCenteredCircle hR F hFs)
        (localConformalDiskH1Trace hR F hFs hL u) := by
  refine (denseRange_smoothTraceH1Lin hb hL).induction_on
    (p := fun v => localConformalDiskH1Trace hR F hFs hL
      (neumannH1AffineMultiplier hb (F 1) v) =
        boundaryContinuousMultiplier (localConformalCenteredCircle hR F hFs)
          (localConformalDiskH1Trace hR F hFs hL v)) u ?_ ?_
  · exact isClosed_eq ((localConformalDiskH1Trace hR F hFs hL).continuous.comp
      (neumannH1AffineMultiplier hb (F 1)).continuous)
      ((boundaryContinuousMultiplier (localConformalCenteredCircle hR F hFs)).continuous.comp
        (localConformalDiskH1Trace hR F hFs hL).continuous)
  · intro f
    change localConformalDiskH1Trace hR F hFs hL
      (neumannH1AffineMultiplier hb (F 1) (smoothTraceH1 _ f)) = _
    rw [vekuaAffineMultiplier_smooth hb hL.1.1]
    apply Lp.ext
    filter_upwards [localConformalDiskH1Trace_smooth_ae hR F hFs hb hL hhol hinj hC
        (vekuaAffineTraceTest (F 1) f),
      boundaryContinuousMultiplier_ae (localConformalCenteredCircle hR F hFs)
        (localConformalDiskH1Trace hR F hFs hL (smoothTraceH1 _ f)),
      localConformalDiskH1Trace_smooth_ae hR F hFs hb hL hhol hinj hC f]
      with θ hp hm hf
    change localConformalDiskH1Trace hR F hFs hL
      (smoothTraceH1 _ (vekuaAffineTraceTest (F 1) f)) θ =
        boundaryContinuousMultiplier (localConformalCenteredCircle hR F hFs)
          (localConformalDiskH1Trace hR F hFs hL (smoothTraceH1 _ f)) θ
    rw [hp, hm, hf, localConformalCenteredCircle_apply]
    rfl

include hhol hinj hC in
theorem localConformalDiskH1Trace_affineMultiplier_pow j
    u :
    localConformalDiskH1Trace hR F hFs hL (((neumannH1AffineMultiplier hb (F 1)) ^ j) u) =
      boundaryContinuousMultiplier ((localConformalCenteredCircle hR F hFs) ^ j)
        (localConformalDiskH1Trace hR F hFs hL u) := by
  rw [show localConformalDiskH1Trace hR F hFs hL (((neumannH1AffineMultiplier hb (F 1)) ^ j) u) = ((boundaryContinuousMultiplier (localConformalCenteredCircle hR F hFs)) ^ j) (localConformalDiskH1Trace hR F hFs hL u) by
    induction j with
    | zero => simp
    | succ j ih =>
      rw [pow_succ', ContinuousLinearMap.mul_apply,
        localConformalDiskH1Trace_affineMultiplier hR F hFs hb hL hhol hinj hC, ih,
        pow_succ', ContinuousLinearMap.mul_apply], vekua_boundaryMultiplier_pow]

include hhol hinj hC in
/-- Every affine power, including the zero power, has the genuine normalized
Fourier multiplier represented by its averaged convolution power. -/
theorem localConformalDiskHalfTrace_affineMultiplier_pow (j : ℕ)
    (u : NeumannH1 (F '' ball 0 1)) :
    localConformalDiskHalfTrace hR F hFs hL
        (((neumannH1AffineMultiplier hb (F 1)) ^ j) u) =
      normalizedHardyMultiplier
        (seqConvPow (fourierCoeff (localConformalCenteredCircle hR F hFs)) j)
        (wl1Norm_seqConvPow_le (by norm_num)
          (localConformalCenteredCircle_isWL1_half hR F hFs) j).1
        (localConformalDiskHalfTrace hR F hFs hL u) := by
  apply vekua_fromL2_injective (1 / 2)
  funext n
  rw [fromL2_half_localConformalDiskHalfTrace,
    localConformalDiskH1Trace_affineMultiplier_pow hR F hFs hb hL hhol hinj hC,
    boundaryFourier_continuousMultiplier,
    vekua_fromL2_multiplier, fromL2_half_localConformalDiskHalfTrace]
  · rw [vekua_circle_coeff_pow _
      (vekua_summable_coeff (by norm_num)
        (localConformalCenteredCircle_isWL1_half hR F hFs))]
  · rw [vekua_circle_coeff_pow _
      (vekua_summable_coeff (by norm_num)
        (localConformalCenteredCircle_isWL1_half hR F hFs))]
    exact vekua_summable_coeff (by norm_num)
      (wl1Norm_seqConvPow_le (by norm_num)
        (localConformalCenteredCircle_isWL1_half hR F hFs) j).1

end TraceCoordinates

/-- The normalized primitive powers have exactly the original averaged
Fourier primitive powers, including their prescribed constant coefficients. -/
theorem fromL2_localConformalHardyPrimitive_pow  (hR : 1 < R) F
    (hFs : ContDiffOn ℝ ∞ F (Φ14)) j b :
    fromL2 (1 / 2) (((localConformalHardyPrimitive hR F hFs) ^ j) b) =
      antiPrimIter (localConformalHardyPrimitiveMultiplier F) j (fromL2 (1 / 2) b) := by
  induction j with
  | zero => simp [antiPrimIter]
  | succ j ih =>
    rw [pow_succ', ContinuousLinearMap.mul_apply]
    change fromL2 (1 / 2) (normalizedHardyPrimitive _ _ _) = _
    rw [fromL2_normalizedHardyPrimitive, ih]
    exact (Function.iterate_succ_apply' _ _ _).symm

theorem normalizedHardyAverage_localConformalHardyPrimitive_pow 
    (hR : 1 < R) F
    hFs j b :
    normalizedHardyAverage (((localConformalHardyPrimitive hR F hFs) ^ j) b) =
      antiPrimIter (localConformalHardyPrimitiveMultiplier F) j (normalizedHardyAverage b) := by
  induction j with
  | zero => simp [antiPrimIter]
  | succ j ih =>
    rw [pow_succ', ContinuousLinearMap.mul_apply]
    change normalizedHardyAverage (normalizedHardyPrimitive _ _ _) = _
    rw [normalizedHardyAverage_primitive, ih]
    exact (Function.iterate_succ_apply' _ _ _).symm

/-- The genuine continuous angular velocity multiplier, reconstructed from
its absolutely summable averaged coefficients. -/
def localConformalPrimitiveCircle (F : ℂ → ℂ) : C(AddCircle (2 * Real.pi), ℂ) :=
  hardyCircleReconstruction (localConformalHardyPrimitiveMultiplier F)

theorem localConformalPrimitiveCircle_coeff  (hR : 1 < R) F
    (hFs : ContDiffOn ℝ ∞ F (Φ14)) :
    fourierCoeff (localConformalPrimitiveCircle F) = localConformalHardyPrimitiveMultiplier F :=
  hardyCircleReconstruction_fourierCoeff (summable_norm_of_isWL1_one
    (physicalCircleTrace_fourier_weights_of_smooth_neighborhood hR F hFs).1)

theorem localConformalPrimitiveCircle_apply  (hR : 1 < R) (F : ℂ → ℂ)
    (hFs : ContDiffOn ℝ ∞ F (Φ14)) (θ : ℝ) :
    localConformalPrimitiveCircle F (θ : AddCircle (2 * Real.pi)) =
      conj (deriv (physicalCircleTrace F) θ) := by
  change hardyCircleReconstruction (localConformalHardyPrimitiveMultiplier F)
    (θ : AddCircle (2 * Real.pi)) = _
  rw [hardyCircleReconstruction_coe (summable_norm_of_isWL1_one (physicalCircleTrace_fourier_weights_of_smooth_neighborhood hR F hFs).1 : Summable (fun n => ‖localConformalHardyPrimitiveMultiplier F n‖))]
  exact hardyFourierTrace_physical_conj_deriv_of_neighborhood hR F
    (hFs.of_le (WithTop.coe_le_coe.mpr le_top)) θ

/-- Actual normalized primitive powers are actual physical interval primitive
powers, with their basepoint at angular origin zero. -/
theorem localConformalHardyPrimitive_pow_volterra_of_H1  (hR : 1 < R) F
    hFs
    (hhol : DifferentiableOn ℂ F (ball 0 1)) (b : L2Z)
    (hbn : IsNonpositiveFourierSupport b)
    (hb1 : IsSobolevSeq 1 (normalizedHardyAverage b)) (j : ℕ) θ :
    hardyFourierTrace (normalizedHardyAverage
      (((localConformalHardyPrimitive hR F hFs) ^ j) b)) θ =
      volterraPrimitiveIterate (fun s => conj (deriv (physicalCircleTrace F) s))
        (hardyFourierTrace (normalizedHardyAverage b)) j θ := by
  rw [normalizedHardyAverage_localConformalHardyPrimitive_pow,
    ← localConformalPrimitiveCircle_coeff hR F hFs,
    hardyFourierTrace_antiPrimIter_eq_volterraPrimitiveIterate
      (localConformalPrimitiveCircle F) (by
        rw [localConformalPrimitiveCircle_coeff hR F hFs]
        exact (physicalCircleTrace_fourier_weights_of_smooth_neighborhood hR F hFs).1) hb1 (by
        rw [localConformalPrimitiveCircle_coeff hR F hFs]
        exact localConformalHardyPrimitiveMultiplier_strictNegative hR F hFs hhol) (by
        intro n hn
        simp [normalizedHardyAverage, fromL2, hbn n hn])]
  rw [funext (localConformalPrimitiveCircle_apply hR F hFs)]

private theorem vekua_trace_term_volterra  (hR : 1 < R) (F : ℂ → ℂ)
    hFs
    (hhol : DifferentiableOn ℂ F (ball 0 1)) (b : L2Z)
    (hbn : IsNonpositiveFourierSupport b) (hb1 : IsSobolevSeq 1 (fromL2 (1 / 2) b))
    (j : ℕ) (θ : ℝ) :
    hardyFourierTrace
      (vekuaBdryTerm (fourierCoeff (localConformalCenteredCircle hR F hFs))
        (localConformalHardyPrimitiveMultiplier F) (fromL2 (1 / 2) b) j) θ =
      (F (circleMap 0 1 θ) - F 1) ^ j *
        volterraPrimitiveIterate (fun s => conj (deriv (physicalCircleTrace F) s))
          (hardyFourierTrace (fromL2 (1 / 2) b)) j θ := by
  let G := localConformalCenteredCircle hR F hFs
  let h := fromL2 (1 / 2) b
  have ha : IsWL1 1 (localConformalHardyPrimitiveMultiplier F) :=
    (physicalCircleTrace_fourier_weights_of_smooth_neighborhood hR F hFs).1
  have hs :=
    summable_norm_antiPrimIter_of_H1 ha hb1 j
  let H := hardyCircleReconstruction (antiPrimIter (localConformalHardyPrimitiveMultiplier F) j h)
  have hg :=
    localConformalCenteredCircle_isWL1_half hR F hFs
  have hGp :=
    vekua_circle_coeff_pow G (vekua_summable_coeff (by norm_num) hg) j
  let P := G ^ j * H
  have hP : fourierCoeff P = vekuaBdryTerm (fourierCoeff G)
      (localConformalHardyPrimitiveMultiplier F) h j := by
    change fourierCoeff (fun q => (G ^ j) q * H q) = _
    rw [fourierCoeff_mul_eq_seqConv (G ^ j) (by
      rw [hGp]
      exact vekua_summable_coeff (by norm_num) (wl1Norm_seqConvPow_le (by norm_num) hg j).1) (H.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)), hGp, hardyCircleReconstruction_fourierCoeff hs]
    rfl
  have hJ := hardyFourierTrace_antiPrimIter_eq_volterraPrimitiveIterate (localConformalPrimitiveCircle F) (by
    rw [localConformalPrimitiveCircle_coeff hR F hFs]
    exact ha) hb1 (by
    rw [localConformalPrimitiveCircle_coeff hR F hFs]
    exact localConformalHardyPrimitiveMultiplier_strictNegative hR F hFs hhol) (by
    intro n hn
    simp [fromL2, hbn n hn]) j θ
  rw [localConformalPrimitiveCircle_coeff hR F hFs, funext (localConformalPrimitiveCircle_apply hR F hFs)] at hJ
  calc
    _ = P (θ : AddCircle (2 * Real.pi)) := by
      rw [← hP]
      exact hardyFourierTrace_fourierCoeff P (by
        rw [hP]
        simpa only [vekuaBdryTerm, IsWL1, Real.rpow_zero, one_mul] using
          (wl1Norm_seqConv_le (by norm_num : (0 : ℝ) ≤ 0) (vekua_isWL1_mono (by norm_num : (0 : ℝ) ≤ 1 / 2) (wl1Norm_seqConvPow_le (by norm_num) hg j).1) (by
            simpa only [IsWL1, Real.rpow_zero, one_mul] using hs)).2.1) θ
    _ = (F (circleMap 0 1 θ) - F 1) ^ j *
        hardyFourierTrace (antiPrimIter (localConformalHardyPrimitiveMultiplier F) j h) θ := by
      change (G (θ : AddCircle (2 * Real.pi))) ^ j * H (θ : AddCircle (2 * Real.pi)) = _
      rw [localConformalCenteredCircle_apply, hardyCircleReconstruction_coe hs]
    _ = _ := by rw [hJ]

section PhysicalCoordinates

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

/-- The normalized Fourier coefficient of each actual H¹ series term is
precisely the original boundary transmutation term. -/
local notation "Φ4" => localConformalCenteredCircle hR F hFs

local notation "Φ10" => localConformalHardyH1Extension hR F hFs hb hL hhol hinj hC hK e he hsource hes

local notation "Φ11" => localConformalDiskHalfTrace_hardyExtension_eq_of_nonpositive hR F hFs hb hL hhol hinj hC hK e he hsource hes

local notation "Φ12" => localConformalDiskHalfTrace hR F hFs hL

theorem localConformalVekuaTrace_term (b : L2Z) (hbn : IsNonpositiveFourierSupport b)
    j n :
    Φ12
      (((neumannH1AffineMultiplier hb (F 1)) ^ j)
        (Φ10
          (((localConformalHardyPrimitive hR F hFs) ^ j) b))) n =
      ((sobWeight n ^ (1 / 2 : ℝ) : ℝ) : ℂ) *
        vekuaBdryTerm (fourierCoeff (Φ4))
          (localConformalHardyPrimitiveMultiplier F) (fromL2 (1 / 2 : ℝ) b) j n := by
  rw [localConformalDiskHalfTrace_affineMultiplier_pow hR F hFs hb hL hhol hinj hC,
    Φ11 _
      (localConformalHardyPrimitive_pow_nonpositive hR F hFs hhol b hbn j),
    normalizedHardyMultiplier_apply, fromL2_localConformalHardyPrimitive_pow]
  rfl

/-- Actual normalized boundary term, constructed as a bounded map. -/
def localConformalVekuaBoundaryTerm (E : ℂ) (j : ℕ) : L2Z →L[ℂ] L2Z :=
  physicalVekuaCoeff E j •
    ((normalizedHardyMultiplier
      (seqConvPow (fourierCoeff (Φ4)) j)
      (wl1Norm_seqConvPow_le (by norm_num)
        (localConformalCenteredCircle_isWL1_half hR F hFs) j).1).comp
      ((localConformalHardyPrimitive hR F hFs) ^ j))

local notation "Φ6" => localConformalVekuaBoundaryTerm hR F hFs

theorem localConformalVekuaBoundaryTerm_apply (E : ℂ) j b n :
    Φ6 E j b n =
      physicalVekuaCoeff E j * ((sobWeight n ^ (1 / 2 : ℝ) : ℝ) : ℂ) *
        vekuaBdryTerm (fourierCoeff (Φ4))
          (localConformalHardyPrimitiveMultiplier F) (fromL2 (1 / 2 : ℝ) b) j n := by
  change (physicalVekuaCoeff E j • normalizedHardyMultiplier (seqConvPow (fourierCoeff (Φ4)) j) ((wl1Norm_seqConvPow_le (by norm_num) (localConformalCenteredCircle_isWL1_half hR F hFs) j).1)
    (((localConformalHardyPrimitive hR F hFs) ^ j) b)) n = _
  rw [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, normalizedHardyMultiplier_apply,
    fromL2_localConformalHardyPrimitive_pow]
  change physicalVekuaCoeff E j *
    ((sobWeight n ^ (1 / 2 : ℝ) : ℝ) * vekuaBdryTerm _ _ _ j n) = _
  ring

/-- The boundary operator is the trace of the genuine convergent H¹ series. -/
local notation "Φ2" => localConformalVekuaH1AtBoundaryOrigin hR F hFs hb hL hhol hinj hC hK e he hsource hes

def localConformalVekuaBoundary (E : ℂ) : L2Z →L[ℂ] L2Z :=
  (Φ12).comp
    (Φ2 E)

local notation "Φ1" => localConformalVekuaBoundary hR F hFs hb hL hhol hinj hC hK e he hsource hes

local notation "Φ7" => localConformalVekuaTrace_term hR F hFs hb hL hhol hinj hC hK e he hsource hes

theorem localConformalVekuaBoundary_hasSum E (b : L2Z)
    (hbn : IsNonpositiveFourierSupport b) :
    HasSum (fun j => Φ6 E j b)
      (Φ1 E b) := by
  have ht j :
      physicalVekuaCoeff E j • Φ12
        (((neumannH1AffineMultiplier hb (F 1)) ^ j)
          (Φ10
            (((localConformalHardyPrimitive hR F hFs) ^ j) b))) =
        Φ6 E j b := by
    ext n
    simp only [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]
    rw [Φ7 b hbn,
      localConformalVekuaBoundaryTerm_apply]
    ring
  simpa only [ht, localConformalVekuaBoundary, ContinuousLinearMap.comp_apply,
    localConformalVekuaH1AtBoundaryOrigin] using
    localConformalVekuaH1_halfTrace_hasSum hR F hFs hb hL hhol hinj hC hK e he hsource hes
      (F 1) E b

include hb hL hhol hinj hC hK e he hsource hes in
theorem localConformalVekuaBoundaryTerm_zero E (b : L2Z)
    (hbn : IsNonpositiveFourierSupport b) :
    Φ6 E 0 b = b := by
  ext n
  rw [localConformalVekuaBoundaryTerm_apply, physicalVekuaCoeff_zero, one_mul, ← Φ7 b hbn 0]
  simp only [pow_zero, ContinuousLinearMap.one_apply]
  rw [Φ11 b hbn]

private theorem vekua_smoothing_strong_term (E : ℂ) b j
    (ht : IsSobolevSeq ((1 / 2) + 1)
      (vekuaBdryTerm (fourierCoeff (Φ4))
        (localConformalHardyPrimitiveMultiplier F) (fromL2 (1 / 2 : ℝ) b) (j + 1))) :
    sobolevSmoothing 1 (by norm_num)
      (physicalVekuaCoeff E (j + 1) • sobVec ((1 / 2 : ℝ) + 1) _ ht) =
      Φ6 E (j + 1) b := by
  ext n
  simp [sobolevSmoothing, localConformalVekuaBoundaryTerm_apply]
  calc
    _ = physicalVekuaCoeff E (j + 1) *
      (((sobWeight n ^ (-(1 : ℝ)) : ℝ) *
        (sobWeight n ^ ((1 / 2 : ℝ) + 1) : ℝ)) *
          vekuaBdryTerm (fourierCoeff (Φ4))
            (localConformalHardyPrimitiveMultiplier F) (fromL2 (1 / 2) b) (j + 1) n) := by ring
    _ = _ := by rw [show ((sobWeight n ^ (-(1 : ℝ)) : ℝ) : ℂ) * (sobWeight n ^ ((1 / 2 : ℝ) + 1) : ℝ) = (sobWeight n ^ (1 / 2 : ℝ) : ℝ) by
      rw [← Complex.ofReal_mul, ← Real.rpow_add (sobWeight_pos n), show -1 + ((1 / 2 : ℝ) + 1) = 1 / 2 by ring]]; ring

/-- The true normalized boundary remainder factors through one-order smoothing.
The stronger vector is constructed from the proved Fourier term bounds. -/
theorem localConformalVekuaBoundary_strong_remainder_hasSum (E : ℂ) (b : L2Z)
    (hbn : IsNonpositiveFourierSupport b) :
    ∃ (hT : ∀ j : ℕ, IsSobolevSeq ((1 / 2) + 1)
          (vekuaBdryTerm (fourierCoeff (Φ4))
            (localConformalHardyPrimitiveMultiplier F) (fromL2 (1 / 2) b) (j + 1)))
      (r : L2Z),
      HasSum (fun j => physicalVekuaCoeff E (j + 1) •
        sobVec ((1 / 2 : ℝ) + 1) _ (hT j)) r ∧
      Φ1 E b - b =
        sobolevSmoothing 1 (by norm_num) r := by
  obtain ⟨hT, hN, -⟩ := vekuaBdry_sub_one_bound (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (vekua_isWL1_mono (by norm_num) (localConformalCenteredCircle_isWL1_two hR F hFs))
    (localConformalHardyPrimitiveMultiplier_isWL1 hR F hFs)
    (isSobolevSeq_fromL2 (1 / 2) b) E
  let f : ℕ → L2Z := fun j => physicalVekuaCoeff E (j + 1) •
    sobVec ((1 / 2) + 1) _ (hT j)
  have hs : HasSum f (∑' j : ℕ, f j) := by
    exact hN.of_norm.hasSum
  have ht := (hasSum_nat_add_iff'
    (f := fun j => Φ6 E j b) 1).2
      (localConformalVekuaBoundary_hasSum hR F hFs hb hL hhol hinj hC hK e he hsource hes
        E b hbn)
  simp [localConformalVekuaBoundaryTerm_zero hR F hFs hb hL hhol hinj hC hK e he hsource hes
      E b hbn] at ht
  exact ⟨hT, ∑' j : ℕ, f j, hs, ht.unique (by
    simpa only [f, vekua_smoothing_strong_term] using ((sobolevSmoothing 1 (by norm_num)).hasSum hs))⟩

/-- The actual boundary remainder is in the range of one-order smoothing. -/
local notation "Φ3" => localConformalVekuaBoundary_strong_remainder_hasSum hR F hFs hb hL hhol hinj hC hK e he hsource hes

theorem localConformalVekuaBoundary_sub_gain E (b : L2Z)
    (hbn : IsNonpositiveFourierSupport b) :
    ∃ r : L2Z,
      Φ1 E b - b =
        sobolevSmoothing 1 (by norm_num) r := by
  obtain ⟨hT, r, hs, hr⟩ := Φ3 E b hbn
  exact ⟨r, hr⟩

/-- Zero actual trace forces one full order of gain on the original input. -/
local notation "Φ8" => localConformalVekuaBoundary_sub_gain hR F hFs hb hL hhol hinj hC hK e he hsource hes

theorem localConformalVekuaBoundary_kernel_smoothing E (b : L2Z)
    (hbn : IsNonpositiveFourierSupport b)
    (hz : Φ1 E b = 0) :
    ∃ r : L2Z, b = sobolevSmoothing 1 (by norm_num) r := by
  obtain ⟨r, hr⟩ := Φ8 E b hbn
  rw [hz, zero_sub] at hr
  refine ⟨-r, ?_⟩
  rw [map_neg, ← hr, neg_neg]

theorem fromL2_half_smoothing_one b :
    fromL2 (1 / 2) (sobolevSmoothing 1 (by norm_num) b) =
      fromL2 ((1 / 2) + 1) b := by
  funext n
  simp only [fromL2, sobolevSmoothing, diagOp_apply]
  rw [← mul_assoc, ← Complex.ofReal_mul, ← Real.rpow_add (sobWeight_pos n), show -(1 / 2 : ℝ) + -1 = -((1 / 2) + 1) by ring]


local notation "VB" => localConformalVekuaBoundary hR F hFs hb hL hhol hinj hC hK
  e he hsource hes

/-- The genuine Vekua coordinate trace preserves order-one regularity of
its original raw coefficients, using the proved stronger remainder. -/
theorem localConformalVekuaBoundary_raw_H1 E (b : L2Z)
    (hbn : IsNonpositiveFourierSupport b)
    (hb1 : IsSobolevSeq 1 (fromL2 (1 / 2) b)) :
    IsSobolevSeq 1 (fromL2 (1 / 2) (VB E b)) := by
  obtain ⟨r, hr⟩ := Φ8 E b hbn
  rw [show VB E b = b + sobolevSmoothing 1 (by norm_num) r by
    rw [sub_eq_iff_eq_add] at hr
    exact hr.trans (add_comm _ _), fromL2_add, fromL2_half_smoothing_one]
  exact isSobolevSeq_add hb1
    (sobNormSq_mono (by norm_num : 1 ≤ (1 / 2 : ℝ) + 1)
      (isSobolevSeq_fromL2 ((1 / 2 : ℝ) + 1) r)).1

/-- For every actual order-one Hardy input the physical boundary series
converges pointwise to the Fourier reconstruction of its actual trace. -/
local notation "Φ13" => circleMap 0 1

theorem localConformalVekuaBoundary_volterra_hasSum_of_H1 E (b : L2Z)
    (hbn : IsNonpositiveFourierSupport b)
    (hb1 : IsSobolevSeq 1 (fromL2 (1 / 2) b)) θ :
    HasSum (fun j => physicalVekuaCoeff E j *
      (F (Φ13 θ) - F 1) ^ j *
      volterraPrimitiveIterate (fun s => conj (deriv (physicalCircleTrace F) s))
        (hardyFourierTrace (fromL2 (1 / 2) b)) j θ)
      (hardyFourierTrace (fromL2 (1 / 2) (VB E b)) θ) := by
  obtain ⟨hT, r, hs, hr⟩ := Φ3 E b hbn
  have hseq : fromL2 (1 / 2) (VB E b) =
      fromL2 (1 / 2) b + fromL2 ((1 / 2) + 1) r := by
    rw [show VB E b = b + sobolevSmoothing 1 (by norm_num) r by
      rw [sub_eq_iff_eq_add] at hr
      exact hr.trans (add_comm _ _), fromL2_add, fromL2_half_smoothing_one]
  have hr1 :=
    (sobNormSq_mono (by norm_num : 1 ≤ (1 / 2 : ℝ) + 1)
      (isSobolevSeq_fromL2 ((1 / 2 : ℝ) + 1) r)).1
  have hbs : Summable (fun n => ‖fromL2 (1 / 2) b n‖) :=
    (sq_tsum_norm_le (s := 0) (by norm_num) (by simpa using hb1)).1
  have hrs : Summable (fun n => ‖fromL2 ((1 / 2) + 1) r n‖) :=
    (sq_tsum_norm_le (s := 0) (by norm_num) (by simpa using hr1)).1
  have ht j : vekuaStrongCircleReconstruction
      (physicalVekuaCoeff E (j + 1) • sobVec ((1 / 2) + 1) _ (hT j))
        (θ : AddCircle (2 * Real.pi)) =
      physicalVekuaCoeff E (j + 1) * (F (Φ13 θ) - F 1) ^ (j + 1) *
        volterraPrimitiveIterate (fun s => conj (deriv (physicalCircleTrace F) s))
          (hardyFourierTrace (fromL2 (1 / 2) b)) (j + 1) θ := by
    rw [map_smul, vekuaStrongCircleReconstruction_sobVec, ContinuousMap.smul_apply,
      smul_eq_mul, hardyCircleReconstruction_coe
        (sq_tsum_norm_le (by norm_num : (0 : ℝ) ≤ 1 / 2) (hT j)).1,
      vekua_trace_term_volterra hR F hFs hhol b hbn hb1]
    ring
  have heval := (ContinuousMap.evalCLM ℂ (θ : AddCircle (2 * Real.pi))).hasSum
    (vekuaStrongCircleReconstruction.hasSum hs)
  change HasSum (fun j => vekuaStrongCircleReconstruction
    (physicalVekuaCoeff E (j + 1) • sobVec ((1 / 2) + 1) _ (hT j))
      (θ : AddCircle (2 * Real.pi)))
    (vekuaStrongCircleReconstruction r (θ : AddCircle (2 * Real.pi))) at heval
  apply (hasSum_nat_add_iff' (f := fun j => physicalVekuaCoeff E j *
    (F (Φ13 θ) - F 1) ^ j *
    volterraPrimitiveIterate (fun s => conj (deriv (physicalCircleTrace F) s))
      (hardyFourierTrace (fromL2 (1 / 2) b)) j θ) 1).1
  simpa only [Finset.sum_range_one, physicalVekuaCoeff, pow_zero, Nat.factorial_zero,
    Nat.cast_one, div_one, one_mul, volterraPrimitiveIterate, show hardyFourierTrace (fromL2 (1 / 2) (VB E b)) θ = hardyFourierTrace (fromL2 (1 / 2) b) θ + vekuaStrongCircleReconstruction r (θ : AddCircle (2 * Real.pi)) by
      rw [hseq, ← hardyCircleReconstruction_coe ((sq_tsum_norm_le (s := 0) (by norm_num) (by simpa using isSobolevSeq_add hb1 hr1)).1),
        vekua_reconstruction_add hbs hrs]
      simp only [ContinuousMap.add_apply, hardyCircleReconstruction_coe hbs,
        vekuaStrongCircleReconstruction_apply, hardyCircleReconstruction_coe hrs],
    add_sub_cancel_left] using show HasSum (fun j => physicalVekuaCoeff E (j + 1) * (F (Φ13 θ) - F 1) ^ (j + 1) * volterraPrimitiveIterate (fun s => conj (deriv (physicalCircleTrace F) s)) (hardyFourierTrace (fromL2 (1 / 2) b)) (j + 1) θ) (vekuaStrongCircleReconstruction r (θ : AddCircle (2 * Real.pi))) by
      simpa only [ht] using heval

private theorem vekua_volterra_next_bound
    (A : C(AddCircle (2 * Real.pi), ℂ))  (hh : Continuous h)
     (_hT : 0 ≤ T) j t (ht : t ∈ Icc 0 T) :
    ‖volterraPrimitiveIterate (fun s => A (s : AddCircle (2 * Real.pi))) h (j + 1) t‖ ≤
      (‖A‖ * ∫ s in 0..t, ‖h s‖) * (‖A‖ * T) ^ j / (j.factorial : ℝ) := by
  let a : ℝ → ℂ := fun s => A (s : AddCircle (2 * Real.pi))
  have ha := A.continuous.comp (AddCircle.continuous_mk' _)
  have hi : 0 ≤ ∫ s in 0..t, ‖h s‖ :=
    intervalIntegral.integral_nonneg ht.1 (fun s _ => norm_nonneg _)
  have hfirst s (hs : s ∈ Icc 0 t) :
      ‖volterraPrimitiveIterate a h 1 s‖ ≤ ‖A‖ * ∫ x in 0..t, ‖h x‖ := by
    change ‖∫ x in 0..s, a x * h x‖ ≤ _
    calc
      _ ≤ _ :=
        intervalIntegral.norm_integral_le_integral_norm hs.1
      _ ≤ ∫ x in 0..s, ‖A‖ * ‖h x‖ := by
        refine intervalIntegral.integral_mono_on hs.1 ((ha.mul hh).norm.intervalIntegrable 0 s)
          ((continuous_const.mul hh.norm).intervalIntegrable 0 s) ?_
        intro x _
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_right (A.norm_coe_le_norm _) (norm_nonneg _)
      _ = _ := intervalIntegral.integral_const_mul _ _
      _ ≤ ‖A‖ * ∫ x in 0..t, ‖h x‖ := by
        exact mul_le_mul_of_nonneg_left
          (intervalIntegral.integral_mono_interval le_rfl hs.1 hs.2
            (Eventually.of_forall (fun x => norm_nonneg (h x))) (hh.norm.intervalIntegrable 0 t))
          (norm_nonneg A)
  rw [← (show volterraPrimitiveIterate a (volterraPrimitiveIterate a h 1) j = volterraPrimitiveIterate a h (j + 1) by
    induction j with
    | zero => rfl
    | succ j ih =>
      funext t
      change (∫ s in 0..t,
        a s * volterraPrimitiveIterate a (volterraPrimitiveIterate a h 1) j s) = _
      rw [ih]
      rfl)]
  exact (volterraPrimitiveIterate_bound_uniform ha (continuous_volterraPrimitiveIterate ha hh 1) ht.1 (norm_nonneg A) (mul_nonneg (norm_nonneg A) hi) (fun s _ => A.norm_coe_le_norm _) hfirst j t ⟨ht.1, le_rfl⟩).trans (div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (mul_nonneg (norm_nonneg A) ht.1)
        (mul_le_mul_of_nonneg_left ht.2 (norm_nonneg A)) j)
      (mul_nonneg (norm_nonneg A) hi)) (Nat.cast_nonneg _))

private theorem vekua_volterra_kernel_unique
    (A G : C(AddCircle (2 * Real.pi), ℂ)) E  (hh : Continuous h)
    {T : ℝ} (hT : 0 ≤ T)
    (hsum : ∀ t ∈ Icc 0 T, HasSum (fun j => physicalVekuaCoeff E (j + 1) *
      G (t : AddCircle (2 * Real.pi)) ^ (j + 1) *
      volterraPrimitiveIterate (fun s => A (s : AddCircle (2 * Real.pi))) h (j + 1) t) (-h t)) :
    ∀ t ∈ Icc 0 T, h t = 0 := by
  let K := ‖-E / 4‖
  let B := ‖G‖
  let M := ‖A‖
  let x := K * B * M * T
  have hK : 0 ≤ K := norm_nonneg _
  apply continuous_eq_zero_of_norm_le_volterra hh (show 0 ≤ K * B * M * Real.exp x by positivity)
  intro t ht
  let I := ∫ s in 0..t, ‖h s‖
  let f : ℕ → ℂ := fun j => physicalVekuaCoeff E (j + 1) *
    G (t : AddCircle (2 * Real.pi)) ^ (j + 1) *
    volterraPrimitiveIterate (fun s => A (s : AddCircle (2 * Real.pi))) h (j + 1) t
  have hmajor j : ‖f j‖ ≤ K * B * M * I * (x ^ j / j.factorial) := by
    calc
      _ ≤ _ := by
        simp only [f, norm_mul]
        exact mul_le_mul (mul_le_mul (show ‖physicalVekuaCoeff E (j + 1)‖ ≤ K ^ (j + 1) by
          rw [norm_physicalVekuaCoeff]
          exact div_le_self (pow_nonneg hK _)
            (by exact_mod_cast Nat.one_le_of_lt (Nat.factorial_pos (j + 1)))) (show ‖G (t : AddCircle (2 * Real.pi)) ^ (j + 1)‖ ≤ B ^ (j + 1) by
          rw [norm_pow]
          exact pow_le_pow_left₀ (norm_nonneg _) (G.norm_coe_le_norm _) _) (norm_nonneg _) (pow_nonneg hK _)) (vekua_volterra_next_bound A hh hT j t ht)
          (norm_nonneg _) (mul_nonneg (pow_nonneg hK _) (pow_nonneg (norm_nonneg _) _))
      _ = _ := by simp [x, pow_succ, mul_pow]; ring
  have hmaj : Summable (fun j => K * B * M * I * (x ^ j / j.factorial)) :=
    (Real.summable_pow_div_factorial x).mul_left _
  have hn :=
    Summable.of_nonneg_of_le (fun j => norm_nonneg _) hmajor hmaj
  calc
    _ = _ := by rw [(hsum t ht).tsum_eq, norm_neg]
    _ ≤ _ := norm_tsum_le_tsum_norm hn
    _ ≤ _ :=
      Summable.tsum_le_tsum hmajor hn hmaj
    _ = _ := by
      rw [tsum_mul_left, Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div]
      ring


theorem localConformalVekuaBoundary_kernel_raw_threeHalves E (b : L2Z)
    (hbn : IsNonpositiveFourierSupport b)
    (hz : VB E b = 0) :
    IsSobolevSeq ((1 / 2) + 1) (fromL2 (1 / 2) b) := by
  obtain ⟨r, hr⟩ := localConformalVekuaBoundary_kernel_smoothing hR F hFs hb hL hhol hinj hC hK
    e he hsource hes E b hbn hz
  rw [hr, fromL2_half_smoothing_one]
  exact isSobolevSeq_fromL2 _ r

/-- Zero actual trace gives a genuine pointwise Volterra equation for the
original data. The raw orthonormal Fourier input is sqrt(2π) times its averaged
input, so this equality has the same constant scale in every term. -/
local notation "Φ9" => localConformalVekuaBoundary_kernel_raw_threeHalves hR F hFs hb hL hhol hinj hC hK e he hsource hes

theorem localConformalVekuaBoundary_kernel_volterra_hasSum E (b : L2Z)
    (hbn : IsNonpositiveFourierSupport b)
    (hz : VB E b = 0)
    θ :
    HasSum (fun j => physicalVekuaCoeff E (j + 1) *
      (F (Φ13 θ) - F 1) ^ (j + 1) *
      volterraPrimitiveIterate (fun s => conj (deriv (physicalCircleTrace F) s))
        (hardyFourierTrace (fromL2 (1 / 2) b)) (j + 1) θ)
      (-hardyFourierTrace (fromL2 (1 / 2) b) θ) := by
  obtain ⟨hT, r, hs, hr⟩ := Φ3 E b hbn
  rw [hz, zero_sub] at hr
  have hb3 := Φ9 E b hbn hz
  have ht j :
      vekuaStrongCircleReconstruction
        (physicalVekuaCoeff E (j + 1) • sobVec ((1 / 2) + 1) _ (hT j))
          (θ : AddCircle (2 * Real.pi)) =
      physicalVekuaCoeff E (j + 1) * (F (Φ13 θ) - F 1) ^ (j + 1) *
        volterraPrimitiveIterate (fun s => conj (deriv (physicalCircleTrace F) s))
          (hardyFourierTrace (fromL2 (1 / 2) b)) (j + 1) θ := by
    rw [map_smul, vekuaStrongCircleReconstruction_sobVec, ContinuousMap.smul_apply,
      smul_eq_mul, hardyCircleReconstruction_coe
        (sq_tsum_norm_le (by norm_num : (0 : ℝ) ≤ 1 / 2) (hT j)).1,
      vekua_trace_term_volterra hR F hFs hhol b hbn ((sobNormSq_mono (by norm_num) hb3).1)]
    ring
  have heval := (ContinuousMap.evalCLM ℂ (θ : AddCircle (2 * Real.pi))).hasSum
    (vekuaStrongCircleReconstruction.hasSum hs)
  change HasSum (fun j => vekuaStrongCircleReconstruction
    (physicalVekuaCoeff E (j + 1) • sobVec ((1 / 2 : ℝ) + 1) _ (hT j))
      (θ : AddCircle (2 * Real.pi)))
    (vekuaStrongCircleReconstruction r (θ : AddCircle (2 * Real.pi))) at heval
  simpa only [ht, show vekuaStrongCircleReconstruction r (θ : AddCircle (2 * Real.pi)) = -hardyFourierTrace (fromL2 (1 / 2 : ℝ) b) θ by
    rw [vekuaStrongCircleReconstruction_apply, hardyCircleReconstruction_coe
      (sq_tsum_norm_le (by norm_num : (0 : ℝ) ≤ 1 / 2) (isSobolevSeq_fromL2 _ r)).1,
      (show fromL2 ((1 / 2) + 1) r = -fromL2 (1 / 2) b by
        calc
          _ = _ :=
            (fromL2_half_smoothing_one r).symm
          _ = _ := congrArg (fromL2 (1 / 2)) hr.symm
          _ = _ := by funext n; simp [fromL2])]
    have hn : -fromL2 (1 / 2 : ℝ) b = (-1 : ℂ) • fromL2 (1 / 2) b := by
      funext n
      simp
    rw [hn, vekua_raw_trace_smul (-1) ((sq_tsum_norm_le (by norm_num : (0 : ℝ) ≤ 1 / 2) hb3).1)]
    ring] using heval

/-- The actual Vekua coordinate trace has no kernel on the full nonpositive
half-trace space. Regularity, the pointwise equation and the Volterra bound
are all derived from the actual zero trace. -/
theorem localConformalVekuaBoundary_eq_zero_imp E (b : L2Z)
    (hbn : IsNonpositiveFourierSupport b)
    (hz : VB E b = 0) :
    b = 0 := by
  have hbs :=
    (sq_tsum_norm_le (by norm_num : (0 : ℝ) ≤ 1 / 2) (Φ9 E b hbn hz)).1
  have hzero := vekua_volterra_kernel_unique (localConformalPrimitiveCircle F)
    (Φ4) E (continuous_hardyFourierTrace hbs) Real.two_pi_pos.le (by
      intro θ _
      simpa [localConformalCenteredCircle_apply hR F hFs, localConformalPrimitiveCircle_apply hR F hFs] using
        localConformalVekuaBoundary_kernel_volterra_hasSum hR F hFs hb hL hhol hinj hC hK
          e he hsource hes E b hbn hz θ)
  apply vekua_fromL2_injective (1 / 2)
  rw [show fromL2 (1 / 2) b = 0 by
    funext n
    change fromL2 (1 / 2) b n = 0
    rw [← congrFun (hardyCircleReconstruction_fourierCoeff hbs) n, fourierCoeff_eq_intervalIntegral _ n 0, zero_add]
    rw [show (∫ θ in 0..2 * Real.pi, fourier (T := 2 * Real.pi) (-n) (θ : AddCircle (2 * Real.pi)) • hardyCircleReconstruction (fromL2 (1 / 2) b) (θ : AddCircle (2 * Real.pi))) = 0 by
      calc
        _ = ∫ θ in (0 : ℝ)..2 * Real.pi, (0 : ℂ) := by
          apply intervalIntegral.integral_congr
          intro θ hθ
          rw [uIcc_of_le Real.two_pi_pos.le] at hθ
          change fourier (T := 2 * Real.pi) (-n) (θ : AddCircle (2 * Real.pi)) •
            hardyCircleReconstruction (fromL2 (1 / 2) b)
              (θ : AddCircle (2 * Real.pi)) = _
          rw [hardyCircleReconstruction_coe hbs, hzero θ hθ, smul_zero]
        _ = 0 := by simp, smul_zero]]
  funext n
  simp [fromL2]

/-- The same actual uniqueness conclusion stated directly for the ordinary
coordinate trace of the physical H¹ vector. -/
theorem localConformalVekuaH1_eq_zero_input_of_coordinate_trace_zero E (b : L2Z)
    (hbn : IsNonpositiveFourierSupport b)
    (ht : localConformalDiskH1Trace hR F hFs hL
      (Φ2 E b) = 0) :
    b = 0 := by
  apply localConformalVekuaBoundary_eq_zero_imp hR F hFs hb hL hhol hinj hC hK
    e he hsource hes E b hbn
  apply vekua_fromL2_injective (1 / 2)
  change fromL2 (1 / 2) (Φ12
    (Φ2 E b)) = _
  rw [fromL2_half_localConformalDiskHalfTrace, ht, map_zero]
  funext n
  simp [fromL2]

end PhysicalCoordinates

end PolyaNeumann

end
