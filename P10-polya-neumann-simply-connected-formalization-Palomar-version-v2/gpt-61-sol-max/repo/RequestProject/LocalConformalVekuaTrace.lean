module

public import RequestProject.PlanarTypes
public import RequestProject.CirclePeriod

public import RequestProject.PlanarGeometry

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

open scoped ContDiff


noncomputable section

namespace PolyaNeumann

open MeasureTheory Set Metric Filter
open scoped ComplexConjugate



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
  measurability

/-- A genuine compact smooth representative of F(z)-F(1) on the closed disk. -/
def localConformalCenteredTraceTest {R : ℝ} (hR : 1 < R) (F : PlaneMap)
    (hFs : RealSmoothOnBall F R) : smoothTraceTests :=
  ⟨smoothDiskCutoff R hR (fun z => F z - F 1),
    smoothDiskCutoff_testFunction hR (hFs.sub contDiffOn_const)⟩

/-- Actual continuous centered boundary coordinate, without an arclength premise. -/
def localConformalCenteredCircle {R : ℝ} (hR : 1 < R) (F : PlaneMap)
    (hFs : RealSmoothOnBall F R) :
    C(AddCircle circlePeriod, ℂ) :=
  diskSmoothCoefficientCircle
    (smoothTraceTestsH1Coefficient (localConformalCenteredTraceTest hR F hFs))

section
variable {R } (hR : 1 < R) (F : PlaneMap) (hFs : RealSmoothOnBall F R)

section
include R hR F hFs

theorem localConformalCenteredCircle_apply (θ : ℝ) :
    localConformalCenteredCircle hR F hFs (θ : AddCircle circlePeriod) =
      F (unitCircleMap θ) - F 1 := by
  rw [localConformalCenteredCircle, diskSmoothCoefficientCircle_apply]
  change smoothDiskCutoff R hR (fun z => F z - F 1) (unitCircleMap θ) = _
  exact smoothDiskCutoff_eq_closedDisk hR _
    (sphere_subset_closedBall (circleMap_mem_sphere 0 (by norm_num) θ))

theorem localConformalCenteredCircle_coeff :
    fourierCoeff (localConformalCenteredCircle hR F hFs) =
      fourierCoeffOn Real.two_pi_pos
        (fun θ => physicalCircleTrace F θ - physicalCircleTrace F 0) := by
  funext n
  rw [localConformalCenteredCircle, diskSmoothCoefficientCircle_coeff]
  congr 1
  funext θ
  change smoothDiskCutoff R hR (fun z => F z - F 1) (unitCircleMap θ) = _
  rw [smoothDiskCutoff_eq_closedDisk hR _
    (sphere_subset_closedBall (circleMap_mem_sphere 0 (by norm_num) θ))]
  simp [physicalCircleTrace, circleMap_zero]

theorem localConformalCenteredCircle_isWL1_two :
    IsWL1 2 (fourierCoeff (localConformalCenteredCircle hR F hFs)) := by
  rw [localConformalCenteredCircle_coeff]
  exact (physicalCircleTrace_fourier_weights_of_smooth_neighborhood hR F hFs).2

end


theorem common_vekua_isWL1_mono  (hst : s ≤ t) 
    (hc : IsWL1 t c) : IsWL1 s c := by
  refine hc.of_nonneg_of_le (fun n => ?_) (fun n => ?_)
  · exact mul_nonneg (Real.rpow_nonneg (sobWeight_pos n).le _) (norm_nonneg _)
  · exact mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow_of_exponent_le (one_le_sobWeight n) hst) (norm_nonneg _)

section
include R hR F hFs

theorem localConformalCenteredCircle_isWL1_half :
    IsWL1 (1 / 2 : ℝ) (fourierCoeff (localConformalCenteredCircle hR F hFs)) :=
  common_vekua_isWL1_mono (by norm_num) (localConformalCenteredCircle_isWL1_two hR F hFs)

theorem localConformalCenteredCircle_isWL1_threeHalves :
    IsWL1 ((1 / 2 : ℝ) + 1) (fourierCoeff (localConformalCenteredCircle hR F hFs)) :=
  common_vekua_isWL1_mono (by norm_num) (localConformalCenteredCircle_isWL1_two hR F hFs)

end


theorem common_vekua_summable_coeff  (hs : 0 ≤ s) 
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
    simp_all
  | succ j ih =>
    rw [pow_succ', ContinuousLinearMap.mul_apply, ih]
    apply Lp.ext
    filter_upwards [boundaryContinuousMultiplier_ae A (boundaryContinuousMultiplier (A ^ j) g),
      boundaryContinuousMultiplier_ae (A ^ j) g,
      boundaryContinuousMultiplier_ae (A ^ (j + 1)) g] with θ ha hj hs
    rw [ha, hj, hs]
    simp  
    ring

private theorem vekua_circle_coeff_pow (A : C(AddCircle circlePeriod, ℂ))
    (hA : Summable (fourierCoeff A)) (j : ℕ) :
    fourierCoeff (A ^ j) = seqConvPow (fourierCoeff A) j := by
  induction j with
  | zero =>
    funext n
    change fourierCoeff (fun _ : AddCircle circlePeriod => 1) n = seqDelta n
    have he : (fun _ : AddCircle circlePeriod => (1 : ℂ)) =
        (fourier (T := 2 * Real.pi) 0 : AddCircle circlePeriod → ℂ) := by
      funext q
      simp
    rw [he, fourierCoeff_fourier]
    simp [seqDelta, Pi.single_apply]
  | succ j ih =>
    have hp : Integrable (A ^ j : C(AddCircle circlePeriod, ℂ)) AddCircle.haarAddCircle :=
      (A ^ j).continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    rw [pow_succ']
    change fourierCoeff (fun q => A q * (A q) ^ j) =
      seqConv (fourierCoeff A) (seqConvPow (fourierCoeff A) j)
    simpa only [ContinuousMap.pow_apply, ih] using fourierCoeff_mul_eq_seqConv A hA hp

theorem common_vekua_fromL2_multiplier c hc
    b :
    fromL2 (1 / 2 : ℝ) (normalizedHardyMultiplier c hc b) =
      seqConv c (fromL2 (1 / 2 : ℝ) b) := by
  funext n
  rw [fromL2, normalizedHardyMultiplier_apply, ← mul_assoc, ← Complex.ofReal_mul,
    mul_comm (sobWeight n ^ (-(1 / 2))), sobWeight_rpow_mul_neg,
    Complex.ofReal_one, one_mul]

private theorem vekua_fromL2_injective s : Function.Injective (fromL2 s) := by
  intro b d hbd
  apply lp.ext
  funext n
  have hn := congrFun hbd n
  have hw : ((sobWeight n ^ (-s) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.rpow_pos_of_pos (sobWeight_pos n) (-s)).ne'
  exact mul_left_cancel₀ hw hn

theorem vekua_reconstruction_add 
    (hc : Summable (fun n => ‖c n‖)) (hd : Summable (fun n => ‖d n‖)) :
    hardyCircleReconstruction (c + d) = hardyCircleReconstruction c + hardyCircleReconstruction d := by
  unfold hardyCircleReconstruction
  simp  [add_smul]
  exact (common_summable_hardyCircleReconstruction_terms hc).tsum_add (common_summable_hardyCircleReconstruction_terms hd)

theorem vekua_reconstruction_smul (a : ℂ) c :
    hardyCircleReconstruction (a • c) = a • hardyCircleReconstruction c := by
  unfold hardyCircleReconstruction
  simp  [← smul_smul]
  exact tsum_const_smul'' a

def vekuaStrongReconstructionLin : L2Z →ₗ[ℂ] C(AddCircle circlePeriod, ℂ) where
  toFun b := hardyCircleReconstruction (fromL2 ((1 / 2 : ℝ) + 1) b)
  map_add' b d := by
    rw [fromL2_add]
    exact vekua_reconstruction_add
      (sq_tsum_norm_le (by norm_num) (isSobolevSeq_fromL2 _ b)).1
      (sq_tsum_norm_le (by norm_num) (isSobolevSeq_fromL2 _ d)).1
  map_smul' a b := by
    rw [fromL2_smul]
    exact vekua_reconstruction_smul a _

theorem vekuaStrongReconstructionLin_norm_le b :
    ‖vekuaStrongReconstructionLin b‖ ≤ Real.sqrt evalConst * ‖b‖ := by
  have hp := isSobolevSeq_fromL2 ((1 / 2) + 1) b
  obtain ⟨hs, hsq⟩ := sq_tsum_norm_le (by norm_num) hp
  have he : 0 ≤ evalConst := tsum_nonneg (fun n => by
    positivity)
  have hn := (norm_sobVec ((1 / 2) + 1) _ hp)
  rw [sobVec_fromL2] at hn
  calc
    _ ≤ ∑' n : ℤ, ‖fromL2 ((1 / 2) + 1) b n‖ := by
      change ‖∑' n : ℤ, fromL2 ((1 / 2) + 1) b n •
        fourier (T := 2 * Real.pi) n‖ ≤ _
      have hs' : Summable (fun n => ‖fromL2 ((1 / 2 : ℝ) + 1) b n •
          fourier (T := 2 * Real.pi) n‖) := by
        simpa  [norm_smul, fourier_norm] using hs
      simpa  [norm_smul, fourier_norm] using norm_tsum_le_tsum_norm hs'
    _ = Real.sqrt ((∑' n : ℤ, ‖fromL2 ((1 / 2) + 1) b n‖) ^ 2) :=
      (Real.sqrt_sq (tsum_nonneg (fun n => norm_nonneg _))).symm
    _ ≤ Real.sqrt (evalConst * sobNormSq ((1 / 2) + 1) (fromL2 ((1 / 2) + 1) b)) :=
      Real.sqrt_le_sqrt hsq
    _ = _ := by rw [Real.sqrt_mul he, ← hn]

/-- Genuine bounded synthesis into continuous circle functions for normalized
order-3/2 data. This permits passing the stronger remainder series pointwise. -/
def vekuaStrongCircleReconstruction : L2Z →L[ℂ] C(AddCircle circlePeriod, ℂ) :=
  vekuaStrongReconstructionLin.mkContinuous (Real.sqrt evalConst)
    vekuaStrongReconstructionLin_norm_le

theorem vekuaStrongCircleReconstruction_apply b :
    vekuaStrongCircleReconstruction b =
      hardyCircleReconstruction (fromL2 ((1 / 2 : ℝ) + 1) b) := rfl

theorem vekuaStrongCircleReconstruction_sobVec c
    hc :
    vekuaStrongCircleReconstruction (sobVec ((1 / 2 : ℝ) + 1) c hc) =
      hardyCircleReconstruction c := by
  rw [vekuaStrongCircleReconstruction_apply, fromL2_sobVec]

private theorem vekua_raw_trace_smul a 
    (hc : Summable (fun n => ‖c n‖)) θ :
    hardyFourierTrace (a • c) θ = a * hardyFourierTrace c θ := by
  have hac : Summable (fun n => ‖(a • c) n‖) := by
    simpa   using hc.mul_left ‖a‖
  rw [← hardyCircleReconstruction_coe hac, vekua_reconstruction_smul,
    ContinuousMap.smul_apply, smul_eq_mul, hardyCircleReconstruction_coe hc]

include R hR F hFs in
theorem fromL2_half_localConformalDiskHalfTrace
    hL
    u :
    fromL2 (1 / 2 : ℝ) (localConformalDiskHalfTrace hR F hFs hL u) =
      boundaryFourier (localConformalDiskH1Trace hR F hFs hL u) :=
  fromL2_half_diskHalfTrace (localConformalH1Pullback hR F hFs hL u)

end


section TraceCoordinates

variable {R C } (hR : 1 < R) (F )
    (hFs : RealSmoothOnBall F R)
    (hb : Bornology.IsBounded (F '' unitDisk))
    (hL : IsLipschitzDomain (F '' unitDisk))
    (hhol : DifferentiableOn ℂ F unitDisk)
    (hinj : InjOn F unitDisk)
    (hC : DiskInverseJacobianBound F C)
local notation "centeredCircleFixed" => localConformalCenteredCircle hR F hFs

local notation "diskH1TraceFixed" => localConformalDiskH1Trace hR F hFs hL


section
include hhol hinj hC

/-- The actual affine H¹ product has the actual centered coordinate trace. -/
theorem localConformalDiskH1Trace_affineMultiplier
    u :
    diskH1TraceFixed (neumannH1AffineMultiplier hb (F 1) u) =
      boundaryContinuousMultiplier centeredCircleFixed
        (diskH1TraceFixed u) := by
  refine (denseRange_smoothTraceH1Lin hb hL).induction_on
    (p := fun v => diskH1TraceFixed
      (neumannH1AffineMultiplier hb (F 1) v) =
        boundaryContinuousMultiplier centeredCircleFixed
          (diskH1TraceFixed v)) u ?_ ?_
  · exact isClosed_eq ((diskH1TraceFixed).continuous.comp
      (neumannH1AffineMultiplier hb (F 1)).continuous)
      ((boundaryContinuousMultiplier centeredCircleFixed).continuous.comp
        (diskH1TraceFixed).continuous)
  · intro f
    change diskH1TraceFixed
      (neumannH1AffineMultiplier hb (F 1) (smoothTraceH1 _ f)) = _
    rw [vekuaAffineMultiplier_smooth hb hL.1.1]
    apply Lp.ext
    filter_upwards [localConformalDiskH1Trace_smooth_ae hR F hFs hb hL hhol hinj hC
        (vekuaAffineTraceTest (F 1) f),
      boundaryContinuousMultiplier_ae centeredCircleFixed
        (diskH1TraceFixed (smoothTraceH1 _ f)),
      localConformalDiskH1Trace_smooth_ae hR F hFs hb hL hhol hinj hC f]
      with θ hp hm hf
    change diskH1TraceFixed
      (smoothTraceH1 _ (vekuaAffineTraceTest (F 1) f)) θ =
        boundaryContinuousMultiplier centeredCircleFixed
          (diskH1TraceFixed (smoothTraceH1 _ f)) θ
    rw [hp, hm, hf, localConformalCenteredCircle_apply]
    rfl

theorem localConformalDiskH1Trace_affineMultiplier_pow j
    u :
    diskH1TraceFixed (((neumannH1AffineMultiplier hb (F 1)) ^ j) u) =
      boundaryContinuousMultiplier (centeredCircleFixed ^ j)
        (diskH1TraceFixed u) := by
  have hp : diskH1TraceFixed
      (((neumannH1AffineMultiplier hb (F 1)) ^ j) u) =
      ((boundaryContinuousMultiplier centeredCircleFixed) ^ j)
        (diskH1TraceFixed u) := by
    induction j with
    | zero => tauto
    | succ j ih =>
      rw [pow_succ', ContinuousLinearMap.mul_apply,
        localConformalDiskH1Trace_affineMultiplier hR F hFs hb hL hhol hinj hC, ih,
        pow_succ', ContinuousLinearMap.mul_apply]
  rw [hp, vekua_boundaryMultiplier_pow]

/-- Every affine power, including the zero power, has the genuine normalized
Fourier multiplier represented by its averaged convolution power. -/
theorem localConformalDiskHalfTrace_affineMultiplier_pow (j : ℕ)
    (u : NeumannH1 (F '' unitDisk)) :
    localConformalDiskHalfTrace hR F hFs hL
        (((neumannH1AffineMultiplier hb (F 1)) ^ j) u) =
      normalizedHardyMultiplier
        (seqConvPow (fourierCoeff centeredCircleFixed) j)
        (wl1Norm_seqConvPow_le (by norm_num)
          (localConformalCenteredCircle_isWL1_half hR F hFs) j).1
        (localConformalDiskHalfTrace hR F hFs hL u) := by
  apply vekua_fromL2_injective (1 / 2)
  funext n
  rw [fromL2_half_localConformalDiskHalfTrace,
    localConformalDiskH1Trace_affineMultiplier_pow hR F hFs hb hL hhol hinj hC,
    boundaryFourier_continuousMultiplier,
    common_vekua_fromL2_multiplier, fromL2_half_localConformalDiskHalfTrace]
  · rw [vekua_circle_coeff_pow _
      (common_vekua_summable_coeff (by norm_num)
        (localConformalCenteredCircle_isWL1_half hR F hFs))]
  · rw [vekua_circle_coeff_pow _
      (common_vekua_summable_coeff (by norm_num)
        (localConformalCenteredCircle_isWL1_half hR F hFs))]
    exact common_vekua_summable_coeff (by norm_num)
      (wl1Norm_seqConvPow_le (by norm_num)
        (localConformalCenteredCircle_isWL1_half hR F hFs) j).1

end


end TraceCoordinates

section
variable {R } (hR : 1 < R) (F : PlaneMap) (hFs : RealSmoothOnBall F R)

section
include R hR F hFs

/-- The normalized primitive powers have exactly the original averaged
Fourier primitive powers, including their prescribed constant coefficients. -/
theorem fromL2_localConformalHardyPrimitive_pow (j : ℕ) (b : L2Z) :
    fromL2 (1 / 2 : ℝ) (((localConformalHardyPrimitive hR F hFs) ^ j) b) =
      antiPrimIter (localConformalHardyPrimitiveMultiplier F) j (fromL2 (1 / 2 : ℝ) b) := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [pow_succ', ContinuousLinearMap.mul_apply]
    change fromL2 (1 / 2) (normalizedHardyPrimitive _ _ _) = _
    rw [fromL2_normalizedHardyPrimitive, ih]
    exact (Function.iterate_succ_apply' _ _ _).symm

theorem normalizedHardyAverage_localConformalHardyPrimitive_pow (j : ℕ) (b : L2Z) :
    normalizedHardyAverage (((localConformalHardyPrimitive hR F hFs) ^ j) b) =
      antiPrimIter (localConformalHardyPrimitiveMultiplier F) j (normalizedHardyAverage b) := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [pow_succ', ContinuousLinearMap.mul_apply]
    change normalizedHardyAverage (normalizedHardyPrimitive _ _ _) = _
    rw [normalizedHardyAverage_primitive, ih]
    exact (Function.iterate_succ_apply' _ _ _).symm

end


/-- The genuine continuous angular velocity multiplier, reconstructed from
its absolutely summable averaged coefficients. -/
def localConformalPrimitiveCircle F  :=
  hardyCircleReconstruction (localConformalHardyPrimitiveMultiplier F)

section
include R hR F hFs

theorem localConformalPrimitiveCircle_coeff :
    fourierCoeff (localConformalPrimitiveCircle F) = localConformalHardyPrimitiveMultiplier F :=
  hardyCircleReconstruction_fourierCoeff (summable_norm_of_isWL1_one
    (physicalCircleTrace_fourier_weights_of_smooth_neighborhood hR F hFs).1)

theorem localConformalPrimitiveCircle_apply (θ : ℝ) :
    localConformalPrimitiveCircle F (θ : AddCircle circlePeriod) =
      conj (deriv (physicalCircleTrace F) θ) := by
  have ha : Summable (fun n => ‖localConformalHardyPrimitiveMultiplier F n‖) :=
    summable_norm_of_isWL1_one
      (physicalCircleTrace_fourier_weights_of_smooth_neighborhood hR F hFs).1
  change hardyCircleReconstruction (localConformalHardyPrimitiveMultiplier F)
    θ = _
  rw [hardyCircleReconstruction_coe ha]
  exact hardyFourierTrace_physical_conj_deriv_of_neighborhood hR F
    (hFs.of_le ((WithTop.coe_le_coe.mpr le_top))) θ

/-- Actual normalized primitive powers are actual physical interval primitive
powers, with their basepoint at angular origin zero. -/
theorem localConformalHardyPrimitive_pow_volterra_of_H1
    (hhol : DifferentiableOn ℂ F unitDisk) (b : L2Z)
    (hbn : IsNonpositiveFourierSupport b)
    (hb1 : IsSobolevSeq 1 (normalizedHardyAverage b)) (j : ℕ) (θ : ℝ) :
    hardyFourierTrace (normalizedHardyAverage
      (((localConformalHardyPrimitive hR F hFs) ^ j) b)) θ =
      volterraPrimitiveIterate (fun s => conj (deriv (physicalCircleTrace F) s))
        (hardyFourierTrace (normalizedHardyAverage b)) j θ := by
  have ha : IsWL1 1 (fourierCoeff (localConformalPrimitiveCircle F)) := by
    rw [localConformalPrimitiveCircle_coeff hR F hFs]
    exact (physicalCircleTrace_fourier_weights_of_smooth_neighborhood hR F hFs).1
  have han : IsStrictNegativeFourierSupport (fourierCoeff (localConformalPrimitiveCircle F)) := by
    rw [localConformalPrimitiveCircle_coeff hR F hFs]
    exact localConformalHardyPrimitiveMultiplier_strictNegative hR F hFs hhol
  have hbn' : IsNonpositiveFourierSupport (normalizedHardyAverage b) := by
    simp_all [fromL2, PolyaNeumann.IsNonpositiveFourierSupport, PolyaNeumann.normalizedHardyAverage]
  rw [normalizedHardyAverage_localConformalHardyPrimitive_pow,
    ← localConformalPrimitiveCircle_coeff hR F hFs,
    hardyFourierTrace_antiPrimIter_eq_volterraPrimitiveIterate
      (localConformalPrimitiveCircle F) ha hb1 han hbn']
  have he  :=
    funext (localConformalPrimitiveCircle_apply hR F hFs)
  rw [he]

private theorem vekua_trace_term_volterra
    (hhol : DifferentiableOn ℂ F unitDisk) (b : L2Z)
    (hbn : IsNonpositiveFourierSupport b) (hb1 : IsSobolevSeq 1 (fromL2 (1 / 2 : ℝ) b))
    j θ :
    hardyFourierTrace
      (vekuaBdryTerm (fourierCoeff (localConformalCenteredCircle hR F hFs))
        (localConformalHardyPrimitiveMultiplier F) (fromL2 (1 / 2 : ℝ) b) j) θ =
      (F (unitCircleMap θ) - F 1) ^ j *
        volterraPrimitiveIterate (fun s => conj (deriv (physicalCircleTrace F) s))
          (hardyFourierTrace (fromL2 (1 / 2 : ℝ) b)) j θ := by
  let A := localConformalPrimitiveCircle F
  let G := localConformalCenteredCircle hR F hFs
  let h := fromL2 (1 / 2) b
  have ha  :=
    (physicalCircleTrace_fourier_weights_of_smooth_neighborhood hR F hFs).1
  have hs : Summable (fun n => ‖antiPrimIter (localConformalHardyPrimitiveMultiplier F) j h n‖) :=
    summable_norm_antiPrimIter_of_H1 ha hb1 j
  let H := hardyCircleReconstruction (antiPrimIter (localConformalHardyPrimitiveMultiplier F) j h)
  have hH  :=
    hardyCircleReconstruction_fourierCoeff hs
  have hg  :=
    localConformalCenteredCircle_isWL1_half hR F hFs
  have hGp  :=
    vekua_circle_coeff_pow G (common_vekua_summable_coeff (by norm_num) hg) j
  have hGps : Summable (fourierCoeff (G ^ j)) := by
    rw [hGp]
    exact common_vekua_summable_coeff (by norm_num) (wl1Norm_seqConvPow_le (by norm_num) hg j).1
  let P := (G ^ j) * H
  have hHi : Integrable H AddCircle.haarAddCircle :=
    H.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hP : fourierCoeff P = vekuaBdryTerm (fourierCoeff G)
      (localConformalHardyPrimitiveMultiplier F) h j := by
    change fourierCoeff (fun q => (G ^ j) q * H q) = _
    rw [fourierCoeff_mul_eq_seqConv (G ^ j) hGps hHi, hGp, hH]
    rfl
  have hPabs : Summable (fun n => ‖fourierCoeff P n‖) := by
    rw [hP]
    have hg0 := common_vekua_isWL1_mono (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (wl1Norm_seqConvPow_le (by norm_num) hg j).1
    have hi0 : IsWL1 0 (antiPrimIter (localConformalHardyPrimitiveMultiplier F) j h) := by
      simpa  [IsWL1] using hs
    simpa  [vekuaBdryTerm, IsWL1] using
      (wl1Norm_seqConv_le (by norm_num) hg0 hi0).2.1
  have hbnp : IsNonpositiveFourierSupport h := by
    grind only [fromL2, PolyaNeumann.IsNonpositiveFourierSupport]
  have hAn : IsStrictNegativeFourierSupport (fourierCoeff A) := by
    rw [localConformalPrimitiveCircle_coeff hR F hFs]
    exact localConformalHardyPrimitiveMultiplier_strictNegative hR F hFs hhol
  have hAw : IsWL1 1 (fourierCoeff A) := by
    rw [localConformalPrimitiveCircle_coeff hR F hFs]
    exact ha
  have hJ := hardyFourierTrace_antiPrimIter_eq_volterraPrimitiveIterate A hAw hb1 hAn hbnp j θ
  rw [localConformalPrimitiveCircle_coeff hR F hFs] at hJ
  have hAv  :=
    funext (localConformalPrimitiveCircle_apply hR F hFs)
  rw [hAv] at hJ
  calc
    _ = P θ := by
      rw [← hP]
      exact hardyFourierTrace_fourierCoeff P hPabs θ
    _ = (F (unitCircleMap θ) - F 1) ^ j *
        hardyFourierTrace (antiPrimIter (localConformalHardyPrimitiveMultiplier F) j h) θ := by
      change (G θ) ^ j * H θ = _
      rw [localConformalCenteredCircle_apply, hardyCircleReconstruction_coe hs]
    _ = _ := by rw [hJ]

end


end


section PhysicalCoordinates

variable {R C K : ℝ} (hR : 1 < R) (F : PlaneMap)
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

/-- The normalized Fourier coefficient of each actual H¹ series term is
precisely the original boundary transmutation term. -/
theorem localConformalVekuaTrace_term (b : L2Z) (hbn : IsNonpositiveFourierSupport b)
    (j : ℕ) (n : ℤ) :
    localConformalDiskHalfTrace hR F hFs hL
      (((neumannH1AffineMultiplier hb (F 1)) ^ j)
        (localConformalHardyH1Extension hR F hFs hb hL hhol hinj hC hK e he hsource hes
          (((localConformalHardyPrimitive hR F hFs) ^ j) b))) n =
      ((sobWeight n ^ (1 / 2 : ℝ) : ℝ) : ℂ) *
        vekuaBdryTerm (fourierCoeff (localConformalCenteredCircle hR F hFs))
          (localConformalHardyPrimitiveMultiplier F) (fromL2 (1 / 2 : ℝ) b) j n := by
  rw [localConformalDiskHalfTrace_affineMultiplier_pow hR F hFs hb hL hhol hinj hC,
    localConformalDiskHalfTrace_hardyExtension_eq_of_nonpositive hR F hFs hb hL hhol
      hinj hC hK e he hsource hes _
      (localConformalHardyPrimitive_pow_nonpositive hR F hFs hhol b hbn j),
    normalizedHardyMultiplier_apply, fromL2_localConformalHardyPrimitive_pow]
  rfl

/-- Actual normalized boundary term, constructed as a bounded map. -/
def localConformalVekuaBoundaryTerm (E : ℂ) (j : ℕ) : L2Z →L[ℂ] L2Z :=
  physicalVekuaCoeff E j •
    ((normalizedHardyMultiplier
      (seqConvPow (fourierCoeff (localConformalCenteredCircle hR F hFs)) j)
      (wl1Norm_seqConvPow_le (by norm_num)
        (localConformalCenteredCircle_isWL1_half hR F hFs) j).1).comp
      ((localConformalHardyPrimitive hR F hFs) ^ j))
local notation "vekuaBoundaryTermFixed" => localConformalVekuaBoundaryTerm hR F hFs


theorem localConformalVekuaBoundaryTerm_apply E j b n :
    vekuaBoundaryTermFixed E j b n =
      physicalVekuaCoeff E j * ((sobWeight n ^ (1 / 2 : ℝ) : ℝ) : ℂ) *
        vekuaBdryTerm (fourierCoeff (localConformalCenteredCircle hR F hFs))
          (localConformalHardyPrimitiveMultiplier F) (fromL2 (1 / 2 : ℝ) b) j n := by
  let c := seqConvPow (fourierCoeff (localConformalCenteredCircle hR F hFs)) j
  have hc  :=
    (wl1Norm_seqConvPow_le (by norm_num)
      (localConformalCenteredCircle_isWL1_half hR F hFs) j).1
  change (physicalVekuaCoeff E j • normalizedHardyMultiplier c hc
    (((localConformalHardyPrimitive hR F hFs) ^ j) b)) n = _
  rw [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, normalizedHardyMultiplier_apply,
    fromL2_localConformalHardyPrimitive_pow]
  simp_all [physicalVekuaCoeff, sobWeight, vekuaBdryTerm, PolyaNeumann.physicalVekuaCoeff, PolyaNeumann.sobWeight, PolyaNeumann.seqConv, PolyaNeumann.antiPrimIter, PolyaNeumann.vekuaBdryTerm] <;> ring

/-- The boundary operator is the trace of the genuine convergent H¹ series. -/
def localConformalVekuaBoundary (E : ℂ) : L2Z →L[ℂ] L2Z :=
  (localConformalDiskHalfTrace hR F hFs hL).comp
    (localConformalVekuaH1AtBoundaryOrigin hR F hFs hb hL hhol hinj hC hK e he hsource hes E)
local notation "vekuaBoundaryFixed" => localConformalVekuaBoundary hR F hFs hb hL hhol hinj hC hK e he hsource hes


theorem localConformalVekuaBoundary_hasSum E (b : L2Z)
    (hbn : IsNonpositiveFourierSupport b) :
    HasSum (fun j : ℕ => vekuaBoundaryTermFixed E j b)
      (vekuaBoundaryFixed E b) := by
  have ht (j : ℕ) :
      physicalVekuaCoeff E j • localConformalDiskHalfTrace hR F hFs hL
        (((neumannH1AffineMultiplier hb (F 1)) ^ j)
          (localConformalHardyH1Extension hR F hFs hb hL hhol hinj hC hK e he hsource hes
            (((localConformalHardyPrimitive hR F hFs) ^ j) b))) =
        vekuaBoundaryTermFixed E j b := by
    ext n
    simp only [lp.coeFn_smul, Pi.smul_apply]
    rw [localConformalVekuaTrace_term hR F hFs hb hL hhol hinj hC hK e he hsource hes b hbn,
      localConformalVekuaBoundaryTerm_apply]
    ring
  simpa only [ht, localConformalVekuaBoundary, ContinuousLinearMap.comp_apply,
    localConformalVekuaH1AtBoundaryOrigin] using
    localConformalVekuaH1_halfTrace_hasSum hR F hFs hb hL hhol hinj hC hK e he hsource hes
      (F 1) E b

section
variable (E : ℂ) (b : L2Z)
include E b

include hb hL hhol hinj hC hK e he hsource hes in
theorem localConformalVekuaBoundaryTerm_zero
    (hbn : IsNonpositiveFourierSupport b) :
    vekuaBoundaryTermFixed E 0 b = b := by
  have ht := localConformalVekuaTrace_term hR F hFs hb hL hhol hinj hC hK e he hsource hes
    b hbn 0
  ext n
  rw [localConformalVekuaBoundaryTerm_apply, physicalVekuaCoeff_zero, one_mul, ← ht]
  simp only [pow_zero, ContinuousLinearMap.one_apply]
  rw [localConformalDiskHalfTrace_hardyExtension_eq_of_nonpositive hR F hFs hb hL hhol
    hinj hC hK e he hsource hes b hbn]

private theorem vekua_smoothing_strong_term (j : ℕ)
    (ht : IsSobolevSeq ((1 / 2 : ℝ) + 1)
      (vekuaBdryTerm (fourierCoeff (localConformalCenteredCircle hR F hFs))
        (localConformalHardyPrimitiveMultiplier F) (fromL2 (1 / 2 : ℝ) b) (j + 1))) :
    sobolevSmoothing 1 (by norm_num)
      (physicalVekuaCoeff E (j + 1) • sobVec ((1 / 2 : ℝ) + 1) _ ht) =
      vekuaBoundaryTermFixed E (j + 1) b := by
  ext n
  simp  [sobolevSmoothing, localConformalVekuaBoundaryTerm_apply]
  have he : -(1 : ℝ) + ((1 / 2 : ℝ) + 1) = 1 / 2 := by ring
  have hw : ((sobWeight n ^ (-(1 : ℝ)) : ℝ) : ℂ) *
      ((sobWeight n ^ ((1 / 2 : ℝ) + 1) : ℝ) : ℂ) =
      ((sobWeight n ^ (1 / 2 : ℝ) : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul, ← Real.rpow_add (sobWeight_pos n), he]
  grind

/-- The true normalized boundary remainder factors through one-order smoothing.
The stronger vector is constructed from the proved Fourier term bounds. -/
theorem localConformalVekuaBoundary_strong_remainder_hasSum
    (hbn : IsNonpositiveFourierSupport b) :
    ∃ (hT : ∀ j : ℕ, IsSobolevSeq ((1 / 2 : ℝ) + 1)
          (vekuaBdryTerm (fourierCoeff (localConformalCenteredCircle hR F hFs))
            (localConformalHardyPrimitiveMultiplier F) (fromL2 (1 / 2 : ℝ) b) (j + 1)))
      (r : L2Z),
      HasSum (fun j : ℕ => physicalVekuaCoeff E (j + 1) •
        sobVec ((1 / 2 : ℝ) + 1) _ (hT j)) r ∧
      vekuaBoundaryFixed E b - b =
        sobolevSmoothing 1 (by norm_num) r := by
  obtain ⟨hT, hN, -⟩ := vekuaBdry_sub_one_bound (by norm_num)
    (localConformalCenteredCircle_isWL1_threeHalves hR F hFs)
    (localConformalHardyPrimitiveMultiplier_isWL1 hR F hFs)
    (isSobolevSeq_fromL2 (1 / 2) b) E
  let f  := fun j => physicalVekuaCoeff E (j + 1) •
    sobVec ((1 / 2) + 1) _ (hT j)
  have hs : HasSum f (∑' j : ℕ, f j) := by
    exact (show Summable (fun j => ‖f j‖) from hN).of_norm.hasSum
  have hmap := (sobolevSmoothing 1 (by norm_num)).hasSum hs
  have hm : HasSum (fun j : ℕ => vekuaBoundaryTermFixed E (j + 1) b)
      (sobolevSmoothing 1 (by norm_num) (∑' j : ℕ, f j)) := by
    simpa only [f, vekua_smoothing_strong_term] using hmap
  have ht := (hasSum_nat_add_iff'
    (f := fun j : ℕ => vekuaBoundaryTermFixed E j b) 1).2
      (localConformalVekuaBoundary_hasSum hR F hFs hb hL hhol hinj hC hK e he hsource hes
        E b hbn)
  simp  [localConformalVekuaBoundaryTerm_zero hR F hFs hb hL hhol hinj hC hK e he hsource hes
      E b hbn] at ht
  exact ⟨hT, ∑' j : ℕ, f j, hs, ht.unique hm⟩

/-- The actual boundary remainder is in the range of one-order smoothing. -/
theorem localConformalVekuaBoundary_sub_gain
    (hbn : IsNonpositiveFourierSupport b) :
    ∃ r : L2Z,
      vekuaBoundaryFixed E b - b =
        sobolevSmoothing 1 (by norm_num) r := by
  obtain ⟨hT, r, hs, hr⟩ := localConformalVekuaBoundary_strong_remainder_hasSum hR F hFs
    hb hL hhol hinj hC hK e he hsource hes E b hbn
  exact ⟨r, hr⟩

/-- Zero actual trace forces one full order of gain on the original input. -/
theorem localConformalVekuaBoundary_kernel_smoothing
    (hbn : IsNonpositiveFourierSupport b)
    (hz : vekuaBoundaryFixed E b = 0) :
    ∃ r : L2Z, b = sobolevSmoothing 1 (by norm_num) r := by
  obtain ⟨r, hr⟩ := localConformalVekuaBoundary_sub_gain hR F hFs hb hL hhol hinj hC hK
    e he hsource hes E b hbn
  rw [hz, zero_sub] at hr
  refine ⟨-r, ?_⟩
  rw [map_neg, ← hr, neg_neg]

end


end PhysicalCoordinates

theorem fromL2_half_smoothing_one b :
    fromL2 (1 / 2 : ℝ) (sobolevSmoothing 1 (by norm_num) b) =
      fromL2 ((1 / 2 : ℝ) + 1) b := by
  funext n
  simp  [fromL2, sobolevSmoothing]
  rw [← mul_assoc, ← Complex.ofReal_mul, ← Real.rpow_add (sobWeight_pos n)]
  ring

section RegularVolterraTrace

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

local notation "VB" => localConformalVekuaBoundary hR F hFs hb hL hhol hinj hC hK
  e he hsource hes

section
variable (E : ℂ) (b : L2Z) (hbn : IsNonpositiveFourierSupport b) (hb1 : IsSobolevSeq 1 (fromL2 (1 / 2 : ℝ) b))
include E b hbn hb1

/-- The genuine Vekua coordinate trace preserves order-one regularity of
its original raw coefficients, using the proved stronger remainder. -/
theorem localConformalVekuaBoundary_raw_H1 :
    IsSobolevSeq 1 (fromL2 (1 / 2 : ℝ) (VB E b)) := by
  obtain ⟨r, hr⟩ := localConformalVekuaBoundary_sub_gain hR F hFs hb hL hhol hinj
    hC hK e he hsource hes E b hbn
  have heq : VB E b = b + sobolevSmoothing 1 (by norm_num) r := by
    rw [sub_eq_iff_eq_add] at hr
    exact hr.trans (add_comm _ _)
  rw [heq, fromL2_add, fromL2_half_smoothing_one]
  exact isSobolevSeq_add hb1
    (sobNormSq_mono (by norm_num)
      (isSobolevSeq_fromL2 ((1 / 2) + 1) r)).1

/-- For every actual order-one Hardy input the physical boundary series
converges pointwise to the Fourier reconstruction of its actual trace. -/
theorem localConformalVekuaBoundary_volterra_hasSum_of_H1 θ :
    HasSum (fun j : ℕ => physicalVekuaCoeff E j *
      (F (unitCircleMap θ) - F 1) ^ j *
      volterraPrimitiveIterate (fun s => conj (deriv (physicalCircleTrace F) s))
        (hardyFourierTrace (fromL2 (1 / 2 : ℝ) b)) j θ)
      (hardyFourierTrace (fromL2 (1 / 2 : ℝ) (VB E b)) θ) := by
  obtain ⟨hT, r, hs, hr⟩ := localConformalVekuaBoundary_strong_remainder_hasSum
    hR F hFs hb hL hhol hinj hC hK e he hsource hes E b hbn
  have heq : VB E b = b + sobolevSmoothing 1 (by norm_num) r := by
    rw [sub_eq_iff_eq_add] at hr
    exact hr.trans (add_comm _ _)
  have hseq : fromL2 (1 / 2 : ℝ) (VB E b) =
      fromL2 (1 / 2 : ℝ) b + fromL2 ((1 / 2 : ℝ) + 1) r := by
    rw [heq, fromL2_add, fromL2_half_smoothing_one]
  have hr1  :=
    (sobNormSq_mono (by norm_num : (1 : ℝ) ≤ (1 / 2 : ℝ) + 1)
      (isSobolevSeq_fromL2 ((1 / 2) + 1) r)).1
  have hbs : Summable (fun n => ‖fromL2 (1 / 2 : ℝ) b n‖) :=
    (sq_tsum_norm_le (s := 0) (by norm_num) (by simpa using hb1)).1
  have hrs : Summable (fun n => ‖fromL2 ((1 / 2 : ℝ) + 1) r n‖) :=
    (sq_tsum_norm_le (s := 0) (by norm_num) (by simpa using hr1)).1
  have hsum : Summable (fun n =>
      ‖(fromL2 (1 / 2 : ℝ) b + fromL2 ((1 / 2 : ℝ) + 1) r) n‖) :=
    (sq_tsum_norm_le (s := 0) (by norm_num)
      (by simpa using isSobolevSeq_add hb1 hr1)).1
  have hval : hardyFourierTrace (fromL2 (1 / 2 : ℝ) (VB E b)) θ =
      hardyFourierTrace (fromL2 (1 / 2 : ℝ) b) θ +
        vekuaStrongCircleReconstruction r (θ : AddCircle circlePeriod) := by
    rw [hseq, ← hardyCircleReconstruction_coe hsum,
      vekua_reconstruction_add hbs hrs]
    simp only [ContinuousMap.add_apply, hardyCircleReconstruction_coe hbs, vekuaStrongCircleReconstruction_apply]
  have ht (j : ℕ) : vekuaStrongCircleReconstruction
      (physicalVekuaCoeff E (j + 1) • sobVec ((1 / 2 : ℝ) + 1) _ (hT j))
        (θ : AddCircle circlePeriod) =
      physicalVekuaCoeff E (j + 1) * (F (unitCircleMap θ) - F 1) ^ (j + 1) *
        volterraPrimitiveIterate (fun s => conj (deriv (physicalCircleTrace F) s))
          (hardyFourierTrace (fromL2 (1 / 2 : ℝ) b)) (j + 1) θ := by
    rw [map_smul, vekuaStrongCircleReconstruction_sobVec, ContinuousMap.smul_apply,
      smul_eq_mul, hardyCircleReconstruction_coe
        (sq_tsum_norm_le (by norm_num) (hT j)).1,
      vekua_trace_term_volterra hR F hFs hhol b hbn hb1]
    ring
  have heval := (ContinuousMap.evalCLM ℂ (θ : AddCircle circlePeriod)).hasSum
    (vekuaStrongCircleReconstruction.hasSum hs)
  change HasSum (fun j : ℕ => vekuaStrongCircleReconstruction
    (physicalVekuaCoeff E (j + 1) • sobVec ((1 / 2) + 1) _ (hT j))
      θ)
    (vekuaStrongCircleReconstruction r θ) at heval
  have htail : HasSum (fun j : ℕ => physicalVekuaCoeff E (j + 1) *
      (F (unitCircleMap θ) - F 1) ^ (j + 1) *
      volterraPrimitiveIterate (fun s => conj (deriv (physicalCircleTrace F) s))
        (hardyFourierTrace (fromL2 (1 / 2 : ℝ) b)) (j + 1) θ)
      (vekuaStrongCircleReconstruction r (θ : AddCircle circlePeriod)) := by
    simpa only [ht] using heval
  apply (hasSum_nat_add_iff' (f := fun j : ℕ => physicalVekuaCoeff E j *
    (F (unitCircleMap θ) - F 1) ^ j *
    volterraPrimitiveIterate (fun s => conj (deriv (physicalCircleTrace F) s))
      (hardyFourierTrace (fromL2 (1 / 2) b)) j θ) 1).1
  simp_all [physicalVekuaCoeff, volterraPrimitiveIterate, PolyaNeumann.physicalVekuaCoeff, PolyaNeumann.volterraPrimitiveIterate,  PolyaNeumann.L2Z]

end


end RegularVolterraTrace

private theorem vekua_volterra_shift a h j :
    volterraPrimitiveIterate a (volterraPrimitiveIterate a h 1) j =
      volterraPrimitiveIterate a h (j + 1) := by
  induction j with
  | zero => rfl
  | succ j ih =>
    simp_all [volterraPrimitiveIterate]

private theorem vekua_volterra_next_bound
    (A : C(AddCircle circlePeriod, ℂ))  (hh : Continuous h)
     j t (ht : t ∈ Icc 0 T) :
    ‖volterraPrimitiveIterate (fun s => A (s : AddCircle circlePeriod)) h (j + 1) t‖ ≤
      (‖A‖ * ∫ s in (0 : ℝ)..t, ‖h s‖) * (‖A‖ * T) ^ j / (j.factorial : ℝ) := by
  let a : ComplexCurve := fun s => A s
  have ha  := A.continuous.comp (AddCircle.continuous_mk' _)
  have hi : 0 ≤ ∫ s in (0 : ℝ)..t, ‖h s‖ :=
    intervalIntegral.integral_nonneg ht.1 (fun s _ => norm_nonneg _)
  have hfirst (s : ℝ) (hs : s ∈ Icc 0 t) :
      ‖volterraPrimitiveIterate a h 1 s‖ ≤ ‖A‖ * ∫ x in (0 : ℝ)..t, ‖h x‖ := by
    calc
      _ ≤ ∫ x in (0)..s, ‖a x * h x‖ :=
        intervalIntegral.norm_integral_le_integral_norm hs.1
      _ ≤ ∫ x in (0)..s, ‖A‖ * ‖h x‖ := by
        refine intervalIntegral.integral_mono_on hs.1 ((ha.mul hh).norm.intervalIntegrable 0 s)
          ((continuous_const.mul hh.norm).intervalIntegrable 0 s) ?_
        intro x _
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_right (A.norm_coe_le_norm _) (norm_nonneg _)
      _ = ‖A‖ * ∫ x in (0)..s, ‖h x‖ := intervalIntegral.integral_const_mul _ _
      _ ≤ ‖A‖ * ∫ x in (0)..t, ‖h x‖ := by
        exact mul_le_mul_of_nonneg_left
          (intervalIntegral.integral_mono_interval le_rfl hs.1 hs.2
            (Eventually.of_forall (fun x => norm_nonneg (h x))) (hh.norm.intervalIntegrable 0 t))
          (norm_nonneg A)
  rw [← vekua_volterra_shift a h j]
  have hbound := volterraPrimitiveIterate_bound_uniform ha
    (continuous_volterraPrimitiveIterate ha hh 1) (norm_nonneg A)
    (mul_nonneg (norm_nonneg A) hi) (fun s _ => A.norm_coe_le_norm _) hfirst j t
      ⟨ht.1, le_rfl⟩
  exact hbound.trans (div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (mul_nonneg (norm_nonneg A) ht.1)
        (mul_le_mul_of_nonneg_left ht.2 (norm_nonneg A)) j)
      (mul_nonneg (norm_nonneg A) hi)) (Nat.cast_nonneg _))

private theorem vekua_volterra_kernel_unique
    (A G : C(AddCircle circlePeriod, ℂ)) E  (hh : Continuous h)
    {T : ℝ} 
    (hsum : ∀ t ∈ Icc 0 T, HasSum (fun j : ℕ => physicalVekuaCoeff E (j + 1) *
      G (t : AddCircle circlePeriod) ^ (j + 1) *
      volterraPrimitiveIterate (fun s => A (s : AddCircle circlePeriod)) h (j + 1) t) (-h t)) :
    ∀ t ∈ Icc 0 T, h t = 0 := by
  let K := ‖-E / 4‖
  let B := ‖G‖
  let M := ‖A‖
  let x := K * B * M * T
  have hK : 0 ≤ K := norm_nonneg _
  have hC : 0 ≤ K * B * M * Real.exp x := by positivity
  apply continuous_eq_zero_of_norm_le_volterra hh hC
  intro t ht
  let I := ∫ s in (0)..t, ‖h s‖
  let f  := fun j => physicalVekuaCoeff E (j + 1) *
    G t ^ (j + 1) *
    volterraPrimitiveIterate (fun s => A s) h (j + 1) t
  have hmajor (j : ℕ) : ‖f j‖ ≤ (K * B * M * I) * (x ^ j / (j.factorial : ℝ)) := by
    have hc : ‖physicalVekuaCoeff E (j + 1)‖ ≤ K ^ (j + 1) := by
      rw [norm_physicalVekuaCoeff]
      exact div_le_self (pow_nonneg hK _)
        (by exact_mod_cast Nat.one_le_of_lt (Nat.factorial_pos (j + 1)))
    have hg : ‖G (t : AddCircle circlePeriod) ^ (j + 1)‖ ≤ B ^ (j + 1) := by
      rw [norm_pow]
      exact pow_le_pow_left₀ (norm_nonneg _) (G.norm_coe_le_norm _) _
    have hj := vekua_volterra_next_bound A hh j t ht
    calc
      _ ≤ (K ^ (j + 1) * B ^ (j + 1)) * ((M * I) * (M * T) ^ j / j.factorial) := by
        simp only [f, norm_mul]
        gcongr
      _ = _ := by simp only [x, pow_succ, mul_pow]; ring
  have hmaj : Summable (fun j : ℕ => (K * B * M * I) * (x ^ j / (j.factorial : ℝ))) :=
    (Real.summable_pow_div_factorial x).mul_left _
  have hn  :=
    Summable.of_nonneg_of_le (fun j => norm_nonneg _) hmajor hmaj
  calc
    ‖h t‖ = ‖∑' j : ℕ, f j‖ := by rw [(hsum t ht).tsum_eq, norm_neg]
    _ ≤ ∑' j : ℕ, ‖f j‖ := norm_tsum_le_tsum_norm hn
    _ ≤ ∑' j : ℕ, (K * B * M * I) * (x ^ j / j.factorial) :=
      Summable.tsum_le_tsum hmajor hn hmaj
    _ = (K * B * M * Real.exp x) * ∫ s in (0)..t, ‖h s‖ := by
      rw [tsum_mul_left, Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div]
      ring

section KernelRegularity

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

section
variable (E ) (b : L2Z) (hbn : IsNonpositiveFourierSupport b) (hz : localConformalVekuaBoundary hR F hFs hb hL hhol hinj hC hK e he hsource hes E b = 0)
include E b hbn hz

theorem localConformalVekuaBoundary_kernel_raw_threeHalves :
    IsSobolevSeq ((1 / 2 : ℝ) + 1) (fromL2 (1 / 2 : ℝ) b) := by
  obtain ⟨r, hr⟩ := localConformalVekuaBoundary_kernel_smoothing hR F hFs hb hL hhol hinj hC hK
    e he hsource hes E b hbn hz
  rw [hr, fromL2_half_smoothing_one]
  exact isSobolevSeq_fromL2 _ r

/-- Zero actual trace gives a genuine pointwise Volterra equation for the
original data. The raw orthonormal Fourier input is sqrt(2π) times its averaged
input, so this equality has the same constant scale in every term. -/
theorem localConformalVekuaBoundary_kernel_volterra_hasSum
    θ :
    HasSum (fun j : ℕ => physicalVekuaCoeff E (j + 1) *
      (F (unitCircleMap θ) - F 1) ^ (j + 1) *
      volterraPrimitiveIterate (fun s => conj (deriv (physicalCircleTrace F) s))
        (hardyFourierTrace (fromL2 (1 / 2 : ℝ) b)) (j + 1) θ)
      (-hardyFourierTrace (fromL2 (1 / 2 : ℝ) b) θ) := by
  obtain ⟨hT, r, hs, hr⟩ := localConformalVekuaBoundary_strong_remainder_hasSum hR F hFs
    hb hL hhol hinj hC hK e he hsource hes E b hbn
  rw [hz, zero_sub] at hr
  have hb3 := localConformalVekuaBoundary_kernel_raw_threeHalves hR F hFs hb hL hhol hinj hC hK
    e he hsource hes E b hbn hz
  have hb1 : IsSobolevSeq 1 (fromL2 (1 / 2 : ℝ) b) := (sobNormSq_mono (by norm_num) hb3).1
  have hbs  :=
    (sq_tsum_norm_le (by norm_num) hb3).1
  have hrseq : fromL2 ((1 / 2 : ℝ) + 1) r = -fromL2 (1 / 2 : ℝ) b := by
    calc
      _ = fromL2 (1 / 2) (sobolevSmoothing 1 (by norm_num) r) :=
        (fromL2_half_smoothing_one r).symm
      _ = fromL2 (1 / 2) (-b) := congrArg (fromL2 (1 / 2)) hr.symm
      _ = _ := by funext n; simp [fromL2]
  have ht (j : ℕ) :
      vekuaStrongCircleReconstruction
        (physicalVekuaCoeff E (j + 1) • sobVec ((1 / 2 : ℝ) + 1) _ (hT j))
          (θ : AddCircle circlePeriod) =
      physicalVekuaCoeff E (j + 1) * (F (unitCircleMap θ) - F 1) ^ (j + 1) *
        volterraPrimitiveIterate (fun s => conj (deriv (physicalCircleTrace F) s))
          (hardyFourierTrace (fromL2 (1 / 2 : ℝ) b)) (j + 1) θ := by
    rw [map_smul, vekuaStrongCircleReconstruction_sobVec, ContinuousMap.smul_apply,
      smul_eq_mul, hardyCircleReconstruction_coe
        (sq_tsum_norm_le (by norm_num) (hT j)).1,
      vekua_trace_term_volterra hR F hFs hhol b hbn hb1]
    ring
  have hval : vekuaStrongCircleReconstruction r (θ : AddCircle circlePeriod) =
      -hardyFourierTrace (fromL2 (1 / 2 : ℝ) b) θ := by
    rw [vekuaStrongCircleReconstruction_apply, hardyCircleReconstruction_coe
      (sq_tsum_norm_le (by norm_num) (isSobolevSeq_fromL2 _ r)).1,
      hrseq]
    have hn : -fromL2 (1 / 2 : ℝ) b = (-1 : ℂ) • fromL2 (1 / 2 : ℝ) b := by
      simp
    rw [hn, vekua_raw_trace_smul (-1) hbs]
    ring
  have heval := (ContinuousMap.evalCLM ℂ (θ : AddCircle circlePeriod)).hasSum
    (vekuaStrongCircleReconstruction.hasSum hs)
  simp_all

/-- The actual Vekua coordinate trace has no kernel on the full nonpositive
half-trace space. Regularity, the pointwise equation and the Volterra bound
are all derived from the actual zero trace. -/
theorem localConformalVekuaBoundary_eq_zero_imp :
    b = 0 := by
  have hb3 := localConformalVekuaBoundary_kernel_raw_threeHalves hR F hFs hb hL hhol hinj hC hK
    e he hsource hes E b hbn hz
  have hbs  :=
    (sq_tsum_norm_le (by norm_num) hb3).1
  have hh  := continuous_hardyFourierTrace hbs
  have hs : ∀ θ ∈ boundaryInterval, HasSum (fun j : ℕ =>
      physicalVekuaCoeff E (j + 1) *
        localConformalCenteredCircle hR F hFs (θ : AddCircle circlePeriod) ^ (j + 1) *
        volterraPrimitiveIterate
          (fun s => localConformalPrimitiveCircle F (s : AddCircle circlePeriod))
          (hardyFourierTrace (fromL2 (1 / 2 : ℝ) b)) (j + 1) θ)
      (-hardyFourierTrace (fromL2 (1 / 2 : ℝ) b) θ) := by
    intro θ _
    simpa  [localConformalCenteredCircle_apply hR F hFs,
      localConformalPrimitiveCircle_apply hR F hFs] using
      localConformalVekuaBoundary_kernel_volterra_hasSum hR F hFs hb hL hhol hinj hC hK
        e he hsource hes E b hbn hz θ
  have hzero := vekua_volterra_kernel_unique (localConformalPrimitiveCircle F)
    (localConformalCenteredCircle hR F hFs) E hh hs
  have hcoeff : fromL2 (1 / 2 : ℝ) b = 0 := by
    funext n
    change fromL2 (1 / 2) b n = 0
    have hc := congrFun (hardyCircleReconstruction_fourierCoeff hbs) n
    rw [← hc, fourierCoeff_eq_intervalIntegral _ n 0, zero_add]
    have hi : (∫ θ in (0 : ℝ)..2 * Real.pi,
        fourier (T := 2 * Real.pi) (-n) (θ : AddCircle circlePeriod) •
          hardyCircleReconstruction (fromL2 (1 / 2 : ℝ) b)
            (θ : AddCircle circlePeriod)) = 0 := by
      calc
        _ = ∫ θ in (0)..2 * Real.pi, (0 : ℂ) := by
          apply intervalIntegral.integral_congr
          intro θ hθ
          rw [uIcc_of_le Real.two_pi_pos.le] at hθ
          change fourier (T := 2 * Real.pi) (-n) θ •
            hardyCircleReconstruction (fromL2 (1 / 2) b)
              θ = 0
          rw [hardyCircleReconstruction_coe hbs, hzero θ hθ, smul_zero]
        _ = 0 := by simp
    rw [hi, smul_zero]
  apply vekua_fromL2_injective (1 / 2)
  rw [hcoeff]
  funext n
  simp [fromL2]

end


/-- The same actual uniqueness conclusion stated directly for the ordinary
coordinate trace of the physical H¹ vector. -/
theorem localConformalVekuaH1_eq_zero_input_of_coordinate_trace_zero E (b : L2Z)
    (hbn : IsNonpositiveFourierSupport b)
    (ht : localConformalDiskH1Trace hR F hFs hL
      (localConformalVekuaH1AtBoundaryOrigin hR F hFs hb hL hhol hinj hC hK e he hsource hes E b) = 0) :
    b = 0 := by
  apply localConformalVekuaBoundary_eq_zero_imp hR F hFs hb hL hhol hinj hC hK
    e he hsource hes E b hbn
  apply vekua_fromL2_injective (1 / 2)
  change fromL2 (1 / 2) (localConformalDiskHalfTrace hR F hFs hL
    (localConformalVekuaH1AtBoundaryOrigin hR F hFs hb hL hhol hinj hC hK e he hsource hes E b)) =
      fromL2 (1 / 2) 0
  rw [fromL2_half_localConformalDiskHalfTrace, ht, map_zero]
  funext n
  simp [fromL2]

end KernelRegularity

end PolyaNeumann

end
