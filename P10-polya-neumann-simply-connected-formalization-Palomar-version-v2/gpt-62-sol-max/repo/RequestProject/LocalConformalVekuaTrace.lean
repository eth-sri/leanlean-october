module

public import RequestProject.CircleFourier
public import RequestProject.ConformalDiskCoordinates

public import RequestProject.LocalConformalVekuaSeries
public import RequestProject.HardyVolterraBridge

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

set_option autoImplicit false

noncomputable section

namespace PolyaNeumann

open MeasureTheory Set Metric Filter
open scoped Topology ComplexConjugate

private def vekuaAffineTraceTest (p : ℂ) (f : smoothTraceTests) : smoothTraceTests :=
  ⟨fun z => (z - p) * f z,
    ⟨(contDiff_id.sub contDiff_const).mul f.property.1,
      f.property.2.1.mul_left, subset_univ _⟩⟩

private theorem vekuaAffineMultiplier_smooth {Ω : Set ℂ}
    (hb : Bornology.IsBounded Ω) (hΩ : IsOpen Ω) (p : ℂ) (f : smoothTraceTests) :
    neumannH1AffineMultiplier hb p (smoothTraceH1 Ω f) =
      smoothTraceH1 Ω (vekuaAffineTraceTest p f) := by
  apply h1Value_injective hΩ
  rw [h1Value_neumannH1AffineMultiplier, h1Value_smoothTraceH1]
  apply Lp.ext
  filter_upwards [neumannAffineL2Multiplier_ae p (neumannH1AffineBound_spec hb p)
      ((smoothTraceTests_memLp Ω f).toLp (f : ℂ → ℂ)),
    (smoothTraceTests_memLp Ω f).coeFn_toLp,
    (smoothTraceTests_memLp Ω (vekuaAffineTraceTest p f)).coeFn_toLp]
    with z hm hf hp
  rw [hm]
  change (z - p) * ((smoothTraceTests_memLp Ω f).toLp (f : ℂ → ℂ)) z =
    ((smoothTraceTests_memLp Ω (vekuaAffineTraceTest p f)).toLp
      (vekuaAffineTraceTest p f : ℂ → ℂ)) z
  rw [hf, hp]
  rfl

section

variable {R : ℝ} (hR : 1 < R) (F : ℂ → ℂ) (hFs : ContDiffOn ℝ (⊤ : ℕ∞) F (ball (0 : ℂ) R))
include R hR F hFs

/-- A genuine compact smooth representative of F(z)-F(1) on the closed disk. -/
def localConformalCenteredTraceTest  : smoothTraceTests :=
  ⟨smoothDiskCutoff R hR (fun z => F z - F 1),
    smoothDiskCutoff_testFunction hR (hFs.sub contDiffOn_const)⟩

/-- Actual continuous centered boundary coordinate, without an arclength premise. -/
def localConformalCenteredCircle  :
    C(AddCircle (2 * Real.pi), ℂ) :=
  diskSmoothCoefficientCircle
    (smoothTraceTestsH1Coefficient (localConformalCenteredTraceTest hR F hFs))

theorem localConformalCenteredCircle_apply  (θ : ℝ) :
    localConformalCenteredCircle hR F hFs (θ : AddCircle (2 * Real.pi)) =
      F (circleMap 0 1 θ) - F 1 := by
  rw [localConformalCenteredCircle, diskSmoothCoefficientCircle_apply]
  change smoothDiskCutoff R hR (fun z => F z - F 1) (circleMap 0 1 θ) = _
  exact smoothDiskCutoff_eq_closedDisk hR _
    (sphere_subset_closedBall (circleMap_mem_sphere (0 : ℂ) (by norm_num) θ))

theorem localConformalCenteredCircle_coeff  :
    fourierCoeff (localConformalCenteredCircle hR F hFs) =
      fourierCoeffOn Real.two_pi_pos
        (fun θ => physicalCircleTrace F θ - physicalCircleTrace F 0) := by
  funext n
  rw [localConformalCenteredCircle, diskSmoothCoefficientCircle_coeff]
  congr 1
  funext θ
  change smoothDiskCutoff R hR (fun z => F z - F 1) (circleMap 0 1 θ) = _
  rw [smoothDiskCutoff_eq_closedDisk hR _
    (sphere_subset_closedBall (circleMap_mem_sphere (0 : ℂ) (by norm_num) θ))]
  simp [physicalCircleTrace, circleMap_zero]

theorem localConformalCenteredCircle_isWL1_two  :
    IsWL1 2 (fourierCoeff (localConformalCenteredCircle hR F hFs)) := by
  rw [localConformalCenteredCircle_coeff]
  exact (physicalCircleTrace_fourier_weights_of_smooth_neighborhood hR F hFs).2

end

section

variable {R : ℝ} (hR : 1 < R) (F : ℂ → ℂ) (hFs : ContDiffOn ℝ (⊤ : ℕ∞) F (ball (0 : ℂ) R))
include R hR F hFs

theorem localConformalCenteredCircle_isWL1_half  :
    IsWL1 (1 / 2 : ℝ) (fourierCoeff (localConformalCenteredCircle hR F hFs)) :=
  IsWL1.mono (by norm_num) (localConformalCenteredCircle_isWL1_two hR F hFs)

theorem localConformalCenteredCircle_isWL1_threeHalves  :
    IsWL1 ((1 / 2 : ℝ) + 1) (fourierCoeff (localConformalCenteredCircle hR F hFs)) :=
  IsWL1.mono (by norm_num) (localConformalCenteredCircle_isWL1_two hR F hFs)

end

section

variable (A : C(AddCircle (2 * Real.pi), ℂ))
include A

private theorem vekua_boundaryMultiplier_pow 
    (j : ℕ) (g : BoundaryL2) :
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
    simp only [pow_succ', ContinuousMap.mul_apply]
    ring

private theorem vekua_circle_coeff_pow 
    (hA : Summable (fourierCoeff A)) (j : ℕ) :
    fourierCoeff (A ^ j) = seqConvPow (fourierCoeff A) j := by
  induction j with
  | zero =>
    funext n
    change fourierCoeff (fun _ : AddCircle (2 * Real.pi) => (1 : ℂ)) n = seqDelta n
    have he : (fun _ : AddCircle (2 * Real.pi) => (1 : ℂ)) =
        (fourier (T := 2 * Real.pi) 0 : AddCircle (2 * Real.pi) → ℂ) := by
      funext q
      simp
    simp [he, fourierCoeff_fourier, seqDelta, Pi.single_apply]
  | succ j ih =>
    have hp : Integrable (A ^ j : C(AddCircle (2 * Real.pi), ℂ)) AddCircle.haarAddCircle :=
      (A ^ j).continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    rw [pow_succ']
    change fourierCoeff (fun q => A q * (A q) ^ j) =
      seqConv (fourierCoeff A) (seqConvPow (fourierCoeff A) j)
    simpa only [ContinuousMap.pow_apply, ih] using fourierCoeff_mul_eq_seqConv A hA hp

end

private theorem vekua_summable_circle_terms {c : ℤ → ℂ}
    (hc : Summable (fun n => ‖c n‖)) :
    Summable (fun n => c n • fourier (T := 2 * Real.pi) n) := by
  apply Summable.of_norm
  simpa only [norm_smul, fourier_norm, mul_one] using hc

theorem vekua_reconstruction_add {c d : ℤ → ℂ}
    (hc : Summable (fun n => ‖c n‖)) (hd : Summable (fun n => ‖d n‖)) :
    hardyCircleReconstruction (c + d) = hardyCircleReconstruction c + hardyCircleReconstruction d := by
  unfold hardyCircleReconstruction
  simp  [add_smul]
  exact (vekua_summable_circle_terms hc).tsum_add (vekua_summable_circle_terms hd)

theorem vekua_reconstruction_smul (a : ℂ) (c : ℤ → ℂ) :
    hardyCircleReconstruction (a • c) = a • hardyCircleReconstruction c := by
  unfold hardyCircleReconstruction
  simp  [smul_eq_mul, ← smul_smul]
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

theorem vekuaStrongReconstructionLin_norm_le (b : L2Z) :
    ‖vekuaStrongReconstructionLin b‖ ≤ Real.sqrt evalConst * ‖b‖ := by
  have hp := isSobolevSeq_fromL2 ((1 / 2 : ℝ) + 1) b
  obtain ⟨hs, hsq⟩ := sq_tsum_norm_le (by norm_num : (0 : ℝ) ≤ 1 / 2) hp
  have he : 0 ≤ evalConst := tsum_nonneg (fun n => by positivity)
  have hn := (norm_sobVec ((1 / 2 : ℝ) + 1) _ hp)
  rw [sobVec_fromL2] at hn
  calc
    _ ≤ ∑' n : ℤ, ‖fromL2 ((1 / 2 : ℝ) + 1) b n‖ := by
      change ‖∑' n : ℤ, fromL2 ((1 / 2 : ℝ) + 1) b n •
        fourier (T := 2 * Real.pi) n‖ ≤ _
      have hs' : Summable (fun n => ‖fromL2 ((1 / 2 : ℝ) + 1) b n •
          fourier (T := 2 * Real.pi) n‖) := by
        simpa only [norm_smul, fourier_norm, mul_one] using hs
      simpa only [norm_smul, fourier_norm, mul_one] using norm_tsum_le_tsum_norm hs'
    _ = Real.sqrt ((∑' n : ℤ, ‖fromL2 ((1 / 2 : ℝ) + 1) b n‖) ^ 2) :=
      (Real.sqrt_sq (tsum_nonneg (fun n => norm_nonneg _))).symm
    _ ≤ Real.sqrt (evalConst * sobNormSq ((1 / 2 : ℝ) + 1) (fromL2 ((1 / 2 : ℝ) + 1) b)) :=
      Real.sqrt_le_sqrt hsq
    _ = _ := by simp_all

/-- Genuine bounded synthesis into continuous circle functions for normalized
order-3/2 data. This permits passing the stronger remainder series pointwise. -/
def vekuaStrongCircleReconstruction : L2Z →L[ℂ] C(AddCircle (2 * Real.pi), ℂ) :=
  vekuaStrongReconstructionLin.mkContinuous (Real.sqrt evalConst)
    vekuaStrongReconstructionLin_norm_le

theorem vekuaStrongCircleReconstruction_apply (b : L2Z) :
    vekuaStrongCircleReconstruction b =
      hardyCircleReconstruction (fromL2 ((1 / 2 : ℝ) + 1) b) := rfl

theorem vekuaStrongCircleReconstruction_sobVec (c : ℤ → ℂ)
    (hc : IsSobolevSeq ((1 / 2 : ℝ) + 1) c) :
    vekuaStrongCircleReconstruction (sobVec ((1 / 2 : ℝ) + 1) c hc) =
      hardyCircleReconstruction c := by
  rw [vekuaStrongCircleReconstruction_apply, fromL2_sobVec]

theorem fromL2_half_localConformalDiskHalfTrace {R : ℝ} (hR : 1 < R) (F : ℂ → ℂ)
    (hFs : ContDiffOn ℝ (⊤ : ℕ∞) F (ball (0 : ℂ) R))
    (hL : IsLipschitzDomain (F '' ball (0 : ℂ) 1))
    (u : NeumannH1 (F '' ball (0 : ℂ) 1)) :
    fromL2 (1 / 2 : ℝ) (localConformalDiskHalfTrace hR F hFs hL u) =
      boundaryFourier (localConformalDiskH1Trace hR F hFs hL u) :=
  fromL2_half_diskHalfTrace (localConformalH1Pullback hR F hFs hL u)

section TraceCoordinates

variable {F : ℂ → ℂ} (coords : ConformalDiskCoordinates F)

local notation "Ω" => F '' ball (0 : ℂ) 1
local notation "M" => neumannH1AffineMultiplier coords.bounded (F 1)
local notation "C" => localConformalCenteredCircle coords.one_lt_radius F coords.smooth

/-- The actual affine H¹ product has the actual centered coordinate trace. -/
theorem localConformalDiskH1Trace_affineMultiplier
    (u : NeumannH1 Ω) :
    coords.trace (M u) =
      boundaryContinuousMultiplier (C)
        (coords.trace u) := by
  refine (denseRange_smoothTraceH1Lin coords.bounded coords.lipschitz).induction_on
    (p := fun v => coords.trace
      (M v) =
        boundaryContinuousMultiplier (C)
          (coords.trace v)) u ?_ ?_
  · exact isClosed_eq ((coords.trace).continuous.comp
      (ContinuousLinearMap.continuous M))
      ((boundaryContinuousMultiplier (C)).continuous.comp
        (coords.trace).continuous)
  · intro f
    change coords.trace
      (M (smoothTraceH1 _ f)) = _
    rw [vekuaAffineMultiplier_smooth coords.bounded coords.lipschitz.1.1]
    apply Lp.ext
    filter_upwards [localConformalDiskH1Trace_smooth_ae coords
        (vekuaAffineTraceTest (F 1) f),
      boundaryContinuousMultiplier_ae (C)
        (coords.trace (smoothTraceH1 _ f)),
      localConformalDiskH1Trace_smooth_ae coords f]
      with θ hp hm hf
    change coords.trace
      (smoothTraceH1 _ (vekuaAffineTraceTest (F 1) f)) θ =
        boundaryContinuousMultiplier (C)
          (coords.trace (smoothTraceH1 _ f)) θ
    rw [hp, hm, hf, localConformalCenteredCircle_apply]
    rfl

theorem localConformalDiskH1Trace_affineMultiplier_pow (j : ℕ)
    (u : NeumannH1 Ω) :
    coords.trace ((M ^ j) u) =
      boundaryContinuousMultiplier ((C) ^ j)
        (coords.trace u) := by
  rw [← vekua_boundaryMultiplier_pow]
  have h : Function.Semiconj coords.trace M (boundaryContinuousMultiplier C) :=
    localConformalDiskH1Trace_affineMultiplier coords
  simpa only [FunLike.coe_pow_eq_iterate] using h.iterate_right j u

/-- Every affine power, including the zero power, has the genuine normalized
Fourier multiplier represented by its averaged convolution power. -/
theorem localConformalDiskHalfTrace_affineMultiplier_pow (j : ℕ)
    (u : NeumannH1 Ω) :
    coords.halfTrace
        ((M ^ j) u) =
      normalizedHardyMultiplier
        (seqConvPow (fourierCoeff (C)) j)
        (wl1Norm_seqConvPow_le (by norm_num)
          (localConformalCenteredCircle_isWL1_half coords.one_lt_radius F coords.smooth) j).1
        (coords.halfTrace u) := by
  apply fromL2_injective (1 / 2 : ℝ)
  funext n
  rw [fromL2_half_localConformalDiskHalfTrace,
    localConformalDiskH1Trace_affineMultiplier_pow coords,
    boundaryFourier_continuousMultiplier,
    fromL2_normalizedHardyMultiplier, fromL2_half_localConformalDiskHalfTrace]
  · rw [vekua_circle_coeff_pow _
      (IsWL1.summable (by norm_num)
        (localConformalCenteredCircle_isWL1_half coords.one_lt_radius F coords.smooth))]
  · rw [vekua_circle_coeff_pow _
      (IsWL1.summable (by norm_num)
        (localConformalCenteredCircle_isWL1_half coords.one_lt_radius F coords.smooth))]
    exact IsWL1.summable (by norm_num)
      (wl1Norm_seqConvPow_le (by norm_num)
        (localConformalCenteredCircle_isWL1_half coords.one_lt_radius F coords.smooth) j).1

end TraceCoordinates

section

variable {R : ℝ} (hR : 1 < R) (F : ℂ → ℂ) (hFs : ContDiffOn ℝ (⊤ : ℕ∞) F (ball (0 : ℂ) R)) (j : ℕ) (b : L2Z)
include R hR F hFs j b

/-- The normalized primitive powers have exactly the original averaged
Fourier primitive powers, including their prescribed constant coefficients. -/
theorem fromL2_localConformalHardyPrimitive_pow  :
    fromL2 (1 / 2 : ℝ) (((localConformalHardyPrimitive hR F hFs) ^ j) b) =
      antiPrimIter (localConformalHardyPrimitiveMultiplier F) j (fromL2 (1 / 2 : ℝ) b) := by
  have h : Function.Semiconj (fromL2 (1 / 2 : ℝ)) (localConformalHardyPrimitive hR F hFs)
      (antiPrim (localConformalHardyPrimitiveMultiplier F)) :=
    fromL2_normalizedHardyPrimitive _ _
  simpa only [FunLike.coe_pow_eq_iterate, antiPrimIter] using h.iterate_right j b

theorem normalizedHardyAverage_localConformalHardyPrimitive_pow  :
    normalizedHardyAverage (((localConformalHardyPrimitive hR F hFs) ^ j) b) =
      antiPrimIter (localConformalHardyPrimitiveMultiplier F) j (normalizedHardyAverage b) := by
  have h : Function.Semiconj normalizedHardyAverage (localConformalHardyPrimitive hR F hFs)
      (antiPrim (localConformalHardyPrimitiveMultiplier F)) := normalizedHardyAverage_primitive _ _
  simpa only [FunLike.coe_pow_eq_iterate, antiPrimIter] using h.iterate_right j b

end

/-- The genuine continuous angular velocity multiplier, reconstructed from
its absolutely summable averaged coefficients. -/
def localConformalPrimitiveCircle (F : ℂ → ℂ) : C(AddCircle (2 * Real.pi), ℂ) :=
  hardyCircleReconstruction (localConformalHardyPrimitiveMultiplier F)

section

variable {R : ℝ} (hR : 1 < R) (F : ℂ → ℂ) (hFs : ContDiffOn ℝ (⊤ : ℕ∞) F (ball (0 : ℂ) R))
include R hR F hFs

theorem localConformalPrimitiveCircle_coeff  :
    fourierCoeff (localConformalPrimitiveCircle F) = localConformalHardyPrimitiveMultiplier F :=
  hardyCircleReconstruction_fourierCoeff (summable_norm_of_isWL1_one
    (physicalCircleTrace_fourier_weights_of_smooth_neighborhood hR F hFs).1)

theorem localConformalPrimitiveCircle_isWL1 : IsWL1 1 (fourierCoeff (localConformalPrimitiveCircle F)) := by
  rw [localConformalPrimitiveCircle_coeff hR F hFs]
  exact (physicalCircleTrace_fourier_weights_of_smooth_neighborhood hR F hFs).1

theorem localConformalPrimitiveCircle_strictNegative (hhol : DifferentiableOn ℂ F (ball 0 1)) :
    IsStrictNegativeFourierSupport (fourierCoeff (localConformalPrimitiveCircle F)) := by
  rw [localConformalPrimitiveCircle_coeff hR F hFs]
  exact localConformalHardyPrimitiveMultiplier_strictNegative hR F hFs hhol

theorem localConformalPrimitiveCircle_apply  (θ : ℝ) :
    localConformalPrimitiveCircle F (θ : AddCircle (2 * Real.pi)) =
      conj (deriv (physicalCircleTrace F) θ) := by
  rw [localConformalPrimitiveCircle, localConformalHardyPrimitiveMultiplier, hardyCircleReconstruction_coe
    (summable_norm_of_isWL1_one (physicalCircleTrace_fourier_weights_of_smooth_neighborhood hR F hFs).1)]
  exact hardyFourierTrace_physical_conj_deriv_of_neighborhood hR F (hFs.of_le (by simp)) θ

/-- Actual normalized primitive powers are actual physical interval primitive
powers, with their basepoint at angular origin zero. -/
theorem localConformalHardyPrimitive_pow_volterra_of_H1 
    (hhol : DifferentiableOn ℂ F (ball (0 : ℂ) 1)) (b : L2Z)
    (hbn : IsNonpositiveFourierSupport b)
    (hb1 : IsSobolevSeq 1 (normalizedHardyAverage b)) (j : ℕ) (θ : ℝ) :
    hardyFourierTrace (normalizedHardyAverage
      (((localConformalHardyPrimitive hR F hFs) ^ j) b)) θ =
      volterraPrimitiveIterate (fun s => conj (deriv (physicalCircleTrace F) s))
        (hardyFourierTrace (normalizedHardyAverage b)) j θ := by
  have hbn' : IsNonpositiveFourierSupport (normalizedHardyAverage b) := by
    intro n hn
    simp [normalizedHardyAverage, fromL2, hbn n hn]
  rw [normalizedHardyAverage_localConformalHardyPrimitive_pow,
    ← localConformalPrimitiveCircle_coeff hR F hFs,
    hardyFourierTrace_antiPrimIter_eq_volterraPrimitiveIterate
      (localConformalPrimitiveCircle F) (localConformalPrimitiveCircle_isWL1 hR F hFs) hb1
      (localConformalPrimitiveCircle_strictNegative hR F hFs hhol) hbn']
  have he :=
    funext (localConformalPrimitiveCircle_apply hR F hFs)
  tauto

private theorem vekua_trace_term_volterra 
    (hhol : DifferentiableOn ℂ F (ball (0 : ℂ) 1)) (b : L2Z)
    (hbn : IsNonpositiveFourierSupport b) (hb1 : IsSobolevSeq 1 (fromL2 (1 / 2 : ℝ) b))
    (j : ℕ) (θ : ℝ) :
    hardyFourierTrace
      (vekuaBdryTerm (fourierCoeff (localConformalCenteredCircle hR F hFs))
        (localConformalHardyPrimitiveMultiplier F) (fromL2 (1 / 2 : ℝ) b) j) θ =
      (F (circleMap 0 1 θ) - F 1) ^ j *
        volterraPrimitiveIterate (fun s => conj (deriv (physicalCircleTrace F) s))
          (hardyFourierTrace (fromL2 (1 / 2 : ℝ) b)) j θ := by
  let A := localConformalPrimitiveCircle F
  let G := localConformalCenteredCircle hR F hFs
  let h := fromL2 (1 / 2 : ℝ) b
  have ha : IsWL1 1 (localConformalHardyPrimitiveMultiplier F) :=
    (physicalCircleTrace_fourier_weights_of_smooth_neighborhood hR F hFs).1
  have hs : Summable (fun n => ‖antiPrimIter (localConformalHardyPrimitiveMultiplier F) j h n‖) :=
    summable_norm_antiPrimIter_of_H1 ha hb1 j
  let H := hardyCircleReconstruction (antiPrimIter (localConformalHardyPrimitiveMultiplier F) j h)
  have hH : fourierCoeff H = antiPrimIter (localConformalHardyPrimitiveMultiplier F) j h :=
    hardyCircleReconstruction_fourierCoeff hs
  have hg : IsWL1 (1 / 2 : ℝ) (fourierCoeff G) :=
    localConformalCenteredCircle_isWL1_half hR F hFs
  have hGp : fourierCoeff (G ^ j) = seqConvPow (fourierCoeff G) j :=
    vekua_circle_coeff_pow G (IsWL1.summable (by norm_num) hg) j
  have hGps : Summable (fourierCoeff (G ^ j)) := by
    rw [hGp]
    exact IsWL1.summable (by norm_num) (wl1Norm_seqConvPow_le (by norm_num) hg j).1
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
    have hg0 := IsWL1.mono (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (wl1Norm_seqConvPow_le (by norm_num) hg j).1
    have hi0 : IsWL1 0 (antiPrimIter (localConformalHardyPrimitiveMultiplier F) j h) := by
      simpa only [IsWL1, Real.rpow_zero, one_mul] using hs
    simpa only [vekuaBdryTerm, IsWL1, Real.rpow_zero, one_mul] using
      (wl1Norm_seqConv_le (by norm_num : (0 : ℝ) ≤ 0) hg0 hi0).2.1
  have hbnp : IsNonpositiveFourierSupport h := by
    intro n hn
    simp [h, fromL2, hbn n hn]
  have hJ := hardyFourierTrace_antiPrimIter_eq_volterraPrimitiveIterate A
    (localConformalPrimitiveCircle_isWL1 hR F hFs) hb1
    (localConformalPrimitiveCircle_strictNegative hR F hFs hhol) hbnp j θ
  rw [localConformalPrimitiveCircle_coeff hR F hFs] at hJ
  have hAv : (fun s : ℝ => A (s : AddCircle (2 * Real.pi))) =
      (fun s : ℝ => conj (deriv (physicalCircleTrace F) s)) :=
    funext (localConformalPrimitiveCircle_apply hR F hFs)
  rw [hAv] at hJ
  calc
    _ = P (θ : AddCircle (2 * Real.pi)) := by
      rw [← hP]
      exact hardyFourierTrace_fourierCoeff P hPabs θ
    _ = (F (circleMap 0 1 θ) - F 1) ^ j *
        hardyFourierTrace (antiPrimIter (localConformalHardyPrimitiveMultiplier F) j h) θ := by
      change (G (θ : AddCircle (2 * Real.pi))) ^ j * H (θ : AddCircle (2 * Real.pi)) = _
      rw [localConformalCenteredCircle_apply, hardyCircleReconstruction_coe hs]
    _ = _ := by tauto

end

section PhysicalCoordinates

variable {F : ℂ → ℂ} (coords : ConformalDiskCoordinates F)
include coords

local notation "J" => localConformalHardyPrimitive coords.one_lt_radius F coords.smooth
local notation "G" => fourierCoeff (localConformalCenteredCircle coords.one_lt_radius F coords.smooth)

/-- The normalized boundary term is the trace of the corresponding H¹ term. -/
def localConformalVekuaBoundaryTerm (E : ℂ) (j : ℕ) (b : L2Z) : L2Z :=
  physicalVekuaCoeff E j • coords.halfTrace
    (((neumannH1AffineMultiplier coords.bounded (F 1)) ^ j)
      (localConformalHardyH1Extension coords ((J ^ j) b)))

theorem localConformalVekuaBoundaryTerm_apply (E : ℂ) (j : ℕ) (b : L2Z)
    (hbn : IsNonpositiveFourierSupport b) (n : ℤ) :
    localConformalVekuaBoundaryTerm coords E j b n =
      physicalVekuaCoeff E j * ((sobWeight n ^ (1 / 2 : ℝ) : ℝ) : ℂ) *
        vekuaBdryTerm G (localConformalHardyPrimitiveMultiplier F) (fromL2 (1 / 2 : ℝ) b) j n := by
  simp only [localConformalVekuaBoundaryTerm, lp.coeFn_smul, Pi.smul_apply]
  rw [localConformalDiskHalfTrace_affineMultiplier_pow coords,
    localConformalDiskHalfTrace_hardyExtension_eq_of_nonpositive coords _
      (localConformalHardyPrimitive_pow_nonpositive coords.one_lt_radius F coords.smooth coords.holomorphic b hbn j),
    normalizedHardyMultiplier_apply, fromL2_localConformalHardyPrimitive_pow]
  simp only [smul_eq_mul, vekuaBdryTerm, mul_assoc]

/-- The boundary operator is the trace of the genuine convergent H¹ series. -/
def localConformalVekuaBoundary (E : ℂ) : L2Z →L[ℂ] L2Z :=
  coords.halfTrace.comp (localConformalVekuaH1AtBoundaryOrigin coords E)

theorem localConformalVekuaBoundary_hasSum (E : ℂ) (b : L2Z) :
    HasSum (fun j : ℕ => localConformalVekuaBoundaryTerm coords E j b)
      (localConformalVekuaBoundary coords E b) := by
  simpa only [localConformalVekuaBoundaryTerm, localConformalVekuaBoundary,
    ContinuousLinearMap.comp_apply, localConformalVekuaH1AtBoundaryOrigin, map_smul] using
    coords.halfTrace.hasSum (localConformalVekuaH1_hasSum coords (F 1) E b)

theorem localConformalVekuaBoundaryTerm_zero (E : ℂ) (b : L2Z)
    (hbn : IsNonpositiveFourierSupport b) :
    localConformalVekuaBoundaryTerm coords E 0 b = b := by
  simp only [localConformalVekuaBoundaryTerm, physicalVekuaCoeff_zero, one_smul,
    pow_zero, ContinuousLinearMap.one_apply]
  exact localConformalDiskHalfTrace_hardyExtension_eq_of_nonpositive coords b hbn

private theorem vekua_smoothing_strong_term (E : ℂ) (b : L2Z)
    (hbn : IsNonpositiveFourierSupport b) (j : ℕ)
    (ht : IsSobolevSeq ((1 / 2 : ℝ) + 1)
      (vekuaBdryTerm (G)
        (localConformalHardyPrimitiveMultiplier F) (fromL2 (1 / 2 : ℝ) b) (j + 1))) :
    sobolevSmoothing 1 (by norm_num)
      (physicalVekuaCoeff E (j + 1) • sobVec ((1 / 2 : ℝ) + 1) _ ht) =
      localConformalVekuaBoundaryTerm coords E (j + 1) b := by
  ext n
  simp only [map_smul, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul,
    sobolevSmoothing, diagOp_apply, sobVec_apply, localConformalVekuaBoundaryTerm_apply coords _ _ _ hbn]
  have he : -(1 : ℝ) + ((1 / 2 : ℝ) + 1) = 1 / 2 := by ring
  have hw : ((sobWeight n ^ (-(1 : ℝ)) : ℝ) : ℂ) *
      ((sobWeight n ^ ((1 / 2 : ℝ) + 1) : ℝ) : ℂ) =
      ((sobWeight n ^ (1 / 2 : ℝ) : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul, ← Real.rpow_add (sobWeight_pos n), he]
  grind

section

variable (E : ℂ) (b : L2Z) (hbn : IsNonpositiveFourierSupport b)
include E b hbn

/-- The true normalized boundary remainder factors through one-order smoothing.
The stronger vector is constructed from the proved Fourier term bounds. -/
theorem localConformalVekuaBoundary_strong_remainder_hasSum  :
    ∃ (hT : ∀ j : ℕ, IsSobolevSeq ((1 / 2 : ℝ) + 1)
          (vekuaBdryTerm (G)
            (localConformalHardyPrimitiveMultiplier F) (fromL2 (1 / 2 : ℝ) b) (j + 1)))
      (r : L2Z),
      HasSum (fun j : ℕ => physicalVekuaCoeff E (j + 1) •
        sobVec ((1 / 2 : ℝ) + 1) _ (hT j)) r ∧
      localConformalVekuaBoundary coords E b - b =
        sobolevSmoothing 1 (by norm_num) r := by
  obtain ⟨hT, hN, -⟩ := vekuaBdry_sub_one_bound (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (localConformalCenteredCircle_isWL1_threeHalves coords.one_lt_radius F coords.smooth)
    (localConformalHardyPrimitiveMultiplier_isWL1 coords.one_lt_radius F coords.smooth)
    (isSobolevSeq_fromL2 (1 / 2 : ℝ) b) E
  let f := fun j => physicalVekuaCoeff E (j + 1) •
    sobVec ((1 / 2 : ℝ) + 1) _ (hT j)
  have hs : HasSum f (∑' j : ℕ, f j) := by
    exact (show Summable (fun j => ‖f j‖) from hN).of_norm.hasSum
  have hmap := (sobolevSmoothing 1 (by norm_num)).hasSum hs
  have hm : HasSum (fun j : ℕ => localConformalVekuaBoundaryTerm coords E (j + 1) b)
      (sobolevSmoothing 1 (by norm_num) (∑' j : ℕ, f j)) := by
    simpa only [f, vekua_smoothing_strong_term coords E b hbn] using hmap
  have ht := (hasSum_nat_add_iff'
    (f := fun j : ℕ => localConformalVekuaBoundaryTerm coords E j b) 1).2
      (localConformalVekuaBoundary_hasSum coords E b)
  simp  [localConformalVekuaBoundaryTerm_zero coords
      E b hbn] at ht
  exact ⟨hT, ∑' j : ℕ, f j, hs, ht.unique hm⟩

/-- The actual boundary remainder is in the range of one-order smoothing. -/
theorem localConformalVekuaBoundary_sub_gain  :
    ∃ r : L2Z,
      localConformalVekuaBoundary coords E b - b =
        sobolevSmoothing 1 (by norm_num) r := by
  obtain ⟨hT, r, hs, hr⟩ := localConformalVekuaBoundary_strong_remainder_hasSum coords E b hbn
  exact ⟨r, hr⟩


end

end PhysicalCoordinates

theorem fromL2_half_smoothing_one (b : L2Z) :
    fromL2 (1 / 2 : ℝ) (sobolevSmoothing 1 (by norm_num) b) =
      fromL2 ((1 / 2 : ℝ) + 1) b := by
  funext n
  simp only [fromL2, sobolevSmoothing, diagOp_apply]
  rw [← mul_assoc, ← Complex.ofReal_mul, ← Real.rpow_add (sobWeight_pos n)]
  ring

section RegularVolterraTrace

variable {F : ℂ → ℂ} (coords : ConformalDiskCoordinates F)
include coords

local notation "VB" => localConformalVekuaBoundary coords

section

variable (E : ℂ) (b : L2Z) (hbn : IsNonpositiveFourierSupport b) (hb1 : IsSobolevSeq 1 (fromL2 (1 / 2 : ℝ) b))
include E b hbn hb1

/-- The genuine Vekua coordinate trace preserves order-one regularity of
its original raw coefficients, using the proved stronger remainder. -/
theorem localConformalVekuaBoundary_raw_H1  :
    IsSobolevSeq 1 (fromL2 (1 / 2 : ℝ) (VB E b)) := by
  obtain ⟨r, hr⟩ := localConformalVekuaBoundary_sub_gain coords E b hbn
  have heq : VB E b = b + sobolevSmoothing 1 (by norm_num) r := by
    rw [sub_eq_iff_eq_add] at hr
    exact hr.trans (add_comm _ _)
  rw [heq, fromL2_add, fromL2_half_smoothing_one]
  exact isSobolevSeq_add hb1
    (sobNormSq_mono (by norm_num : (1 : ℝ) ≤ (1 / 2 : ℝ) + 1)
      (isSobolevSeq_fromL2 ((1 / 2 : ℝ) + 1) r)).1

/-- For every actual order-one Hardy input the physical boundary series
converges pointwise to the Fourier reconstruction of its actual trace. -/
theorem localConformalVekuaBoundary_volterra_hasSum_of_H1  (θ : ℝ) :
    HasSum (fun j : ℕ => physicalVekuaCoeff E j *
      (F (circleMap 0 1 θ) - F 1) ^ j *
      volterraPrimitiveIterate (fun s => conj (deriv (physicalCircleTrace F) s))
        (hardyFourierTrace (fromL2 (1 / 2 : ℝ) b)) j θ)
      (hardyFourierTrace (fromL2 (1 / 2 : ℝ) (VB E b)) θ) := by
  obtain ⟨hT, r, hs, hr⟩ := localConformalVekuaBoundary_strong_remainder_hasSum coords E b hbn
  have heq : VB E b = b + sobolevSmoothing 1 (by norm_num) r := by
    rw [sub_eq_iff_eq_add] at hr
    exact hr.trans (add_comm _ _)
  have hseq : fromL2 (1 / 2 : ℝ) (VB E b) =
      fromL2 (1 / 2 : ℝ) b + fromL2 ((1 / 2 : ℝ) + 1) r := by
    rw [heq, fromL2_add, fromL2_half_smoothing_one]
  have hr1 :=
    (sobNormSq_mono (by norm_num : (1 : ℝ) ≤ (1 / 2 : ℝ) + 1)
      (isSobolevSeq_fromL2 ((1 / 2 : ℝ) + 1) r)).1
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
        vekuaStrongCircleReconstruction r (θ : AddCircle (2 * Real.pi)) := by
    rw [hseq, ← hardyCircleReconstruction_coe hsum,
      vekua_reconstruction_add hbs hrs]
    simp only [ContinuousMap.add_apply, hardyCircleReconstruction_coe hbs,
      vekuaStrongCircleReconstruction_apply]
  have ht (j : ℕ) : vekuaStrongCircleReconstruction
      (physicalVekuaCoeff E (j + 1) • sobVec ((1 / 2 : ℝ) + 1) _ (hT j))
        (θ : AddCircle (2 * Real.pi)) =
      physicalVekuaCoeff E (j + 1) * (F (circleMap 0 1 θ) - F 1) ^ (j + 1) *
        volterraPrimitiveIterate (fun s => conj (deriv (physicalCircleTrace F) s))
          (hardyFourierTrace (fromL2 (1 / 2 : ℝ) b)) (j + 1) θ := by
    rw [map_smul, vekuaStrongCircleReconstruction_sobVec, ContinuousMap.smul_apply,
      hardyCircleReconstruction_coe
        (sq_tsum_norm_le (by norm_num : (0 : ℝ) ≤ 1 / 2) (hT j)).1,
      vekua_trace_term_volterra coords.one_lt_radius F coords.smooth coords.holomorphic b hbn hb1]
    ring
  have heval := (ContinuousMap.evalCLM ℂ (θ : AddCircle (2 * Real.pi))).hasSum
    (vekuaStrongCircleReconstruction.hasSum hs)
  change HasSum (fun j : ℕ => vekuaStrongCircleReconstruction
    (physicalVekuaCoeff E (j + 1) • sobVec ((1 / 2 : ℝ) + 1) _ (hT j))
      (θ : AddCircle (2 * Real.pi)))
    (vekuaStrongCircleReconstruction r (θ : AddCircle (2 * Real.pi))) at heval
  have htail : HasSum (fun j : ℕ => physicalVekuaCoeff E (j + 1) *
      (F (circleMap 0 1 θ) - F 1) ^ (j + 1) *
      volterraPrimitiveIterate (fun s => conj (deriv (physicalCircleTrace F) s))
        (hardyFourierTrace (fromL2 (1 / 2 : ℝ) b)) (j + 1) θ)
      (vekuaStrongCircleReconstruction r (θ : AddCircle (2 * Real.pi))) := by
    simp_all
  apply (hasSum_nat_add_iff' (f := fun j : ℕ => physicalVekuaCoeff E j *
    (F (circleMap 0 1 θ) - F 1) ^ j *
    volterraPrimitiveIterate (fun s => conj (deriv (physicalCircleTrace F) s))
      (hardyFourierTrace (fromL2 (1 / 2 : ℝ) b)) j θ) 1).1
  simpa only [Finset.sum_range_one, physicalVekuaCoeff, pow_zero, Nat.factorial_zero,
    Nat.cast_one, div_one, one_mul, volterraPrimitiveIterate, hval,
    add_sub_cancel_left] using htail

end

end RegularVolterraTrace

end PolyaNeumann

end
