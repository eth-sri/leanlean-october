module

public import RequestProject.CircleAnalysisNotation

public import RequestProject.DiskCoordinates

public import RequestProject.LocalConformalVekuaSeries
public import RequestProject.HardyVolterraBridge
public import RequestProject.VolterraUniqueness
public import RequestProject.PlanarNotation

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

open scoped ContDiff

namespace PolyaNeumann

open MeasureTheory Set Metric Filter
open scoped Topology ComplexConjugate

section

variable (Φ : SmoothDiskMap) (A : C(ParamCircle, ℂ)) (a : ℂ) (hA : Summable (fourierCoeff A))
    (c : ℤ → ℂ) (j : ℕ) (hc : IsWL1 halfOrder c) (b : L2Z)

private def vekuaAffineTraceTest (p : ℂ) (f : smoothTraceTests) : smoothTraceTests :=
  ⟨fun z => (z - p) * f z,
    ⟨(contDiff_id.sub contDiff_const).mul f.property.1,
      f.property.2.1.mul_left, subset_univ _⟩⟩

private theorem vekuaAffineMultiplier_smooth {Ω : Set ℂ}
    (hb : Bornology.IsBounded Ω) (hΩ : IsOpen Ω) (p : ℂ) (f : smoothTraceTests) :
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
  
  rw [hf, hp]
  rfl

include Φ in
/-- A genuine compact smooth representative of F(z)-F(1) on the closed disk. -/
def SmoothDiskMap.centeredTraceTest : smoothTraceTests :=
  ⟨smoothDiskCutoff Φ.radius Φ.one_lt_radius (fun z => Φ.map z - Φ.map 1),
    smoothDiskCutoff_testFunction Φ.one_lt_radius (Φ.smooth.sub contDiffOn_const)⟩

include Φ in
/-- Actual continuous centered boundary coordinate, without an arclength premise. -/
def SmoothDiskMap.centeredCircle :
    C(ParamCircle, ℂ) :=
  diskSmoothCoefficientCircle
    (smoothTraceTestsH1Coefficient Φ.centeredTraceTest)

theorem localConformalCenteredCircle_apply (θ : ℝ) :
    Φ.centeredCircle (θ : ParamCircle) =
      Φ.map (unitCirclePt θ) - Φ.map 1 := by
  rw [SmoothDiskMap.centeredCircle, diskSmoothCoefficientCircle_apply]
  change smoothDiskCutoff Φ.radius Φ.one_lt_radius (fun z => Φ.map z - Φ.map 1) (unitCirclePt θ) = _
  exact smoothDiskCutoff_eq_closedDisk Φ.one_lt_radius _
    (sphere_subset_closedBall (circleMap_mem_sphere (0 : ℂ) (by norm_num) θ))

theorem localConformalCenteredCircle_coeff :
    fourierCoeff Φ.centeredCircle =
      angleCoeff
        (fun θ => Φ.boundary θ - Φ.boundary 0) := by
  funext n
  rw [SmoothDiskMap.centeredCircle, diskSmoothCoefficientCircle_coeff]
  congr 1
  funext θ
  change smoothDiskCutoff Φ.radius Φ.one_lt_radius (fun z => Φ.map z - Φ.map 1) (unitCirclePt θ) = _
  rw [smoothDiskCutoff_eq_closedDisk Φ.one_lt_radius _
    (sphere_subset_closedBall (circleMap_mem_sphere (0 : ℂ) (by norm_num) θ))]
  simp [physicalCircleTrace, circleMap_zero]

theorem localConformalCenteredCircle_isWL1_two :
    IsWL1 2 (fourierCoeff Φ.centeredCircle) := by
  rw [localConformalCenteredCircle_coeff]
  exact (physicalCircleTrace_fourier_weights_of_smooth_neighborhood Φ).2

theorem vekua_isWL1_mono {s t : ℝ} (hst : s ≤ t) {c : ℤ → ℂ}
    (hc : IsWL1 t c) : IsWL1 s c := by
  refine hc.of_nonneg_of_le (fun n => ?_) (fun n => ?_)
  · exact mul_nonneg (Real.rpow_nonneg (sobWeight_pos n).le _) (norm_nonneg _)
  · exact mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow_of_exponent_le (one_le_sobWeight n) hst) (norm_nonneg _)

theorem localConformalCenteredCircle_isWL1_half :
    IsWL1 halfOrder (fourierCoeff Φ.centeredCircle) :=
  vekua_isWL1_mono (by norm_num) (localConformalCenteredCircle_isWL1_two Φ)

theorem localConformalCenteredCircle_isWL1_threeHalves :
    IsWL1 (halfOrder + 1) (fourierCoeff Φ.centeredCircle) :=
  vekua_isWL1_mono (by norm_num) (localConformalCenteredCircle_isWL1_two Φ)

theorem vekua_summable_coeff {s : ℝ} (hs : 0 ≤ s) {c : ℤ → ℂ}
    (hc : IsWL1 s c) : Summable c := by
  apply Summable.of_norm
  exact hc.of_nonneg_of_le ((by norm_num)) (fun n =>
    le_mul_of_one_le_left (norm_nonneg _) (Real.one_le_rpow (one_le_sobWeight n) hs))

private theorem vekua_boundaryMultiplier_pow (g : BoundaryL2) :
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
    simp [pow_succ'] <;> ring

include hA in
private theorem vekua_circle_coeff_pow :
    fourierCoeff (A ^ j) = seqConvPow (fourierCoeff A) j := by
  induction j with
  | zero =>
    funext n
    change fourierCoeff (fun _ : ParamCircle => (1 : ℂ)) n = seqDelta n
    have he : (fun _ : ParamCircle => (1 : ℂ)) =
        (fourier  0 : ParamCircle → ℂ) := by
      funext q
      simp
    simp [he, fourierCoeff_fourier, seqDelta, Pi.single_apply]
  | succ j ih =>
    
    rw [pow_succ']
    change fourierCoeff (fun q => A q * (A q) ^ j) =
      seqConv (fourierCoeff A) (seqConvPow (fourierCoeff A) j)
    simpa only [ContinuousMap.pow_apply, ih] using fourierCoeff_mul_eq_seqConv A hA ((A ^ j).continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))

theorem vekua_fromL2_multiplier :
    fromL2 halfOrder (normalizedHardyMultiplier c hc b) =
      seqConv c (fromL2 halfOrder b) := by
  funext n
  rw [fromL2, normalizedHardyMultiplier_apply, ← mul_assoc, ← Complex.ofReal_mul,
    mul_comm (sobWeight n ^ (-halfOrder)), sobWeight_rpow_mul_neg,
    Complex.ofReal_one, one_mul]

private theorem vekua_fromL2_injective (s : ℝ) : Function.Injective (fromL2 s) := by
  intro b d hbd
  apply lp.ext
  funext n
  have hn := congrFun hbd n
  
  refine mul_left_cancel₀ ?_ hn
  exact_mod_cast (Real.rpow_pos_of_pos (sobWeight_pos n) (-s)).ne'

theorem vekua_reconstruction_add {c d : ℤ → ℂ}
    (hc : Summable (fun n => ‖c n‖)) (hd : Summable (fun n => ‖d n‖)) :
    hardyCircleReconstruction (c + d) = hardyCircleReconstruction c + hardyCircleReconstruction d := by
  unfold hardyCircleReconstruction
  simp [add_smul]
  exact (summable_hardyCircleReconstruction_terms hc).tsum_add (summable_hardyCircleReconstruction_terms hd)

theorem vekua_reconstruction_smul :
    hardyCircleReconstruction (a • c) = a • hardyCircleReconstruction c := by
  unfold hardyCircleReconstruction
  simp [smul_eq_mul, ← smul_smul]
  exact tsum_const_smul'' a

def vekuaStrongReconstructionLin : L2Z →ₗ[ℂ] C(ParamCircle, ℂ) where
  toFun b := hardyCircleReconstruction (fromL2 (halfOrder + 1) b)
  map_add' b d := by
    rw [fromL2_add]
    exact vekua_reconstruction_add
      (sq_tsum_norm_le (by norm_num : (0 : ℝ) ≤ 1 / 2) (isSobolevSeq_fromL2 _ b)).1
      (sq_tsum_norm_le (by norm_num : (0 : ℝ) ≤ 1 / 2) (isSobolevSeq_fromL2 _ d)).1
  map_smul' a b := by
    rw [fromL2_smul]
    exact vekua_reconstruction_smul a _

theorem vekuaStrongReconstructionLin_norm_le :
    ‖vekuaStrongReconstructionLin b‖ ≤ Real.sqrt evalConst * ‖b‖ := by
  have hp := isSobolevSeq_fromL2 (halfOrder + 1) b
  obtain ⟨hs, hsq⟩ := sq_tsum_norm_le (by positivity) hp
  have he : 0 ≤ evalConst := tsum_nonneg (fun n => by
    positivity)
  have hn := (norm_sobVec (halfOrder + 1) _ hp)
  rw [sobVec_fromL2] at hn
  calc
    _ ≤ ∑' n : ℤ, ‖fromL2 (halfOrder + 1) b n‖ := by
      change ‖∑' n : ℤ, fromL2 (halfOrder + 1) b n •
        fourier  n‖ ≤ _
      have hs' : Summable (fun n => ‖fromL2 (halfOrder + 1) b n •
          fourier (T := anglePeriod) n‖) := by
        simpa only [norm_smul, fourier_norm, mul_one] using hs
      simpa [norm_smul, fourier_norm] using norm_tsum_le_tsum_norm hs'
    _ = _ :=
      (Real.sqrt_sq ((by positivity))).symm
    _ ≤ _ :=
      Real.sqrt_le_sqrt hsq
    _ = _ := by simp [*]

/-- Genuine bounded synthesis into continuous circle functions for normalized
order-3/2 data. This permits passing the stronger remainder series pointwise. -/
def vekuaStrongCircleReconstruction : L2Z →L[ℂ] C(ParamCircle, ℂ) :=
  vekuaStrongReconstructionLin.mkContinuous (Real.sqrt evalConst)
    vekuaStrongReconstructionLin_norm_le

theorem vekuaStrongCircleReconstruction_apply :
    vekuaStrongCircleReconstruction b =
      hardyCircleReconstruction (fromL2 (halfOrder + 1) b) := rfl

theorem vekuaStrongCircleReconstruction_sobVec
    (hc : IsSobolevSeq (halfOrder + 1) c) :
    vekuaStrongCircleReconstruction (sobVec (halfOrder + 1) c hc) =
      hardyCircleReconstruction c := by
  rw [vekuaStrongCircleReconstruction_apply, fromL2_sobVec]

private theorem vekua_raw_trace_smul {c : ℤ → ℂ}
    (hc : Summable (fun n => ‖c n‖)) (θ : ℝ) :
    hardyFourierTrace (a • c) θ = a * hardyFourierTrace c θ := by
  have hac : Summable (fun n => ‖(a • c) n‖) := by
    simpa only [Pi.smul_apply, smul_eq_mul, norm_mul] using hc.mul_left ‖a‖
  rw [← hardyCircleReconstruction_coe hac, vekua_reconstruction_smul,
    ContinuousMap.smul_apply, smul_eq_mul, hardyCircleReconstruction_coe hc]

theorem fromL2_half_localConformalDiskHalfTrace
    (hL : IsLipschitzDomain Φ.domain) (u : NeumannH1 Φ.domain) :
    fromL2 halfOrder (Φ.pulledBackHalfTrace hL u) =
      boundaryFourier (Φ.pulledBackTrace hL u) :=
  fromL2_half_diskHalfTrace (Φ.h1Pullback hL u)

end

section TraceCoordinates

section

variable (Φ : ConformalDiskMap) (j : ℕ) (u : NeumannH1 Φ.domain)

/-- The actual affine H¹ product has the actual centered coordinate trace. -/
theorem localConformalDiskH1Trace_affineMultiplier :
    Φ.pulledBackTrace Φ.lipschitzDomain (neumannH1AffineMultiplier Φ.bounded (Φ.map 1) u) =
      boundaryContinuousMultiplier Φ.centeredCircle
        (Φ.pulledBackTrace Φ.lipschitzDomain u) := by
  refine (denseRange_smoothTraceH1Lin Φ.bounded Φ.lipschitzDomain).induction_on
     u ?_ ?_
  · exact isClosed_eq ((Φ.pulledBackTrace Φ.lipschitzDomain).continuous.comp
      (neumannH1AffineMultiplier Φ.bounded (Φ.map 1)).continuous)
      ((boundaryContinuousMultiplier Φ.centeredCircle).continuous.comp
        (Φ.pulledBackTrace Φ.lipschitzDomain).continuous)
  · intro f
    change Φ.pulledBackTrace Φ.lipschitzDomain
      (neumannH1AffineMultiplier Φ.bounded (Φ.map 1) (smoothTraceH1 _ f)) = _
    rw [vekuaAffineMultiplier_smooth Φ.bounded Φ.lipschitzDomain.1.1]
    apply Lp.ext
    filter_upwards [localConformalDiskH1Trace_smooth_ae Φ (vekuaAffineTraceTest (Φ.map 1) f),
      boundaryContinuousMultiplier_ae Φ.centeredCircle
        (Φ.pulledBackTrace Φ.lipschitzDomain (smoothTraceH1 _ f)),
      localConformalDiskH1Trace_smooth_ae Φ f]
      with θ hp hm hf
    change Φ.pulledBackTrace Φ.lipschitzDomain
      (smoothTraceH1 _ (vekuaAffineTraceTest (Φ.map 1) f)) θ =
        boundaryContinuousMultiplier Φ.centeredCircle
          (Φ.pulledBackTrace Φ.lipschitzDomain (smoothTraceH1 _ f)) θ
    rw [hp, hm, hf, localConformalCenteredCircle_apply]
    rfl

theorem localConformalDiskH1Trace_affineMultiplier_pow :
    Φ.pulledBackTrace Φ.lipschitzDomain (((neumannH1AffineMultiplier Φ.bounded (Φ.map 1)) ^ j) u) =
      boundaryContinuousMultiplier (Φ.centeredCircle ^ j)
        (Φ.pulledBackTrace Φ.lipschitzDomain u) := by
  have hp : Φ.pulledBackTrace Φ.lipschitzDomain
      (((neumannH1AffineMultiplier Φ.bounded (Φ.map 1)) ^ j) u) =
      ((boundaryContinuousMultiplier Φ.centeredCircle) ^ j)
        (Φ.pulledBackTrace Φ.lipschitzDomain u) := by
    induction j with
    | zero => rfl
    | succ j ih =>
      rw [pow_succ', ContinuousLinearMap.mul_apply,
        localConformalDiskH1Trace_affineMultiplier Φ, ih,
        pow_succ', ContinuousLinearMap.mul_apply]
  rw [hp, vekua_boundaryMultiplier_pow]

/-- Every affine power, including the zero power, has the genuine normalized
Fourier multiplier represented by its averaged convolution power. -/
theorem localConformalDiskHalfTrace_affineMultiplier_pow :
    Φ.pulledBackHalfTrace Φ.lipschitzDomain
        (((neumannH1AffineMultiplier Φ.bounded (Φ.map 1)) ^ j) u) =
      normalizedHardyMultiplier
        (seqConvPow (fourierCoeff Φ.centeredCircle) j)
        (wl1Norm_seqConvPow_le (by norm_num)
          (localConformalCenteredCircle_isWL1_half Φ) j).1
        (Φ.pulledBackHalfTrace Φ.lipschitzDomain u) := by
  apply vekua_fromL2_injective halfOrder
  funext n
  rw [fromL2_half_localConformalDiskHalfTrace,
    localConformalDiskH1Trace_affineMultiplier_pow Φ,
    boundaryFourier_continuousMultiplier,
    vekua_fromL2_multiplier, fromL2_half_localConformalDiskHalfTrace]
  · rw [vekua_circle_coeff_pow _
      (vekua_summable_coeff (by norm_num)
        (localConformalCenteredCircle_isWL1_half Φ))]
  · rw [vekua_circle_coeff_pow _
      (vekua_summable_coeff (by norm_num)
        (localConformalCenteredCircle_isWL1_half Φ))]
    exact vekua_summable_coeff (by norm_num)
      (wl1Norm_seqConvPow_le (by norm_num)
        (localConformalCenteredCircle_isWL1_half Φ) j).1

end

end TraceCoordinates

section

variable (Φ : SmoothDiskMap) (j : ℕ) (hhol : DifferentiableOn ℂ Φ.map unitDisk) (b : L2Z)
    (hbn : IsNonpositiveFourierSupport b)

/-- The normalized primitive powers have exactly the original averaged
Fourier primitive powers, including their prescribed constant coefficients. -/
theorem fromL2_localConformalHardyPrimitive_pow :
    fromL2 halfOrder ((Φ.hardyPrimitive ^ j) b) =
      antiPrimIter (localConformalHardyPrimitiveMultiplier Φ.map) j (fromL2 halfOrder b) := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [pow_succ', ContinuousLinearMap.mul_apply]
    change fromL2 halfOrder (normalizedHardyPrimitive _ _ _) = _
    rw [fromL2_normalizedHardyPrimitive, ih]
    exact (Function.iterate_succ_apply' _ _ _).symm

theorem normalizedHardyAverage_localConformalHardyPrimitive_pow :
    normalizedHardyAverage ((Φ.hardyPrimitive ^ j) b) =
      antiPrimIter (localConformalHardyPrimitiveMultiplier Φ.map) j (normalizedHardyAverage b) := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [pow_succ', ContinuousLinearMap.mul_apply]
    change normalizedHardyAverage (normalizedHardyPrimitive _ _ _) = _
    rw [normalizedHardyAverage_primitive, ih]
    exact (Function.iterate_succ_apply' _ _ _).symm

/-- The genuine continuous angular velocity multiplier, reconstructed from
its absolutely summable averaged coefficients. -/
def localConformalPrimitiveCircle (F : ℂ → ℂ) : C(ParamCircle, ℂ) :=
  hardyCircleReconstruction (localConformalHardyPrimitiveMultiplier F)

theorem localConformalPrimitiveCircle_coeff :
    fourierCoeff (localConformalPrimitiveCircle Φ.map) = localConformalHardyPrimitiveMultiplier Φ.map :=
  hardyCircleReconstruction_fourierCoeff (summable_norm_of_isWL1_one
    (physicalCircleTrace_fourier_weights_of_smooth_neighborhood Φ).1)

theorem localConformalPrimitiveCircle_apply (θ : ℝ) :
    localConformalPrimitiveCircle Φ.map (θ : ParamCircle) =
      conj (deriv Φ.boundary θ) := by
  have ha : Summable (fun n => ‖localConformalHardyPrimitiveMultiplier Φ.map n‖) :=
    summable_norm_of_isWL1_one
      (physicalCircleTrace_fourier_weights_of_smooth_neighborhood Φ).1
  change hardyCircleReconstruction (localConformalHardyPrimitiveMultiplier Φ.map)
    (θ : ParamCircle) = _
  rw [hardyCircleReconstruction_coe ha]
  exact hardyFourierTrace_physical_conj_deriv_of_neighborhood Φ.one_lt_radius Φ.map
    (Φ.smooth.of_le (show (4 : WithTop ℕ∞) ≤ (⊤ : ℕ∞) from
      WithTop.coe_le_coe.mpr le_top)) θ

include hbn hhol in
/-- Actual normalized primitive powers are actual physical interval primitive
powers, with their basepoint at angular origin zero. -/
theorem localConformalHardyPrimitive_pow_volterra_of_H1
    (hb1 : IsSobolevSeq 1 (normalizedHardyAverage b)) (j : ℕ) (θ : ℝ) :
    hardyFourierTrace (normalizedHardyAverage
      ((Φ.hardyPrimitive ^ j) b)) θ =
      volterraPrimitiveIterate (fun s => conj (deriv Φ.boundary s))
        (hardyFourierTrace (normalizedHardyAverage b)) j θ := by
  have ha : IsWL1 1 (fourierCoeff (localConformalPrimitiveCircle Φ.map)) := by
    rw [localConformalPrimitiveCircle_coeff Φ]
    exact (physicalCircleTrace_fourier_weights_of_smooth_neighborhood Φ).1
  have han : IsStrictNegativeFourierSupport (fourierCoeff (localConformalPrimitiveCircle Φ.map)) := by
    rw [localConformalPrimitiveCircle_coeff Φ]
    exact localConformalHardyPrimitiveMultiplier_strictNegative Φ hhol
  have hbn' : IsNonpositiveFourierSupport (normalizedHardyAverage b) := by
    intro n hn
    simp [normalizedHardyAverage, fromL2, hbn n hn]
  rw [normalizedHardyAverage_localConformalHardyPrimitive_pow,
    ← localConformalPrimitiveCircle_coeff Φ,
    hardyFourierTrace_antiPrimIter_eq_volterraPrimitiveIterate
      (localConformalPrimitiveCircle Φ.map) ha hb1 han hbn']
  have he  :=
    funext (localConformalPrimitiveCircle_apply Φ)
  rw [he]

include hbn hhol in
private theorem vekua_trace_term_volterra
    (hb1 : IsSobolevSeq 1 (fromL2 halfOrder b)) (j : ℕ) (θ : ℝ) :
    hardyFourierTrace
      (vekuaBdryTerm (fourierCoeff Φ.centeredCircle)
        (localConformalHardyPrimitiveMultiplier Φ.map) (fromL2 halfOrder b) j) θ =
      (Φ.map (unitCirclePt θ) - Φ.map 1) ^ j *
        volterraPrimitiveIterate (fun s => conj (deriv Φ.boundary s))
          (hardyFourierTrace (fromL2 halfOrder b)) j θ := by
  let A := localConformalPrimitiveCircle Φ.map
  let G := Φ.centeredCircle
  let h := fromL2 halfOrder b
  have ha  :=
    (physicalCircleTrace_fourier_weights_of_smooth_neighborhood Φ).1
  have hs : Summable (fun n => ‖antiPrimIter (localConformalHardyPrimitiveMultiplier Φ.map) j h n‖) :=
    summable_norm_antiPrimIter_of_H1 ha hb1 j
  let H := hardyCircleReconstruction (antiPrimIter (localConformalHardyPrimitiveMultiplier Φ.map) j h)
  have hH  :=
    hardyCircleReconstruction_fourierCoeff hs
  have hg  :=
    localConformalCenteredCircle_isWL1_half Φ
  have hGp  :=
    vekua_circle_coeff_pow G (vekua_summable_coeff (by norm_num) hg) j
  
  let P := (G ^ j) * H
  
  have hP : fourierCoeff P = vekuaBdryTerm (fourierCoeff G)
      (localConformalHardyPrimitiveMultiplier Φ.map) h j := by
    change fourierCoeff (fun q => (G ^ j) q * H q) = _
    rw [fourierCoeff_mul_eq_seqConv (G ^ j) (by
      rw [hGp]
      exact vekua_summable_coeff (by norm_num) (wl1Norm_seqConvPow_le (by norm_num) hg j).1) (H.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)), hGp, (hardyCircleReconstruction_fourierCoeff hs)]
    rfl
  have hPabs : Summable (fun n => ‖fourierCoeff P n‖) := by
    rw [hP]
    have hg0 := vekua_isWL1_mono (by positivity)
      (wl1Norm_seqConvPow_le (by norm_num) hg j).1
    have hi0 : IsWL1 0 (antiPrimIter (localConformalHardyPrimitiveMultiplier Φ.map) j h) := by
      simpa only [IsWL1, Real.rpow_zero, one_mul] using hs
    simpa [vekuaBdryTerm, IsWL1, Real.rpow_zero] using (wl1Norm_seqConv_le (by norm_num : (0 : ℝ) ≤ 0) hg0 hi0).2.1
  have hbnp : IsNonpositiveFourierSupport h := by
    intro n hn
    simp [h, fromL2, hbn n hn]
  have hAn : IsStrictNegativeFourierSupport (fourierCoeff A) := by
    rw [localConformalPrimitiveCircle_coeff Φ]
    exact localConformalHardyPrimitiveMultiplier_strictNegative Φ hhol
  have hAw : IsWL1 1 (fourierCoeff A) := by
    rw [localConformalPrimitiveCircle_coeff Φ]
    exact ha
  have hJ := hardyFourierTrace_antiPrimIter_eq_volterraPrimitiveIterate A hAw hb1 hAn hbnp j θ
  rw [localConformalPrimitiveCircle_coeff Φ] at hJ
  have hAv  :=
    funext (localConformalPrimitiveCircle_apply Φ)
  rw [hAv] at hJ
  calc
    _ = P θ := by
      rw [← hP]
      exact hardyFourierTrace_fourierCoeff P hPabs θ
    _ = (Φ.map (unitCirclePt θ) - Φ.map 1) ^ j *
        hardyFourierTrace (antiPrimIter (localConformalHardyPrimitiveMultiplier Φ.map) j h) θ := by
      change (G (θ : ParamCircle)) ^ j * H (θ : ParamCircle) = _
      rw [localConformalCenteredCircle_apply, hardyCircleReconstruction_coe hs]
    _ = _ := by rw [hJ]

end

section PhysicalCoordinates

section

variable (Φ : DiskCoordinates) (E : ℂ) (b : L2Z) (hbn : IsNonpositiveFourierSupport b)

include hbn in
/-- The normalized Fourier coefficient of each actual H¹ series term is
precisely the original boundary transmutation term. -/
theorem localConformalVekuaTrace_term (j : ℕ) (n : ℤ) :
    Φ.pulledBackHalfTrace Φ.lipschitzDomain
      (((neumannH1AffineMultiplier Φ.bounded (Φ.map 1)) ^ j)
        (Φ.hardyH1Extension ((Φ.hardyPrimitive ^ j) b))) n =
      ((sobWeight n ^ halfOrder : ℝ) : ℂ) *
        vekuaBdryTerm (fourierCoeff Φ.centeredCircle)
          (localConformalHardyPrimitiveMultiplier Φ.map) (fromL2 halfOrder b) j n := by
  rw [localConformalDiskHalfTrace_affineMultiplier_pow Φ,
    localConformalDiskHalfTrace_hardyExtension_eq_of_nonpositive Φ _
      (localConformalHardyPrimitive_pow_nonpositive Φ Φ.holomorphic b hbn j),
    normalizedHardyMultiplier_apply, fromL2_localConformalHardyPrimitive_pow]
  rfl

/-- Actual normalized boundary term, constructed as a bounded map. -/
def SmoothDiskMap.vekuaBoundaryTerm (Φ : SmoothDiskMap) (E : ℂ) (j : ℕ) : FourierOp :=
  physicalVekuaCoeff E j •
    ((normalizedHardyMultiplier
      (seqConvPow (fourierCoeff Φ.centeredCircle) j)
      (wl1Norm_seqConvPow_le (by norm_num)
        (localConformalCenteredCircle_isWL1_half Φ) j).1).comp
      (Φ.hardyPrimitive ^ j))

theorem localConformalVekuaBoundaryTerm_apply (Φ : SmoothDiskMap) (E : ℂ) (j : ℕ)
    (b : L2Z) (n : ℤ) :
    Φ.vekuaBoundaryTerm E j b n =
      physicalVekuaCoeff E j * ((sobWeight n ^ halfOrder : ℝ) : ℂ) *
        vekuaBdryTerm (fourierCoeff Φ.centeredCircle)
          (localConformalHardyPrimitiveMultiplier Φ.map) (fromL2 halfOrder b) j n := by
  let c := seqConvPow (fourierCoeff Φ.centeredCircle) j
  have hc  :=
    (wl1Norm_seqConvPow_le (by norm_num)
      (localConformalCenteredCircle_isWL1_half Φ) j).1
  change (physicalVekuaCoeff E j • normalizedHardyMultiplier c hc
    ((Φ.hardyPrimitive ^ j) b)) n = _
  rw [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, normalizedHardyMultiplier_apply,
    fromL2_localConformalHardyPrimitive_pow]
  change physicalVekuaCoeff E j *
    (((sobWeight n ^ halfOrder : ℝ) : ℂ) * vekuaBdryTerm _ _ _ j n) = _
  ring

include E Φ in
/-- The boundary operator is the trace of the genuine convergent H¹ series. -/
def DiskCoordinates.vekuaBoundary : FourierOp :=
  (Φ.pulledBackHalfTrace Φ.lipschitzDomain).comp
    (Φ.vekuaH1AtBoundaryOrigin E)

include hbn in
theorem localConformalVekuaBoundary_hasSum :
    HasSum (fun j : ℕ => Φ.vekuaBoundaryTerm E j b)
      (Φ.vekuaBoundary E b) := by
  have ht (j : ℕ) :
      physicalVekuaCoeff E j • Φ.pulledBackHalfTrace Φ.lipschitzDomain
        (((neumannH1AffineMultiplier Φ.bounded (Φ.map 1)) ^ j)
          (Φ.hardyH1Extension ((Φ.hardyPrimitive ^ j) b))) =
        Φ.vekuaBoundaryTerm E j b := by
    ext n
    simp only [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]
    rw [localConformalVekuaTrace_term Φ b hbn,
      localConformalVekuaBoundaryTerm_apply]
    ring
  simpa only [ht, DiskCoordinates.vekuaBoundary, ContinuousLinearMap.comp_apply,
    DiskCoordinates.vekuaH1AtBoundaryOrigin] using
    localConformalVekuaH1_halfTrace_hasSum Φ (Φ.map 1) E b

include hbn in
theorem localConformalVekuaBoundaryTerm_zero :
    Φ.vekuaBoundaryTerm E 0 b = b := by
  have ht := localConformalVekuaTrace_term Φ b hbn 0
  ext n
  rw [localConformalVekuaBoundaryTerm_apply, physicalVekuaCoeff_zero, one_mul, ← ht]
  simp only [pow_zero, ContinuousLinearMap.one_apply]
  rw [localConformalDiskHalfTrace_hardyExtension_eq_of_nonpositive Φ b hbn]

private theorem vekua_smoothing_strong_term (Φ : SmoothDiskMap) (E : ℂ) (b : L2Z)
    (j : ℕ)
    (ht : IsSobolevSeq (halfOrder + 1)
      (vekuaBdryTerm (fourierCoeff Φ.centeredCircle)
        (localConformalHardyPrimitiveMultiplier Φ.map) (fromL2 halfOrder b) (j + 1))) :
    sobolevSmoothing 1 (by norm_num)
      (physicalVekuaCoeff E (j + 1) • sobVec (halfOrder + 1) _ ht) =
      Φ.vekuaBoundaryTerm E (j + 1) b := by
  ext n
  simp only [map_smul, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul,
    sobolevSmoothing, diagOp_apply, sobVec_apply, localConformalVekuaBoundaryTerm_apply]
  have he : -(1 : ℝ) + (halfOrder + 1) = 1 / 2 := by ring
  have hw : ((sobWeight n ^ (-(1 : ℝ)) : ℝ) : ℂ) *
      ((sobWeight n ^ (halfOrder + 1) : ℝ) : ℂ) =
      ((sobWeight n ^ halfOrder : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul, ← Real.rpow_add (sobWeight_pos n), he]
  grind

include hbn in
/-- The true normalized boundary remainder factors through one-order smoothing.
The stronger vector is constructed from the proved Fourier term bounds. -/
theorem localConformalVekuaBoundary_strong_remainder_hasSum :
    ∃ (hT : ∀ j : ℕ, IsSobolevSeq (halfOrder + 1)
          (vekuaBdryTerm (fourierCoeff Φ.centeredCircle)
            (localConformalHardyPrimitiveMultiplier Φ.map) (fromL2 halfOrder b) (j + 1)))
      (r : L2Z),
      HasSum (fun j : ℕ => physicalVekuaCoeff E (j + 1) •
        sobVec (halfOrder + 1) _ (hT j)) r ∧
      Φ.vekuaBoundary E b - b =
        sobolevSmoothing 1 (by norm_num) r := by
  obtain ⟨hT, hN, -⟩ := vekuaBdry_sub_one_bound (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (localConformalCenteredCircle_isWL1_threeHalves Φ)
    (localConformalHardyPrimitiveMultiplier_isWL1 Φ)
    (isSobolevSeq_fromL2 halfOrder b) E
  let f  := fun j => physicalVekuaCoeff E (j + 1) •
    sobVec (halfOrder + 1) _ (hT j)
  have hs := (show Summable (fun j => ‖f j‖) from hN).of_norm.hasSum
  have hmap := (sobolevSmoothing 1 (by norm_num)).hasSum hs
  have hm : HasSum (fun j : ℕ => Φ.vekuaBoundaryTerm E (j + 1) b)
      (sobolevSmoothing 1 (by norm_num) (∑' j : ℕ, f j)) := by
    simpa only [f, vekua_smoothing_strong_term] using hmap
  have ht := (hasSum_nat_add_iff'
     1).2
      (localConformalVekuaBoundary_hasSum Φ E b hbn)
  simp only [Finset.sum_range_one,
    localConformalVekuaBoundaryTerm_zero Φ E b hbn] at ht
  exact ⟨hT, ∑' j : ℕ, f j, hs, ht.unique hm⟩

include hbn in
/-- The actual boundary remainder is in the range of one-order smoothing. -/
theorem localConformalVekuaBoundary_sub_gain :
    ∃ r : L2Z,
      Φ.vekuaBoundary E b - b =
        sobolevSmoothing 1 (by norm_num) r := by
  obtain ⟨hT, r, hs, hr⟩ := localConformalVekuaBoundary_strong_remainder_hasSum Φ E b hbn
  exact ⟨r, hr⟩

include hbn in
/-- Zero actual trace forces one full order of gain on the original input. -/
theorem localConformalVekuaBoundary_kernel_smoothing (hz : Φ.vekuaBoundary E b = 0) :
    ∃ r : L2Z, b = sobolevSmoothing 1 (by norm_num) r := by
  obtain ⟨r, hr⟩ := localConformalVekuaBoundary_sub_gain Φ E b hbn
  rw [hz, zero_sub] at hr
  refine ⟨-r, ?_⟩
  rw [map_neg, ← hr, neg_neg]

end

end PhysicalCoordinates

theorem fromL2_half_smoothing_one (b : L2Z) :
    fromL2 halfOrder (sobolevSmoothing 1 (by norm_num) b) =
      fromL2 (halfOrder + 1) b := by
  funext n
  simp only [fromL2, sobolevSmoothing, diagOp_apply]
  rw [← mul_assoc, ← Complex.ofReal_mul, ← Real.rpow_add (sobWeight_pos n)]
  ring

section RegularVolterraTrace

section

variable (Φ : DiskCoordinates) (E : ℂ) (b : L2Z) (hbn : IsNonpositiveFourierSupport b)
    (hb1 : IsSobolevSeq 1 (fromL2 halfOrder b))
include hb1 hbn

/-- The genuine Vekua coordinate trace preserves order-one regularity of
its original raw coefficients, using the proved stronger remainder. -/
theorem localConformalVekuaBoundary_raw_H1 :
    IsSobolevSeq 1 (fromL2 halfOrder (Φ.vekuaBoundary E b)) := by
  obtain ⟨r, hr⟩ := localConformalVekuaBoundary_sub_gain Φ E b hbn
  have heq : Φ.vekuaBoundary E b = b + sobolevSmoothing 1 (by norm_num) r := by
    rw [sub_eq_iff_eq_add] at hr
    exact hr.trans (add_comm _ _)
  rw [heq, fromL2_add, fromL2_half_smoothing_one]
  exact isSobolevSeq_add hb1
    (sobNormSq_mono (by norm_num)
      (isSobolevSeq_fromL2 (halfOrder + 1) r)).1

/-- For every actual order-one Hardy input the physical boundary series
converges pointwise to the Fourier reconstruction of its actual trace. -/
theorem localConformalVekuaBoundary_volterra_hasSum_of_H1
    (θ : ℝ) :
    HasSum (fun j : ℕ => physicalVekuaCoeff E j *
      (Φ.map (unitCirclePt θ) - Φ.map 1) ^ j *
      volterraPrimitiveIterate (fun s => conj (deriv Φ.boundary s))
        (hardyFourierTrace (fromL2 halfOrder b)) j θ)
      (hardyFourierTrace (fromL2 halfOrder (Φ.vekuaBoundary E b)) θ) := by
  obtain ⟨hT, r, hs, hr⟩ := localConformalVekuaBoundary_strong_remainder_hasSum
    Φ E b hbn
  have heq : Φ.vekuaBoundary E b = b + sobolevSmoothing 1 (by norm_num) r := by
    rw [sub_eq_iff_eq_add] at hr
    exact hr.trans (add_comm _ _)
  have hseq : fromL2 halfOrder (Φ.vekuaBoundary E b) =
      fromL2 halfOrder b + fromL2 (halfOrder + 1) r := by
    rw [heq, fromL2_add, fromL2_half_smoothing_one]
  have hr1  :=
    (sobNormSq_mono (by norm_num : (1 : ℝ) ≤ halfOrder + 1)
      (isSobolevSeq_fromL2 (halfOrder + 1) r)).1
  have hbs : Summable (fun n => ‖fromL2 halfOrder b n‖) :=
    (sq_tsum_norm_le (s := 0) (by norm_num) (by simpa using hb1)).1
  have hrs : Summable (fun n => ‖fromL2 (halfOrder + 1) r n‖) :=
    (sq_tsum_norm_le (s := 0) (by norm_num) (by simpa using hr1)).1
  have hsum : Summable (fun n =>
      ‖(fromL2 halfOrder b + fromL2 (halfOrder + 1) r) n‖) :=
    (sq_tsum_norm_le (s := 0) (by norm_num)
      (by simpa using isSobolevSeq_add hb1 hr1)).1
  have hval : hardyFourierTrace (fromL2 halfOrder (Φ.vekuaBoundary E b)) θ =
      hardyFourierTrace (fromL2 halfOrder b) θ +
        vekuaStrongCircleReconstruction r (θ : ParamCircle) := by
    rw [hseq, ← hardyCircleReconstruction_coe hsum,
      vekua_reconstruction_add hbs hrs]
    simp only [ContinuousMap.add_apply, hardyCircleReconstruction_coe hbs,
      vekuaStrongCircleReconstruction_apply, hardyCircleReconstruction_coe hrs]
  have ht (j : ℕ) : vekuaStrongCircleReconstruction
      (physicalVekuaCoeff E (j + 1) • sobVec (halfOrder + 1) _ (hT j))
        (θ : ParamCircle) =
      physicalVekuaCoeff E (j + 1) * (Φ.map (unitCirclePt θ) - Φ.map 1) ^ (j + 1) *
        volterraPrimitiveIterate (fun s => conj (deriv Φ.boundary s))
          (hardyFourierTrace (fromL2 halfOrder b)) (j + 1) θ := by
    rw [map_smul, vekuaStrongCircleReconstruction_sobVec, ContinuousMap.smul_apply,
      smul_eq_mul, hardyCircleReconstruction_coe
        (sq_tsum_norm_le (by norm_num : (0 : ℝ) ≤ 1 / 2) (hT j)).1,
      vekua_trace_term_volterra Φ Φ.holomorphic b hbn hb1]
    ring
  have heval := (ContinuousMap.evalCLM ℂ (θ : ParamCircle)).hasSum
    (vekuaStrongCircleReconstruction.hasSum hs)
  change HasSum (fun j : ℕ => vekuaStrongCircleReconstruction
    (physicalVekuaCoeff E (j + 1) • sobVec (halfOrder + 1) _ (hT j))
      (θ : ParamCircle))
    (vekuaStrongCircleReconstruction r (θ : ParamCircle)) at heval
  have htail : HasSum (fun j : ℕ => physicalVekuaCoeff E (j + 1) *
      (Φ.map (unitCirclePt θ) - Φ.map 1) ^ (j + 1) *
      volterraPrimitiveIterate (fun s => conj (deriv Φ.boundary s))
        (hardyFourierTrace (fromL2 halfOrder b)) (j + 1) θ)
      (vekuaStrongCircleReconstruction r (θ : ParamCircle)) := by
    simpa only [ht] using heval
  apply (hasSum_nat_add_iff'  1).1
  simpa only [Finset.sum_range_one, physicalVekuaCoeff, pow_zero, Nat.factorial_zero,
    Nat.cast_one, div_one, one_mul, volterraPrimitiveIterate, hval,
    add_sub_cancel_left] using htail

end

end RegularVolterraTrace

private theorem vekua_volterra_shift (a h : ℝ → ℂ) (j : ℕ) :
    volterraPrimitiveIterate a (volterraPrimitiveIterate a h 1) j =
      volterraPrimitiveIterate a h (j + 1) := by
  induction j with
  | zero => rfl
  | succ j ih =>
    funext t
    change (∫ s in (0 : ℝ)..t,
      a s * volterraPrimitiveIterate a (volterraPrimitiveIterate a h 1) j s) = _
    rw [ih]
    rfl

private theorem vekua_volterra_next_bound
    (A : C(ParamCircle, ℂ)) {h : ℝ → ℂ} (hh : Continuous h)
    {T : ℝ} (j : ℕ) (t : ℝ) (ht : t ∈ Icc 0 T) :
    ‖volterraPrimitiveIterate (fun s => A (s : ParamCircle)) h (j + 1) t‖ ≤
      (‖A‖ * ∫ s in (0 : ℝ)..t, ‖h s‖) * (‖A‖ * T) ^ j / (j.factorial : ℝ) := by
  let a : ℝ → ℂ := fun s => A (s : ParamCircle)
  have ha  := A.continuous.comp (AddCircle.continuous_mk' _)
  have hi : 0 ≤ ∫ s in (0 : ℝ)..t, ‖h s‖ :=
    intervalIntegral.integral_nonneg ht.1 (fun s _ => norm_nonneg _)
  have hfirst (s : ℝ) (hs : s ∈ Icc 0 t) :
      ‖volterraPrimitiveIterate a h 1 s‖ ≤ ‖A‖ * ∫ x in (0 : ℝ)..t, ‖h x‖ := by
    change ‖∫ x in (0 : ℝ)..s, a x * h x‖ ≤ _
    calc
      _ ≤ ∫ x in (0 : ℝ)..s, ‖a x * h x‖ :=
        intervalIntegral.norm_integral_le_integral_norm hs.1
      _ ≤ ∫ x in (0 : ℝ)..s, ‖A‖ * ‖h x‖ := by
        refine intervalIntegral.integral_mono_on hs.1 ((ha.mul hh).norm.intervalIntegrable 0 s)
          ((continuous_const.mul hh.norm).intervalIntegrable 0 s) ?_
        intro x _
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_right (A.norm_coe_le_norm _) (norm_nonneg _)
      _ = ‖A‖ * ∫ x in (0 : ℝ)..s, ‖h x‖ := intervalIntegral.integral_const_mul _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left
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
    (A G : C(ParamCircle, ℂ)) (E : ℂ) {h : ℝ → ℂ} (hh : Continuous h)
    {T : ℝ} (hT : 0 ≤ T)
    (hsum : ∀ t ∈ Icc 0 T, HasSum (fun j : ℕ => physicalVekuaCoeff E (j + 1) *
      G (t : ParamCircle) ^ (j + 1) *
      volterraPrimitiveIterate (fun s => A (s : ParamCircle)) h (j + 1) t) (-h t)) :
    ∀ t ∈ Icc 0 T, h t = 0 := by
  let K := ‖-E / 4‖
  let B := ‖G‖
  let M := ‖A‖
  let x := K * B * M * T
  have hK : 0 ≤ K := norm_nonneg _
  have hB : 0 ≤ B := norm_nonneg _
  
  have hC : 0 ≤ K * B * M * Real.exp x := by positivity
  apply continuous_eq_zero_of_norm_le_volterra hh hC
  intro t ht
  let I := ∫ s in 0..t, ‖h s‖
  
  let f  := fun j => physicalVekuaCoeff E (j + 1) *
    G t ^ (j + 1) *
    volterraPrimitiveIterate (fun s => A s) h (j + 1) t
  have hmajor (j : ℕ) : ‖f j‖ ≤ (K * B * M * I) * (x ^ j / j.factorial) := by
    have hc : ‖physicalVekuaCoeff E (j + 1)‖ ≤ K ^ (j + 1) := by
      rw [norm_physicalVekuaCoeff]
      exact div_le_self (pow_nonneg hK _)
        (by exact_mod_cast Nat.one_le_of_lt ((by positivity)))
    have hg : ‖G t ^ (j + 1)‖ ≤ B ^ (j + 1) := by
      rw [norm_pow]
      exact pow_le_pow_left₀ (norm_nonneg _) (G.norm_coe_le_norm _) _
    have hj := vekua_volterra_next_bound A hh j t ht
    calc
      _ ≤ (K ^ (j + 1) * B ^ (j + 1)) * ((M * I) * (M * T) ^ j / j.factorial) := by
        simp only [f, norm_mul]
        gcongr
      _ = _ := by ring
  have hmaj : Summable (fun j : ℕ => (K * B * M * I) * (x ^ j / (j.factorial : ℝ))) :=
    (Real.summable_pow_div_factorial x).mul_left _
  have hn  :=
    Summable.of_nonneg_of_le ((by norm_num)) hmajor hmaj
  calc
    _ = ‖∑' j : ℕ, f j‖ := by rw [(hsum t ht).tsum_eq, norm_neg]
    _ ≤ _ := norm_tsum_le_tsum_norm hn
    _ ≤ _ :=
      Summable.tsum_le_tsum hmajor hn hmaj
    _ = _ := by
      rw [tsum_mul_left, Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div]
      ring

section KernelRegularity

section

variable (Φ : DiskCoordinates) (E : ℂ) (b : L2Z) (hbn : IsNonpositiveFourierSupport b)
    (hz : Φ.vekuaBoundary E b = 0)
include hbn

include hz in
theorem localConformalVekuaBoundary_kernel_raw_threeHalves :
    IsSobolevSeq (halfOrder + 1) (fromL2 halfOrder b) := by
  obtain ⟨r, hr⟩ := localConformalVekuaBoundary_kernel_smoothing Φ E b hbn hz
  rw [hr, fromL2_half_smoothing_one]
  exact isSobolevSeq_fromL2 _ r

include hz in
/-- Zero actual trace gives a genuine pointwise Volterra equation for the
original data. The raw orthonormal Fourier input is sqrt(2π) times its averaged
input, so this equality has the same constant scale in every term. -/
theorem localConformalVekuaBoundary_kernel_volterra_hasSum (θ : ℝ) :
    HasSum (fun j : ℕ => physicalVekuaCoeff E (j + 1) *
      (Φ.map (unitCirclePt θ) - Φ.map 1) ^ (j + 1) *
      volterraPrimitiveIterate (fun s => conj (deriv Φ.boundary s))
        (hardyFourierTrace (fromL2 halfOrder b)) (j + 1) θ)
      (-hardyFourierTrace (fromL2 halfOrder b) θ) := by
  obtain ⟨hT, r, hs, hr⟩ := localConformalVekuaBoundary_strong_remainder_hasSum Φ E b hbn
  rw [hz, zero_sub] at hr
  have hb3 := localConformalVekuaBoundary_kernel_raw_threeHalves Φ E b hbn hz
  have hb1 : IsSobolevSeq 1 (fromL2 halfOrder b) := (sobNormSq_mono (by norm_num) hb3).1
  have hbs  :=
    (sq_tsum_norm_le (by positivity) hb3).1
  have hrseq : fromL2 (halfOrder + 1) r = -fromL2 halfOrder b := calc
      _ = fromL2 halfOrder (sobolevSmoothing 1 (by norm_num) r) :=
        (fromL2_half_smoothing_one r).symm
      _ = fromL2 halfOrder (-b) := congrArg (fromL2 halfOrder) hr.symm
      _ = _ := by funext n; simp [fromL2]
  have ht (j : ℕ) :
      vekuaStrongCircleReconstruction
        (physicalVekuaCoeff E (j + 1) • sobVec (halfOrder + 1) _ (hT j))
          (θ : ParamCircle) =
      physicalVekuaCoeff E (j + 1) * (Φ.map (unitCirclePt θ) - Φ.map 1) ^ (j + 1) *
        volterraPrimitiveIterate (fun s => conj (deriv Φ.boundary s))
          (hardyFourierTrace (fromL2 halfOrder b)) (j + 1) θ := by
    rw [map_smul, vekuaStrongCircleReconstruction_sobVec, ContinuousMap.smul_apply,
      smul_eq_mul, hardyCircleReconstruction_coe
        (sq_tsum_norm_le (by norm_num : (0 : ℝ) ≤ 1 / 2) (hT j)).1,
      vekua_trace_term_volterra Φ Φ.holomorphic b hbn hb1]
    ring
  have hval : vekuaStrongCircleReconstruction r θ =
      -hardyFourierTrace (fromL2 halfOrder b) θ := by
    rw [vekuaStrongCircleReconstruction_apply, hardyCircleReconstruction_coe
      (sq_tsum_norm_le (by positivity) (isSobolevSeq_fromL2 _ r)).1,
      hrseq]
    have hn : -fromL2 halfOrder b = (-1 : ℂ) • fromL2 halfOrder b := by
      simp
    rw [hn, vekua_raw_trace_smul (-1) hbs]
    ring
  have heval := (ContinuousMap.evalCLM ℂ (θ : ParamCircle)).hasSum
    (vekuaStrongCircleReconstruction.hasSum hs)
  change HasSum (fun j : ℕ => vekuaStrongCircleReconstruction
    (physicalVekuaCoeff E (j + 1) • sobVec (halfOrder + 1) _ (hT j))
      (θ : ParamCircle))
    (vekuaStrongCircleReconstruction r (θ : ParamCircle)) at heval
  simpa only [ht, hval] using heval

include hz in
/-- The actual Vekua coordinate trace has no kernel on the full nonpositive
half-trace space. Regularity, the pointwise equation and the Volterra bound
are all derived from the actual zero trace. -/
theorem localConformalVekuaBoundary_eq_zero_imp :
    b = 0 := by
  have hb3 := localConformalVekuaBoundary_kernel_raw_threeHalves Φ E b hbn hz
  have hbs  :=
    (sq_tsum_norm_le (by norm_num : (0 : ℝ) ≤ 1 / 2) hb3).1
  have hh  := continuous_hardyFourierTrace hbs
  have hs : ∀ θ ∈ angleInterval, HasSum (fun j : ℕ =>
      physicalVekuaCoeff E (j + 1) *
        Φ.centeredCircle (θ : ParamCircle) ^ (j + 1) *
        volterraPrimitiveIterate
          (fun s => localConformalPrimitiveCircle Φ.map (s : ParamCircle))
          (hardyFourierTrace (fromL2 halfOrder b)) (j + 1) θ)
      (-hardyFourierTrace (fromL2 halfOrder b) θ) := by
    intro θ _
    simpa only [localConformalCenteredCircle_apply Φ,
      localConformalPrimitiveCircle_apply Φ] using
      localConformalVekuaBoundary_kernel_volterra_hasSum Φ E b hbn hz θ
  have hzero := vekua_volterra_kernel_unique (localConformalPrimitiveCircle Φ.map)
    Φ.centeredCircle E hh Real.two_pi_pos.le hs
  have hcoeff : fromL2 halfOrder b = 0 := by
    funext n
    change fromL2 halfOrder b n = (0 : ℂ)
    have hc := congrFun (hardyCircleReconstruction_fourierCoeff hbs) n
    rw [← hc, fourierCoeff_eq_intervalIntegral _ n 0, zero_add]
    have hi : (∫ₚ θ,
        fourier  (-n) (θ : ParamCircle) •
          hardyCircleReconstruction (fromL2 halfOrder b)
            (θ : ParamCircle)) = 0 := by
      calc
        _ = ∫ₚ θ, (0 : ℂ) := by
          apply intervalIntegral.integral_congr
          intro θ hθ
          rw [uIcc_of_le Real.two_pi_pos.le] at hθ
          change fourier (T := anglePeriod) (-n) (θ : ParamCircle) •
            hardyCircleReconstruction (fromL2 halfOrder b)
              (θ : ParamCircle) = (0 : ℂ)
          rw [hardyCircleReconstruction_coe hbs, hzero θ hθ, smul_zero]
        _ = 0 := by simp
    rw [hi, smul_zero]
  apply vekua_fromL2_injective halfOrder
  rw [hcoeff]
  funext n
  simp [fromL2]

/-- The same actual uniqueness conclusion stated directly for the ordinary
coordinate trace of the physical H¹ vector. -/
theorem localConformalVekuaH1_eq_zero_input_of_coordinate_trace_zero
    (ht : Φ.pulledBackTrace Φ.lipschitzDomain
      (Φ.vekuaH1AtBoundaryOrigin E b) = 0) :
    b = 0 := by
  apply localConformalVekuaBoundary_eq_zero_imp Φ E b hbn
  apply vekua_fromL2_injective halfOrder
  change fromL2 halfOrder (Φ.pulledBackHalfTrace Φ.lipschitzDomain
    (Φ.vekuaH1AtBoundaryOrigin E b)) =
      fromL2 halfOrder 0
  rw [fromL2_half_localConformalDiskHalfTrace, ht, map_zero]
  funext n
  simp [fromL2]

end

end KernelRegularity

end PolyaNeumann

end
