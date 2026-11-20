module

public import RequestProject.CircleAnalysisNotation

public import RequestProject.DiskCoordinates

public import RequestProject.PhysicalDrivenKernelRealization
public import RequestProject.PhysicalDrivenRowsReconstruction
public import RequestProject.LocalConformalVekuaConormalBridge
public import RequestProject.PlanarNotation

/-!
# The genuine coordinate load of an observation-kernel vector

The angular variable is the conformal circle parameter, with its actual
variable velocity. Each positive Vekua term has a genuine Volterra
derivative. Fourier integration by parts and the convergent actual H¹
trace series identify the coordinate conormal, including frequency zero.
The exceptional actual driven row then identifies this load with the
original L² forcing. No boundary-parametrization assertion for the
variable-speed curve, or presumed conormal identity, is used.

The supplied conformal coordinates and their arclength reparametrization remain separate.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open scoped ContDiff

namespace PolyaNeumann

open MeasureTheory Set Metric Filter
open scoped Topology ComplexConjugate InnerProductSpace

private def kernel_conormal_eval (n : ℤ) : BoundaryL2 →L[ℂ] ℂ :=
  (innerSL ℂ (stdBasisZ n)).comp boundaryFourier.toLinearIsometry.toContinuousLinearMap

private theorem kernel_conormal_eval_apply (n : ℤ) (v : BoundaryL2) :
    kernel_conormal_eval n v = boundaryFourier v n := hardy_inner_stdBasisZ n (boundaryFourier v)

theorem kernel_conormal_coeff_ae {f : ℝ → ℂ} (v : BoundaryL2)
    (hv : (v : ℝ → ℂ) =ᵐ[angleMeasure] f) (n : ℤ) :
    boundaryFourier v n = fourierScale *
      angleCoeff f n := by
  rw [boundaryFourier_apply, fourierCoeffOn_congr_ae Real.two_pi_pos hv]

section CoordinateTerms

section

variable (Φ : SmoothDiskMap) (b : L2Z) (hb1 : IsSobolevSeq 1 (fromL2 halfOrder b)) (j : ℕ)
include hb1

private theorem kernel_conormal_primitive_H1 :
    IsSobolevSeq 1 (normalizedHardyAverage ((Φ.hardyPrimitive ^ j) b)) := by
  rw [normalizedHardyAverage_localConformalHardyPrimitive_pow]
  exact (antiPrimIter_bound (by norm_num : (0 : ℝ) ≤ 1)
    (physicalCircleTrace_fourier_weights_of_smooth_neighborhood Φ).1
    (isSobolevSeq_smul _ hb1) j).1

theorem kernel_conormal_primitive_raw_H1 :
    IsSobolevSeq 1 (fromL2 halfOrder ((Φ.hardyPrimitive ^ j) b)) := by
  rw [fromL2_localConformalHardyPrimitive_pow]
  exact (antiPrimIter_bound (by norm_num : (0 : ℝ) ≤ 1)
    (physicalCircleTrace_fourier_weights_of_smooth_neighborhood Φ).1 hb1 j).1

end

section

variable (Φ : DiskCoordinates) (E : ℂ) (b : L2Z) (hbn : IsNonpositiveFourierSupport b)
    (hb1 : IsSobolevSeq 1 (fromL2 halfOrder b)) (j : ℕ) (n : ℤ)

include hb1 hbn in
/-- The actual ordinary coordinate trace agrees a.e. with its genuine
order-one averaged Fourier reconstruction, for every such Hardy input. -/
theorem localConformalVekua_coordinate_trace_reconstruction_ae :
    ((Φ.pulledBackTrace Φ.lipschitzDomain) (Φ.vekuaH1 (Φ.map 1) E b) : ℝ → ℂ)
      =ᵐ[angleMeasure]
        hardyFourierTrace (normalizedHardyAverage
          (Φ.vekuaBoundary E b)) := by
  have hreg := localConformalVekuaBoundary_raw_H1 Φ E b hbn hb1
  have hcoef := normalizedHardyAverage_localConformalDiskHalfTrace Φ Φ.lipschitzDomain
    (Φ.vekuaH1 (Φ.map 1) E b)
  change normalizedHardyAverage
      (Φ.vekuaBoundary E b) = angleCoeff ((Φ.pulledBackTrace Φ.lipschitzDomain) (Φ.vekuaH1 (Φ.map 1) E b)) at hcoef
  have ht := boundaryL2_ae_hardyFourierTrace_of_H1 ((Φ.pulledBackTrace Φ.lipschitzDomain) (Φ.vekuaH1 (Φ.map 1) E b))
    (by rw [← hcoef]; exact isSobolevSeq_smul _ hreg)
  rwa [← hcoef] at ht

include hb1 hbn in
/-- Actual ordinary trace representatives for independent affine and
primitive powers. The constant primitive coefficient is retained. -/
theorem localConformalHardy_affine_primitive_trace_ae (k : ℕ) :
    ((Φ.pulledBackTrace Φ.lipschitzDomain) (((neumannH1AffineMultiplier Φ.bounded (Φ.map 1)) ^ j) (Φ.hardyH1Extension ((Φ.hardyPrimitive ^ k) b))) : ℝ → ℂ)
      =ᵐ[angleMeasure]
        fun θ => (Φ.boundary θ - Φ.map 1) ^ j *
          hardyFourierTrace (normalizedHardyAverage ((Φ.hardyPrimitive ^ k) b)) θ := by
  have hnk := localConformalHardyPrimitive_pow_nonpositive Φ Φ.holomorphic b hbn k
  have hc : normalizedHardyAverage ((Φ.pulledBackHalfTrace Φ.lipschitzDomain) (Φ.hardyH1Extension ((Φ.hardyPrimitive ^ k) b))) =
      normalizedHardyAverage ((Φ.hardyPrimitive ^ k) b) := by
    rw [localConformalDiskHalfTrace_hardyExtension_eq_of_nonpositive Φ _ hnk]
  have hcoef := normalizedHardyAverage_localConformalDiskHalfTrace Φ Φ.lipschitzDomain
    (Φ.hardyH1Extension ((Φ.hardyPrimitive ^ k) b))
  rw [hc] at hcoef
  have hu := boundaryL2_ae_hardyFourierTrace_of_H1 ((Φ.pulledBackTrace Φ.lipschitzDomain) (Φ.hardyH1Extension ((Φ.hardyPrimitive ^ k) b)))
    (by rw [← hcoef]; exact kernel_conormal_primitive_H1 Φ b hb1 k)
  rw [← hcoef] at hu
  rw [localConformalDiskH1Trace_affineMultiplier_pow Φ]
  filter_upwards [hu, boundaryContinuousMultiplier_ae
    (Φ.centeredCircle ^ j) ((Φ.pulledBackTrace Φ.lipschitzDomain) (Φ.hardyH1Extension ((Φ.hardyPrimitive ^ k) b)))]
    with θ hu hm
  rw [hm, hu]
  simp [ContinuousMap.pow_apply, localConformalCenteredCircle_apply, physicalCircleTrace]

theorem kernel_conormal_primitive_deriv (Φ : SmoothDiskMap)
    (hhol : DifferentiableOn ℂ Φ.map unitDisk) (b : L2Z) (hbn : IsNonpositiveFourierSupport b)
    (hb1 : IsSobolevSeq 1 (fromL2 halfOrder b)) (j : ℕ) (θ : ℝ) :
    HasDerivAt (hardyFourierTrace (normalizedHardyAverage ((Φ.hardyPrimitive ^ (j + 1)) b)))
      (conj (deriv Φ.boundary θ) *
        hardyFourierTrace (normalizedHardyAverage ((Φ.hardyPrimitive ^ j) b)) θ) θ := by
  letI : Fact (0 < anglePeriod) := ⟨Real.two_pi_pos⟩
  have hnorm : IsSobolevSeq 1 (normalizedHardyAverage b) := by
    exact isSobolevSeq_smul fourierScale⁻¹ hb1
  have hbn' : IsNonpositiveFourierSupport (normalizedHardyAverage b) := by
    intro n hn
    simp [normalizedHardyAverage, fromL2, hbn n hn]
  have hA : IsWL1 1 (fourierCoeff (localConformalPrimitiveCircle Φ.map)) := by
    rw [localConformalPrimitiveCircle_coeff Φ]
    exact (physicalCircleTrace_fourier_weights_of_smooth_neighborhood Φ).1
  have hAn : IsStrictNegativeFourierSupport
      (fourierCoeff (localConformalPrimitiveCircle Φ.map)) := by
    rw [localConformalPrimitiveCircle_coeff Φ]
    exact localConformalHardyPrimitiveMultiplier_strictNegative Φ hhol
  have hder := hasDerivAt_hardyFourierTrace_antiPrimIter_succ
    (localConformalPrimitiveCircle Φ.map) hA hnorm hAn hbn' j θ
  rw [localConformalPrimitiveCircle_coeff Φ] at hder
  rw [← normalizedHardyAverage_localConformalHardyPrimitive_pow Φ (j + 1) b,
    ← normalizedHardyAverage_localConformalHardyPrimitive_pow Φ j b,
    localConformalPrimitiveCircle_apply Φ] at hder
  exact hder

include hb1 hbn in
/-- True Fourier tangential differentiation of one positive Vekua term.
Both velocity products are actual boundary L² vectors. -/
theorem localConformalVekua_trace_term_fourier_derivative :
    (Complex.I * (n : ℂ)) *
      boundaryFourier ((Φ.pulledBackTrace Φ.lipschitzDomain) (((neumannH1AffineMultiplier Φ.bounded (Φ.map 1)) ^ (j + 1)) (Φ.hardyH1Extension ((Φ.hardyPrimitive ^ (j + 1)) b)))) n =
      boundaryFourier
        ((((j + 1 : ℕ) : ℂ) • (boundaryContinuousMultiplier (localConformalVelocityCircle Φ.map)) ((Φ.pulledBackTrace Φ.lipschitzDomain) (((neumannH1AffineMultiplier Φ.bounded (Φ.map 1)) ^ j) (Φ.hardyH1Extension ((Φ.hardyPrimitive ^ (j + 1)) b))))) +
          (boundaryContinuousMultiplier (localConformalPrimitiveCircle Φ.map)) ((Φ.pulledBackTrace Φ.lipschitzDomain) (((neumannH1AffineMultiplier Φ.bounded (Φ.map 1)) ^ (j + 1)) (Φ.hardyH1Extension ((Φ.hardyPrimitive ^ j) b))))) n := by
  let hj (k : ℕ)  := hardyFourierTrace (normalizedHardyAverage ((Φ.hardyPrimitive ^ k) b))
  let f  := fun θ => (Φ.boundary θ - Φ.map 1) ^ (j + 1) * hj (j + 1) θ
  let d  := fun θ => ((j + 1 : ℕ) : ℂ) * deriv Φ.boundary θ *
    ((Φ.boundary θ - Φ.map 1) ^ j * hj (j + 1) θ) +
    conj (deriv Φ.boundary θ) * ((Φ.boundary θ - Φ.map 1) ^ (j + 1) * hj j θ)
  have hc (k : ℕ) : Continuous (hj k) := continuous_hardyFourierTrace
    (sq_tsum_norm_le (s := 0) (by norm_num)
      (by simpa using kernel_conormal_primitive_H1 Φ b hb1 k)).1
  have hd (θ : ℝ) : HasDerivAt f (d θ) θ := by
    have hg := (Φ.boundaryC1.differentiable (by simp) θ).hasDerivAt.sub_const (Φ.map 1)
    convert (hg.pow (j + 1)).mul
      (kernel_conormal_primitive_deriv Φ Φ.holomorphic b hbn hb1 j θ) using 1 ;
      dsimp only [f, d, hj] ;
        simp only [Nat.add_sub_cancel, Pi.pow_apply] ; ring_nf
  have hdc : Continuous d := by
    exact (((continuous_const.mul Φ.boundaryC1.continuous_deriv_one).mul
      ((Φ.boundaryC1.continuous.sub continuous_const).pow j |>.mul (hc (j + 1)))).add
      ((Complex.continuous_conj.comp Φ.boundaryC1.continuous_deriv_one).mul
        ((Φ.boundaryC1.continuous.sub continuous_const).pow (j + 1) |>.mul (hc j))))
  have hf1  := contDiff_one_iff_deriv.mpr
    ⟨fun θ => (hd θ).differentiableAt, by
      have he  := funext fun θ => (hd θ).deriv
      simp [*]⟩
  have hp : f 0 = f anglePeriod := by
    have hΓ := Φ.periodic_boundary 0
    have hh := hardyFourierTrace_periodic (normalizedHardyAverage ((Φ.hardyPrimitive ^ (j + 1)) b)) 0
    simp only [zero_add] at hΓ hh
    dsimp only [f, hj]
    rw [hΓ, hh]
  have hibp := fourierCoeffOn_of_ac_ae_hasDerivAt (driven_c1_absolutelyContinuous hf1)
    (memLp_angle_of_continuousOn hdc.continuousOn)
    (Eventually.of_forall fun θ _ => hd θ) hp n
  have hv := localConformalHardy_affine_primitive_trace_ae Φ b hbn hb1 (j + 1) (j + 1)
  have hdv :
      (((((j + 1 : ℕ) : ℂ) • (boundaryContinuousMultiplier (localConformalVelocityCircle Φ.map)) ((Φ.pulledBackTrace Φ.lipschitzDomain) (((neumannH1AffineMultiplier Φ.bounded (Φ.map 1)) ^ j) (Φ.hardyH1Extension ((Φ.hardyPrimitive ^ (j + 1)) b))))) +
        (boundaryContinuousMultiplier (localConformalPrimitiveCircle Φ.map)) ((Φ.pulledBackTrace Φ.lipschitzDomain) (((neumannH1AffineMultiplier Φ.bounded (Φ.map 1)) ^ (j + 1)) (Φ.hardyH1Extension ((Φ.hardyPrimitive ^ j) b))))) : ℝ → ℂ)
      =ᵐ[angleMeasure] d := by
    filter_upwards [Lp.coeFn_add
        (((((j + 1 : ℕ) : ℂ) • (boundaryContinuousMultiplier (localConformalVelocityCircle Φ.map)) ((Φ.pulledBackTrace Φ.lipschitzDomain) (((neumannH1AffineMultiplier Φ.bounded (Φ.map 1)) ^ j) (Φ.hardyH1Extension ((Φ.hardyPrimitive ^ (j + 1)) b)))))))
        ((boundaryContinuousMultiplier (localConformalPrimitiveCircle Φ.map)) ((Φ.pulledBackTrace Φ.lipschitzDomain) (((neumannH1AffineMultiplier Φ.bounded (Φ.map 1)) ^ (j + 1)) (Φ.hardyH1Extension ((Φ.hardyPrimitive ^ j) b))))),
      Lp.coeFn_smul (((j + 1 : ℕ) : ℂ))
        ((boundaryContinuousMultiplier (localConformalVelocityCircle Φ.map)) ((Φ.pulledBackTrace Φ.lipschitzDomain) (((neumannH1AffineMultiplier Φ.bounded (Φ.map 1)) ^ j) (Φ.hardyH1Extension ((Φ.hardyPrimitive ^ (j + 1)) b))))),
      boundaryContinuousMultiplier_ae (localConformalVelocityCircle Φ.map)
        ((Φ.pulledBackTrace Φ.lipschitzDomain) (((neumannH1AffineMultiplier Φ.bounded (Φ.map 1)) ^ j) (Φ.hardyH1Extension ((Φ.hardyPrimitive ^ (j + 1)) b)))),
      boundaryContinuousMultiplier_ae (localConformalPrimitiveCircle Φ.map)
        ((Φ.pulledBackTrace Φ.lipschitzDomain) (((neumannH1AffineMultiplier Φ.bounded (Φ.map 1)) ^ (j + 1)) (Φ.hardyH1Extension ((Φ.hardyPrimitive ^ j) b)))),
      localConformalHardy_affine_primitive_trace_ae Φ b hbn hb1 j (j + 1),
      localConformalHardy_affine_primitive_trace_ae Φ b hbn hb1 (j + 1) j] with θ ha hs hβ hα hx hy
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hβ, hα, hx, hy,
      localConformalVelocityCircle_apply Φ,
      localConformalPrimitiveCircle_apply Φ, d, hj]
    ring
  let v  :=
      (((j + 1 : ℕ) : ℂ) • (boundaryContinuousMultiplier (localConformalVelocityCircle Φ.map)) ((Φ.pulledBackTrace Φ.lipschitzDomain) (((neumannH1AffineMultiplier Φ.bounded (Φ.map 1)) ^ j) (Φ.hardyH1Extension ((Φ.hardyPrimitive ^ (j + 1)) b))))) +
        (boundaryContinuousMultiplier (localConformalPrimitiveCircle Φ.map)) ((Φ.pulledBackTrace Φ.lipschitzDomain) (((neumannH1AffineMultiplier Φ.bounded (Φ.map 1)) ^ (j + 1)) (Φ.hardyH1Extension ((Φ.hardyPrimitive ^ j) b))))
  have hdv' : (v : ℝ → ℂ) =ᵐ[angleMeasure] d := by
    dsimp only [v]
    filter_upwards [hdv,
      Lp.coeFn_add
        (((j + 1 : ℕ) : ℂ) • (boundaryContinuousMultiplier (localConformalVelocityCircle Φ.map)) ((Φ.pulledBackTrace Φ.lipschitzDomain) (((neumannH1AffineMultiplier Φ.bounded (Φ.map 1)) ^ j) (Φ.hardyH1Extension ((Φ.hardyPrimitive ^ (j + 1)) b)))))
        ((boundaryContinuousMultiplier (localConformalPrimitiveCircle Φ.map)) ((Φ.pulledBackTrace Φ.lipschitzDomain) (((neumannH1AffineMultiplier Φ.bounded (Φ.map 1)) ^ (j + 1)) (Φ.hardyH1Extension ((Φ.hardyPrimitive ^ j) b))))),
      Lp.coeFn_smul (((j + 1 : ℕ) : ℂ))
        ((boundaryContinuousMultiplier (localConformalVelocityCircle Φ.map)) ((Φ.pulledBackTrace Φ.lipschitzDomain) (((neumannH1AffineMultiplier Φ.bounded (Φ.map 1)) ^ j) (Φ.hardyH1Extension ((Φ.hardyPrimitive ^ (j + 1)) b)))))] with θ h ha hs
    exact ha.trans (by
      rw [Pi.add_apply, hs]
      exact h)
  
  rw [kernel_conormal_coeff_ae _ hv n,
    kernel_conormal_coeff_ae v hdv' n, hibp]
  ring

include hb1 hbn in
/-- The actual coordinate remainder has the Fourier derivative of its
true trace. Only bounded trace/evaluation maps transport the HasSums;
the derivative of each summand was proved by actual scalar FTC above. -/
theorem localConformalVekuaRemainder_fourier_derivative :
    (Complex.I * (n : ℂ)) * boundaryFourier ((Φ.pulledBackTrace Φ.lipschitzDomain) (Φ.vekuaRemainder (Φ.map 1) E b)) n =
      boundaryFourier ((boundaryContinuousMultiplier (localConformalVelocityCircle Φ.map)) ((Φ.pulledBackTrace Φ.lipschitzDomain) (Φ.vekuaGradientA (Φ.map 1) E b)) +
        (boundaryContinuousMultiplier (localConformalPrimitiveCircle Φ.map)) ((Φ.pulledBackTrace Φ.lipschitzDomain) (Φ.vekuaGradientB (Φ.map 1) E b))) n := by
  let P := ((boundaryContinuousMultiplier (localConformalVelocityCircle Φ.map))).comp (Φ.pulledBackTrace Φ.lipschitzDomain)
  let Q := ((boundaryContinuousMultiplier (localConformalPrimitiveCircle Φ.map))).comp (Φ.pulledBackTrace Φ.lipschitzDomain)
  have hl := ((kernel_conormal_eval n).hasSum
    (((Φ.pulledBackTrace Φ.lipschitzDomain)).hasSum (localConformalVekuaRemainder_hasSum Φ (Φ.map 1) E b))).mul_left (Complex.I * (n : ℂ))
  have hr := (kernel_conormal_eval n).hasSum
    ((P.hasSum (localConformalVekuaGradientA_hasSum Φ (Φ.map 1) E b)).add
      (Q.hasSum (localConformalVekuaGradientB_hasSum Φ (Φ.map 1) E b)))
  have heq (j : ℕ) :
      (Complex.I * (n : ℂ)) * kernel_conormal_eval n
          ((Φ.pulledBackTrace Φ.lipschitzDomain) (physicalVekuaCoeff E (j + 1) •
            (((neumannH1AffineMultiplier Φ.bounded (Φ.map 1)) ^ (j + 1)) (Φ.hardyH1Extension ((Φ.hardyPrimitive ^ (j + 1)) b))))) =
        kernel_conormal_eval n
          (P ((physicalVekuaCoeff E (j + 1) * ((j + 1 : ℕ) : ℂ)) •
              (((neumannH1AffineMultiplier Φ.bounded (Φ.map 1)) ^ j) (Φ.hardyH1Extension ((Φ.hardyPrimitive ^ (j + 1)) b)))) +
            Q (physicalVekuaCoeff E (j + 1) •
              (((neumannH1AffineMultiplier Φ.bounded (Φ.map 1)) ^ (j + 1)) (Φ.hardyH1Extension ((Φ.hardyPrimitive ^ j) b))))) := by
    simp only [kernel_conormal_eval_apply, P, Q, ContinuousLinearMap.comp_apply,
      map_add, map_smul, smul_eq_mul]
    have hterm := localConformalVekua_trace_term_fourier_derivative Φ b hbn hb1 j n
    simp only [map_add, map_smul, lp.coeFn_add, Pi.add_apply, lp.coeFn_smul,
      Pi.smul_apply, smul_eq_mul] at hterm
    calc
      _ = physicalVekuaCoeff E (j + 1) *
          ((Complex.I * (n : ℂ)) *
            boundaryFourier ((Φ.pulledBackTrace Φ.lipschitzDomain) (((neumannH1AffineMultiplier Φ.bounded (Φ.map 1)) ^ (j + 1)) (Φ.hardyH1Extension ((Φ.hardyPrimitive ^ (j + 1)) b)))) n) := by ring
      _ = _ := by rw [hterm]; ring
  have hl' : HasSum (fun j : ℕ => kernel_conormal_eval n
      (P ((physicalVekuaCoeff E (j + 1) * ((j + 1 : ℕ) : ℂ)) •
          (((neumannH1AffineMultiplier Φ.bounded (Φ.map 1)) ^ j) (Φ.hardyH1Extension ((Φ.hardyPrimitive ^ (j + 1)) b)))) +
        Q (physicalVekuaCoeff E (j + 1) •
          (((neumannH1AffineMultiplier Φ.bounded (Φ.map 1)) ^ (j + 1)) (Φ.hardyH1Extension ((Φ.hardyPrimitive ^ j) b))))))
      ((Complex.I * (n : ℂ)) * boundaryFourier ((Φ.pulledBackTrace Φ.lipschitzDomain) (Φ.vekuaRemainder (Φ.map 1) E b)) n) := by
    have hls := HasSum.congr_fun hl (fun j => (heq j).symm)
    simpa only [kernel_conormal_eval_apply] using hls
  have hr' : HasSum (fun j : ℕ => kernel_conormal_eval n
      (P ((physicalVekuaCoeff E (j + 1) * ((j + 1 : ℕ) : ℂ)) •
          (((neumannH1AffineMultiplier Φ.bounded (Φ.map 1)) ^ j) (Φ.hardyH1Extension ((Φ.hardyPrimitive ^ (j + 1)) b)))) +
        Q (physicalVekuaCoeff E (j + 1) •
          (((neumannH1AffineMultiplier Φ.bounded (Φ.map 1)) ^ (j + 1)) (Φ.hardyH1Extension ((Φ.hardyPrimitive ^ j) b))))))
      (boundaryFourier ((boundaryContinuousMultiplier (localConformalVelocityCircle Φ.map)) ((Φ.pulledBackTrace Φ.lipschitzDomain) (Φ.vekuaGradientA (Φ.map 1) E b)) +
        (boundaryContinuousMultiplier (localConformalPrimitiveCircle Φ.map)) ((Φ.pulledBackTrace Φ.lipschitzDomain) (Φ.vekuaGradientB (Φ.map 1) E b))) n) := by
    simpa only [P, Q, ContinuousLinearMap.comp_apply, kernel_conormal_eval_apply] using hr
  exact hl'.unique hr'

include hbn in
private theorem kernel_conormal_principal_coeff :
    normalizedConormalPrincipal b n =
      ((sobWeight n ^ (-halfOrder) : ℝ) : ℂ) *
        (-(n : ℂ) * fromL2 halfOrder b n) := by
  by_cases hn : 0 < n
  · simp [normalizedConormal_principal_apply, hbn n hn, mul_zero, fromL2]
  · have hn0 : (n : ℝ) ≤ 0 := by exact_mod_cast (le_of_not_gt hn)
    have habs  := abs_of_nonpos hn0
    rw [normalizedConormal_principal_apply, fromL2]
    have hw : sobWeight n ^ (-halfOrder) *
        sobWeight n ^ (-halfOrder) = (sobWeight n)⁻¹ := by
      rw [← Real.rpow_add (sobWeight_pos n),
        show -halfOrder + -halfOrder = -1 by ring, Real.rpow_neg_one]
    have hcast : ((|(n : ℝ)| / (1 + |(n : ℝ)|) : ℝ) : ℂ) =
        -(n : ℂ) * ((sobWeight n)⁻¹ : ℝ) := by
      rw [habs, sobWeight, habs]
      push_cast
      ring
    rw [hcast]
    calc
      _ = -n * ((((sobWeight n ^ (-halfOrder) : ℝ) : ℂ) *
          ((sobWeight n ^ (-halfOrder) : ℝ) : ℂ)) * b n) := by
        rw [← Complex.ofReal_mul, hw]
        ring
      _ = _ := by ring

include hb1 hbn in
/-- Exact coordinate conormal/tangential identity for every genuine
order-one nonpositive input. This includes the zero mode and uses the
actual companion A, not a presumed derivative of the principal H¹ vector. -/
theorem localConformalVekua_normalizedConormal_fourier :
    Φ.conormal E b n = ((sobWeight n ^ (-halfOrder) : ℝ) : ℂ) *
      (-(n : ℂ) * boundaryFourier ((Φ.pulledBackTrace Φ.lipschitzDomain) (Φ.vekuaH1 (Φ.map 1) E b)) n -
        2 * Complex.I * boundaryFourier ((boundaryContinuousMultiplier (localConformalVelocityCircle Φ.map)) ((Φ.pulledBackTrace Φ.lipschitzDomain) (Φ.vekuaGradientA (Φ.map 1) E b))) n) := by
  have hrem := localConformalVekuaCoordinateConormalRemainder_eq_conormalRemOp
    Φ E b hbn
  have hdiff := localConformalVekuaRemainder_fourier_derivative Φ E b hbn hb1 n
  have hbase : boundaryFourier ((Φ.pulledBackTrace Φ.lipschitzDomain) (Φ.hardyH1Extension b)) = fromL2 halfOrder b := by
    rw [← fromL2_half_localConformalDiskHalfTrace,
      localConformalDiskHalfTrace_hardyExtension_eq_of_nonpositive Φ b hbn]
  simp only [localConformalVekuaRemainder_apply, map_sub, lp.coeFn_sub,
    Pi.sub_apply, map_add, lp.coeFn_add, Pi.add_apply] at hdiff
  rw [hbase] at hdiff
  have hdiff' := congrArg (fun z : ℂ => Complex.I * z) hdiff
  simp only [mul_sub, ← mul_assoc, Complex.I_mul_I, neg_one_mul] at hdiff'
  change normalizedConormalPrincipal b n +
    sobolevSmoothing 1 zero_le_one (conormalRemOp (by norm_num) (localConformalVelocityCircle_isWL1_half Φ) (localConformalHardyPrimitiveMultiplier_isWL1 Φ) (localConformalCenteredCircle_isWL1_half Φ) E b) n = _
  rw [← hrem, sobolevSmoothing, diagOp_apply,
    DiskCoordinates.vekuaCoordinateConormalRemainder,
    ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.comp_apply]
  simp only [map_add, map_smul, lp.coeFn_add, Pi.add_apply, lp.coeFn_smul,
    Pi.smul_apply, smul_eq_mul]
  rw [kernel_conormal_principal_coeff b hbn n]
  have hpow : sobWeight n ^ ((-1 : ℝ) / 2) =
      sobWeight n ^ (-halfOrder) := by
    ring
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply,
    map_smul, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]
  ring_nf at hdiff' ⊢
  rw [hpow]
  linear_combination -((sobWeight n ^ (-halfOrder) : ℝ) : ℂ) * hdiff'

end

end CoordinateTerms

section DrivenCoordinates

private theorem kernel_conormal_volterra_eqOn {T : ℝ} {a f h : ℝ → ℂ}
    (he : EqOn f h (Icc 0 T)) (j : ℕ) :
    EqOn (volterraPrimitiveIterate a f j) (volterraPrimitiveIterate a h j) (Icc 0 T) := by
  induction j with
  | zero => exact he
  | succ j ih =>
    intro θ hθ
    
    apply intervalIntegral.integral_congr
    intro s hs
    rw [uIcc_of_le hθ.1] at hs
    dsimp only
    rw [ih (Icc_subset_Icc le_rfl hθ.2 hs)]

section

variable (g : ℝ → ℂ) (Φ : SmoothDiskMap) (hg : MemLp g 2 angleMeasure)

/-- The genuine companion A has precisely the first actual scaled driven
row as its ordinary coordinate trace. No row or conormal correspondence
is assumed. -/
theorem physicalDrivenKernelH1_gradientA_coordinate_trace_ae (Φ : DiskCoordinates) {L : NNReal}
    (hΓLip : LipschitzWith L Φ.boundary) {E : ℝ} (hE : 0 < E) {W : TransportPath}
    (hW : IsTransport Φ.boundary E W) (g : ℝ → ℂ) (hg : MemLp g 2 angleMeasure)
    (hO : observationAdj W g = 0) :
    ((Φ.pulledBackTrace Φ.lipschitzDomain) (Φ.vekuaGradientA (Φ.map 1) (E : ℂ) (physicalDrivenKernelInput hΓLip Φ.boundaryC1 hW g hg hO)) : ℝ → ℂ)
      =ᵐ[angleMeasure]
        physicalDrivenScaledRow E (physicalDrivenVector W g) 1 := by
  have hbn := physicalDrivenKernelInput_nonpositive Φ Φ.bounded Φ.lipschitzDomain Φ.holomorphic Φ.deriv_lower
    Φ.chart Φ.chart_eq Φ.source hΓLip hE hW g hg hO
  have hb1 := fromL2_physicalDrivenKernelInput_isSobolevSeq_one hΓLip Φ.boundaryC1 hW g hg hO
  have hJbn := localConformalHardyPrimitive_nonpositive Φ Φ.holomorphic (physicalDrivenKernelInput hΓLip Φ.boundaryC1 hW g hg hO) hbn
  have hJ1 := kernel_conormal_primitive_raw_H1 Φ (physicalDrivenKernelInput hΓLip Φ.boundaryC1 hW g hg hO) hb1 1
  have ht := localConformalVekua_coordinate_trace_reconstruction_ae Φ (E : ℂ) (Φ.hardyPrimitive (physicalDrivenKernelInput hΓLip Φ.boundaryC1 hW g hg hO)) hJbn hJ1
  have hprim : EqOn
      (hardyFourierTrace (normalizedHardyAverage (Φ.hardyPrimitive (physicalDrivenKernelInput hΓLip Φ.boundaryC1 hW g hg hO))))
      (volterraPrimitiveIterate (fun s => star (deriv Φ.boundary s))
        (physicalDrivenGauge Φ.boundary E (physicalDrivenVector W g) 0) 1)
      angleInterval := by
    intro θ hθ
    have hJ := localConformalHardyPrimitive_pow_volterra_of_H1 Φ Φ.holomorphic (physicalDrivenKernelInput hΓLip Φ.boundaryC1 hW g hg hO) hbn
      (isSobolevSeq_smul _ hb1) 1 θ
    simp at hJ
    rw [hJ]
    apply kernel_conormal_volterra_eqOn ?_ 1 hθ
    intro s hs
    rw [hardyFourierTrace_physicalDrivenKernelInput,
      physicalDrivenPeriodicGauge_eqOn _ E W g hO 0 hs]
  have hpoint {θ : ℝ} (hθ : θ ∈ angleInterval) :
      (-(E : ℂ) / 4) * hardyFourierTrace (normalizedHardyAverage
        (Φ.vekuaBoundary (E : ℂ) (Φ.hardyPrimitive (physicalDrivenKernelInput hΓLip Φ.boundaryC1 hW g hg hO)))) θ =
      physicalDrivenScaledRow E (physicalDrivenVector W g) 1 θ := by
    have hs := localConformalVekuaBoundary_average_volterra_hasSum_of_H1 Φ (E : ℂ) (Φ.hardyPrimitive (physicalDrivenKernelInput hΓLip Φ.boundaryC1 hW g hg hO)) hJbn hJ1 θ
    rw [← hs.tsum_eq]
    have hr := physicalDrivenScaledRow_eq_volterraVekua_of_intervalIntegrable hΓLip Φ.boundaryC1
      hE.le hW g (intervalIntegrable_boundary_of_memLp g hg) 1 hθ
    simp at hr
    rw [hr]
    congr 1
    apply tsum_congr
    intro j
    rw [kernel_conormal_volterra_eqOn hprim j hθ]
    simp [physicalDrivenCentered, physicalCircleTrace, circleMap_zero]
  rw [localConformalVekuaGradientA_apply, map_smul]
  have hs := Lp.coeFn_smul (-(E : ℂ) / 4)
    ((Φ.pulledBackTrace Φ.lipschitzDomain) (Φ.vekuaH1 (Φ.map 1) (E : ℂ) (Φ.hardyPrimitive (physicalDrivenKernelInput hΓLip Φ.boundaryC1 hW g hg hO))))
  filter_upwards [hs, ht, ae_restrict_mem measurableSet_Ioc]
    with θ hs ht hθ
  rw [hs]
  simp [smul_eq_mul, ht]
  exact hpoint (Ioc_subset_Icc_self hθ)

include hg in
/-- The original L² forcing, regarded as the genuine ordinary coordinate
load, with no arclength or constant-speed assertion. -/
def physicalDrivenKernelCoordinateLoad : BoundaryL2 := hg.toLp g

theorem physicalDrivenKernelCoordinateLoad_ae :
    (physicalDrivenKernelCoordinateLoad g hg : ℝ → ℂ)
      =ᵐ[angleMeasure] g := hg.coeFn_toLp

private theorem kernel_conormal_row_derivative_memLp {E : ℝ}
    {W : TransportPath} (hW : IsTransport Φ.boundary E W) (g : ℝ → ℂ)
    (hg : MemLp g 2 angleMeasure) :
    MemLp (fun θ => 2 * deriv Φ.boundary θ *
      physicalDrivenScaledRow E (physicalDrivenVector W g) 1 θ - Complex.I * g θ)
      2 angleMeasure := by
  have hy := physicalDrivenVector_continuousOn_of_intervalIntegrable hW.1 g
    (intervalIntegrable_boundary_of_memLp g hg)
  have hrow : ContinuousOn (physicalDrivenScaledRow E (physicalDrivenVector W g) 1)
      angleInterval := by
    exact continuousOn_const.mul (physicalDrivenRow_continuousOn _ hy 1)
  have hc : ContinuousOn (fun θ : ℝ => (2 : ℂ) * deriv Φ.boundary θ *
      physicalDrivenScaledRow E (physicalDrivenVector W g) 1 θ)
      angleInterval :=
    (continuousOn_const.mul Φ.boundaryC1.continuous_deriv_one.continuousOn).mul hrow
  exact (memLp_angle_of_continuousOn hc).sub (hg.const_mul Complex.I)

private theorem kernel_conormal_row_fourier_derivative {L : NNReal}
    (hΓLip : LipschitzWith L Φ.boundary) {E : ℝ} {W : TransportPath}
    (hW : IsTransport Φ.boundary E W) (g : ℝ → ℂ) (hg : MemLp g 2 angleMeasure)
    (hO : observationAdj W g = 0) (n : ℤ) :
    angleCoeff
      (fun θ => 2 * deriv Φ.boundary θ * physicalDrivenScaledRow E (physicalDrivenVector W g) 1 θ -
        Complex.I * g θ) n =
      (Complex.I * (n : ℂ)) *
        angleCoeff (physicalDrivenRow (physicalDrivenVector W g) 0) n := by
  have h := fourierCoeffOn_of_ac_ae_hasDerivAt
    (physicalDrivenScaledRow_absolutelyContinuous_of_intervalIntegrable hΓLip hW g
      (intervalIntegrable_boundary_of_memLp g hg) 0)
    (kernel_conormal_row_derivative_memLp Φ hW g hg)
    (physicalDrivenScaledRow_zero_ae_hasDerivAt_of_intervalIntegrable hΓLip Φ.boundaryC1 hW g
      (intervalIntegrable_boundary_of_memLp g hg))
    (by simp [physicalDrivenScaledRow, physicalDrivenRow,
      physicalDrivenVector_zero, physicalDrivenVector_endpoint W g hO]) n
  have hzero : physicalDrivenScaledRow E (physicalDrivenVector W g) 0 =
      physicalDrivenRow (physicalDrivenVector W g) 0 := by
    funext θ
    simp [physicalDrivenScaledRow, pow_zero]
  simp [*]

end

/-- The normalized conormal of the actual observation-kernel realization
is exactly the half-smoothed unitary Fourier transform of its original
coordinate L² forcing. Frequency zero is proved by the same true AC IBP. -/
theorem physicalDrivenKernelH1_normalizedConormal_eq_coordinateLoad (Φ : DiskCoordinates) {L : NNReal}
    (hΓLip : LipschitzWith L Φ.boundary) {E : ℝ} (hE : 0 < E) {W : TransportPath}
    (hW : IsTransport Φ.boundary E W) (g : ℝ → ℂ) (hg : MemLp g 2 angleMeasure)
    (hO : observationAdj W g = 0) :
    Φ.conormal (E : ℂ) (physicalDrivenKernelInput hΓLip Φ.boundaryC1 hW g hg hO) = sobolevSmoothing halfOrder (by norm_num)
      (boundaryFourier (physicalDrivenKernelCoordinateLoad g hg)) := by
  have hbn := physicalDrivenKernelInput_nonpositive Φ Φ.bounded Φ.lipschitzDomain Φ.holomorphic Φ.deriv_lower
    Φ.chart Φ.chart_eq Φ.source hΓLip hE hW g hg hO
  have hb1 := fromL2_physicalDrivenKernelInput_isSobolevSeq_one hΓLip Φ.boundaryC1 hW g hg hO
  let A  := boundaryContinuousMultiplier (localConformalVelocityCircle Φ.map)
    ((Φ.pulledBackTrace Φ.lipschitzDomain) (Φ.vekuaGradientA (Φ.map 1) (E : ℂ) (physicalDrivenKernelInput hΓLip Φ.boundaryC1 hW g hg hO)))
  have hA : (A : ℝ → ℂ) =ᵐ[angleMeasure]
      fun θ => deriv Φ.boundary θ * physicalDrivenScaledRow E (physicalDrivenVector W g) 1 θ := by
    filter_upwards [boundaryContinuousMultiplier_ae (localConformalVelocityCircle Φ.map)
        ((Φ.pulledBackTrace Φ.lipschitzDomain) (Φ.vekuaGradientA (Φ.map 1) (E : ℂ) (physicalDrivenKernelInput hΓLip Φ.boundaryC1 hW g hg hO))),
      physicalDrivenKernelH1_gradientA_coordinate_trace_ae Φ hΓLip hE hW g hg hO] with θ hm hr
    rw [hm, hr, localConformalVelocityCircle_apply Φ]
  let d  := (2 : ℂ) • A - Complex.I • physicalDrivenKernelCoordinateLoad g hg
  have hd : (d : ℝ → ℂ) =ᵐ[angleMeasure]
      fun θ => 2 * deriv Φ.boundary θ * physicalDrivenScaledRow E (physicalDrivenVector W g) 1 θ -
        Complex.I * g θ := by
    filter_upwards [Lp.coeFn_sub ((2 : ℂ) • A)
        (Complex.I • physicalDrivenKernelCoordinateLoad g hg),
      Lp.coeFn_smul (2 : ℂ) A,
      Lp.coeFn_smul Complex.I (physicalDrivenKernelCoordinateLoad g hg), hA,
      physicalDrivenKernelCoordinateLoad_ae g hg] with θ hs h2 hi hA hg
    rw [hs]
    simp [h2, hi, smul_eq_mul, hA, hg] <;> ring
  have ht := physicalDrivenKernelH1_coordinate_trace_ae Φ hΓLip hE hW g hg hO
  apply lp.ext
  funext n
  have hf := kernel_conormal_row_fourier_derivative Φ hΓLip hW g hg hO n
  have hf' : boundaryFourier d n = (Complex.I * (n : ℂ)) *
      boundaryFourier ((Φ.pulledBackTrace Φ.lipschitzDomain) (Φ.vekuaH1 (Φ.map 1) (E : ℂ) (physicalDrivenKernelInput hΓLip Φ.boundaryC1 hW g hg hO))) n := by
    dsimp only [physicalDrivenKernelH1] at ht
    rw [kernel_conormal_coeff_ae d hd n,
      kernel_conormal_coeff_ae ((Φ.pulledBackTrace Φ.lipschitzDomain) (Φ.vekuaH1 (Φ.map 1) (E : ℂ) (physicalDrivenKernelInput hΓLip Φ.boundaryC1 hW g hg hO))) ht n, hf]
    ring
  simp only [d, map_sub, map_smul, lp.coeFn_sub, Pi.sub_apply, lp.coeFn_smul,
    Pi.smul_apply, smul_eq_mul] at hf'
  have hi := congrArg (fun z : ℂ => Complex.I * z) hf'
  simp only [mul_sub, ← mul_assoc, Complex.I_mul_I, neg_one_mul] at hi
  rw [localConformalVekua_normalizedConormal_fourier Φ (E : ℂ) (physicalDrivenKernelInput hΓLip Φ.boundaryC1 hW g hg hO) hbn hb1 n]
  change _ = ((sobWeight n ^ (-halfOrder) : ℝ) : ℂ) *
    boundaryFourier (physicalDrivenKernelCoordinateLoad g hg) n
  linear_combination -((sobWeight n ^ (-halfOrder) : ℝ) : ℂ) * hi

end DrivenCoordinates

end PolyaNeumann

end
