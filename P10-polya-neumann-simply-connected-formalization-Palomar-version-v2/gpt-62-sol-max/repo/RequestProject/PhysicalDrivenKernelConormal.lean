module

public import RequestProject.CircleFourier
public import RequestProject.ConformalDiskCoordinates

public import RequestProject.PhysicalVolterraNormalization
public import RequestProject.IntervalRegularity
public import RequestProject.CutFourier
public import RequestProject.LocalConformalVekuaConormalBridge

/-!
# The genuine coordinate load of an observation-kernel vector

Fourier integration by parts identifies the true conormal, including the zeroth mode.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace PolyaNeumann

open MeasureTheory Set Metric Filter
open scoped Topology ComplexConjugate InnerProductSpace

private def kernel_conormal_eval (n : ℤ) : BoundaryL2 →L[ℂ] ℂ :=
  (innerSL ℂ (stdBasisZ n)).comp boundaryFourier.toLinearIsometry.toContinuousLinearMap

private theorem kernel_conormal_eval_apply (n : ℤ) (v : BoundaryL2) :
    kernel_conormal_eval n v = boundaryFourier v n := by
  exact inner_stdBasisZ n (boundaryFourier v)

/-- A genuine boundary L² function with order-one coefficients equals
their continuous Fourier reconstruction a.e. This uses the actual
unitary boundary Fourier transform, without presuming a representative. -/
theorem boundaryL2_ae_hardyFourierTrace_of_H1
    (v : BoundaryL2)
    (hv : IsSobolevSeq 1 (fourierCoeffOn Real.two_pi_pos (v : ℝ → ℂ))) :
    (v : ℝ → ℂ) =ᵐ[volume.restrict (Ioc 0 (2 * Real.pi))]
      hardyFourierTrace (fourierCoeffOn Real.two_pi_pos (v : ℝ → ℂ)) := by
  let c := fourierCoeffOn Real.two_pi_pos (v : ℝ → ℂ)
  have hc :=
    (sq_tsum_norm_le (s := 0) (by norm_num) (by simpa using hv)).1
  let H := hardyCircleReconstruction c
  let f : ℝ → ℂ := fun θ => H (θ : AddCircle (2 * Real.pi))
  have hfc := H.continuous.comp (AddCircle.continuous_mk' _)
  let w : BoundaryL2 := hfc.continuousOn.memLp_Ioc.toLp f
  have haw : (w : ℝ → ℂ) =ᵐ[volume.restrict (Ioc 0 (2 * Real.pi))] f := MemLp.coeFn_toLp _
  have hcoef : fourierCoeffOn Real.two_pi_pos (w : ℝ → ℂ) = c := by
    rw [fourierCoeffOn_congr_ae Real.two_pi_pos haw]
    change fourierCoeffOn Real.two_pi_pos
      (fun θ : ℝ => H (θ : AddCircle (2 * Real.pi))) = c
    rw [← fourierCoeff_eq_on_circle, hardyCircleReconstruction_fourierCoeff hc]
  have hF : boundaryFourier v = boundaryFourier w := by
    apply lp.ext
    funext n
    rw [boundaryFourier_apply, boundaryFourier_apply, hcoef]
  have he := boundaryFourier.injective hF
  have hav : (v : ℝ → ℂ) =ᵐ[volume.restrict (Ioc 0 (2 * Real.pi))] f := by
    rw [he]
    exact haw
  filter_upwards [hav] with θ hθ
  exact hθ.trans (hardyCircleReconstruction_coe hc θ)

theorem normalizedHardyAverage_localConformalDiskHalfTrace
    {R : ℝ} (hR : 1 < R) (F : ℂ → ℂ)
    (hFs : ContDiffOn ℝ (⊤ : ℕ∞) F (ball (0 : ℂ) R))
    (hL : IsLipschitzDomain (F '' ball (0 : ℂ) 1))
    (u : NeumannH1 (F '' ball (0 : ℂ) 1)) :
    normalizedHardyAverage (localConformalDiskHalfTrace hR F hFs hL u) =
      fourierCoeffOn Real.two_pi_pos (localConformalDiskH1Trace hR F hFs hL u) := by
  have hs : (Real.sqrt (2 * Real.pi) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr Real.two_pi_pos).ne'
  funext n
  change (Real.sqrt (2 * Real.pi) : ℂ)⁻¹ *
    fromL2 (1 / 2 : ℝ) (localConformalDiskHalfTrace hR F hFs hL u) n = _
  rw [fromL2_half_localConformalDiskHalfTrace, boundaryFourier_apply,
    ← mul_assoc, inv_mul_cancel₀ hs, one_mul]

section CoordinateTerms

variable {R : ℝ}
    (hR : 1 < R)
    (F : ℂ → ℂ)
    (hFs : ContDiffOn ℝ (⊤ : ℕ∞) F (ball (0 : ℂ) R))
    (hhol : DifferentiableOn ℂ F (ball (0 : ℂ) 1))
    (coords : ConformalDiskCoordinates F)

local notation "ΩF" => F '' ball (0 : ℂ) 1
local notation "ΓF" => physicalCircleTrace F
local notation "hΓF" => contDiff_physicalCircleTrace_of_neighborhood coords.one_lt_radius F
  (coords.smooth.of_le (by simp))
local notation "UF" => localConformalHardyH1Extension coords
local notation "JF" => localConformalHardyPrimitive coords.one_lt_radius F coords.smooth
local notation "MF" => neumannH1AffineMultiplier coords.bounded (F 1)
local notation "TF" => coords.trace
local notation "QF" => coords.halfTrace
local notation "VF" => localConformalVekuaH1 coords
local notation "AF" => localConformalVekuaGradientA coords
local notation "BF" => localConformalVekuaGradientB coords
local notation "RF" => localConformalVekuaRemainder coords
local notation "VelF" => boundaryContinuousMultiplier (localConformalVelocityCircle F)
local notation "BarVelF" => boundaryContinuousMultiplier (localConformalPrimitiveCircle F)
local notation "hβF" => localConformalVelocityCircle_isWL1_half coords.one_lt_radius F coords.smooth
local notation "haF" => localConformalHardyPrimitiveMultiplier_isWL1 coords.one_lt_radius F coords.smooth
local notation "hgF" => localConformalCenteredCircle_isWL1_half coords.one_lt_radius F coords.smooth
local notation "NCF" => normalizedConormal hβF haF hgF

private theorem kernel_conormal_primitive_H1 (b : L2Z)
    (hb1 : IsSobolevSeq 1 (fromL2 (1 / 2 : ℝ) b)) (j : ℕ) :
    IsSobolevSeq 1 (normalizedHardyAverage (((localConformalHardyPrimitive hR F hFs) ^ j) b)) := by
  rw [normalizedHardyAverage_localConformalHardyPrimitive_pow]
  exact (antiPrimIter_bound (by norm_num : (0 : ℝ) ≤ 1)
    (physicalCircleTrace_fourier_weights_of_smooth_neighborhood hR F hFs).1
    (isSobolevSeq_smul _ hb1) j).1


section

variable {F}
include coords

/-- Actual ordinary trace representatives for independent affine and
primitive powers. The constant primitive coefficient is retained. -/
theorem localConformalHardy_affine_primitive_trace_ae (b : L2Z)
    (hbn : IsNonpositiveFourierSupport b)
    (hb1 : IsSobolevSeq 1 (fromL2 (1 / 2 : ℝ) b)) (j k : ℕ) :
    (TF ((MF ^ j) (UF ((JF ^ k) b))) : ℝ → ℂ)
      =ᵐ[volume.restrict (Ioc 0 (2 * Real.pi))]
        fun θ => (ΓF θ - F 1) ^ j *
          hardyFourierTrace (normalizedHardyAverage ((JF ^ k) b)) θ := by
  have hnk := localConformalHardyPrimitive_pow_nonpositive coords.one_lt_radius F coords.smooth coords.holomorphic b hbn k
  have hc : normalizedHardyAverage (QF (UF ((JF ^ k) b))) =
      normalizedHardyAverage ((JF ^ k) b) := by
    rw [localConformalDiskHalfTrace_hardyExtension_eq_of_nonpositive coords _ hnk]
  have hcoef := normalizedHardyAverage_localConformalDiskHalfTrace coords.one_lt_radius F coords.smooth coords.lipschitz
    (UF ((JF ^ k) b))
  rw [hc] at hcoef
  have hu := boundaryL2_ae_hardyFourierTrace_of_H1 (TF (UF ((JF ^ k) b)))
    (by rw [← hcoef]; exact kernel_conormal_primitive_H1 coords.one_lt_radius F coords.smooth b hb1 k)
  rw [← hcoef] at hu
  rw [localConformalDiskH1Trace_affineMultiplier_pow coords]
  filter_upwards [hu, boundaryContinuousMultiplier_ae
    ((localConformalCenteredCircle coords.one_lt_radius F coords.smooth) ^ j) (TF (UF ((JF ^ k) b)))]
    with θ hu hm
  rw [hm, hu]
  simp  [ContinuousMap.pow_apply, localConformalCenteredCircle_apply,
    physicalCircleTrace]

end

theorem kernel_conormal_primitive_deriv (hhol : DifferentiableOn ℂ F (ball (0 : ℂ) 1))
    (b : L2Z)
    (hbn : IsNonpositiveFourierSupport b)
    (hb1 : IsSobolevSeq 1 (fromL2 (1 / 2 : ℝ) b)) (j : ℕ) (θ : ℝ) :
    HasDerivAt (hardyFourierTrace (normalizedHardyAverage (((localConformalHardyPrimitive hR F hFs) ^ (j + 1)) b)))
      (conj (deriv ΓF θ) *
        hardyFourierTrace (normalizedHardyAverage (((localConformalHardyPrimitive hR F hFs) ^ j) b)) θ) θ := by
  have hnorm : IsSobolevSeq 1 (normalizedHardyAverage b) := by
    exact isSobolevSeq_smul (Real.sqrt (2 * Real.pi) : ℂ)⁻¹ hb1
  have hbn' : IsNonpositiveFourierSupport (normalizedHardyAverage b) := by
    intro n hn
    simp [normalizedHardyAverage, fromL2, hbn n hn]
  have hder := hasDerivAt_hardyFourierTrace_antiPrimIter_succ (localConformalPrimitiveCircle F)
    (localConformalPrimitiveCircle_isWL1 hR F hFs) hnorm
    (localConformalPrimitiveCircle_strictNegative hR F hFs hhol) hbn' j θ
  rw [localConformalPrimitiveCircle_coeff hR F hFs] at hder
  rw [← normalizedHardyAverage_localConformalHardyPrimitive_pow hR F hFs (j + 1) b,
    ← normalizedHardyAverage_localConformalHardyPrimitive_pow hR F hFs j b,
    localConformalPrimitiveCircle_apply hR F hFs] at hder
  exact hder

section

variable {F}
include coords

/-- True Fourier tangential differentiation of one positive Vekua term.
Both velocity products are actual boundary L² vectors. -/
theorem localConformalVekua_trace_term_fourier_derivative (b : L2Z)
    (hbn : IsNonpositiveFourierSupport b)
    (hb1 : IsSobolevSeq 1 (fromL2 (1 / 2 : ℝ) b)) (j : ℕ) (n : ℤ) :
    (Complex.I * (n : ℂ)) *
      boundaryFourier (TF ((MF ^ (j + 1)) (UF ((JF ^ (j + 1)) b)))) n =
      boundaryFourier
        ((((j + 1 : ℕ) : ℂ) • VelF (TF ((MF ^ j) (UF ((JF ^ (j + 1)) b))))) +
          BarVelF (TF ((MF ^ (j + 1)) (UF ((JF ^ j) b))))) n := by
  let hj (k : ℕ) : ℝ → ℂ := hardyFourierTrace (normalizedHardyAverage ((JF ^ k) b))
  let f : ℝ → ℂ := fun θ => (ΓF θ - F 1) ^ (j + 1) * hj (j + 1) θ
  let d : ℝ → ℂ := fun θ => ((j + 1 : ℕ) : ℂ) * deriv ΓF θ *
    ((ΓF θ - F 1) ^ j * hj (j + 1) θ) +
    conj (deriv ΓF θ) * ((ΓF θ - F 1) ^ (j + 1) * hj j θ)
  have hc (k : ℕ) : Continuous (hj k) := continuous_hardyFourierTrace
    (sq_tsum_norm_le (s := 0) (by norm_num)
      (by simpa using kernel_conormal_primitive_H1 coords.one_lt_radius F coords.smooth b hb1 k)).1
  have hd (θ : ℝ) : HasDerivAt f (d θ) θ := by
    have hg := ((hΓF).differentiable (by simp) θ).hasDerivAt.sub_const (F 1)
    convert (hg.pow (j + 1)).mul
      (kernel_conormal_primitive_deriv coords.one_lt_radius F coords.smooth coords.holomorphic b hbn hb1 j θ) using 1 ;
      dsimp only [f, d, hj] ;
        simp only [Nat.add_sub_cancel, Pi.pow_apply] ; ring_nf
  have hdc : Continuous d := by
    exact (((continuous_const.mul (hΓF).continuous_deriv_one).mul
      (((hΓF).continuous.sub continuous_const).pow j |>.mul (hc (j + 1)))).add
      ((Complex.continuous_conj.comp (hΓF).continuous_deriv_one).mul
        (((hΓF).continuous.sub continuous_const).pow (j + 1) |>.mul (hc j))))
  have hp : f 0 = f (2 * Real.pi) := by
    have hΓ := physicalCircleTrace_periodic F 0
    have hh := hardyFourierTrace_periodic (normalizedHardyAverage ((JF ^ (j + 1)) b)) 0
    simp only [zero_add] at hΓ hh
    dsimp only [f, hj]
    rw [hΓ, hh]
  have hibp := fourierCoeffOn_deriv hd hdc hp n
  have hv := localConformalHardy_affine_primitive_trace_ae coords b hbn hb1 (j + 1) (j + 1)
  let u := VelF (TF ((MF ^ j) (UF ((JF ^ (j + 1)) b))))
  let w := BarVelF (TF ((MF ^ (j + 1)) (UF ((JF ^ j) b))))
  let c : ℂ := (j + 1 : ℕ)
  let v : BoundaryL2 := c • u + w
  have hdv : (v : ℝ → ℂ) =ᵐ[volume.restrict (Ioc 0 (2 * Real.pi))] d := by
    filter_upwards [Lp.coeFn_add (c • u) w, Lp.coeFn_smul c u,
      boundaryContinuousMultiplier_ae (localConformalVelocityCircle F) (TF ((MF ^ j) (UF ((JF ^ (j + 1)) b)))),
      boundaryContinuousMultiplier_ae (localConformalPrimitiveCircle F) (TF ((MF ^ (j + 1)) (UF ((JF ^ j) b)))),
      localConformalHardy_affine_primitive_trace_ae coords b hbn hb1 j (j + 1),
      localConformalHardy_affine_primitive_trace_ae coords b hbn hb1 (j + 1) j] with θ ha hs hβ hα hx hy
    change v θ = d θ
    change u θ = _ at hβ
    change w θ = _ at hα
    rw [show v θ = _ from ha, Pi.add_apply, hs]
    simp only [Pi.smul_apply, smul_eq_mul, hβ, hα, hx, hy, localConformalVelocityCircle_apply coords.one_lt_radius F coords.smooth, localConformalPrimitiveCircle_apply coords.one_lt_radius F coords.smooth, c]
    ring
  change Complex.I * (n : ℂ) * boundaryFourier
      (TF ((MF ^ (j + 1)) (UF ((JF ^ (j + 1)) b)))) n = boundaryFourier v n
  rw [boundaryFourier_apply_of_ae _ hv n, boundaryFourier_apply_of_ae v hdv n, hibp]
  ring

/-- The actual coordinate remainder has the Fourier derivative of its
true trace. Only bounded trace/evaluation maps transport the HasSums;
the derivative of each summand was proved by actual scalar FTC above. -/
theorem localConformalVekuaRemainder_fourier_derivative (E : ℂ) (b : L2Z)
    (hbn : IsNonpositiveFourierSupport b)
    (hb1 : IsSobolevSeq 1 (fromL2 (1 / 2 : ℝ) b)) (n : ℤ) :
    (Complex.I * (n : ℂ)) * boundaryFourier (TF (RF (F 1) E b)) n =
      boundaryFourier (VelF (TF (AF (F 1) E b)) +
        BarVelF (TF (BF (F 1) E b))) n := by
  let P := (VelF).comp TF
  let Q := (BarVelF).comp TF
  have hl := ((kernel_conormal_eval n).hasSum
    ((TF).hasSum (localConformalVekuaRemainder_hasSum coords (F 1) E b))).mul_left (Complex.I * (n : ℂ))
  have hr := (kernel_conormal_eval n).hasSum
    ((P.hasSum (localConformalVekuaGradientA_hasSum coords (F 1) E b)).add
      (Q.hasSum (localConformalVekuaGradientB_hasSum coords (F 1) E b)))
  have hsum := hl.unique (hr.congr_fun fun j => by
    dsimp  [Function.comp_apply, P, Q, ContinuousLinearMap.comp_apply]
    simp only [kernel_conormal_eval_apply, map_add, map_smul, smul_eq_mul]
    have hterm := localConformalVekua_trace_term_fourier_derivative coords b hbn hb1 j n
    simp only [map_add, map_smul, lp.coeFn_add, Pi.add_apply, lp.coeFn_smul,
      Pi.smul_apply, smul_eq_mul] at hterm
    linear_combination physicalVekuaCoeff E (j + 1) * hterm)
  simpa only [P, Q, ContinuousLinearMap.comp_apply, kernel_conormal_eval_apply] using hsum

end

private theorem kernel_conormal_principal_coeff (b : L2Z)
    (hbn : IsNonpositiveFourierSupport b) (n : ℤ) :
    normalizedConormalPrincipal b n =
      ((sobWeight n ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
        (-(n : ℂ) * fromL2 (1 / 2 : ℝ) b n) := by
  by_cases hn : 0 < n
  · simp  [normalizedConormal_principal_apply, hbn n hn, mul_zero, fromL2]
  · have hn0 : (n : ℝ) ≤ 0 := by exact_mod_cast (le_of_not_gt hn)
    have habs : |(n : ℝ)| = -(n : ℝ) := abs_of_nonpos hn0
    rw [normalizedConormal_principal_apply, fromL2]
    have hw : sobWeight n ^ (-(1 / 2 : ℝ)) *
        sobWeight n ^ (-(1 / 2 : ℝ)) = (sobWeight n)⁻¹ := by
      rw [← Real.rpow_add (sobWeight_pos n),
        show -(1 / 2 : ℝ) + -(1 / 2 : ℝ) = -1 by ring, Real.rpow_neg_one]
    have hcast : ((|(n : ℝ)| / (1 + |(n : ℝ)|) : ℝ) : ℂ) =
        -(n : ℂ) * ((sobWeight n)⁻¹ : ℝ) := by
      rw [habs, sobWeight, habs]
      push_cast
      ring
    rw [hcast]
    calc
      _ = -(n : ℂ) * ((((sobWeight n ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
          ((sobWeight n ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)) * b n) := by
        rw [← Complex.ofReal_mul, hw]
        ring
      _ = _ := by ring

section

variable {F}
include coords

/-- Exact coordinate conormal/tangential identity for every genuine
order-one nonpositive input. This includes the zero mode and uses the
actual companion A, not a presumed derivative of the principal H¹ vector. -/
theorem localConformalVekua_normalizedConormal_fourier (E : ℂ) (b : L2Z)
    (hbn : IsNonpositiveFourierSupport b)
    (hb1 : IsSobolevSeq 1 (fromL2 (1 / 2 : ℝ) b)) (n : ℤ) :
    NCF E b n = ((sobWeight n ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
      (-(n : ℂ) * boundaryFourier (TF (VF (F 1) E b)) n -
        2 * Complex.I * boundaryFourier (VelF (TF (AF (F 1) E b))) n) := by
  have hrem := localConformalVekuaCoordinateConormalRemainder_eq_conormalRemOp coords E b hbn
  have hdiff := localConformalVekuaRemainder_fourier_derivative coords E b hbn hb1 n
  have hbase : boundaryFourier (TF (UF b)) = fromL2 (1 / 2 : ℝ) b := by
    rw [← fromL2_half_localConformalDiskHalfTrace,
      localConformalDiskHalfTrace_hardyExtension_eq_of_nonpositive coords b hbn]
  simp  [localConformalVekuaRemainder_apply, map_sub, map_add] at hdiff
  rw [hbase] at hdiff
  have hdiff' := congrArg (fun z : ℂ => Complex.I * z) hdiff
  simp only [mul_sub, ← mul_assoc, Complex.I_mul_I, neg_one_mul] at hdiff'
  change normalizedConormalPrincipal b n +
    sobolevSmoothing 1 zero_le_one (conormalRemOp (by norm_num) hβF haF hgF E b) n = _
  rw [← hrem, sobolevSmoothing, diagOp_apply,
    localConformalVekuaCoordinateConormalRemainder,
    ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.comp_apply]
  simp only [map_add, map_smul, lp.coeFn_add, Pi.add_apply, lp.coeFn_smul,
    Pi.smul_apply, smul_eq_mul]
  rw [kernel_conormal_principal_coeff b hbn n]
  have hpow : sobWeight n ^ ((-1 : ℝ) / 2) =
      sobWeight n ^ (-(1 / 2 : ℝ)) := by
    congr 1; ring
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply,
    map_smul, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]
  ring_nf at hdiff' ⊢
  rw [hpow]
  linear_combination -((sobWeight n ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * hdiff'

end

end CoordinateTerms

end PolyaNeumann

end
