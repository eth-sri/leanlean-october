module

public import RequestProject.CircleFourier
public import RequestProject.ConformalDiskCoordinates

public import RequestProject.LocalConformalVekuaConormalBridge
public import RequestProject.NeumannResonanceDimension
public import RequestProject.LocalConformalHardySubspace
public import RequestProject.PhysicalDrivenHardyRegularity
public import RequestProject.PhysicalDrivenKernelConormal
public import RequestProject.LocalConformalArcReparam
public import Mathlib.Analysis.Complex.Angle
public import RequestProject.VekuaTower

/-! The actual coordinate traces and their common vector transport equation. -/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace PolyaNeumann

open Set MeasureTheory Filter Metric
open scoped Topology ComplexConjugate

theorem volterraPrimitiveIterate_iterate (a h : ℝ → ℂ) (j k : ℕ) :
    volterraPrimitiveIterate a (volterraPrimitiveIterate a h k) j =
      volterraPrimitiveIterate a h (j + k) := by
  induction j with
  | zero => simp [volterraPrimitiveIterate]
  | succ j ih => rw [show j + 1 + k = j + k + 1 by omega]; simp [volterraPrimitiveIterate, ih]

section

variable (γ : ℝ → ℂ) (E : ℂ) (h : ℝ → ℂ)
include γ E h

/-- The actual interval-integral series defining row n of a Vekua trace. -/
def volterraVekuaTraceRowTerm 
    (n j : ℕ) (θ : ℝ) : ℂ :=
  physicalVekuaCoeff E j * (γ θ - γ 0) ^ j *
    volterraPrimitiveIterate (fun s => conj (deriv γ s)) h (j + n) θ

def volterraVekuaTraceRow 
    (n : ℕ) (θ : ℝ) : ℂ :=
  ∑' j : ℕ, volterraVekuaTraceRowTerm γ E h n j θ

end

/-- A true conormal kernel gains regularity from NC−I smoothing. -/
theorem normalizedConormal_kernel_raw_H1
    {β a g : ℤ → ℂ} (hβ : IsWL1 (1 / 2 : ℝ) β)
    (ha : IsWL1 (1 / 2 : ℝ) a) (hg : IsWL1 (1 / 2 : ℝ) g)
    (E : ℂ) (b : L2Z) (hb : normalizedConormal hβ ha hg E b = 0) :
    IsSobolevSeq 1 (fromL2 (1 / 2 : ℝ) b) := by
  have he := congrArg (fun A : L2Z →L[ℂ] L2Z => A b)
    (normalizedConormal_sub_one_eq hβ ha hg E)
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply,
    ContinuousLinearMap.comp_apply, hb, zero_sub] at he
  have hr : b = sobolevSmoothing 1 zero_le_one (b - conormalRemOp (by norm_num) hβ ha hg E b) := by
    have h := congrArg Neg.neg he
    simpa only [← map_neg, neg_sub, neg_neg] using h
  rw [hr, fromL2_half_smoothing_one]
  exact (sobNormSq_mono (by norm_num : (1 : ℝ) ≤ (1 / 2 : ℝ) + 1)
    (isSobolevSeq_fromL2 ((1 / 2 : ℝ) + 1) _)).1

section PhysicalCoordinates

variable {R : ℝ}
    (hR : 1 < R)
    (F : ℂ → ℂ)
    (hFs : ContDiffOn ℝ (⊤ : ℕ∞) F (ball (0 : ℂ) R))
    (coords : ConformalDiskCoordinates F)

local notation "JF" => localConformalHardyPrimitive coords.one_lt_radius F coords.smooth
local notation "VB" => localConformalVekuaBoundary coords
local notation "hβF" => localConformalVelocityCircle_isWL1_half coords.one_lt_radius F coords.smooth
local notation "haF" => localConformalHardyPrimitiveMultiplier_isWL1 coords.one_lt_radius F coords.smooth
local notation "hgF" => localConformalCenteredCircle_isWL1_half coords.one_lt_radius F coords.smooth

section

variable {F}
include coords

/-- These are actual normalized Vekua traces, reconstructed in ordinary
averaged coordinates. No formal row or derivative is substituted. -/
def localConformalVekuaTraceRow (E : ℂ) (b : L2Z) (n : ℕ) (θ : ℝ) : ℂ :=
  hardyFourierTrace (normalizedHardyAverage (VB E ((JF ^ n) b))) θ

end

theorem localConformalHardyPrimitive_pow_raw_H1 (b : L2Z)
    (hb1 : IsSobolevSeq 1 (fromL2 (1 / 2 : ℝ) b)) (n : ℕ) :
    IsSobolevSeq 1 (fromL2 (1 / 2 : ℝ) (((localConformalHardyPrimitive hR F hFs) ^ n) b)) := by
  rw [fromL2_localConformalHardyPrimitive_pow hR F hFs]
  exact (antiPrimIter_bound (by norm_num : (0 : ℝ) ≤ 1)
    (physicalCircleTrace_fourier_weights_of_smooth_neighborhood hR F hFs).1 hb1 n).1

section

variable {F}
include coords

/-- Each continuous reconstructed row represents the actual coordinate trace. -/
theorem localConformalVekuaTraceRow_ae (E : ℂ) (b : L2Z)
    (hbn : IsNonpositiveFourierSupport b) (hb : IsSobolevSeq 1 (fromL2 (1 / 2) b)) (j : ℕ) :
    (coords.trace
        (localConformalVekuaH1 coords (F 1) E ((JF ^ j) b)) : ℝ → ℂ)
      =ᵐ[volume.restrict (Ioc 0 (2 * Real.pi))] localConformalVekuaTraceRow coords E b j := by
  let u := localConformalVekuaH1 coords (F 1) E ((JF ^ j) b)
  let T := coords.trace u
  have hc := normalizedHardyAverage_localConformalDiskHalfTrace coords.one_lt_radius F
    coords.smooth coords.lipschitz u
  change normalizedHardyAverage (VB E ((JF ^ j) b)) = fourierCoeffOn Real.two_pi_pos T at hc
  have hr := localConformalVekuaBoundary_raw_H1 coords E ((JF ^ j) b)
    (localConformalHardyPrimitive_pow_nonpositive coords.one_lt_radius F coords.smooth coords.holomorphic b hbn j)
    (localConformalHardyPrimitive_pow_raw_H1 coords.one_lt_radius F coords.smooth b hb j)
  change (T : ℝ → ℂ) =ᵐ[_] hardyFourierTrace (normalizedHardyAverage (VB E ((JF ^ j) b)))
  rw [hc]
  exact boundaryL2_ae_hardyFourierTrace_of_H1 T (by rw [← hc]; exact isSobolevSeq_smul _ hr)

end

section

variable (E : ℂ) (b : L2Z)
include E b

section

variable {F}
include coords

/-- Every actual coordinate trace row equals its true interval-integral
series, for the full nonpositive input including frequency zero. -/
theorem localConformalVekuaTraceRow_eq_volterra 
    (hbn : IsNonpositiveFourierSupport b)
    (hb1 : IsSobolevSeq 1 (fromL2 (1 / 2 : ℝ) b)) (n : ℕ) (θ : ℝ) :
    localConformalVekuaTraceRow coords E b n θ =
      volterraVekuaTraceRow (physicalCircleTrace F) E
        (hardyFourierTrace (normalizedHardyAverage b)) n θ := by
  have hpn := localConformalHardyPrimitive_pow_nonpositive coords.one_lt_radius F coords.smooth coords.holomorphic b hbn n
  have hp1 := localConformalHardyPrimitive_pow_raw_H1 coords.one_lt_radius F coords.smooth b hb1 n
  have havg : IsSobolevSeq 1 (normalizedHardyAverage b) := isSobolevSeq_smul _ hb1
  have hfun : hardyFourierTrace (normalizedHardyAverage ((JF ^ n) b)) =
      volterraPrimitiveIterate (fun s => conj (deriv (physicalCircleTrace F) s))
        (hardyFourierTrace (normalizedHardyAverage b)) n := by
    funext s
    exact localConformalHardyPrimitive_pow_volterra_of_H1 coords.one_lt_radius F coords.smooth coords.holomorphic b hbn havg n s
  have hs := localConformalVekuaBoundary_average_volterra_hasSum_of_H1 coords E ((JF ^ n) b) hpn hp1 θ
  rw [hfun] at hs
  simp only [starRingEnd_apply] at hs
  change localConformalVekuaTraceRow coords E b n θ = _
  simpa only [localConformalVekuaTraceRow, volterraVekuaTraceRow,
    volterraVekuaTraceRowTerm, physicalCircleTrace, circleMap_zero,
    starRingEnd_apply, Complex.exp_zero, Complex.ofReal_zero, Complex.ofReal_one, zero_add,
    zero_mul, one_mul, mul_one, volterraPrimitiveIterate_iterate] using hs.tsum_eq.symm

theorem localConformalVekuaTraceRow_periodic  (n : ℕ) :
    Function.Periodic
      (localConformalVekuaTraceRow coords E b n)
      (2 * Real.pi) := hardyFourierTrace_periodic _

end

end

section
variable {F}
include coords

local notation "Γ" => physicalCircleTrace F
local notation "U" => localConformalVekuaTraceRow coords
local notation "s₂" => (Real.sqrt 2 : ℂ)
local notation "H" b => hardyFourierTrace (normalizedHardyAverage b)

private theorem circleTrace_smooth : ContDiff ℝ 1 Γ :=
  contDiff_physicalCircleTrace_of_neighborhood coords.one_lt_radius F
    (coords.smooth.of_le (WithTop.coe_le_coe.mpr le_top))

omit coords in
private theorem hardyTrace_continuous (b : L2Z)
    (hb1 : IsSobolevSeq 1 (fromL2 (1 / 2 : ℝ) b)) : Continuous (H b) := by
  have ha : IsSobolevSeq 1 (normalizedHardyAverage b) := isSobolevSeq_smul _ hb1
  exact continuous_hardyFourierTrace (sq_tsum_norm_le (s := 0) (by norm_num) (by simpa using ha)).1

/-- Physical transport coordinates retain y₀=U₀/√2 and yₙ=qⁿUₙ. -/
def localConformalVekuaTransportCoordinate (E : ℝ) (b : L2Z) (n : ℕ) (θ : ℝ) : ℂ :=
  if n = 0 then U (E : ℂ) b 0 θ / s₂ else physicalDrivenQ E ^ n * U (E : ℂ) b n θ

def localConformalVekuaTransportVector (_coords : ConformalDiskCoordinates F) (E : ℝ) (b : L2Z) : ℝ → Ell2 :=
  vekuaTowerVector Γ E (H b)

local notation "Y" => localConformalVekuaTransportVector coords

variable (E : ℝ) (hE : 0 ≤ E) (b : L2Z) (hbn : IsNonpositiveFourierSupport b)
    (hb1 : IsSobolevSeq 1 (fromL2 (1 / 2 : ℝ) b))

include hE hbn hb1 in
theorem localConformalVekuaTransportVector_coord (θ : ℝ) (n : ℕ) :
    (Y E b θ : ℕ → ℂ) n = localConformalVekuaTransportCoordinate coords E b n θ := by
  have hs := vekuaRows_hasSum (E := E) (circleTrace_smooth coords) (hardyTrace_continuous b hb1) θ n
  rw [physicalDrivenQ_sq hE] at hs
  change HasSum (fun j : ℕ => physicalDrivenQ E ^ n * volterraVekuaTraceRowTerm Γ (E : ℂ) (H b) n j θ) _ at hs
  have he : (vekuaRows Γ E (H b) θ : ℕ → ℂ) n = physicalDrivenQ E ^ n * U (E : ℂ) b n θ := by
    rw [← hs.tsum_eq, tsum_mul_left, localConformalVekuaTraceRow_eq_volterra coords (E : ℂ) b hbn hb1]
    rfl
  cases n with
  | zero =>
    rw [localConformalVekuaTransportVector, vekuaTowerVector_zero_coord, he]
    simp [localConformalVekuaTransportCoordinate]
  | succ n =>
    rw [localConformalVekuaTransportVector, vekuaTowerVector_succ_coord, he]
    simp [localConformalVekuaTransportCoordinate]

include hb1 in
theorem localConformalVekuaTransportVector_continuous : Continuous (Y E b) :=
  continuous_vekuaTowerVector (circleTrace_smooth coords) (hardyTrace_continuous b hb1)

include hE hbn hb1 in
theorem localConformalVekuaTransportVector_periodic : Function.Periodic (Y E b) (2 * Real.pi) := by
  intro t
  apply lp.ext; funext n
  rw [localConformalVekuaTransportVector_coord coords E hE b hbn hb1,
    localConformalVekuaTransportVector_coord coords E hE b hbn hb1]
  simp  [localConformalVekuaTransportCoordinate,
    localConformalVekuaTraceRow_periodic coords (E : ℂ) b _ t]

theorem localConformalVekuaTransportVector_origin : Y E b 0 = ((H b) 0 / s₂) • basisVec 0 :=
  vekuaTowerVector_origin Γ E (H b)

include hE hbn hb1 in
theorem localConformalVekuaTransport_zeroCoeff (θ : ℝ) :
    (2 * (-(E : ℂ) / 4) * deriv Γ θ * U (E : ℂ) b 1 θ) / s₂ =
      (transportCoeff Γ E θ (Y E b θ) : ℕ → ℂ) 0 := by
  rw [transportCoeff_coord_zero, localConformalVekuaTransportVector_coord coords E hE b hbn hb1]
  simp only [localConformalVekuaTransportCoordinate, if_false, pow_one]
  change _ = physicalDrivenQ E * _
  rw [← physicalDrivenQ_sq hE]
  have hs : s₂ ^ 2 = 2 := by exact_mod_cast Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  grind

include hb1 in
theorem localConformalVekuaPositive_hasDerivAt (t : ℝ) :
    HasDerivAt (fun s => vekuaPositivePart (Y E b s))
      (vekuaPositivePart (transportCoeff Γ E t (Y E b t))) t :=
  hasDerivAt_vekuaTower_positive (circleTrace_smooth coords) (hardyTrace_continuous b hb1) t

end

section

variable (E : ℂ) (b : L2Z)
include E b

/-- Kernel inputs obtain the regularity needed by the actual transport
construction from the proved normalized-conormal smoothing formula. -/
theorem localConformalVekuaConormal_kernel_raw_H1 
    (hker : normalizedConormal (localConformalVelocityCircle_isWL1_half hR F hFs) (localConformalHardyPrimitiveMultiplier_isWL1 hR F hFs) (localConformalCenteredCircle_isWL1_half hR F hFs) E b = 0) :
    IsSobolevSeq 1 (fromL2 (1 / 2 : ℝ) b) :=
  normalizedConormal_kernel_raw_H1 (localConformalVelocityCircle_isWL1_half hR F hFs) (localConformalHardyPrimitiveMultiplier_isWL1 hR F hFs) (localConformalCenteredCircle_isWL1_half hR F hFs) E b hker

section

variable {F}
include coords

theorem localConformalVekuaTraceRow_continuous 
    (hbn : IsNonpositiveFourierSupport b)
    (hb1 : IsSobolevSeq 1 (fromL2 (1 / 2 : ℝ) b)) (n : ℕ) :
    Continuous (localConformalVekuaTraceRow coords E b n) := by
  have hp1 := localConformalHardyPrimitive_pow_raw_H1 coords.one_lt_radius F coords.smooth b hb1 n
  have hpn := localConformalHardyPrimitive_pow_nonpositive coords.one_lt_radius F coords.smooth coords.holomorphic b hbn n
  have hr := localConformalVekuaBoundary_raw_H1 coords E ((JF ^ n) b) hpn hp1
  have havg0 := isSobolevSeq_smul (Real.sqrt (2 * Real.pi) : ℂ)⁻¹ hr
  have havg : IsSobolevSeq 1 (normalizedHardyAverage (VB E ((JF ^ n) b))) := by
    assumption
  exact continuous_hardyFourierTrace (sq_tsum_norm_le (s := 0) (by norm_num)
    (by simpa using havg)).1

end

end


end PhysicalCoordinates

end PolyaNeumann

end
