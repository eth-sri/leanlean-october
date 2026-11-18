module

public import RequestProject.PhysicalDrivenHardyRegularity
public import RequestProject.PhysicalDrivenRowsReconstruction
public import RequestProject.LocalConformalVekuaConormalBridge

/-!
# Genuine H¹ realization and coordinate load of the driven observation kernel

Unifies the `L²` driven observation-kernel Hardy input `physicalDrivenKernelInput`,
coordinate trace reconstruction for `V_E b` and its companion `A_E b`, Fourier
tangential differentiation of the Vekua remainder, and the normalized conormal
identity `NCF E bF = Λ⁻¹ᐟ² (boundaryFourier (hg.toLp g))`.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace PolyaNeumann

open MeasureTheory Set Metric Filter
open scoped Topology ComplexConjugate InnerProductSpace

local instance : Fact (0 < 2 * Real.pi) := ⟨Real.two_pi_pos⟩

private theorem kernel_circle_coeff (H : C(AddCircle (2 * Real.pi), ℂ)) :
    fourierCoeff H = fourierCoeffOn Real.two_pi_pos
      (fun θ : ℝ => H (θ : AddCircle (2 * Real.pi))) := by
  funext n
  have he : AddCircle.liftIoc (2 * Real.pi) 0
      (fun θ : ℝ => H (θ : AddCircle (2 * Real.pi))) =
      (H : AddCircle (2 * Real.pi) → ℂ) := by
    funext q
    change H ((AddCircle.equivIoc (2 * Real.pi) 0 q : ℝ) : AddCircle (2 * Real.pi)) = H q
    have hrep : ((AddCircle.equivIoc (2 * Real.pi) 0 q : ℝ) : AddCircle (2 * Real.pi)) = q :=
      (AddCircle.equivIoc (2 * Real.pi) 0).symm_apply_apply q
    rw [hrep]
  have h := fourierCoeff_liftIoc_eq (T := 2 * Real.pi) (a := 0)
    (fun θ : ℝ => H (θ : AddCircle (2 * Real.pi))) n
  simpa only [he, zero_add] using h

private theorem kernel_volterra_eqOn {T : ℝ} {a f h : ℝ → ℂ}
    (he : EqOn f h (Icc 0 T)) (j : ℕ) :
    EqOn (volterraPrimitiveIterate a f j) (volterraPrimitiveIterate a h j) (Icc 0 T) := by
  induction j with
  | zero => exact he
  | succ j ih =>
    intro θ hθ
    refine intervalIntegral.integral_congr fun s hs => ?_
    rw [uIcc_of_le hθ.1] at hs
    rw [ih ⟨hs.1, hs.2.trans hθ.2⟩]

private def kernel_conormal_eval (n : ℤ) : BoundaryL2 →L[ℂ] ℂ :=
  (innerSL ℂ (stdBasisZ n)).comp boundaryFourier.toLinearIsometry.toContinuousLinearMap

private theorem kernel_conormal_eval_apply (n : ℤ) (v : BoundaryL2) :
    kernel_conormal_eval n v = boundaryFourier v n := by
  change ⟪stdBasisZ n, boundaryFourier v⟫_ℂ = _
  rw [stdBasisZ_apply, lp.inner_single_left]; simp

private theorem kernel_conormal_coeff_ae {f : ℝ → ℂ} (v : BoundaryL2)
    (hv : (v : ℝ → ℂ) =ᵐ[volume.restrict (Ioc 0 (2 * Real.pi))] f) (n : ℤ) :
    boundaryFourier v n = (Real.sqrt (2 * Real.pi) : ℂ) *
      fourierCoeffOn Real.two_pi_pos f n := by
  rw [boundaryFourier_apply, fourierCoeffOn_congr_ae Real.two_pi_pos hv]

/-- A boundary `L²` function with order-one coefficients equals its continuous
Fourier reconstruction almost everywhere. -/
theorem boundaryL2_ae_hardyFourierTrace_of_H1
    (v : BoundaryL2)
    (hv : IsSobolevSeq 1 (fourierCoeffOn Real.two_pi_pos (v : ℝ → ℂ))) :
    (v : ℝ → ℂ) =ᵐ[volume.restrict (Ioc 0 (2 * Real.pi))]
      hardyFourierTrace (fourierCoeffOn Real.two_pi_pos (v : ℝ → ℂ)) := by
  let c := fourierCoeffOn Real.two_pi_pos (v : ℝ → ℂ)
  have hc : Summable (fun n => ‖c n‖) :=
    (sq_tsum_norm_le (s := 0) (by norm_num) (by simpa using hv)).1
  let H := hardyCircleReconstruction c
  let f : ℝ → ℂ := fun θ => H (θ : AddCircle (2 * Real.pi))
  have hfm := continuousOn_memLp_boundary (H.continuous.comp (AddCircle.continuous_mk' _)).continuousOn
  let w : BoundaryL2 := hfm.toLp f
  have haw : (w : ℝ → ℂ) =ᵐ[volume.restrict (Ioc 0 (2 * Real.pi))] f := hfm.coeFn_toLp
  have hcoef : fourierCoeffOn Real.two_pi_pos (w : ℝ → ℂ) = c := by
    rw [fourierCoeffOn_congr_ae Real.two_pi_pos haw]
    change fourierCoeffOn Real.two_pi_pos (fun θ : ℝ => H (θ : AddCircle (2 * Real.pi))) = c
    rw [← kernel_circle_coeff, hardyCircleReconstruction_fourierCoeff hc]
  have he : v = w := boundaryFourier.injective <| lp.ext <| funext fun n => by
    rw [boundaryFourier_apply, boundaryFourier_apply, hcoef]
  rw [he, hcoef]
  filter_upwards [haw] with θ hθ
  exact hθ.trans (hardyCircleReconstruction_coe hc θ)

theorem normalizedHardyAverage_localConformalDiskHalfTrace
    {R : ℝ} (hR : 1 < R) (F : ℂ → ℂ)
    (hFs : ContDiffOn ℝ (⊤ : ℕ∞) F (ball (0 : ℂ) R))
    (hL : IsLipschitzDomain (F '' ball (0 : ℂ) 1))
    (u : NeumannH1 (F '' ball (0 : ℂ) 1)) :
    normalizedHardyAverage (localConformalDiskHalfTrace hR F hFs hL u) =
      fourierCoeffOn Real.two_pi_pos (localConformalDiskH1Trace hR F hFs hL u) := by
  have hs : (Real.sqrt (2 * Real.pi) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr Real.two_pi_pos).ne'
  funext n
  change (Real.sqrt (2 * Real.pi) : ℂ)⁻¹ *
    fromL2 (1 / 2 : ℝ) (localConformalDiskHalfTrace hR F hFs hL u) n = _
  rw [fromL2_half_localConformalDiskHalfTrace, boundaryFourier_apply,
    ← mul_assoc, inv_mul_cancel₀ hs, one_mul]

/-- The genuine normalized Hardy input of the driven kernel. -/
def physicalDrivenKernelInput
    {γ : ℝ → ℂ} {L : NNReal} (hγLip : LipschitzWith L γ) (hγ : ContDiff ℝ 1 γ)
    {E : ℝ} {W : ℝ → Ell2 →L[ℂ] Ell2} (hW : IsTransport γ E W)
    (g : ℝ → ℂ) (hg : MemLp g 2 (volume.restrict (Ioc 0 (2 * Real.pi))))
    (hO : observationAdj W g = 0) : L2Z :=
  (Real.sqrt (2 * Real.pi) : ℂ) • sobVec (1 / 2 : ℝ)
    (fourierCoeffOn Real.two_pi_pos (physicalDrivenPeriodicGauge γ E W g 0))
    (physicalDrivenPeriodicGauge_zero_isSobolevSeq_half hγLip hγ hW g hg hO)

theorem fromL2_physicalDrivenKernelInput
    {γ : ℝ → ℂ} {L : NNReal} (hγLip : LipschitzWith L γ) (hγ : ContDiff ℝ 1 γ)
    {E : ℝ} {W : ℝ → Ell2 →L[ℂ] Ell2} (hW : IsTransport γ E W)
    (g : ℝ → ℂ) (hg : MemLp g 2 (volume.restrict (Ioc 0 (2 * Real.pi))))
    (hO : observationAdj W g = 0) :
    fromL2 (1 / 2 : ℝ) (physicalDrivenKernelInput hγLip hγ hW g hg hO) =
      (Real.sqrt (2 * Real.pi) : ℂ) •
        fourierCoeffOn Real.two_pi_pos (physicalDrivenPeriodicGauge γ E W g 0) := by
  rw [physicalDrivenKernelInput, fromL2_smul, fromL2_sobVec]

theorem fromL2_physicalDrivenKernelInput_isSobolevSeq_one
    {γ : ℝ → ℂ} {L : NNReal} (hγLip : LipschitzWith L γ) (hγ : ContDiff ℝ 1 γ)
    {E : ℝ} {W : ℝ → Ell2 →L[ℂ] Ell2} (hW : IsTransport γ E W)
    (g : ℝ → ℂ) (hg : MemLp g 2 (volume.restrict (Ioc 0 (2 * Real.pi))))
    (hO : observationAdj W g = 0) :
    IsSobolevSeq 1 (fromL2 (1 / 2 : ℝ)
      (physicalDrivenKernelInput hγLip hγ hW g hg hO)) := by
  rw [fromL2_physicalDrivenKernelInput]
  exact isSobolevSeq_smul _ (physicalDrivenPeriodicGauge_zero_isSobolevSeq_one hγLip hγ hW g hg hO)

theorem hardyFourierTrace_physicalDrivenKernelInput
    {γ : ℝ → ℂ} {L : NNReal} (hγLip : LipschitzWith L γ) (hγ : ContDiff ℝ 1 γ)
    {E : ℝ} {W : ℝ → Ell2 →L[ℂ] Ell2} (hW : IsTransport γ E W)
    (g : ℝ → ℂ) (hg : MemLp g 2 (volume.restrict (Ioc 0 (2 * Real.pi))))
    (hO : observationAdj W g = 0) (θ : ℝ) :
    hardyFourierTrace (normalizedHardyAverage
      (physicalDrivenKernelInput hγLip hγ hW g hg hO)) θ =
      physicalDrivenPeriodicGauge γ E W g 0 θ := by
  have hs : (Real.sqrt (2 * Real.pi) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr Real.two_pi_pos).ne'
  have havg : normalizedHardyAverage (physicalDrivenKernelInput hγLip hγ hW g hg hO) =
      fourierCoeffOn Real.two_pi_pos (physicalDrivenPeriodicGauge γ E W g 0) := by
    change (Real.sqrt (2 * Real.pi) : ℂ)⁻¹ •
      fromL2 (1 / 2 : ℝ) (physicalDrivenKernelInput hγLip hγ hW g hg hO) = _
    rw [fromL2_physicalDrivenKernelInput, smul_smul, inv_mul_cancel₀ hs, one_smul]
  let H : C(AddCircle (2 * Real.pi), ℂ) :=
    ⟨AddCircle.liftIco (2 * Real.pi) 0 (physicalDrivenGauge γ E (physicalDrivenVector W g) 0), by
      obtain ⟨h0, hL⟩ := physicalDrivenGauge_actual_endpoints γ E W g hO 0
      exact AddCircle.liftIco_zero_continuous (h0.trans hL.symm)
        (physicalDrivenGauge_continuousOn γ hγ.continuous E _
          (physicalDrivenVector_continuousOn_of_intervalIntegrable hW.1 g
            (intervalIntegrable_boundary_of_memLp g hg)) 0)⟩
  have hcoef : fourierCoeff H =
      fourierCoeffOn Real.two_pi_pos (physicalDrivenPeriodicGauge γ E W g 0) :=
    kernel_circle_coeff H
  have hsum : Summable (fun n => ‖fourierCoeff H n‖) := by
    rw [hcoef]
    exact (sq_tsum_norm_le (s := 0) (by norm_num) (by
      simpa only [zero_add] using
        physicalDrivenPeriodicGauge_zero_isSobolevSeq_one hγLip hγ hW g hg hO)).1
  rw [havg, ← hcoef]
  exact hardyFourierTrace_fourierCoeff H hsum θ

section CoordinateTerms

variable {R C K : ℝ} (hR : 1 < R) (F : ℂ → ℂ)
    (hFs : ContDiffOn ℝ (⊤ : ℕ∞) F (ball (0 : ℂ) R))
    (hb : Bornology.IsBounded (F '' ball (0 : ℂ) 1))
    (hL : IsLipschitzDomain (F '' ball (0 : ℂ) 1))
    (hhol : DifferentiableOn ℂ F (ball (0 : ℂ) 1))
    (hinj : InjOn F (ball (0 : ℂ) 1))
    (hC : ∀ z ∈ ball (0 : ℂ) 1, 1 ≤ C * ‖deriv F z‖ ^ 2)
    (hK : ∀ z ∈ ball (0 : ℂ) 1, ‖fderiv ℝ F z 1‖ ≤ K)
    (e : OpenPartialHomeomorph ℂ ℂ) (he : (e : ℂ → ℂ) = F)
    (hsource : closedBall (0 : ℂ) 1 ⊆ e.source)
    (hes : ContDiffOn ℝ (⊤ : ℕ∞) e.symm e.target)

local notation "ΩF" => F '' ball (0 : ℂ) 1
local notation "ΓF" => physicalCircleTrace F
local notation "hΓF" => contDiff_physicalCircleTrace_of_neighborhood hR F
  (hFs.of_le (by simp))
local notation "UF" => localConformalHardyH1Extension hR F hFs hb hL hhol hinj hC hK e he hsource hes
local notation "JF" => localConformalHardyPrimitive hR F hFs
local notation "MF" => neumannH1AffineMultiplier hb (F 1)
local notation "TF" => localConformalDiskH1Trace hR F hFs hL
local notation "QF" => localConformalDiskHalfTrace hR F hFs hL
local notation "VF" => localConformalVekuaH1 hR F hFs hb hL hhol hinj hC hK e he hsource hes
local notation "AF" => localConformalVekuaGradientA hR F hFs hb hL hhol hinj hC hK e he hsource hes
local notation "BF" => localConformalVekuaGradientB hR F hFs hb hL hhol hinj hC hK e he hsource hes
local notation "RF" => localConformalVekuaRemainder hR F hFs hb hL hhol hinj hC hK e he hsource hes
local notation "VelF" => boundaryContinuousMultiplier (localConformalVelocityCircle F)
local notation "BarVelF" => boundaryContinuousMultiplier (localConformalPrimitiveCircle F)
local notation "hβF" => localConformalVelocityCircle_isWL1_half hR F hFs
local notation "haF" => localConformalHardyPrimitiveMultiplier_isWL1 hR F hFs
local notation "hgF" => localConformalCenteredCircle_isWL1_half hR F hFs
local notation "NCF" => normalizedConormal hβF haF hgF

private theorem kernel_conormal_primitive_H1 (b : L2Z)
    (hb1 : IsSobolevSeq 1 (fromL2 (1 / 2 : ℝ) b)) (j : ℕ) :
    IsSobolevSeq 1 (normalizedHardyAverage ((JF ^ j) b)) := by
  rw [normalizedHardyAverage_localConformalHardyPrimitive_pow]
  exact (antiPrimIter_bound (by norm_num : (0 : ℝ) ≤ 1)
    (physicalCircleTrace_fourier_weights_of_smooth_neighborhood hR F hFs).1
    (isSobolevSeq_smul _ hb1) j).1

private theorem kernel_conormal_primitive_raw_H1 (b : L2Z)
    (hb1 : IsSobolevSeq 1 (fromL2 (1 / 2 : ℝ) b)) (j : ℕ) :
    IsSobolevSeq 1 (fromL2 (1 / 2 : ℝ) ((JF ^ j) b)) := by
  rw [fromL2_localConformalHardyPrimitive_pow]
  exact (antiPrimIter_bound (by norm_num : (0 : ℝ) ≤ 1)
    (physicalCircleTrace_fourier_weights_of_smooth_neighborhood hR F hFs).1 hb1 j).1

theorem localConformalVekua_coordinate_trace_reconstruction_ae (E : ℂ) (b : L2Z)
    (hbn : IsNonpositiveFourierSupport b)
    (hb1 : IsSobolevSeq 1 (fromL2 (1 / 2 : ℝ) b)) :
    (TF (VF (F 1) E b) : ℝ → ℂ)
      =ᵐ[volume.restrict (Ioc 0 (2 * Real.pi))]
        hardyFourierTrace (normalizedHardyAverage
          (localConformalVekuaBoundary hR F hFs hb hL hhol hinj hC hK
            e he hsource hes E b)) := by
  have hreg := localConformalVekuaBoundary_raw_H1 hR F hFs hb hL hhol hinj hC hK
    e he hsource hes E b hbn hb1
  have hcoef := normalizedHardyAverage_localConformalDiskHalfTrace hR F hFs hL (VF (F 1) E b)
  change normalizedHardyAverage
      (localConformalVekuaBoundary hR F hFs hb hL hhol hinj hC hK e he hsource hes E b) =
    fourierCoeffOn Real.two_pi_pos (TF (VF (F 1) E b)) at hcoef
  have ht := boundaryL2_ae_hardyFourierTrace_of_H1 (TF (VF (F 1) E b))
    (by rw [← hcoef]; exact isSobolevSeq_smul _ hreg)
  rwa [← hcoef] at ht

theorem localConformalHardy_affine_primitive_trace_ae (b : L2Z)
    (hbn : IsNonpositiveFourierSupport b)
    (hb1 : IsSobolevSeq 1 (fromL2 (1 / 2 : ℝ) b)) (j k : ℕ) :
    (TF ((MF ^ j) (UF ((JF ^ k) b))) : ℝ → ℂ)
      =ᵐ[volume.restrict (Ioc 0 (2 * Real.pi))]
        fun θ => (ΓF θ - F 1) ^ j *
          hardyFourierTrace (normalizedHardyAverage ((JF ^ k) b)) θ := by
  have hnk := localConformalHardyPrimitive_pow_nonpositive hR F hFs hhol b hbn k
  have hc : normalizedHardyAverage (QF (UF ((JF ^ k) b))) =
      normalizedHardyAverage ((JF ^ k) b) := by
    rw [localConformalDiskHalfTrace_hardyExtension_eq_of_nonpositive hR F hFs hb hL
      hhol hinj hC hK e he hsource hes _ hnk]
  have hcoef := normalizedHardyAverage_localConformalDiskHalfTrace hR F hFs hL (UF ((JF ^ k) b))
  rw [hc] at hcoef
  have hu := boundaryL2_ae_hardyFourierTrace_of_H1 (TF (UF ((JF ^ k) b)))
    (by rw [← hcoef]; exact kernel_conormal_primitive_H1 hR F hFs b hb1 k)
  rw [← hcoef] at hu
  rw [localConformalDiskH1Trace_affineMultiplier_pow hR F hFs hb hL hhol hinj hC]
  filter_upwards [hu, boundaryContinuousMultiplier_ae
    ((localConformalCenteredCircle hR F hFs) ^ j) (TF (UF ((JF ^ k) b)))] with θ hu hm
  rw [hm, hu]
  simp only [ContinuousMap.pow_apply, localConformalCenteredCircle_apply, physicalCircleTrace]

theorem kernel_conormal_primitive_deriv (hhol : DifferentiableOn ℂ F (ball (0 : ℂ) 1))
    (b : L2Z) (hbn : IsNonpositiveFourierSupport b)
    (hb1 : IsSobolevSeq 1 (fromL2 (1 / 2 : ℝ) b)) (j : ℕ) (θ : ℝ) :
    HasDerivAt (hardyFourierTrace (normalizedHardyAverage ((JF ^ (j + 1)) b)))
      (conj (deriv ΓF θ) *
        hardyFourierTrace (normalizedHardyAverage ((JF ^ j) b)) θ) θ := by
  have hnorm : IsSobolevSeq 1 (normalizedHardyAverage b) :=
    isSobolevSeq_smul (Real.sqrt (2 * Real.pi) : ℂ)⁻¹ hb1
  have hder := hasDerivAt_hardyFourierTrace_antiPrimIter_succ
    (localConformalPrimitiveCircle F)
    (by rw [localConformalPrimitiveCircle_coeff hR F hFs]
        exact (physicalCircleTrace_fourier_weights_of_smooth_neighborhood hR F hFs).1)
    hnorm
    (by rw [localConformalPrimitiveCircle_coeff hR F hFs]
        exact localConformalHardyPrimitiveMultiplier_strictNegative hR F hFs hhol)
    (fun n hn => by simp [normalizedHardyAverage, fromL2, hbn n hn]) j θ
  rwa [localConformalPrimitiveCircle_coeff hR F hFs,
    ← normalizedHardyAverage_localConformalHardyPrimitive_pow hR F hFs (j + 1) b,
    ← normalizedHardyAverage_localConformalHardyPrimitive_pow hR F hFs j b,
    localConformalPrimitiveCircle_apply hR F hFs] at hder

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
      (by simpa using kernel_conormal_primitive_H1 hR F hFs b hb1 k)).1
  have hd (θ : ℝ) : HasDerivAt f (d θ) θ := by
    have hg := ((hΓF).differentiable (by simp) θ).hasDerivAt.sub_const (F 1)
    convert (hg.pow (j + 1)).mul
      (kernel_conormal_primitive_deriv hR F hFs hhol b hbn hb1 j θ) using 1
    dsimp only [f, d, hj]; simp only [Nat.add_sub_cancel, Pi.pow_apply]; ring_nf
  have hdc : Continuous d :=
    (((continuous_const.mul (hΓF).continuous_deriv_one).mul
      (((hΓF).continuous.sub continuous_const).pow j |>.mul (hc (j + 1)))).add
      ((Complex.continuous_conj.comp (hΓF).continuous_deriv_one).mul
        (((hΓF).continuous.sub continuous_const).pow (j + 1) |>.mul (hc j))))
  have hf1 : ContDiff ℝ 1 f := contDiff_one_iff_deriv.mpr
    ⟨fun θ => (hd θ).differentiableAt, by
      rw [show deriv f = d from funext fun θ => (hd θ).deriv]; exact hdc⟩
  have hp : f 0 = f (2 * Real.pi) := by
    have hΓ := physicalCircleTrace_periodic F 0
    have hh := hardyFourierTrace_periodic (normalizedHardyAverage ((JF ^ (j + 1)) b)) 0
    simp only [zero_add] at hΓ hh
    dsimp only [f, hj]; rw [hΓ, hh]
  have hibp := fourierCoeffOn_of_ac_ae_hasDerivAt (c1_absolutelyContinuousOnInterval hf1)
    (continuousOn_memLp_boundary hdc.continuousOn) (Eventually.of_forall fun θ _ => hd θ) hp n
  have hv := localConformalHardy_affine_primitive_trace_ae hR F hFs hb hL hhol hinj
    hC hK e he hsource hes b hbn hb1 (j + 1) (j + 1)
  let v : BoundaryL2 :=
    (((j + 1 : ℕ) : ℂ) • VelF (TF ((MF ^ j) (UF ((JF ^ (j + 1)) b))))) +
      BarVelF (TF ((MF ^ (j + 1)) (UF ((JF ^ j) b))))
  have hdv : (v : ℝ → ℂ) =ᵐ[volume.restrict (Ioc 0 (2 * Real.pi))] d := by
    filter_upwards [Lp.coeFn_add
        (((j + 1 : ℕ) : ℂ) • VelF (TF ((MF ^ j) (UF ((JF ^ (j + 1)) b)))))
        (BarVelF (TF ((MF ^ (j + 1)) (UF ((JF ^ j) b))))),
      Lp.coeFn_smul ((j + 1 : ℕ) : ℂ) (VelF (TF ((MF ^ j) (UF ((JF ^ (j + 1)) b))))),
      boundaryContinuousMultiplier_ae (localConformalVelocityCircle F)
        (TF ((MF ^ j) (UF ((JF ^ (j + 1)) b)))),
      boundaryContinuousMultiplier_ae (localConformalPrimitiveCircle F)
        (TF ((MF ^ (j + 1)) (UF ((JF ^ j) b)))),
      localConformalHardy_affine_primitive_trace_ae hR F hFs hb hL hhol hinj
        hC hK e he hsource hes b hbn hb1 j (j + 1),
      localConformalHardy_affine_primitive_trace_ae hR F hFs hb hL hhol hinj
        hC hK e he hsource hes b hbn hb1 (j + 1) j] with θ ha hs hβ hα hx hy
    dsimp only [v]
    rw [ha, Pi.add_apply, hs]
    simp only [Pi.smul_apply, smul_eq_mul, hβ, hα, hx, hy,
      localConformalVelocityCircle_apply hR F hFs,
      localConformalPrimitiveCircle_apply hR F hFs, d, hj]
    ring
  change Complex.I * (n : ℂ) * boundaryFourier
      (TF ((MF ^ (j + 1)) (UF ((JF ^ (j + 1)) b)))) n = boundaryFourier v n
  rw [kernel_conormal_coeff_ae _ hv n, kernel_conormal_coeff_ae v hdv n, hibp]
  ring

theorem localConformalVekuaRemainder_fourier_derivative (E : ℂ) (b : L2Z)
    (hbn : IsNonpositiveFourierSupport b)
    (hb1 : IsSobolevSeq 1 (fromL2 (1 / 2 : ℝ) b)) (n : ℤ) :
    (Complex.I * (n : ℂ)) * boundaryFourier (TF (RF (F 1) E b)) n =
      boundaryFourier (VelF (TF (AF (F 1) E b)) +
        BarVelF (TF (BF (F 1) E b))) n := by
  let P := (VelF).comp TF
  let Q := (BarVelF).comp TF
  have hl := ((kernel_conormal_eval n).hasSum
    ((TF).hasSum (localConformalVekuaRemainder_hasSum hR F hFs hb hL hhol hinj hC hK
      e he hsource hes (F 1) E b))).mul_left (Complex.I * (n : ℂ))
  have hr := (kernel_conormal_eval n).hasSum
    ((P.hasSum (localConformalVekuaGradientA_hasSum hR F hFs hb hL hhol hinj hC hK
      e he hsource hes (F 1) E b)).add
      (Q.hasSum (localConformalVekuaGradientB_hasSum hR F hFs hb hL hhol hinj hC hK
        e he hsource hes (F 1) E b)))
  have heq (j : ℕ) :
      (Complex.I * (n : ℂ)) * kernel_conormal_eval n
          (TF (physicalVekuaCoeff E (j + 1) • ((MF ^ (j + 1)) (UF ((JF ^ (j + 1)) b))))) =
        kernel_conormal_eval n
          (P ((physicalVekuaCoeff E (j + 1) * ((j + 1 : ℕ) : ℂ)) •
              ((MF ^ j) (UF ((JF ^ (j + 1)) b)))) +
            Q (physicalVekuaCoeff E (j + 1) • ((MF ^ (j + 1)) (UF ((JF ^ j) b))))) := by
    simp only [kernel_conormal_eval_apply, P, Q, ContinuousLinearMap.comp_apply,
      map_add, map_smul, smul_eq_mul]
    have hterm := localConformalVekua_trace_term_fourier_derivative hR F hFs hb hL
      hhol hinj hC hK e he hsource hes b hbn hb1 j n
    simp only [map_add, map_smul, lp.coeFn_add, Pi.add_apply, lp.coeFn_smul,
      Pi.smul_apply, smul_eq_mul] at hterm
    calc
      _ = physicalVekuaCoeff E (j + 1) *
          ((Complex.I * (n : ℂ)) *
            boundaryFourier (TF ((MF ^ (j + 1)) (UF ((JF ^ (j + 1)) b)))) n) := by ring
      _ = _ := by rw [hterm]; ring
  have hl' : HasSum (fun j : ℕ => kernel_conormal_eval n
      (P ((physicalVekuaCoeff E (j + 1) * ((j + 1 : ℕ) : ℂ)) •
          ((MF ^ j) (UF ((JF ^ (j + 1)) b)))) +
        Q (physicalVekuaCoeff E (j + 1) • ((MF ^ (j + 1)) (UF ((JF ^ j) b))))))
      ((Complex.I * (n : ℂ)) * boundaryFourier (TF (RF (F 1) E b)) n) := by
    simpa only [kernel_conormal_eval_apply] using hl.congr_fun fun j => (heq j).symm
  exact hl'.unique (by
    simpa only [P, Q, ContinuousLinearMap.comp_apply, kernel_conormal_eval_apply] using hr)

private theorem kernel_conormal_principal_coeff (b : L2Z)
    (hbn : IsNonpositiveFourierSupport b) (n : ℤ) :
    normalizedConormalPrincipal b n =
      ((sobWeight n ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
        (-(n : ℂ) * fromL2 (1 / 2 : ℝ) b n) := by
  by_cases hn : 0 < n
  · simp only [normalizedConormal_principal_apply, hbn n hn, mul_zero, fromL2]
  · have habs : |(n : ℝ)| = -(n : ℝ) := abs_of_nonpos (by exact_mod_cast le_of_not_gt hn)
    rw [normalizedConormal_principal_apply, fromL2]
    have hw : sobWeight n ^ (-(1 / 2 : ℝ)) * sobWeight n ^ (-(1 / 2 : ℝ)) = (sobWeight n)⁻¹ := by
      rw [← Real.rpow_add (sobWeight_pos n),
        show -(1 / 2 : ℝ) + -(1 / 2 : ℝ) = -1 by ring, Real.rpow_neg_one]
    rw [show ((|(n : ℝ)| / (1 + |(n : ℝ)|) : ℝ) : ℂ) = -(n : ℂ) * ((sobWeight n)⁻¹ : ℝ) by
      rw [habs, sobWeight, habs]; push_cast; ring]
    calc
      _ = -(n : ℂ) * ((((sobWeight n ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
          ((sobWeight n ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)) * b n) := by
        rw [← Complex.ofReal_mul, hw]; ring
      _ = _ := by ring

theorem localConformalVekua_normalizedConormal_fourier (E : ℂ) (b : L2Z)
    (hbn : IsNonpositiveFourierSupport b)
    (hb1 : IsSobolevSeq 1 (fromL2 (1 / 2 : ℝ) b)) (n : ℤ) :
    NCF E b n = ((sobWeight n ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
      (-(n : ℂ) * boundaryFourier (TF (VF (F 1) E b)) n -
        2 * Complex.I * boundaryFourier (VelF (TF (AF (F 1) E b))) n) := by
  have hrem := localConformalVekuaCoordinateConormalRemainder_eq_conormalRemOp
    hR F hFs hb hL hhol hinj hC hK e he hsource hes E b hbn
  have hdiff := localConformalVekuaRemainder_fourier_derivative hR F hFs hb hL hhol hinj
    hC hK e he hsource hes E b hbn hb1 n
  have hbase : boundaryFourier (TF (UF b)) = fromL2 (1 / 2 : ℝ) b := by
    rw [← fromL2_half_localConformalDiskHalfTrace,
      localConformalDiskHalfTrace_hardyExtension_eq_of_nonpositive hR F hFs hb hL hhol
        hinj hC hK e he hsource hes b hbn]
  simp only [localConformalVekuaRemainder_apply, map_sub, lp.coeFn_sub,
    Pi.sub_apply, map_add, lp.coeFn_add, Pi.add_apply] at hdiff
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
  have hpow : sobWeight n ^ ((-1 : ℝ) / 2) = sobWeight n ^ (-(1 / 2 : ℝ)) := by congr 1; ring
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply,
    map_smul, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]
  ring_nf at hdiff' ⊢
  rw [hpow]
  linear_combination -((sobWeight n ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * hdiff'

end CoordinateTerms

section DrivenCoordinates

variable {R C K : ℝ} (hR : 1 < R) (F : ℂ → ℂ)
    (hFs : ContDiffOn ℝ (⊤ : ℕ∞) F (ball (0 : ℂ) R))
    (hb : Bornology.IsBounded (F '' ball (0 : ℂ) 1))
    (hL : IsLipschitzDomain (F '' ball (0 : ℂ) 1))
    (hhol : DifferentiableOn ℂ F (ball (0 : ℂ) 1))
    (hinj : InjOn F (ball (0 : ℂ) 1))
    (hC : ∀ z ∈ ball (0 : ℂ) 1, 1 ≤ C * ‖deriv F z‖ ^ 2)
    (hK : ∀ z ∈ ball (0 : ℂ) 1, ‖fderiv ℝ F z 1‖ ≤ K)
    (e : OpenPartialHomeomorph ℂ ℂ) (he : (e : ℂ → ℂ) = F)
    (hsource : closedBall (0 : ℂ) 1 ⊆ e.source)
    (hes : ContDiffOn ℝ (⊤ : ℕ∞) e.symm e.target)
    {L : NNReal} (hΓLip : LipschitzWith L (physicalCircleTrace F))
    {E : ℝ} (hE : 0 < E)
    {W : ℝ → Ell2 →L[ℂ] Ell2} (hW : IsTransport (physicalCircleTrace F) E W)
    (g : ℝ → ℂ) (hg : MemLp g 2 (volume.restrict (Ioc 0 (2 * Real.pi))))
    (hO : observationAdj W g = 0)

local notation "ΓF" => physicalCircleTrace F
local notation "hΓF" => contDiff_physicalCircleTrace_of_neighborhood hR F
  (hFs.of_le (by simp))
local notation "bF" => physicalDrivenKernelInput hΓLip hΓF hW g hg hO
local notation "JF" => localConformalHardyPrimitive hR F hFs
local notation "TF" => localConformalDiskH1Trace hR F hFs hL
local notation "VF" => localConformalVekuaH1 hR F hFs hb hL hhol hinj hC hK e he hsource hes
local notation "AF" => localConformalVekuaGradientA hR F hFs hb hL hhol hinj hC hK e he hsource hes
local notation "hβF" => localConformalVelocityCircle_isWL1_half hR F hFs
local notation "haF" => localConformalHardyPrimitiveMultiplier_isWL1 hR F hFs
local notation "hgF" => localConformalCenteredCircle_isWL1_half hR F hFs
local notation "NCF" => normalizedConormal hβF haF hgF

include hb hL hhol hC e he hsource hE in
theorem physicalDrivenKernelInput_nonpositive : IsNonpositiveFourierSupport bF := by
  have hinjc : InjOn F (closedBall (0 : ℂ) 1) := fun z hz w hw hzw =>
    e.injOn (hsource hz) (hsource hw) (by simpa only [he] using hzw)
  have hnz : ∀ z ∈ closedBall (0 : ℂ) 1, fderiv ℝ F z 1 ≠ 0 := by
    have hc : ContinuousOn (fun z => C * ‖fderiv ℝ F z 1‖ ^ 2) (closedBall (0 : ℂ) 1) :=
      (continuousOn_const.mul
        ((((hFs.continuousOn_fderiv_of_isOpen isOpen_ball (by simp)).clm_apply
          continuousOn_const).norm).pow 2)).mono (closedBall_subset_ball hR)
    have hle : ∀ z ∈ ball (0 : ℂ) 1, (1 : ℝ) ≤ C * ‖fderiv ℝ F z 1‖ ^ 2 := fun z hz => by
      have hfd : fderiv ℝ F z 1 = deriv F z := by
        rw [(hhol.differentiableAt (isOpen_ball.mem_nhds hz)).fderiv_restrictScalars ℝ]
        change fderiv ℂ F z 1 = _; rw [fderiv_eq_deriv_mul, mul_one]
      rw [hfd]; exact hC z hz
    intro z hz hzero
    have hbound : (1 : ℝ) ≤ C * ‖fderiv ℝ F z 1‖ ^ 2 :=
      le_on_closure hle continuousOn_const
        (by simpa only [closure_ball (0 : ℂ) (by norm_num : (1 : ℝ) ≠ 0)] using hc)
        (by simpa only [closure_ball (0 : ℂ) (by norm_num : (1 : ℝ) ≠ 0)] using hz)
    norm_num [hzero] at hbound
  have hs := localConformal_physicalDrivenGauge_nonpositive_of_memLp hb hL hR F hFs
    hhol hinjc hnz rfl hΓLip hE hW g hg hO 0
  intro n hn
  simp only [physicalDrivenKernelInput, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul,
    sobVec_apply, hs n hn, mul_zero]

include hE in
/-- Unified coordinate trace identification for `(JF ^ k) bF` (`k = 0` gives
`VF (F 1) E bF` and `k = 1` gives `AF (F 1) E bF`). -/
private theorem physicalDrivenKernelH1_scaledRow_trace_ae (k : ℕ) :
    (((-(E : ℂ) / 4) ^ k • TF (VF (F 1) (E : ℂ) ((JF ^ k) bF)) : BoundaryL2) : ℝ → ℂ)
      =ᵐ[volume.restrict (Ioc 0 (2 * Real.pi))]
        physicalDrivenScaledRow E (physicalDrivenVector W g) k := by
  have hbn := physicalDrivenKernelInput_nonpositive hR F hFs hb hL hhol hC
    e he hsource hΓLip hE hW g hg hO
  have hb1 := fromL2_physicalDrivenKernelInput_isSobolevSeq_one hΓLip hΓF hW g hg hO
  have hJbn := localConformalHardyPrimitive_pow_nonpositive hR F hFs hhol bF hbn k
  have hJ1 := kernel_conormal_primitive_raw_H1 hR F hFs bF hb1 k
  have ht := localConformalVekua_coordinate_trace_reconstruction_ae hR F hFs hb hL
    hhol hinj hC hK e he hsource hes (E : ℂ) ((JF ^ k) bF) hJbn hJ1
  have hprim : EqOn
      (hardyFourierTrace (normalizedHardyAverage ((JF ^ k) bF)))
      (volterraPrimitiveIterate (fun s => star (deriv ΓF s))
        (physicalDrivenGauge ΓF E (physicalDrivenVector W g) 0) k)
      (Icc 0 (2 * Real.pi)) := fun θ hθ => by
    rw [localConformalHardyPrimitive_pow_volterra_of_H1 hR F hFs hhol bF hbn
      (isSobolevSeq_smul _ hb1) k θ]
    exact kernel_volterra_eqOn (fun s hs => by
      rw [hardyFourierTrace_physicalDrivenKernelInput,
        physicalDrivenPeriodicGauge_eqOn _ E W g hO 0 hs]) k hθ
  filter_upwards [Lp.coeFn_smul ((-(E : ℂ) / 4) ^ k) (TF (VF (F 1) (E : ℂ) ((JF ^ k) bF))),
    ht, ae_restrict_mem measurableSet_Ioc] with θ hsm htθ hθ
  have hθc := Ioc_subset_Icc_self hθ
  rw [hsm, Pi.smul_apply, smul_eq_mul, htθ,
    ← (localConformalVekuaBoundary_average_volterra_hasSum_of_H1 hR F hFs hb hL hhol hinj
      hC hK e he hsource hes (E : ℂ) ((JF ^ k) bF) hJbn hJ1 θ).tsum_eq,
    physicalDrivenScaledRow_eq_volterraVekua_of_intervalIntegrable hΓLip hΓF hE.le hW g
      (intervalIntegrable_boundary_of_memLp g hg) k hθc]
  congr 1
  refine tsum_congr fun j => ?_
  rw [kernel_volterra_eqOn hprim j hθc]
  simp [physicalDrivenCentered, physicalCircleTrace, circleMap_zero]

include hb hL hhol hinj hC hK e he hsource hes hE in
theorem physicalDrivenKernelH1_normalizedConormal_eq_coordinateLoad :
    NCF (E : ℂ) bF = sobolevSmoothing (1 / 2 : ℝ) (by norm_num)
      (boundaryFourier (hg.toLp g)) := by
  have hbn := physicalDrivenKernelInput_nonpositive hR F hFs hb hL hhol hC
    e he hsource hΓLip hE hW g hg hO
  have hb1 := fromL2_physicalDrivenKernelInput_isSobolevSeq_one hΓLip hΓF hW g hg hO
  let A : BoundaryL2 := boundaryContinuousMultiplier (localConformalVelocityCircle F)
    (TF (AF (F 1) (E : ℂ) bF))
  have hA1 := physicalDrivenKernelH1_scaledRow_trace_ae hR F hFs hb hL hhol hinj hC hK
    e he hsource hes hΓLip hE hW g hg hO 1
  rw [pow_one, pow_one, ← map_smul, ← localConformalVekuaGradientA_apply] at hA1
  have hA : (A : ℝ → ℂ) =ᵐ[volume.restrict (Ioc 0 (2 * Real.pi))]
      fun θ => deriv ΓF θ * physicalDrivenScaledRow E (physicalDrivenVector W g) 1 θ := by
    filter_upwards [boundaryContinuousMultiplier_ae (localConformalVelocityCircle F)
      (TF (AF (F 1) (E : ℂ) bF)), hA1] with θ hm hr
    rw [hm, hr, localConformalVelocityCircle_apply hR F hFs]
  let d : BoundaryL2 := (2 : ℂ) • A - Complex.I • hg.toLp g
  have hd : (d : ℝ → ℂ) =ᵐ[volume.restrict (Ioc 0 (2 * Real.pi))]
      fun θ => 2 * deriv ΓF θ * physicalDrivenScaledRow E (physicalDrivenVector W g) 1 θ -
        Complex.I * g θ := by
    filter_upwards [Lp.coeFn_sub ((2 : ℂ) • A) (Complex.I • hg.toLp g),
      Lp.coeFn_smul (2 : ℂ) A, Lp.coeFn_smul Complex.I (hg.toLp g), hA, hg.coeFn_toLp]
      with θ hs h2 hi hAθ hgθ
    rw [hs, Pi.sub_apply, h2, hi]
    simp only [Pi.smul_apply, smul_eq_mul, hAθ, hgθ]; ring
  have ht0 := physicalDrivenKernelH1_scaledRow_trace_ae hR F hFs hb hL hhol hinj hC hK
    e he hsource hes hΓLip hE hW g hg hO 0
  simp only [pow_zero, one_smul, ContinuousLinearMap.one_apply,
    show physicalDrivenScaledRow E (physicalDrivenVector W g) 0 =
      physicalDrivenRow (physicalDrivenVector W g) 0 from
      funext fun _ => by simp [physicalDrivenScaledRow]] at ht0
  have hd_mem : MemLp (fun θ => 2 * deriv ΓF θ *
      physicalDrivenScaledRow E (physicalDrivenVector W g) 1 θ - Complex.I * g θ)
      2 (volume.restrict (Ioc 0 (2 * Real.pi))) := by
    have hy := physicalDrivenVector_continuousOn_of_intervalIntegrable hW.1 g
      (intervalIntegrable_boundary_of_memLp g hg)
    exact (continuousOn_memLp_boundary
      ((continuousOn_const.mul (hΓF).continuous_deriv_one.continuousOn).mul
        (continuousOn_const.mul (physicalDrivenRow_continuousOn _ hy 1)))).sub
      (hg.const_mul Complex.I)
  apply lp.ext; funext n
  have hf := fourierCoeffOn_of_ac_ae_hasDerivAt
    (physicalDrivenScaledRow_absolutelyContinuous_of_intervalIntegrable hΓLip hW g
      (intervalIntegrable_boundary_of_memLp g hg) 0)
    hd_mem
    (physicalDrivenScaledRow_zero_ae_hasDerivAt_of_intervalIntegrable hΓLip hΓF hW g
      (intervalIntegrable_boundary_of_memLp g hg))
    (by simp [physicalDrivenScaledRow, physicalDrivenRow,
      physicalDrivenVector_zero, physicalDrivenVector_endpoint W g hO]) n
  rw [show physicalDrivenScaledRow E (physicalDrivenVector W g) 0 =
    physicalDrivenRow (physicalDrivenVector W g) 0 from
      funext fun _ => by simp [physicalDrivenScaledRow]] at hf
  have hf' : boundaryFourier d n = (Complex.I * (n : ℂ)) *
      boundaryFourier (TF (VF (F 1) (E : ℂ) bF)) n := by
    rw [kernel_conormal_coeff_ae d hd n,
      kernel_conormal_coeff_ae (TF (VF (F 1) (E : ℂ) bF)) ht0 n, hf]; ring
  simp only [d, map_sub, map_smul, lp.coeFn_sub, Pi.sub_apply, lp.coeFn_smul,
    Pi.smul_apply, smul_eq_mul] at hf'
  have hi := congrArg (fun z : ℂ => Complex.I * z) hf'
  simp only [mul_sub, ← mul_assoc, Complex.I_mul_I, neg_one_mul] at hi
  rw [localConformalVekua_normalizedConormal_fourier hR F hFs hb hL hhol hinj hC hK
    e he hsource hes (E : ℂ) bF hbn hb1 n]
  change _ = ((sobWeight n ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * boundaryFourier (hg.toLp g) n
  dsimp only [A] at hi
  linear_combination -((sobWeight n ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * hi

end DrivenCoordinates

end PolyaNeumann

end
