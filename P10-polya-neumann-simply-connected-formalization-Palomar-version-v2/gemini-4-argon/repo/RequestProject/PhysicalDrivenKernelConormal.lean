module

public import RequestProject.PhysicalDrivenKernelRealization
public import RequestProject.PhysicalDrivenRowsReconstruction
public import RequestProject.LocalConformalVekuaConormalBridge

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


noncomputable section

namespace PolyaNeumann

open MeasureTheory Set Metric Filter
open scoped Topology ComplexConjugate InnerProductSpace ContDiff


private theorem kernel_conormal_basis n b :
    ⟪stdBasisZ n, b⟫_ℂ = b n := by
  rw [stdBasisZ_apply, lp.inner_single_left]
  simp

private def kernel_conormal_eval (n : ℤ) : BoundaryL2 →L[ℂ] ℂ :=
  (innerSL ℂ (stdBasisZ n)).comp boundaryFourier.toLinearIsometry.toContinuousLinearMap

private theorem kernel_conormal_eval_apply n v :
    kernel_conormal_eval n v = boundaryFourier v n := by
  exact kernel_conormal_basis n (boundaryFourier v)

private theorem kernel_conormal_memLp {f : ℝ → ℂ}
    (hf : ContinuousOn f (Icc 0 (2 * Real.pi))) :
    MemLp f 2 (volume.restrict (Ioc 0 (2 * Real.pi))) := by
  obtain ⟨B, hB⟩ := isCompact_Icc.exists_bound_of_continuousOn hf
  refine MemLp.of_bound
    ((hf.mono Ioc_subset_Icc_self).aestronglyMeasurable measurableSet_Ioc) B ?_
  exact ae_restrict_of_forall_mem measurableSet_Ioc fun θ hθ =>
    hB θ (Ioc_subset_Icc_self hθ)

private theorem kernel_conormal_coeff_ae  (v : BoundaryL2)
    (hv : v =ᵐ[volume.restrict (Ioc 0 (2 * Real.pi))] f) n :
    boundaryFourier v n = (Real.sqrt (2 * Real.pi) : ℂ) *
      fourierCoeffOn Real.two_pi_pos f n := by
  rw [boundaryFourier_apply, fourierCoeffOn_congr_ae Real.two_pi_pos hv]

section CoordinateTerms

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

local notation "ΓF" => physicalCircleTrace F
local notation "hΓF" => contDiff_physicalCircleTrace_of_neighborhood hR F
  (hFs.of_le (by simp))
local notation "UF" => localConformalHardyH1Extension hR F hFs hb hL hhol hinj hC hK e he hsource hes
local notation "JF" => localConformalHardyPrimitive hR F hFs
local notation "MF" => neumannH1AffineMultiplier hb (F 1)
local notation "TF" => localConformalDiskH1Trace hR F hFs hL
local notation "VF" => localConformalVekuaH1 hR F hFs hb hL hhol hinj hC hK e he hsource hes
local notation "AF" => localConformalVekuaGradientA hR F hFs hb hL hhol hinj hC hK e he hsource hes
local notation "RF" => localConformalVekuaRemainder hR F hFs hb hL hhol hinj hC hK e he hsource hes
local notation "VelF" => boundaryContinuousMultiplier (localConformalVelocityCircle F)
local notation "BarVelF" => boundaryContinuousMultiplier (localConformalPrimitiveCircle F)
local notation "hβF" => localConformalVelocityCircle_isWL1_half hR F hFs
local notation "haF" => localConformalHardyPrimitiveMultiplier_isWL1 hR F hFs
local notation "hgF" => localConformalCenteredCircle_isWL1_half hR F hFs
local notation "NCF" => normalizedConormal hβF haF hgF

private theorem kernel_conormal_primitive_H1 b
    (hb1 : IsSobolevSeq 1 (fromL2 (1 / 2) b)) j :
    IsSobolevSeq 1 (normalizedHardyAverage ((JF ^ j) b)) := by
  rw [normalizedHardyAverage_localConformalHardyPrimitive_pow]
  exact (antiPrimIter_bound (by norm_num : (0 : ℝ) ≤ 1)
    (physicalCircleTrace_fourier_weights_of_smooth_neighborhood hR F hFs).1
    (isSobolevSeq_smul _ hb1) j).1

local notation "Φ4" => localConformalVekuaBoundary hR F hFs hb hL hhol hinj hC hK e he hsource hes

theorem localConformalVekua_coordinate_trace_reconstruction_ae E (b : L2Z)
    (hbn : IsNonpositiveFourierSupport b)
    (hb1 : IsSobolevSeq 1 (fromL2 (1 / 2) b)) :
    (TF (VF (F 1) E b) : ℝ → ℂ)
      =ᵐ[volume.restrict (Ioc 0 (2 * Real.pi))]
        hardyFourierTrace (normalizedHardyAverage
          (Φ4 E b)) := by
  have hcoef := normalizedHardyAverage_localConformalDiskHalfTrace hR F hFs hL
    (VF (F 1) E b)
  change normalizedHardyAverage
      (Φ4 E b) = fourierCoeffOn Real.two_pi_pos (TF (VF (F 1) E b)) at hcoef
  have ht := boundaryL2_ae_hardyFourierTrace_of_H1 (TF (VF (F 1) E b))
    (by rw [← hcoef]; exact isSobolevSeq_smul _ (localConformalVekuaBoundary_raw_H1 hR F hFs hb hL hhol hinj hC hK e he hsource hes E b hbn hb1))
  rwa [← hcoef] at ht

/-- Actual ordinary trace representatives for independent affine and
primitive powers. The constant primitive coefficient is retained. -/
local notation "Φ3" => localConformalDiskHalfTrace_hardyExtension_eq_of_nonpositive hR F hFs hb hL hhol hinj hC hK e he hsource hes

theorem localConformalHardy_affine_primitive_trace_ae (b : L2Z)
    (hbn : IsNonpositiveFourierSupport b)
    (hb1 : IsSobolevSeq 1 (fromL2 (1 / 2) b)) j k :
    (TF ((MF ^ j) (UF ((JF ^ k) b))) : ℝ → ℂ)
      =ᵐ[volume.restrict (Ioc 0 (2 * Real.pi))]
        fun θ => (ΓF θ - F 1) ^ j *
          hardyFourierTrace (normalizedHardyAverage ((JF ^ k) b)) θ := by
  have hcoef := normalizedHardyAverage_localConformalDiskHalfTrace hR F hFs hL
    (UF ((JF ^ k) b))
  rw [show normalizedHardyAverage ((localConformalDiskHalfTrace hR F hFs hL) (UF ((JF ^ k) b))) = normalizedHardyAverage ((JF ^ k) b) by
    rw [Φ3 _ (localConformalHardyPrimitive_pow_nonpositive hR F hFs hhol b hbn k)]] at hcoef
  have hu := boundaryL2_ae_hardyFourierTrace_of_H1 (TF (UF ((JF ^ k) b)))
    (by rw [← hcoef]; exact kernel_conormal_primitive_H1 hR F hFs b hb1 k)
  rw [← hcoef] at hu
  rw [localConformalDiskH1Trace_affineMultiplier_pow hR F hFs hb hL hhol hinj hC]
  filter_upwards [hu, boundaryContinuousMultiplier_ae
    ((localConformalCenteredCircle hR F hFs) ^ j) (TF (UF ((JF ^ k) b)))]
    with θ hu hm
  rw [hm, hu]
  simp [localConformalCenteredCircle_apply, physicalCircleTrace]

local notation "Φ0" => localConformalHardy_affine_primitive_trace_ae hR F hFs hb hL hhol hinj hC hK e he hsource hes

theorem localConformalVekua_normalizedConormal_fourier E (b : L2Z)
    (hbn : IsNonpositiveFourierSupport b)
    (hb1 : IsSobolevSeq 1 (fromL2 (1 / 2) b)) n :
    NCF E b n = ((sobWeight n ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
      (-(n : ℂ) * boundaryFourier (TF (VF (F 1) E b)) n -
        2 * Complex.I * boundaryFourier (VelF (TF (AF (F 1) E b))) n) := by
  have hdiff : Complex.I * (n : ℂ) * boundaryFourier (TF (RF (F 1) E b)) n = boundaryFourier (VelF (TF (AF (F 1) E b)) + BarVelF (TF ((localConformalVekuaGradientB hR F hFs hb hL hhol hinj hC hK e he hsource hes) (F 1) E b))) n := by
    let P := (VelF).comp TF
    let Q := (BarVelF).comp TF
    have heq j :
        Complex.I * n * kernel_conormal_eval n
            (TF (physicalVekuaCoeff E (j + 1) •
              ((MF ^ (j + 1)) (UF ((JF ^ (j + 1)) b))))) =
          kernel_conormal_eval n
            (P ((physicalVekuaCoeff E (j + 1) * (j + 1 : ℕ)) •
                ((MF ^ j) (UF ((JF ^ (j + 1)) b)))) +
              Q (physicalVekuaCoeff E (j + 1) •
                ((MF ^ (j + 1)) (UF ((JF ^ j) b))))) := by
      simp only [kernel_conormal_eval_apply, P, Q, ContinuousLinearMap.comp_apply,
        map_add, map_smul, smul_eq_mul]
      have hterm : Complex.I * (n : ℂ) * boundaryFourier (TF ((MF ^ (j + 1)) (UF ((JF ^ (j + 1)) b)))) n = boundaryFourier ((((j + 1 : ℕ) : ℂ) • VelF (TF ((MF ^ j) (UF ((JF ^ (j + 1)) b))))) + BarVelF (TF ((MF ^ (j + 1)) (UF ((JF ^ j) b))))) n := by
        let hj k : ℝ → ℂ := hardyFourierTrace (normalizedHardyAverage ((JF ^ k) b))
        let f : ℝ → ℂ := fun θ => (ΓF θ - F 1) ^ (j + 1) * hj (j + 1) θ
        let d : ℝ → ℂ := fun θ => (j + 1 : ℕ) * deriv ΓF θ *
          ((ΓF θ - F 1) ^ j * hj (j + 1) θ) +
          conj (deriv ΓF θ) * ((ΓF θ - F 1) ^ (j + 1) * hj j θ)
        have hc k : Continuous (hj k) := continuous_hardyFourierTrace
          (sq_tsum_norm_le (s := 0) (by norm_num)
            (by simpa using kernel_conormal_primitive_H1 hR F hFs b hb1 k)).1
        have hd θ : HasDerivAt f (d θ) θ := by
          convert ((((hΓF).differentiable (by simp) θ).hasDerivAt.sub_const (F 1)).pow (j + 1)).mul
            (by
              letI : Fact (0 < 2 * Real.pi) := ⟨Real.two_pi_pos⟩
              have hder := hasDerivAt_hardyFourierTrace_antiPrimIter_succ
                (localConformalPrimitiveCircle F) (by
                  rw [localConformalPrimitiveCircle_coeff hR F hFs]
                  exact (physicalCircleTrace_fourier_weights_of_smooth_neighborhood hR F hFs).1) (show IsSobolevSeq 1 (normalizedHardyAverage b) from (isSobolevSeq_smul (Real.sqrt (2 * Real.pi))⁻¹ hb1)) (show IsStrictNegativeFourierSupport (fourierCoeff (localConformalPrimitiveCircle F)) by
                  rw [localConformalPrimitiveCircle_coeff hR F hFs]
                  exact localConformalHardyPrimitiveMultiplier_strictNegative hR F hFs hhol) (show IsNonpositiveFourierSupport (normalizedHardyAverage b) by
                  intro n hn
                  simp [normalizedHardyAverage, fromL2, hbn n hn]) j θ
              rw [localConformalPrimitiveCircle_coeff hR F hFs, ← normalizedHardyAverage_localConformalHardyPrimitive_pow hR F hFs (j + 1) b,
                ← normalizedHardyAverage_localConformalHardyPrimitive_pow hR F hFs j b,
                localConformalPrimitiveCircle_apply hR F hFs] at hder
              exact hder) using 1 ;
            dsimp only [f, d, hj] ;
              simp only [Nat.add_sub_cancel, Pi.pow_apply] ; ring_nf
        have hdc : Continuous d := by
          exact (((continuous_const.mul (hΓF).continuous_deriv_one).mul
            (((hΓF).continuous.sub continuous_const).pow j |>.mul (hc (j + 1)))).add
            ((Complex.continuous_conj.comp (hΓF).continuous_deriv_one).mul
              (((hΓF).continuous.sub continuous_const).pow (j + 1) |>.mul (hc j))))
        have hf1 := contDiff_one_iff_deriv.mpr
          ⟨fun θ => (hd θ).differentiableAt, by
            have he := funext fun θ => (hd θ).deriv
            rw [he]
            exact hdc⟩
        let v :=
            ((j + 1 : ℕ) : ℂ) • VelF (TF ((MF ^ j) (UF ((JF ^ (j + 1)) b)))) +
              BarVelF (TF ((MF ^ (j + 1)) (UF ((JF ^ j) b))))
        have hdv' : v =ᵐ[volume.restrict (Ioc 0 (2 * Real.pi))] d := by
          dsimp only [v]
          filter_upwards [show (((((j + 1 : ℕ) : ℂ) • VelF (TF ((MF ^ j) (UF ((JF ^ (j + 1)) b))))) + BarVelF (TF ((MF ^ (j + 1)) (UF ((JF ^ j) b))))) : ℝ → ℂ) =ᵐ[volume.restrict (Ioc 0 (2 * Real.pi))] d by
            filter_upwards [Lp.coeFn_add
                (((((j + 1 : ℕ) : ℂ) • VelF (TF ((MF ^ j) (UF ((JF ^ (j + 1)) b)))))))
                (BarVelF (TF ((MF ^ (j + 1)) (UF ((JF ^ j) b))))),
              Lp.coeFn_smul (((j + 1 : ℕ) : ℂ))
                (VelF (TF ((MF ^ j) (UF ((JF ^ (j + 1)) b))))),
              boundaryContinuousMultiplier_ae (localConformalVelocityCircle F)
                (TF ((MF ^ j) (UF ((JF ^ (j + 1)) b)))),
              boundaryContinuousMultiplier_ae (localConformalPrimitiveCircle F)
                (TF ((MF ^ (j + 1)) (UF ((JF ^ j) b)))),
              Φ0 b hbn hb1 j (j + 1),
              Φ0 b hbn hb1 (j + 1) j] with θ ha hs hβ hα hx hy
            simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hβ, hα, hx, hy,
              localConformalVelocityCircle_apply hR F hFs,
              localConformalPrimitiveCircle_apply hR F hFs, d, hj]
            ring,
            Lp.coeFn_add
              (((j + 1 : ℕ) : ℂ) • VelF (TF ((MF ^ j) (UF ((JF ^ (j + 1)) b)))))
              (BarVelF (TF ((MF ^ (j + 1)) (UF ((JF ^ j) b))))),
            Lp.coeFn_smul ((j + 1 : ℕ) : ℂ)
              (VelF (TF ((MF ^ j) (UF ((JF ^ (j + 1)) b)))))] with θ h ha hs
          exact ha.trans (by
            rw [Pi.add_apply, hs]
            exact h)
        change Complex.I * n * boundaryFourier
            (TF ((MF ^ (j + 1)) (UF ((JF ^ (j + 1)) b)))) n = _
        rw [kernel_conormal_coeff_ae _ (Φ0 b hbn hb1 (j + 1) (j + 1)) n,
          kernel_conormal_coeff_ae v hdv' n, (fourierCoeffOn_of_ac_ae_hasDerivAt (by
            obtain ⟨B, hB⟩ := hf1.contDiffOn.exists_lipschitzOnWith
              (by norm_num : (1 : WithTop ℕ∞) ≠ 0) (convex_Icc 0 (2 * Real.pi)) isCompact_Icc
            apply LipschitzOnWith.absolutelyContinuousOnInterval
            simpa [uIcc_of_le Real.two_pi_pos.le] using hB) (kernel_conormal_memLp hdc.continuousOn) (Eventually.of_forall fun θ _ => hd θ) (by
              have hΓ := physicalCircleTrace_periodic F 0
              have hh := hardyFourierTrace_periodic (normalizedHardyAverage ((JF ^ (j + 1)) b)) 0
              simp only [zero_add] at hΓ hh
              dsimp only [f, hj]
              rw [hΓ, hh]) n)]
        ring
      simp only [map_add, map_smul, lp.coeFn_add, Pi.add_apply, lp.coeFn_smul,
        Pi.smul_apply, smul_eq_mul] at hterm
      calc
        _ = physicalVekuaCoeff E (j + 1) *
            ((Complex.I * n) *
              boundaryFourier (TF ((MF ^ (j + 1)) (UF ((JF ^ (j + 1)) b)))) n) := by ring
        _ = _ := by rw [hterm]; ring
    exact (show HasSum (fun j => kernel_conormal_eval n (P ((physicalVekuaCoeff E (j + 1) * (j + 1 : ℕ)) • ((MF ^ j) (UF ((JF ^ (j + 1)) b)))) + Q (physicalVekuaCoeff E (j + 1) • ((MF ^ (j + 1)) (UF ((JF ^ j) b)))))) ((Complex.I * n) * boundaryFourier (TF (RF (F 1) E b)) n) by
      simpa [kernel_conormal_eval_apply] using (HasSum.congr_fun (((kernel_conormal_eval n).hasSum ((TF).hasSum (localConformalVekuaRemainder_hasSum hR F hFs hb hL hhol hinj hC hK e he hsource hes (F 1) E b))).mul_left (Complex.I * n)) (fun j => (heq j).symm))).unique (by
      simpa [P, Q, kernel_conormal_eval_apply] using ((kernel_conormal_eval n).hasSum ((P.hasSum (localConformalVekuaGradientA_hasSum hR F hFs hb hL hhol hinj hC hK e he hsource hes (F 1) E b)).add (Q.hasSum (localConformalVekuaGradientB_hasSum hR F hFs hb hL hhol hinj hC hK e he hsource hes (F 1) E b)))))
  simp [localConformalVekuaRemainder_apply] at hdiff
  rw [show boundaryFourier (TF (UF b)) = fromL2 (1 / 2) b by
    rw [← fromL2_half_localConformalDiskHalfTrace,
      Φ3 b hbn]] at hdiff
  have hdiff' := congrArg (fun z => Complex.I * z) hdiff
  simp [mul_sub, ← mul_assoc] at hdiff'
  change normalizedConormalPrincipal b n +
    sobolevSmoothing 1 zero_le_one (conormalRemOp (by norm_num) hβF haF hgF E b) n = _
  rw [← localConformalVekuaCoordinateConormalRemainder_eq_conormalRemOp hR F hFs hb hL hhol hinj hC hK e he hsource hes E b hbn, sobolevSmoothing, diagOp_apply,
    localConformalVekuaCoordinateConormalRemainder,
    ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.comp_apply]
  simp only [map_add, map_smul, lp.coeFn_add, Pi.add_apply, lp.coeFn_smul,
    Pi.smul_apply, smul_eq_mul]
  rw [show normalizedConormalPrincipal b n = (sobWeight n ^ (-(1 / 2 : ℝ)) : ℝ) * (-(n : ℂ) * fromL2 (1 / 2) b n) by
    by_cases hn : 0 < n
    · simp [normalizedConormal_principal_apply, hbn n hn, fromL2]
    · have hn0 : (n : ℝ) ≤ 0 := by exact_mod_cast (le_of_not_gt hn)
      have habs := abs_of_nonpos hn0
      rw [normalizedConormal_principal_apply, fromL2, show (|(n : ℝ)| / (1 + |(n : ℝ)|) : ℝ) = -(n : ℂ) * ((sobWeight n)⁻¹) by
        rw [habs, sobWeight, habs]
        push_cast
        ring]
      calc
        _ = -n * (((sobWeight n ^ (-(1 / 2 : ℝ)) : ℝ) *
            (sobWeight n ^ (-(1 / 2 : ℝ)) : ℝ)) * b n) := by
          rw [← Complex.ofReal_mul, show sobWeight n ^ (-(1 / 2 : ℝ)) * sobWeight n ^ (-(1 / 2 : ℝ)) = (sobWeight n)⁻¹ by
            rw [← Real.rpow_add (sobWeight_pos n),
              show -(1 / 2 : ℝ) + -(1 / 2) = -1 by ring, Real.rpow_neg_one]]
          ring
        _ = _ := by ring]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply,
    map_smul, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]
  ring_nf at hdiff' ⊢
  rw [show sobWeight n ^ ((-1 : ℝ) / 2) = sobWeight n ^ (-(1 / 2 : ℝ)) by
    congr 1; ring]
  linear_combination -((sobWeight n ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * hdiff'

variable
    {L : NNReal} (hΓLip : LipschitzWith L (physicalCircleTrace F))
    {E : ℝ} (hE : 0 < E)
    {W : ℝ → Ell2 →L[ℂ] Ell2} (hW : IsTransport (physicalCircleTrace F) E W)
    (g : ℝ → ℂ) (hg : MemLp g 2 (volume.restrict (Ioc 0 (2 * Real.pi))))
    (hO : observationAdj W g = 0)

local notation "bF" => physicalDrivenKernelInput hΓLip hΓF hW g hg hO

private theorem kernel_conormal_volterra_eqOn  
    (he : EqOn f h (Icc 0 T)) j :
    EqOn (volterraPrimitiveIterate a f j) (volterraPrimitiveIterate a h j) (Icc 0 T) := by
  induction j with
  | zero => exact he
  | succ j ih =>
    intro θ hθ
    change (∫ s in 0..θ, a s * volterraPrimitiveIterate a f j s) = _
    apply intervalIntegral.integral_congr
    intro s hs
    rw [uIcc_of_le hθ.1] at hs
    dsimp only
    rw [ih (Icc_subset_Icc le_rfl hθ.2 hs)]

include hE in
/-- The genuine companion A has precisely the first actual scaled driven
row as its ordinary coordinate trace. No row or conormal correspondence
is assumed. -/
def physicalDrivenKernelCoordinateLoad : BoundaryL2 := hg.toLp g

theorem physicalDrivenKernelCoordinateLoad_ae :
    (physicalDrivenKernelCoordinateLoad g hg : ℝ → ℂ)
      =ᵐ[volume.restrict (Ioc 0 (2 * Real.pi))] g := hg.coeFn_toLp

include hR hFs hW hg in
private theorem kernel_conormal_row_derivative_memLp :
    MemLp (fun θ => 2 * deriv ΓF θ *
      physicalDrivenScaledRow E (physicalDrivenVector W g) 1 θ - Complex.I * g θ)
      2 (volume.restrict (Ioc 0 (2 * Real.pi))) := by
  exact (kernel_conormal_memLp ((continuousOn_const.mul (hΓF).continuous_deriv_one.continuousOn).mul (continuousOn_const.mul (physicalDrivenRow_continuousOn _ (physicalDrivenVector_continuousOn_of_intervalIntegrable hW.1 g (intervalIntegrable_boundary_of_memLp g hg)) 1)))).sub (by
    exact hg.const_mul Complex.I)

include hR hFs hΓLip hW hg hO in
private theorem kernel_conormal_row_fourier_derivative (n : ℤ) :
    fourierCoeffOn Real.two_pi_pos
      (fun θ => 2 * deriv ΓF θ * physicalDrivenScaledRow E (physicalDrivenVector W g) 1 θ -
        Complex.I * g θ) n =
      Complex.I * (n : ℂ) *
        fourierCoeffOn Real.two_pi_pos (physicalDrivenRow (physicalDrivenVector W g) 0) n := by
  have h := fourierCoeffOn_of_ac_ae_hasDerivAt
    (physicalDrivenScaledRow_absolutelyContinuous_of_intervalIntegrable hΓLip hW g
      (intervalIntegrable_boundary_of_memLp g hg) 0)
    (kernel_conormal_row_derivative_memLp hR F hFs hW g hg)
    (physicalDrivenScaledRow_zero_ae_hasDerivAt_of_intervalIntegrable hΓLip hΓF hW g
      (intervalIntegrable_boundary_of_memLp g hg))
    (by simp [physicalDrivenScaledRow, physicalDrivenRow, physicalDrivenVector_endpoint W g hO]) n
  rw [show physicalDrivenScaledRow E (physicalDrivenVector W g) 0 = physicalDrivenRow (physicalDrivenVector W g) 0 by
    funext θ
    simp [physicalDrivenScaledRow]] at h
  exact h

include hb hL hhol hinj hC hK e he hsource hes hE in
/-- The normalized conormal of the actual observation-kernel realization
is exactly the half-smoothed unitary Fourier transform of its original
coordinate L² forcing. Frequency zero is proved by the same true AC IBP. -/
theorem physicalDrivenKernelH1_normalizedConormal_eq_coordinateLoad :
    NCF (E : ℂ) bF = sobolevSmoothing (1 / 2) (by norm_num)
      (boundaryFourier (physicalDrivenKernelCoordinateLoad g hg)) := by
  let A := VelF
    (TF (AF (F 1) E bF))
  have hA : A =ᵐ[volume.restrict (Ioc 0 (2 * Real.pi))]
      fun θ => deriv ΓF θ * physicalDrivenScaledRow E (physicalDrivenVector W g) 1 θ := by
    filter_upwards [boundaryContinuousMultiplier_ae (localConformalVelocityCircle F)
        (TF (AF (F 1) E bF)),
      have h_inl : (TF (AF (F 1) (E : ℂ) bF) : ℝ → ℂ) =ᵐ[volume.restrict (Ioc 0 (2 * Real.pi))] physicalDrivenScaledRow E (physicalDrivenVector W g) 1 := by
        have hbn := physicalDrivenKernelInput_nonpositive hR F hFs hb hL hhol hC
          e he hsource hΓLip hE hW g hg hO
        have hb1 := fromL2_physicalDrivenKernelInput_isSobolevSeq_one hΓLip hΓF hW g hg hO
        have hJbn := localConformalHardyPrimitive_nonpositive hR F hFs hhol bF hbn
        have hJ1 : IsSobolevSeq 1 (fromL2 (1 / 2) (JF bF)) := by
          have h_inl : IsSobolevSeq 1 (fromL2 (1 / 2) ((JF ^ 1) bF)) := by
            rw [fromL2_localConformalHardyPrimitive_pow]
            exact (antiPrimIter_bound (by norm_num : (0 : ℝ) ≤ 1)
              (physicalCircleTrace_fourier_weights_of_smooth_neighborhood hR F hFs).1 hb1 1).1
          simpa using h_inl
        have ht := localConformalVekua_coordinate_trace_reconstruction_ae hR F hFs hb hL
          hhol hinj hC hK e he hsource hes E (JF bF) hJbn hJ1
        have hpoint {θ : ℝ} (hθ : θ ∈ Icc 0 (2 * Real.pi)) :
            (-E / 4) * hardyFourierTrace (normalizedHardyAverage
              (localConformalVekuaBoundary hR F hFs hb hL hhol hinj hC hK
                e he hsource hes E (JF bF))) θ =
            physicalDrivenScaledRow E (physicalDrivenVector W g) 1 θ := by
          have hs := localConformalVekuaBoundary_average_volterra_hasSum_of_H1 hR F hFs
            hb hL hhol hinj hC hK e he hsource hes E (JF bF) hJbn hJ1 θ
          rw [← hs.tsum_eq]
          have hr := physicalDrivenScaledRow_eq_volterraVekua_of_intervalIntegrable hΓLip hΓF
            hE.le hW g (intervalIntegrable_boundary_of_memLp g hg) 1 hθ
          simp at hr
          rw [hr]
          congr 1
          apply tsum_congr
          intro j
          rw [kernel_conormal_volterra_eqOn (show EqOn (hardyFourierTrace (normalizedHardyAverage (JF bF))) (volterraPrimitiveIterate (fun s => star (deriv ΓF s)) (physicalDrivenGauge ΓF E (physicalDrivenVector W g) 0) 1) (Icc 0 (2 * Real.pi)) by
            intro θ hθ
            have hJ := localConformalHardyPrimitive_pow_volterra_of_H1 hR F hFs hhol bF hbn
              (isSobolevSeq_smul _ hb1) 1 θ
            simp at hJ
            rw [hJ]
            apply kernel_conormal_volterra_eqOn ?_ 1 hθ
            intro s hs
            rw [hardyFourierTrace_physicalDrivenKernelInput,
              physicalDrivenPeriodicGauge_eqOn _ E W g hO 0 hs]) j hθ]
          simp [physicalDrivenCentered, physicalCircleTrace, circleMap_zero]
        rw [localConformalVekuaGradientA_apply, map_smul]
        have hs := Lp.coeFn_smul (-(E : ℂ) / 4)
          (TF (VF (F 1) (E : ℂ) (JF bF)))
        filter_upwards [hs, ht, ae_restrict_mem measurableSet_Ioc]
          with θ hs ht hθ
        rw [hs]
        simp [ht]
        exact hpoint (Ioc_subset_Icc_self hθ)
      h_inl] with θ hm hr
    rw [hm, hr, localConformalVelocityCircle_apply hR F hFs]
  let d := (2 : ℂ) • A - Complex.I • physicalDrivenKernelCoordinateLoad g hg
  have ht := physicalDrivenKernelH1_coordinate_trace_ae hR F hFs hb hL hhol hinj hC hK
    e he hsource hes hΓLip hE hW g hg hO
  apply lp.ext
  funext n
  have hf' : boundaryFourier d n = Complex.I * (n : ℂ) *
      boundaryFourier (TF (VF (F 1) E bF)) n := by
    dsimp only [physicalDrivenKernelH1] at ht
    rw [kernel_conormal_coeff_ae d (show d =ᵐ[volume.restrict (Ioc 0 (2 * Real.pi))] fun θ => 2 * deriv ΓF θ * physicalDrivenScaledRow E (physicalDrivenVector W g) 1 θ - Complex.I * g θ by
      filter_upwards [Lp.coeFn_sub ((2 : ℂ) • A)
          (Complex.I • physicalDrivenKernelCoordinateLoad g hg),
        Lp.coeFn_smul (2 : ℂ) A,
        Lp.coeFn_smul Complex.I (physicalDrivenKernelCoordinateLoad g hg), hA,
        physicalDrivenKernelCoordinateLoad_ae g hg] with θ hs h2 hi hA hg
      rw [hs]
      simp
      rw [h2, hi]
      simp [hA, hg]
      ring) n,
      kernel_conormal_coeff_ae (TF (VF (F 1) E bF)) ht n, kernel_conormal_row_fourier_derivative hR F hFs hΓLip hW g hg hO n]
    ring
  simp only [d, map_sub, map_smul, lp.coeFn_sub, Pi.sub_apply, lp.coeFn_smul,
    Pi.smul_apply, smul_eq_mul] at hf'
  have hi := congrArg (fun z => Complex.I * z) hf'
  simp only [mul_sub, ← mul_assoc, Complex.I_mul_I, neg_one_mul] at hi
  rw [localConformalVekua_normalizedConormal_fourier hR F hFs hb hL hhol hinj hC hK
    e he hsource hes E bF (physicalDrivenKernelInput_nonpositive hR F hFs hb hL hhol hC e he hsource hΓLip hE hW g hg hO) (fromL2_physicalDrivenKernelInput_isSobolevSeq_one hΓLip hΓF hW g hg hO) n]
  change _ = (sobWeight n ^ (-(1 / 2 : ℝ)) : ℝ) *
    boundaryFourier (physicalDrivenKernelCoordinateLoad g hg) n
  dsimp only [A] at hi
  linear_combination -((sobWeight n ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * hi

end CoordinateTerms

end PolyaNeumann

end
