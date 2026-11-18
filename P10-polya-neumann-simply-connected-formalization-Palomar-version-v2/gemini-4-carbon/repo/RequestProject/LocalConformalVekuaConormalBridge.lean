module

public import RequestProject.LocalConformalVekuaSeries
public import RequestProject.LocalConformalVekuaTrace
public import RequestProject.LocalConformalGradient
public import RequestProject.ConormalNormalization
public import RequestProject.LocalConformalBoundaryLoad
public import Mathlib.Tactic.Module

/-!
# Identification of the actual Vekua flux and the Fourier conormal remainder

Combines the principal Hardy conormal pairing, the H¹ gradient series for the
physical Vekua remainder `V_E b - U b`, the direct Wirtinger-velocity Green
pairing in conformal boundary coordinates, and the Fourier series identification
with `normalizedConormal`.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace PolyaNeumann

open MeasureTheory Set Metric Filter
open scoped Real Topology InnerProductSpace ComplexConjugate

local instance conormalBridgeTwoPiPos : Fact (0 < 2 * Real.pi) := ⟨Real.two_pi_pos⟩

/-! ## Principal Hardy conormal pairing -/

theorem normalizedConormalPrincipal_single (n : ℤ) :
    normalizedConormalPrincipal (stdBasisZ n) =
      ((|(n : ℝ)| / (1 + |(n : ℝ)|) : ℝ) : ℂ) • stdBasisZ n := by
  apply lp.ext; funext k
  rw [normalizedConormal_principal_apply]
  simp only [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, stdBasisZ_apply, lp.single_apply]
  by_cases hkn : k = n <;> simp [hkn]

private theorem conormal_scale_cancel (m : ℕ) (t : ℝ) (a : ℂ)
    (ht : t ^ 2 = 2 * π * ((m + 1 : ℕ) : ℝ)) :
    ((t : ℂ) * (((m : ℝ) / (1 + (m : ℝ)) : ℝ) : ℂ)) * conj ((t : ℂ) * a) =
      (2 * π : ℂ) * (m : ℂ) * conj a := by
  have hm : (1 + (m : ℝ)) ≠ 0 := by positivity
  have hr : t ^ 2 * ((m : ℝ) / (1 + (m : ℝ))) = 2 * π * (m : ℝ) := by
    rw [ht]; push_cast; field_simp [hm]; ring
  calc
    _ = ((t ^ 2 * ((m : ℝ) / (1 + (m : ℝ))) : ℝ) : ℂ) * conj a := by
      simp only [map_mul, Complex.conj_ofReal]; push_cast; ring
    _ = _ := by rw [hr]; push_cast; ring

theorem diskAntiholomorphicH1Test_principal_conormal (m : ℕ)
    (w : NeumannH1 (ball (0 : ℂ) 1)) :
    (∑ i : Fin 2, ⟪h1Gradient (ball (0 : ℂ) 1) i w,
      h1Gradient (ball (0 : ℂ) 1) i (diskAntiholomorphicH1Test m)⟫_ℂ) =
      ⟪diskHalfTrace w, normalizedConormalPrincipal
        (diskHalfTrace (diskAntiholomorphicH1Test m))⟫_ℂ := by
  have hg := congrArg conj (disk_gradient_form_antiholomorphicTest m w)
  simp only [map_sum, inner_conj_symm, map_mul, Complex.conj_ofReal,
    Complex.conj_natCast, map_ofNat] at hg
  have hsingle (x : L2Z) (n : ℤ) : ⟪x, stdBasisZ n⟫_ℂ = conj (x n) := by
    rw [stdBasisZ_apply, lp.inner_single_right]; simp [RCLike.inner_apply]
  have hneg : diskHalfTrace w (-(m : ℤ)) = (diskHardyTraceScale m : ℂ) *
      fourierCoeffOn Real.two_pi_pos (diskH1Trace w : ℝ → ℂ) (-(m : ℤ)) := by
    rw [diskHalfTrace_apply, boundaryFourier_apply]
    simp only [diskHardyTraceScale, sobWeight, Complex.ofReal_mul]; ring
  rw [hg, diskHalfTrace_antiholomorphicTest, map_smul,
    normalizedConormalPrincipal_single, smul_smul, inner_smul_right, hsingle, hneg]
  simp only [Int.cast_neg, Int.cast_natCast, abs_neg,
    abs_of_nonneg (Nat.cast_nonneg m : (0 : ℝ) ≤ (m : ℝ))]
  rw [show (Real.sqrt (sobWeight (-(m : ℤ))) : ℂ) * (Real.sqrt (2 * π) : ℂ) =
      (diskHardyTraceScale m : ℂ) by simp only [diskHardyTraceScale, Complex.ofReal_mul],
    conormal_scale_cancel m _ _ (diskHardyTraceScale_sq m)]

theorem diskHardyExtension_principal_conormal (b : L2Z)
    (w : NeumannH1 (ball (0 : ℂ) 1)) :
    (∑ i : Fin 2, ⟪h1Gradient (ball (0 : ℂ) 1) i w,
      h1Gradient (ball (0 : ℂ) 1) i (diskHardyExtension b)⟫_ℂ) =
      ⟪diskHalfTrace w, normalizedConormalPrincipal ((1 - posProj) b)⟫_ℂ := by
  let A : NeumannH1 (ball (0 : ℂ) 1) →L[ℂ] ℂ :=
    (innerSL ℂ (h1GradientVector (ball (0 : ℂ) 1) w)).comp (h1GradientVector (ball (0 : ℂ) 1))
  let B := (innerSL ℂ (diskHalfTrace w)).comp (normalizedConormalPrincipal.comp diskHalfTrace)
  have hA_app (u : NeumannH1 (ball (0 : ℂ) 1)) :
      A u = ∑ i : Fin 2, ⟪h1Gradient (ball (0 : ℂ) 1) i w, h1Gradient (ball (0 : ℂ) 1) i u⟫_ℂ := by
    change ⟪h1GradientVector (ball (0 : ℂ) 1) w, h1GradientVector (ball (0 : ℂ) 1) u⟫_ℂ = _
    simp only [PiLp.inner_apply, h1GradientVector_apply]
  have hA := A.hasSum (diskHardyExtension_hasSum b)
  have he : (fun m : ℕ => A ((b (-(m : ℤ)) / (diskHardyTraceScale m : ℂ)) •
        diskAntiholomorphicH1Test m)) =
      (fun m : ℕ => B ((b (-(m : ℤ)) / (diskHardyTraceScale m : ℂ)) •
        diskAntiholomorphicH1Test m)) := funext fun m => by
    simp only [map_smul]
    exact congrArg _ ((hA_app _).trans (diskAntiholomorphicH1Test_principal_conormal m w))
  rw [he] at hA
  have h := hA.unique (B.hasSum (diskHardyExtension_hasSum b))
  simpa only [hA_app, B, ContinuousLinearMap.comp_apply, innerSL_apply_apply,
    diskHalfTrace_diskHardyExtension] using h

/-! ## Physical H¹ gradient series for the Vekua remainder -/

private theorem conormal_coeff_succ_bound (E : ℂ) (j : ℕ) :
    ‖physicalVekuaCoeff E (j + 1)‖ ≤ ‖-E / 4‖ * ‖physicalVekuaCoeff E j‖ := by
  have h := congrArg norm (physicalVekuaCoeff_succ E j)
  simp only [norm_mul, Complex.norm_natCast] at h
  exact (le_mul_of_one_le_right (norm_nonneg _)
    (by exact_mod_cast (by omega : 1 ≤ j + 1))).trans_eq h

section BoundedSeries

variable {X H : Type*}
    [NormedAddCommGroup X] [NormedSpace ℂ X]
    [NormedAddCommGroup H] [NormedSpace ℂ H] [CompleteSpace H]

def boundedPhysicalVekuaGradientBTerm (M : H →L[ℂ] H) (U : X →L[ℂ] H)
    (J : X →L[ℂ] X) (E : ℂ) (j : ℕ) : X →L[ℂ] H :=
  physicalVekuaCoeff E (j + 1) • (M.comp ((M ^ j).comp (U.comp (J ^ j))))

omit [CompleteSpace H] in
theorem boundedPhysicalVekuaGradientBTerm_apply (M : H →L[ℂ] H) (U : X →L[ℂ] H)
    (J : X →L[ℂ] X) (E : ℂ) (j : ℕ) (b : X) :
    boundedPhysicalVekuaGradientBTerm M U J E j b =
      physicalVekuaCoeff E (j + 1) • (M ^ (j + 1)) (U ((J ^ j) b)) := by
  change physicalVekuaCoeff E (j + 1) • M ((M ^ j) (U ((J ^ j) b))) = _
  rw [pow_succ', ContinuousLinearMap.mul_apply]

omit [CompleteSpace H] in
theorem summable_norm_boundedPhysicalVekuaGradientBTerm (M : H →L[ℂ] H)
    (U : X →L[ℂ] H) (J : X →L[ℂ] X) (E : ℂ) :
    Summable (fun j : ℕ => ‖boundedPhysicalVekuaGradientBTerm M U J E j‖) := by
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun j => ?_)
    ((summable_norm_boundedPhysicalVekuaTerm M U J E).mul_left (‖-E / 4‖ * ‖M‖))
  let T : X →L[ℂ] H := (M ^ j).comp (U.comp (J ^ j))
  change ‖physicalVekuaCoeff E (j + 1) • M.comp T‖ ≤
    (‖-E / 4‖ * ‖M‖) * ‖physicalVekuaCoeff E j • T‖
  rw [norm_smul, norm_smul]
  exact (mul_le_mul (conormal_coeff_succ_bound E j) (M.opNorm_comp_le T)
    (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).trans_eq (by ring)

def boundedPhysicalVekuaGradientB (M : H →L[ℂ] H) (U : X →L[ℂ] H)
    (J : X →L[ℂ] X) (E : ℂ) : X →L[ℂ] H :=
  ∑' j : ℕ, boundedPhysicalVekuaGradientBTerm M U J E j

theorem boundedPhysicalVekuaGradientB_hasSum_apply (M : H →L[ℂ] H)
    (U : X →L[ℂ] H) (J : X →L[ℂ] X) (E : ℂ) (b : X) :
    HasSum (fun j : ℕ => physicalVekuaCoeff E (j + 1) •
      (M ^ (j + 1)) (U ((J ^ j) b))) (boundedPhysicalVekuaGradientB M U J E b) := by
  unfold boundedPhysicalVekuaGradientB
  simpa only [ContinuousLinearMap.apply_apply, boundedPhysicalVekuaGradientBTerm_apply] using
    (ContinuousLinearMap.apply ℂ H b).hasSum
      (summable_norm_boundedPhysicalVekuaGradientBTerm M U J E).of_norm.hasSum

end BoundedSeries

private theorem conormal_affine_Dbar_value {Ω : Set ℂ}
    (hb : Bornology.IsBounded Ω) (p : ℂ) (u v : NeumannH1 Ω) (j : ℕ)
    (hprim : h1WirtingerDbar Ω u = h1Value Ω v) :
    h1WirtingerDbar Ω ((neumannH1AffineMultiplier hb p ^ j) u) =
      h1Value Ω ((neumannH1AffineMultiplier hb p ^ j) v) := by
  rw [h1WirtingerDbar_affine_pow hb p u j, hprim,
    ← h1Value_neumannH1AffineMultiplier_pow hb p v j]

private theorem conormal_affine_gradient_x {Ω : Set ℂ}
    (hb : Bornology.IsBounded Ω) (p : ℂ) (u v : NeumannH1 Ω) (j : ℕ)
    (hCR : h1Gradient Ω 0 u = Complex.I • h1Gradient Ω 1 u)
    (hprim : h1WirtingerDbar Ω u = h1Value Ω v) :
    h1Gradient Ω 0 ((neumannH1AffineMultiplier hb p ^ (j + 1)) u) =
      h1Value Ω (((j + 1 : ℕ) : ℂ) • ((neumannH1AffineMultiplier hb p ^ j) u) +
        (neumannH1AffineMultiplier hb p ^ (j + 1)) v) := by
  have hg0 : h1Gradient Ω 0 ((neumannH1AffineMultiplier hb p ^ (j + 1)) u) =
      h1WirtingerD Ω ((neumannH1AffineMultiplier hb p ^ (j + 1)) u) +
        h1WirtingerDbar Ω ((neumannH1AffineMultiplier hb p ^ (j + 1)) u) := by
    rw [h1WirtingerD_apply, h1WirtingerDbar_apply]; module
  rw [hg0, h1WirtingerD_affine_pow_of_antiholomorphic hb p u hCR j,
    conormal_affine_Dbar_value hb p u v (j + 1) hprim, map_add, map_smul]

private theorem conormal_affine_gradient_y {Ω : Set ℂ}
    (hb : Bornology.IsBounded Ω) (p : ℂ) (u v : NeumannH1 Ω) (j : ℕ)
    (hCR : h1Gradient Ω 0 u = Complex.I • h1Gradient Ω 1 u)
    (hprim : h1WirtingerDbar Ω u = h1Value Ω v) :
    h1Gradient Ω 1 ((neumannH1AffineMultiplier hb p ^ (j + 1)) u) =
      h1Value Ω (Complex.I •
        (((j + 1 : ℕ) : ℂ) • ((neumannH1AffineMultiplier hb p ^ j) u) -
          (neumannH1AffineMultiplier hb p ^ (j + 1)) v)) := by
  have hg1 : h1Gradient Ω 1 ((neumannH1AffineMultiplier hb p ^ (j + 1)) u) =
      Complex.I • (h1WirtingerD Ω ((neumannH1AffineMultiplier hb p ^ (j + 1)) u) -
        h1WirtingerDbar Ω ((neumannH1AffineMultiplier hb p ^ (j + 1)) u)) := by
    rw [h1WirtingerD_apply, h1WirtingerDbar_apply]
    simp only [smul_sub, smul_add, smul_smul]
    match_scalars <;> ring_nf
    all_goals simp only [Complex.I_sq, neg_neg]
  rw [hg1, h1WirtingerD_affine_pow_of_antiholomorphic hb p u hCR j,
    conormal_affine_Dbar_value hb p u v (j + 1) hprim, map_smul, map_sub, map_smul]

/-! ## Circle velocity and Fourier weights -/

private theorem bridge_summable_coeff {s : ℝ} (hs : 0 ≤ s) {a : ℤ → ℂ}
    (ha : IsWL1 s a) : Summable a :=
  Summable.of_norm <| ha.of_nonneg_of_le (fun _ => norm_nonneg _) fun n =>
    le_mul_of_one_le_left (norm_nonneg _) (Real.one_le_rpow (one_le_sobWeight n) hs)

private theorem bridge_isWL1_mono {s t : ℝ} (hst : s ≤ t) {a : ℤ → ℂ}
    (ha : IsWL1 t a) : IsWL1 s a :=
  ha.of_nonneg_of_le
    (fun n => mul_nonneg (Real.rpow_nonneg (sobWeight_pos n).le _) (norm_nonneg _))
    (fun n => mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow_of_exponent_le (one_le_sobWeight n) hst) (norm_nonneg _))

/-- The actual continuous nonconjugate angular velocity of F on the circle. -/
def localConformalVelocityCircle (F : ℂ → ℂ) : C(AddCircle (2 * Real.pi), ℂ) :=
  ⟨fun q => conj (localConformalPrimitiveCircle F q),
    Complex.continuous_conj.comp (localConformalPrimitiveCircle F).continuous⟩

theorem localConformalVelocityCircle_apply {R : ℝ} (hR : 1 < R) (F : ℂ → ℂ)
    (hFs : ContDiffOn ℝ (⊤ : ℕ∞) F (ball (0 : ℂ) R)) (θ : ℝ) :
    localConformalVelocityCircle F (θ : AddCircle (2 * Real.pi)) =
      deriv (physicalCircleTrace F) θ := by
  change conj (localConformalPrimitiveCircle F (θ : AddCircle (2 * Real.pi))) = _
  rw [localConformalPrimitiveCircle_apply hR F hFs, Complex.conj_conj]

private theorem bridge_circle_coeff (A : C(AddCircle (2 * Real.pi), ℂ)) :
    fourierCoeff A = fourierCoeffOn Real.two_pi_pos
      (fun θ : ℝ => A (θ : AddCircle (2 * Real.pi))) := by
  funext n
  have he : AddCircle.liftIoc (2 * Real.pi) 0
      (fun θ : ℝ => A (θ : AddCircle (2 * Real.pi))) =
      (A : AddCircle (2 * Real.pi) → ℂ) := by
    funext q
    change A ((AddCircle.equivIoc (2 * Real.pi) 0 q : ℝ) : AddCircle (2 * Real.pi)) = A q
    have hrep : ((AddCircle.equivIoc (2 * Real.pi) 0 q : ℝ) : AddCircle (2 * Real.pi)) = q :=
      (AddCircle.equivIoc (2 * Real.pi) 0).symm_apply_apply q
    rw [hrep]
  have h := fourierCoeff_liftIoc_eq (T := 2 * Real.pi) (a := 0)
    (fun θ : ℝ => A (θ : AddCircle (2 * Real.pi))) n
  simpa only [he, zero_add] using h

theorem localConformalVelocityCircle_coeff {R : ℝ} (hR : 1 < R) (F : ℂ → ℂ)
    (hFs : ContDiffOn ℝ (⊤ : ℕ∞) F (ball (0 : ℂ) R)) :
    fourierCoeff (localConformalVelocityCircle F) =
      fourierCoeffOn Real.two_pi_pos (deriv (physicalCircleTrace F)) := by
  rw [bridge_circle_coeff]
  congr 1
  exact funext (localConformalVelocityCircle_apply hR F hFs)

theorem localConformalVelocityCircle_isWL1_half {R : ℝ} (hR : 1 < R)
    (F : ℂ → ℂ) (hFs : ContDiffOn ℝ (⊤ : ℕ∞) F (ball (0 : ℂ) R)) :
    IsWL1 (1 / 2 : ℝ) (fourierCoeff (localConformalVelocityCircle F)) := by
  rw [localConformalVelocityCircle_coeff hR F hFs]
  exact bridge_isWL1_mono (by norm_num)
    (periodic_contDiff_four_fourier_weights
      (contDiff_physicalCircleTrace_four_of_neighborhood hR F
        (hFs.of_le (WithTop.coe_le_coe.mpr le_top)))
      (physicalCircleTrace_periodic F)).1

private theorem bridge_half_pairing (q t b : L2Z)
    (hq : ∀ n, q n = (Real.sqrt (sobWeight n) : ℂ) * t n) :
    ⟪q, sobolevSmoothing (1 / 2 : ℝ) (by norm_num) b⟫_ℂ = ⟪t, b⟫_ℂ := by
  rw [lp.inner_eq_tsum, lp.inner_eq_tsum]
  refine tsum_congr fun n => ?_
  simp only [RCLike.inner_apply', hq, sobolevSmoothing, diagOp_apply,
    map_mul, Complex.conj_ofReal]
  have hw : (Real.sqrt (sobWeight n) : ℂ) *
      ((sobWeight n ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) = 1 := by
    rw [Real.sqrt_eq_rpow, ← Complex.ofReal_mul, sobWeight_rpow_mul_neg, Complex.ofReal_one]
  calc
    _ = ((Real.sqrt (sobWeight n) : ℂ) * ((sobWeight n ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)) *
        (conj (t n) * b n) := by ring
    _ = _ := by rw [hw, one_mul]

/-! ## Direct Wirtinger–velocity Green pairing in conformal boundary coordinates -/

private theorem smooth_dbar_green {Ω : Set ℂ}
    (hb : Bornology.IsBounded Ω) (hL : IsLipschitzDomain Ω) {γ : ℝ → ℂ}
    (hγ : IsBoundaryParam Ω γ) {p : ℂ → ℂ} (hp : TestFunction univ p) :
    (∫ z in Ω, dirD p 1 z) + Complex.I * (∫ z in Ω, dirD p Complex.I z) =
      ∫ s in Ioc (0 : ℝ) (2 * Real.pi), -Complex.I * (p (γ s) * deriv γ s) := by
  obtain ⟨Kp, hKp⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hp.2.1 hp.1 (by simp)
  have hg : (∫ s in Ioc (0 : ℝ) (2 * Real.pi), p (γ s) * deriv γ s) =
      2 * Complex.I * ∫ z in Ω, dbar p z := by
    simpa only [intervalIntegral.integral_of_le (by positivity : (0 : ℝ) ≤ 2 * Real.pi)]
      using integral_boundary_eq_dbar hb hL hγ hKp hp.2.1
  have hdx : IntegrableOn (dirD p 1) Ω := memLp_one_iff_integrable.mp ((hp.dirD 1).memLp' 1)
  have hdy : IntegrableOn (dirD p Complex.I) Ω :=
    memLp_one_iff_integrable.mp ((hp.dirD Complex.I).memLp' 1)
  rw [integral_const_mul, hg]
  calc
    (∫ z in Ω, dirD p 1 z) + Complex.I * (∫ z in Ω, dirD p Complex.I z) =
        ∫ z in Ω, dirD p 1 z + Complex.I * dirD p Complex.I z := by
      rw [integral_add hdx (hdy.const_mul _), integral_const_mul]
    _ = -Complex.I * (2 * Complex.I * ∫ z in Ω, dbar p z) := by
      rw [← integral_const_mul, ← integral_const_mul]
      refine integral_congr_ae (Eventually.of_forall fun z => ?_)
      dsimp only [dbar, dirD]
      ring_nf
      simp only [Complex.I_sq, show Complex.I ^ 3 = -Complex.I by rw [pow_succ, Complex.I_sq, neg_one_mul]]
      ring

private theorem smooth_d_green {Ω : Set ℂ}
    (hb : Bornology.IsBounded Ω) (hL : IsLipschitzDomain Ω) {γ : ℝ → ℂ}
    (hγ : IsBoundaryParam Ω γ) {p : ℂ → ℂ} (hp : TestFunction univ p) :
    (∫ z in Ω, dirD p 1 z) - Complex.I * (∫ z in Ω, dirD p Complex.I z) =
      ∫ s in Ioc (0 : ℝ) (2 * Real.pi), Complex.I * (p (γ s) * conj (deriv γ s)) := by
  have h := congrArg conj (smooth_dbar_green hb hL hγ hp.conj)
  have hd (v : ℂ) : conj (∫ z in Ω, dirD (fun w => conj (p w)) v z) = ∫ z in Ω, dirD p v z := by
    rw [← integral_conj]
    refine integral_congr_ae (Eventually.of_forall fun z => ?_)
    simp only [dirD_conj (hp.1.of_le (by simp)), Complex.conj_conj]
  rw [map_add, map_mul, Complex.conj_I, hd 1, hd Complex.I, ← integral_conj] at h
  simpa only [sub_eq_add_neg, neg_mul, map_mul, map_neg, Complex.conj_I,
    Complex.conj_conj, neg_neg] using h

section CoordinatePairing

variable {R C : ℝ} (hR : 1 < R) (F : ℂ → ℂ)
    (hFs : ContDiffOn ℝ (⊤ : ℕ∞) F (ball (0 : ℂ) R))
    (hb : Bornology.IsBounded (F '' ball (0 : ℂ) 1))
    (hL : IsLipschitzDomain (F '' ball (0 : ℂ) 1))
    (hhol : DifferentiableOn ℂ F (ball (0 : ℂ) 1))
    (hinj : InjOn F (ball (0 : ℂ) 1))
    (hC : ∀ z ∈ ball (0 : ℂ) 1, 1 ≤ C * ‖deriv F z‖ ^ 2)
    {γ : ℝ → ℂ} (hγ : IsBoundaryParam (F '' ball (0 : ℂ) 1) γ)
    {τ : ℝ → ℝ} {c : ℝ} (hτ : IsC1TraceReparam τ c)
    (hcoord : ∀ θ, F (circleMap 0 1 θ) = γ (τ θ))

local notation "ΩF" => F '' ball (0 : ℂ) 1
local notation "TF" => localConformalDiskH1Trace hR F hFs hL

include hR hFs hγ hτ hcoord in
private theorem bridge_velocity_jacobian (conjugated : Bool) :
    (fun θ : ℝ => if conjugated then
        localConformalPrimitiveCircle F (θ : AddCircle (2 * Real.pi)) else
        localConformalVelocityCircle F (θ : AddCircle (2 * Real.pi))) =ᵐ[
      volume.restrict (Ioc (0 : ℝ) (2 * Real.pi))]
      fun θ => deriv τ θ •
        (if conjugated then conj (deriv γ (τ θ)) else deriv γ (τ θ)) := by
  obtain ⟨B, hB⟩ := hγ.lipschitz
  obtain ⟨D, hD⟩ := hτ.lipschitz
  have hchain := (ae_deriv_comp hB hτ.monotone hD).filter_mono
    (ae_restrict_le : ae (volume.restrict (Ioc (0 : ℝ) (2 * Real.pi))) ≤ ae volume)
  have he : γ ∘ τ = physicalCircleTrace F := funext fun θ => (hcoord θ).symm
  rw [he] at hchain
  filter_upwards [hchain] with θ hθ
  cases conjugated <;> simp only [Bool.false_eq_true, ↓reduceIte,
    localConformalPrimitiveCircle_apply hR F hFs,
    localConformalVelocityCircle_apply hR F hFs, hθ,
    Complex.real_smul, map_mul, Complex.conj_ofReal]

include hb hhol hinj hC hγ hτ hcoord in
private theorem wirtinger_velocity_pairing (conjugated : Bool) (w u : NeumannH1 ΩF) :
    ⟪h1Gradient ΩF 0 w, h1Value ΩF u⟫_ℂ +
        ⟪h1Gradient ΩF 1 w, (if conjugated then -Complex.I else Complex.I) • h1Value ΩF u⟫_ℂ +
        ⟪h1Value ΩF w, (2 : ℂ) •
          (if conjugated then h1WirtingerD ΩF else h1WirtingerDbar ΩF) u⟫_ℂ =
      ⟪TF w, (if conjugated then Complex.I else -Complex.I) •
        boundaryContinuousMultiplier
          (if conjugated then localConformalPrimitiveCircle F else
            localConformalVelocityCircle F) (TF u)⟫_ℂ := by
  let c1 : ℂ := if conjugated then -Complex.I else Complex.I
  let c2 : ℂ := if conjugated then Complex.I else -Complex.I
  let WOp : NeumannH1 ΩF →L[ℂ] L2 ΩF := if conjugated then h1WirtingerD ΩF else h1WirtingerDbar ΩF
  let M : BoundaryL2 →L[ℂ] BoundaryL2 := boundaryContinuousMultiplier
    (if conjugated then localConformalPrimitiveCircle F else localConformalVelocityCircle F)
  change (⟪h1Gradient ΩF 0 w, h1Value ΩF u⟫_ℂ + ⟪h1Gradient ΩF 1 w, c1 • h1Value ΩF u⟫_ℂ) +
      ⟪h1Value ΩF w, (2 : ℂ) • WOp u⟫_ℂ = ⟪TF w, c2 • M (TF u)⟫_ℂ
  refine (denseRange_smoothTraceH1Lin hb hL).induction_on
    (p := fun v => (⟪h1Gradient ΩF 0 v, h1Value ΩF u⟫_ℂ + ⟪h1Gradient ΩF 1 v, c1 • h1Value ΩF u⟫_ℂ) +
      ⟪h1Value ΩF v, (2 : ℂ) • WOp u⟫_ℂ = ⟪TF v, c2 • M (TF u)⟫_ℂ) w ?_ ?_
  · exact isClosed_eq
      ((((h1Gradient ΩF 0).continuous.inner continuous_const).add
        ((h1Gradient ΩF 1).continuous.inner continuous_const)).add
        ((h1Value ΩF).continuous.inner continuous_const))
      ((TF).continuous.inner continuous_const)
  · intro f
    refine (denseRange_smoothTraceH1Lin hb hL).induction_on
      (p := fun v =>
        (⟪h1Gradient ΩF 0 (smoothTraceH1 ΩF f), h1Value ΩF v⟫_ℂ +
          ⟪h1Gradient ΩF 1 (smoothTraceH1 ΩF f), c1 • h1Value ΩF v⟫_ℂ) +
          ⟪h1Value ΩF (smoothTraceH1 ΩF f), (2 : ℂ) • WOp v⟫_ℂ =
          ⟪TF (smoothTraceH1 ΩF f), c2 • M (TF v)⟫_ℂ) u ?_ ?_
    · exact isClosed_eq
        (((continuous_const.inner (h1Value ΩF).continuous).add
          (continuous_const.inner (c1 • h1Value ΩF).continuous)).add
          (continuous_const.inner ((2 : ℂ) • WOp).continuous))
        (continuous_const.inner (c2 • (M.comp TF)).continuous)
    · intro g
      simp only [smoothTraceH1Lin_apply]
      let wf := smoothTraceH1 ΩF f
      let ug := smoothTraceH1 ΩF g
      let p : ℂ → ℂ := fun z => conj (f z) * g z
      have hp : TestFunction univ p :=
        ⟨f.property.conj.1.mul g.property.1, f.property.conj.2.1.mul_right, subset_univ _⟩
      have hgv (i : Fin 2) : ⟪h1Gradient ΩF i wf, h1Value ΩF ug⟫_ℂ =
          ∫ z in ΩF, dirD (fun w => conj (f w)) (coordDir i) z * g z := by
        rw [h1Gradient_smoothTraceH1, h1Value_smoothTraceH1, L2.inner_def]
        apply integral_congr_ae
        filter_upwards [(smoothTraceTests_memLp_deriv ΩF f i).coeFn_toLp,
          (smoothTraceTests_memLp ΩF g).coeFn_toLp] with z hf hg
        simp only [RCLike.inner_apply', hf, hg]
        rw [dirD_conj (f.property.1.of_le (by simp))]; rfl
      have hvg (i : Fin 2) : ⟪h1Value ΩF wf, h1Gradient ΩF i ug⟫_ℂ =
          ∫ z in ΩF, conj (f z) * dirD (g : ℂ → ℂ) (coordDir i) z := by
        rw [h1Value_smoothTraceH1, h1Gradient_smoothTraceH1, L2.inner_def]
        apply integral_congr_ae
        filter_upwards [(smoothTraceTests_memLp ΩF f).coeFn_toLp,
          (smoothTraceTests_memLp_deriv ΩF g i).coeFn_toLp] with z hf hg
        simp only [RCLike.inner_apply', hf, hg, dirD]
      have hprod (i : Fin 2) :
          (∫ z in ΩF, dirD (fun w => conj (f w)) (coordDir i) z * g z) +
            (∫ z in ΩF, conj (f z) * dirD (g : ℂ → ℂ) (coordDir i) z) =
            ∫ z in ΩF, dirD p (coordDir i) z := by
        have h1 : IntegrableOn (fun z => dirD (fun w => conj (f w)) (coordDir i) z * g z) ΩF :=
          integrable_mul_test ((f.property.conj.dirD (coordDir i)).memLp' 2) g.property
        have h2 : IntegrableOn (fun z => conj (f z) * dirD (g : ℂ → ℂ) (coordDir i) z) ΩF :=
          integrable_mul_test (f.property.conj.memLp' 2) (g.property.dirD (coordDir i))
        rw [← integral_add h1 h2]
        refine integral_congr_ae (Eventually.of_forall fun z => ?_)
        simp only [dirD, p]
        rw [fderiv_fun_mul (f.property.conj.1.differentiable (by simp) z)
          (g.property.1.differentiable (by simp) z)]
        simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
        ring
      have hdir0 : coordDir (0 : Fin 2) = (1 : ℂ) := rfl
      have hdir1 : coordDir (1 : Fin 2) = Complex.I := rfl
      cases conjugated
      · dsimp only [c1, c2, WOp, M]
        simp only [Bool.false_eq_true, ↓reduceIte]
        rw [show (2 : ℂ) • h1WirtingerDbar ΩF ug =
              h1Gradient ΩF 0 ug + Complex.I • h1Gradient ΩF 1 ug by
            rw [h1WirtingerDbar_apply]; module,
          inner_smul_right, inner_add_right, inner_smul_right, hgv 0, hgv 1, hvg 0, hvg 1]
        calc
          _ = ((∫ z in ΩF, dirD (fun w => conj (f w)) (coordDir 0) z * g z) +
                (∫ z in ΩF, conj (f z) * dirD (g : ℂ → ℂ) (coordDir 0) z)) +
              Complex.I * ((∫ z in ΩF, dirD (fun w => conj (f w)) (coordDir 1) z * g z) +
                (∫ z in ΩF, conj (f z) * dirD (g : ℂ → ℂ) (coordDir 1) z)) := by ring
          _ = ∫ s in Ioc (0 : ℝ) (2 * Real.pi), -Complex.I * (p (γ s) * deriv γ s) := by
            rw [hprod 0, hprod 1, hdir0, hdir1]
            exact smooth_dbar_green hb hL hγ hp
          _ = ∫ θ in Ioc (0 : ℝ) (2 * Real.pi),
                deriv τ θ • (-Complex.I * (p (γ (τ θ)) * deriv γ (τ θ))) :=
            (integral_traceReparam_conormal hτ _).symm
          _ = _ := by
            rw [L2.inner_def]
            apply integral_congr_ae
            filter_upwards [localConformalDiskH1Trace_smooth_ae hR F hFs hb hL hhol hinj hC f,
              localConformalDiskH1Trace_smooth_ae hR F hFs hb hL hhol hinj hC g,
              Lp.coeFn_smul (-Complex.I)
                (boundaryContinuousMultiplier (localConformalVelocityCircle F)
                  (TF (smoothTraceH1 ΩF g))),
              boundaryContinuousMultiplier_ae (localConformalVelocityCircle F)
                (TF (smoothTraceH1 ΩF g)),
              bridge_velocity_jacobian hR F hFs hγ hτ hcoord false] with θ hf hg hsm hm hj
            simp only [Bool.false_eq_true, ↓reduceIte] at hj
            simp only [p, RCLike.inner_apply', hf, hsm, Pi.smul_apply, smul_eq_mul, hm, hg, hcoord]
            rw [hj]; simp only [Complex.real_smul]; ring
      · dsimp only [c1, c2, WOp, M]
        simp only [↓reduceIte]
        rw [show (2 : ℂ) • h1WirtingerD ΩF ug =
              h1Gradient ΩF 0 ug - Complex.I • h1Gradient ΩF 1 ug by
            rw [h1WirtingerD_apply]; module,
          inner_smul_right, inner_sub_right, inner_smul_right, hgv 0, hgv 1, hvg 0, hvg 1]
        calc
          _ = ((∫ z in ΩF, dirD (fun w => conj (f w)) (coordDir 0) z * g z) +
                (∫ z in ΩF, conj (f z) * dirD (g : ℂ → ℂ) (coordDir 0) z)) -
              Complex.I * ((∫ z in ΩF, dirD (fun w => conj (f w)) (coordDir 1) z * g z) +
                (∫ z in ΩF, conj (f z) * dirD (g : ℂ → ℂ) (coordDir 1) z)) := by ring
          _ = ∫ s in Ioc (0 : ℝ) (2 * Real.pi), Complex.I * (p (γ s) * conj (deriv γ s)) := by
            rw [hprod 0, hprod 1, hdir0, hdir1]
            exact smooth_d_green hb hL hγ hp
          _ = ∫ θ in Ioc (0 : ℝ) (2 * Real.pi),
                deriv τ θ • (Complex.I * (p (γ (τ θ)) * conj (deriv γ (τ θ)))) :=
            (integral_traceReparam_conormal hτ _).symm
          _ = _ := by
            rw [L2.inner_def]
            apply integral_congr_ae
            filter_upwards [localConformalDiskH1Trace_smooth_ae hR F hFs hb hL hhol hinj hC f,
              localConformalDiskH1Trace_smooth_ae hR F hFs hb hL hhol hinj hC g,
              Lp.coeFn_smul Complex.I
                (boundaryContinuousMultiplier (localConformalPrimitiveCircle F)
                  (TF (smoothTraceH1 ΩF g))),
              boundaryContinuousMultiplier_ae (localConformalPrimitiveCircle F)
                (TF (smoothTraceH1 ΩF g)),
              bridge_velocity_jacobian hR F hFs hγ hτ hcoord true] with θ hf hg hsm hm hj
            simp only [↓reduceIte] at hj
            simp only [p, RCLike.inner_apply', hf, hsm, Pi.smul_apply, smul_eq_mul, hm, hg, hcoord]
            rw [hj]; simp only [Complex.real_smul]; ring

end CoordinatePairing

/-! ## Physical coordinates, coordinate flux, and normalized conormal weak form -/

section PhysicalCoordinates

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
local notation "UF" => localConformalHardyH1Extension hR F hFs hb hL hhol hinj hC hK e he hsource hes
local notation "JF" => localConformalHardyPrimitive hR F hFs
local notation "MF" => neumannH1AffineMultiplier hb
local notation "VF" => localConformalVekuaH1 hR F hFs hb hL hhol hinj hC hK e he hsource hes
local notation "TF" => localConformalDiskH1Trace hR F hFs hL
local notation "QF" => localConformalDiskHalfTrace hR F hFs hL

theorem localConformalHardyH1Extension_principal_conormal (b : L2Z)
    (w : NeumannH1 ΩF) :
    (∑ i : Fin 2, ⟪h1Gradient ΩF i w, h1Gradient ΩF i (UF b)⟫_ℂ) =
      ⟪QF w, normalizedConormalPrincipal ((1 - posProj) b)⟫_ℂ := by
  rw [← localConformalH1Pullback_gradient_inner hR F hFs hb hL hhol hinj hC,
    localConformalH1Pullback_hardyExtension]
  exact diskHardyExtension_principal_conormal b (localConformalH1Pullback hR F hFs hL w)

def localConformalVekuaRemainder (p E : ℂ) : L2Z →L[ℂ] NeumannH1 ΩF :=
  VF p E - UF

def localConformalVekuaGradientA (p E : ℂ) : L2Z →L[ℂ] NeumannH1 ΩF :=
  (-E / 4) • ((VF p E).comp JF)

def localConformalVekuaGradientB (p E : ℂ) : L2Z →L[ℂ] NeumannH1 ΩF :=
  boundedPhysicalVekuaGradientB (MF p) UF JF E

local notation "RF" => localConformalVekuaRemainder hR F hFs hb hL hhol hinj hC hK e he hsource hes
local notation "AF" => localConformalVekuaGradientA hR F hFs hb hL hhol hinj hC hK e he hsource hes
local notation "BF" => localConformalVekuaGradientB hR F hFs hb hL hhol hinj hC hK e he hsource hes

theorem localConformalVekuaRemainder_apply (p E : ℂ) (b : L2Z) :
    RF p E b = VF p E b - UF b := rfl

theorem localConformalVekuaGradientA_apply (p E : ℂ) (b : L2Z) :
    AF p E b = (-E / 4) • VF p E (JF b) := rfl

theorem localConformalVekuaRemainder_hasSum (p E : ℂ) (b : L2Z) :
    HasSum (fun j : ℕ => physicalVekuaCoeff E (j + 1) •
      ((MF p) ^ (j + 1)) (UF ((JF ^ (j + 1)) b))) (RF p E b) := by
  have hs := localConformalVekuaH1_hasSum hR F hFs hb hL hhol hinj hC hK
    e he hsource hes p E b
  simpa only [Finset.sum_range_one, physicalVekuaCoeff_zero, pow_zero,
    ContinuousLinearMap.one_apply, one_smul, localConformalVekuaRemainder_apply] using
      (hasSum_nat_add_iff' 1).2 hs

theorem localConformalVekuaGradientA_hasSum (p E : ℂ) (b : L2Z) :
    HasSum (fun j : ℕ => (physicalVekuaCoeff E (j + 1) * ((j + 1 : ℕ) : ℂ)) •
      ((MF p) ^ j) (UF ((JF ^ (j + 1)) b))) (AF p E b) := by
  have hs := (localConformalVekuaH1_hasSum hR F hFs hb hL hhol hinj hC hK
    e he hsource hes p E (JF b)).const_smul (-E / 4)
  simpa only [localConformalVekuaGradientA_apply, physicalVekuaCoeff_succ,
    pow_succ, ContinuousLinearMap.mul_apply, smul_smul] using hs

theorem localConformalVekuaGradientB_hasSum (p E : ℂ) (b : L2Z) :
    HasSum (fun j : ℕ => physicalVekuaCoeff E (j + 1) •
      ((MF p) ^ (j + 1)) (UF ((JF ^ j) b))) (BF p E b) :=
  boundedPhysicalVekuaGradientB_hasSum_apply (MF p) UF JF E b

private theorem conormal_primitive_Dbar (b : L2Z)
    (hbn : IsNonpositiveFourierSupport b) (j : ℕ) :
    h1WirtingerDbar ΩF (UF ((JF ^ (j + 1)) b)) = h1Value ΩF (UF ((JF ^ j) b)) := by
  rw [pow_succ', ContinuousLinearMap.mul_apply]
  exact localConformalHardyH1Extension_wirtingerDbar_primitive hR F hFs hb hL hhol hinj hC hK
    e he hsource hes _ (localConformalHardyPrimitive_pow_nonpositive hR F hFs hhol b hbn j)

theorem localConformalVekuaRemainder_gradient_x (p E : ℂ) (b : L2Z)
    (hbn : IsNonpositiveFourierSupport b) :
    h1Gradient ΩF 0 (RF p E b) = h1Value ΩF (AF p E b + BF p E b) := by
  have heq (j : ℕ) : h1Gradient ΩF 0
      (physicalVekuaCoeff E (j + 1) • ((MF p) ^ (j + 1)) (UF ((JF ^ (j + 1)) b))) =
      h1Value ΩF
        ((physicalVekuaCoeff E (j + 1) * ((j + 1 : ℕ) : ℂ)) •
          ((MF p) ^ j) (UF ((JF ^ (j + 1)) b)) +
          physicalVekuaCoeff E (j + 1) • ((MF p) ^ (j + 1)) (UF ((JF ^ j) b))) := by
    rw [map_smul, conormal_affine_gradient_x hb p _ _ j
      (localConformalHardyH1Extension_cauchyRiemann hR F hFs hb hL hhol hinj hC hK e he hsource hes _)
      (conormal_primitive_Dbar hR F hFs hb hL hhol hinj hC hK e he hsource hes b hbn j),
      ← map_smul, smul_add, smul_smul]
  exact (((h1Gradient ΩF 0).hasSum
    (localConformalVekuaRemainder_hasSum hR F hFs hb hL hhol hinj hC hK e he hsource hes p E b)).congr_fun
    fun j => (heq j).symm).unique <| (h1Value ΩF).hasSum <|
    (localConformalVekuaGradientA_hasSum hR F hFs hb hL hhol hinj hC hK e he hsource hes p E b).add
    (localConformalVekuaGradientB_hasSum hR F hFs hb hL hhol hinj hC hK e he hsource hes p E b)

theorem localConformalVekuaRemainder_gradient_y (p E : ℂ) (b : L2Z)
    (hbn : IsNonpositiveFourierSupport b) :
    h1Gradient ΩF 1 (RF p E b) = h1Value ΩF (Complex.I • (AF p E b - BF p E b)) := by
  have heq (j : ℕ) : h1Gradient ΩF 1
      (physicalVekuaCoeff E (j + 1) • ((MF p) ^ (j + 1)) (UF ((JF ^ (j + 1)) b))) =
      h1Value ΩF (Complex.I •
        ((physicalVekuaCoeff E (j + 1) * ((j + 1 : ℕ) : ℂ)) •
          ((MF p) ^ j) (UF ((JF ^ (j + 1)) b)) -
          physicalVekuaCoeff E (j + 1) • ((MF p) ^ (j + 1)) (UF ((JF ^ j) b)))) := by
    rw [map_smul, conormal_affine_gradient_y hb p _ _ j
      (localConformalHardyH1Extension_cauchyRiemann hR F hFs hb hL hhol hinj hC hK e he hsource hes _)
      (conormal_primitive_Dbar hR F hFs hb hL hhol hinj hC hK e he hsource hes b hbn j),
      ← map_smul]
    congr 1; module
  exact (((h1Gradient ΩF 1).hasSum
    (localConformalVekuaRemainder_hasSum hR F hFs hb hL hhol hinj hC hK e he hsource hes p E b)).congr_fun
    fun j => (heq j).symm).unique <| (h1Value ΩF).hasSum <|
    ((localConformalVekuaGradientA_hasSum hR F hFs hb hL hhol hinj hC hK e he hsource hes p E b).sub
      (localConformalVekuaGradientB_hasSum hR F hFs hb hL hhol hinj hC hK e he hsource hes p E b)).const_smul
      Complex.I

theorem localConformalVekuaGradientA_Dbar (p E : ℂ) (b : L2Z)
    (hbn : IsNonpositiveFourierSupport b) :
    h1WirtingerDbar ΩF (AF p E b) = (-E / 4) • h1Value ΩF (VF p E b) := by
  rw [localConformalVekuaGradientA_apply, map_smul,
    localConformalVekuaH1_wirtingerDbar_primitive hR F hFs hb hL hhol hinj hC hK
      e he hsource hes p E b hbn]

theorem localConformalVekuaGradientB_D (p E : ℂ) (b : L2Z) :
    h1WirtingerD ΩF (BF p E b) = (-E / 4) • h1Value ΩF (VF p E b) := by
  have heq (j : ℕ) : h1WirtingerD ΩF
      (physicalVekuaCoeff E (j + 1) • ((MF p) ^ (j + 1)) (UF ((JF ^ j) b))) =
      (-E / 4) • h1Value ΩF (physicalVekuaCoeff E j • ((MF p) ^ j) (UF ((JF ^ j) b))) := by
    rw [map_smul, h1WirtingerD_affine_pow_of_antiholomorphic hb p _
      (localConformalHardyH1Extension_cauchyRiemann hR F hFs hb hL hhol hinj hC hK
        e he hsource hes _) j, smul_smul, physicalVekuaCoeff_succ, map_smul, smul_smul]
  exact (((h1WirtingerD ΩF).hasSum
    (localConformalVekuaGradientB_hasSum hR F hFs hb hL hhol hinj hC hK
      e he hsource hes p E b)).congr_fun fun j => (heq j).symm).unique <|
    ((h1Value ΩF).hasSum
      (localConformalVekuaH1_hasSum hR F hFs hb hL hhol hinj hC hK
        e he hsource hes p E b)).const_smul (-E / 4)

local notation "MF1" => neumannH1AffineMultiplier hb (F 1)
local notation "βF" => fourierCoeff (localConformalVelocityCircle F)
local notation "aF" => localConformalHardyPrimitiveMultiplier F
local notation "gF" => fourierCoeff (localConformalCenteredCircle hR F hFs)
local notation "hβF" => localConformalVelocityCircle_isWL1_half hR F hFs
local notation "haF" => localConformalHardyPrimitiveMultiplier_isWL1 hR F hFs
local notation "hgF" => localConformalCenteredCircle_isWL1_half hR F hFs

/-- The genuine coordinate flux; its two inputs are the actual H¹ gradient
representatives. The variable circle speed is included in its velocities. -/
def localConformalVekuaCoordinateConormalRemainder (E : ℂ) : L2Z →L[ℂ] BoundaryL2 :=
  (-Complex.I) • ((boundaryContinuousMultiplier (localConformalVelocityCircle F)).comp
      ((TF).comp (AF (F 1) E))) +
    Complex.I • ((boundaryContinuousMultiplier (localConformalPrimitiveCircle F)).comp
      ((TF).comp (BF (F 1) E)))

local notation "CCF" => localConformalVekuaCoordinateConormalRemainder
  hR F hFs hb hL hhol hinj hC hK e he hsource hes

private theorem bridge_fromL2_multiplier (a : ℤ → ℂ)
    (ha : IsWL1 (1 / 2 : ℝ) a) (b : L2Z) :
    fromL2 (1 / 2 : ℝ) (normalizedHardyMultiplier a ha b) =
      seqConv a (fromL2 (1 / 2 : ℝ) b) := by
  funext n
  rw [fromL2, normalizedHardyMultiplier_apply, ← mul_assoc, ← Complex.ofReal_mul,
    mul_comm (sobWeight n ^ (-(1 / 2 : ℝ))), sobWeight_rpow_mul_neg,
    Complex.ofReal_one, one_mul]

theorem localConformalVekuaConormal_trace_term (b : L2Z)
    (hbn : IsNonpositiveFourierSupport b) (j k : ℕ) :
    (boundaryFourier (TF ((MF1 ^ j) (UF ((JF ^ k) b)))) : ℤ → ℂ) =
      seqConv (seqConvPow gF j) (antiPrimIter aF k (fromL2 (1 / 2 : ℝ) b)) := by
  rw [← fromL2_half_localConformalDiskHalfTrace,
    localConformalDiskHalfTrace_affineMultiplier_pow hR F hFs hb hL hhol hinj hC,
    bridge_fromL2_multiplier,
    localConformalDiskHalfTrace_hardyExtension_eq_of_nonpositive hR F hFs hb hL hhol
      hinj hC hK e he hsource hes _
      (localConformalHardyPrimitive_pow_nonpositive hR F hFs hhol b hbn k),
    fromL2_localConformalHardyPrimitive_pow]

def bridge_coordinateNormalizer : BoundaryL2 →L[ℂ] L2Z :=
  (sobolevSmoothing (1 / 2 : ℝ) (by norm_num)).comp
    boundaryFourier.toLinearIsometry.toContinuousLinearMap

private theorem bridge_coordinateNormalizer_multiplier (A : C(AddCircle (2 * Real.pi), ℂ))
    (hA : Summable (fourierCoeff A)) (u : NeumannH1 ΩF) (n : ℤ) :
    bridge_coordinateNormalizer (boundaryContinuousMultiplier A (TF u)) n =
      ((sobWeight n ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
        seqConv (fourierCoeff A) (boundaryFourier (TF u)) n := by
  change ((sobWeight n ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * boundaryFourier _ n = _
  rw [boundaryFourier_continuousMultiplier A hA]

private theorem bridge_smoothed_conormalTerm_apply (j : ℕ) (b : L2Z) (n : ℤ) :
    sobolevSmoothing 1 zero_le_one
        (conormalTermOp (by norm_num) hβF haF hgF j b) n =
      ((sobWeight n ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
        conormalTermMap βF aF gF j (fromL2 (1 / 2 : ℝ) b) n := by
  change ((sobWeight n ^ (-(1 : ℝ)) : ℝ) : ℂ) *
      conormalTermOp (by norm_num) hβF haF hgF j b n = _
  rw [conormalTermOp]
  change ((sobWeight n ^ (-(1 : ℝ)) : ℝ) : ℂ) *
      (((sobWeight n ^ (1 / 2 : ℝ) : ℝ) : ℂ) * conormalTermMap βF aF gF j (fromL2 (1 / 2 : ℝ) b) n) = _
  rw [← mul_assoc, ← Complex.ofReal_mul, ← Real.rpow_add (sobWeight_pos n)]
  norm_num

theorem localConformalVekuaConormal_coordinate_term (E : ℂ) (b : L2Z)
    (hbn : IsNonpositiveFourierSupport b) (j : ℕ) :
    bridge_coordinateNormalizer
      ((-Complex.I) • boundaryContinuousMultiplier (localConformalVelocityCircle F)
          (TF ((physicalVekuaCoeff E (j + 1) * ((j + 1 : ℕ) : ℂ)) •
            (MF1 ^ j) (UF ((JF ^ (j + 1)) b)))) +
        Complex.I • boundaryContinuousMultiplier (localConformalPrimitiveCircle F)
          (TF (physicalVekuaCoeff E (j + 1) •
            (MF1 ^ (j + 1)) (UF ((JF ^ j) b))))) =
      conormalCoeff E j • sobolevSmoothing 1 zero_le_one
        (conormalTermOp (by norm_num) hβF haF hgF j b) := by
  have hβ : Summable βF := bridge_summable_coeff (by norm_num) hβF
  have ha : Summable (fourierCoeff (localConformalPrimitiveCircle F)) := by
    rw [localConformalPrimitiveCircle_coeff hR F hFs]
    exact bridge_summable_coeff (by norm_num) haF
  apply lp.ext; funext n
  simp only [map_add, map_smul, lp.coeFn_add, Pi.add_apply, lp.coeFn_smul,
    Pi.smul_apply, smul_eq_mul]
  rw [bridge_coordinateNormalizer_multiplier hR F hFs hL _ hβ,
    bridge_coordinateNormalizer_multiplier hR F hFs hL _ ha,
    localConformalPrimitiveCircle_coeff hR F hFs,
    localConformalVekuaConormal_trace_term hR F hFs hb hL hhol hinj hC hK e he hsource hes b hbn,
    localConformalVekuaConormal_trace_term hR F hFs hb hL hhol hinj hC hK e he hsource hes b hbn,
    bridge_smoothed_conormalTerm_apply hR F hFs j b n]
  simp only [conormalTermMap, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    conormalCoeff, physicalVekuaCoeff]
  ring

theorem localConformalVekuaCoordinateConormalRemainder_eq_conormalRemOp
    (E : ℂ) (b : L2Z) (hbn : IsNonpositiveFourierSupport b) :
    sobolevSmoothing (1 / 2 : ℝ) (by norm_num) (boundaryFourier (CCF E b)) =
      sobolevSmoothing 1 zero_le_one
        (conormalRemOp (by norm_num) hβF haF hgF E b) := by
  let P := (boundaryContinuousMultiplier (localConformalVelocityCircle F)).comp TF
  let Q := (boundaryContinuousMultiplier (localConformalPrimitiveCircle F)).comp TF
  have hA := (P.hasSum (localConformalVekuaGradientA_hasSum hR F hFs hb hL hhol hinj
    hC hK e he hsource hes (F 1) E b)).const_smul (-Complex.I)
  have hB := (Q.hasSum (localConformalVekuaGradientB_hasSum hR F hFs hb hL hhol hinj
    hC hK e he hsource hes (F 1) E b)).const_smul Complex.I
  have hl := (bridge_coordinateNormalizer.hasSum (hA.add hB)).congr_fun fun j =>
    (localConformalVekuaConormal_coordinate_term hR F hFs hb hL hhol hinj hC hK
      e he hsource hes E b hbn j).symm
  have hl' : HasSum (fun j : ℕ => conormalCoeff E j • sobolevSmoothing 1 zero_le_one
      (conormalTermOp (by norm_num) hβF haF hgF j b))
      (sobolevSmoothing (1 / 2 : ℝ) (by norm_num) (boundaryFourier (CCF E b))) := by
    have h_simpa := hl
    simp only [P, Q, bridge_coordinateNormalizer, localConformalVekuaCoordinateConormalRemainder,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.smul_apply, LinearIsometry.coe_toContinuousLinearMap,
      LinearIsometryEquiv.coe_toLinearIsometry] at h_simpa ⊢
    exact h_simpa
  have hr := (sobolevSmoothing 1 zero_le_one).hasSum
    ((ContinuousLinearMap.apply ℂ L2Z b).hasSum
      (summable_conormalSeries (by norm_num) hβF haF hgF E).hasSum)
  exact hl'.unique <| by
    simpa only [ContinuousLinearMap.apply_apply, ContinuousLinearMap.smul_apply,
      map_smul, conormalRemOp] using hr

variable {γ : ℝ → ℂ} (hγ : IsBoundaryParam (F '' ball (0 : ℂ) 1) γ)
    {τ : ℝ → ℝ} {c : ℝ} (hτ : IsC1TraceReparam τ c)
    (hcoord : ∀ θ, F (circleMap 0 1 θ) = γ (τ θ))

include hγ hτ hcoord in
/-- The actual Vekua solution has the existing normalized conormal weak
form, proved through its genuine physical gradient and boundary flux. -/
theorem localConformalVekuaH1_normalizedConormal_weak_form (E : ℂ) (b : L2Z)
    (hbn : IsNonpositiveFourierSupport b) (w : NeumannH1 ΩF) :
    (∑ i : Fin 2, ⟪h1Gradient ΩF i w, h1Gradient ΩF i (VF (F 1) E b)⟫_ℂ) -
        E * ⟪h1Value ΩF w, h1Value ΩF (VF (F 1) E b)⟫_ℂ =
      ⟪QF w, normalizedConormal hβF haF hgF E b⟫_ℂ := by
  have hA := wirtinger_velocity_pairing hR F hFs hb hL hhol hinj hC hγ hτ hcoord false
    w (AF (F 1) E b)
  have hB := wirtinger_velocity_pairing hR F hFs hb hL hhol hinj hC hγ hτ hcoord true
    w (BF (F 1) E b)
  simp only [Bool.false_eq_true, ↓reduceIte] at hA hB
  have hgx : ⟪h1Gradient ΩF 0 w, h1Value ΩF (AF (F 1) E b)⟫_ℂ +
      ⟪h1Gradient ΩF 0 w, h1Value ΩF (BF (F 1) E b)⟫_ℂ =
      ⟪h1Gradient ΩF 0 w, h1Gradient ΩF 0 (RF (F 1) E b)⟫_ℂ := by
    rw [← inner_add_right, ← map_add,
      localConformalVekuaRemainder_gradient_x hR F hFs hb hL hhol hinj hC hK
        e he hsource hes (F 1) E b hbn]
  have hgy : ⟪h1Gradient ΩF 1 w, Complex.I • h1Value ΩF (AF (F 1) E b)⟫_ℂ +
      ⟪h1Gradient ΩF 1 w, (-Complex.I) • h1Value ΩF (BF (F 1) E b)⟫_ℂ =
      ⟪h1Gradient ΩF 1 w, h1Gradient ΩF 1 (RF (F 1) E b)⟫_ℂ := by
    rw [← inner_add_right,
      show Complex.I • h1Value ΩF (AF (F 1) E b) + (-Complex.I) • h1Value ΩF (BF (F 1) E b) =
        h1Value ΩF (Complex.I • (AF (F 1) E b - BF (F 1) E b)) by
          rw [map_smul, map_sub, smul_sub, neg_smul, sub_eq_add_neg],
      localConformalVekuaRemainder_gradient_y hR F hFs hb hL hhol hinj hC hK
        e he hsource hes (F 1) E b hbn]
  have hmass : ⟪h1Value ΩF w, (2 : ℂ) • h1WirtingerDbar ΩF (AF (F 1) E b)⟫_ℂ +
      ⟪h1Value ΩF w, (2 : ℂ) • h1WirtingerD ΩF (BF (F 1) E b)⟫_ℂ =
      -(E * ⟪h1Value ΩF w, h1Value ΩF (VF (F 1) E b)⟫_ℂ) := by
    rw [localConformalVekuaGradientA_Dbar hR F hFs hb hL hhol hinj hC hK
        e he hsource hes (F 1) E b hbn,
      localConformalVekuaGradientB_D hR F hFs hb hL hhol hinj hC hK
        e he hsource hes (F 1) E b]
    simp only [inner_smul_right]
    ring
  have hrhs : ⟪TF w, (-Complex.I) • boundaryContinuousMultiplier (localConformalVelocityCircle F)
        (TF (AF (F 1) E b))⟫_ℂ +
      ⟪TF w, Complex.I • boundaryContinuousMultiplier (localConformalPrimitiveCircle F)
        (TF (BF (F 1) E b))⟫_ℂ =
      ⟪QF w, sobolevSmoothing 1 zero_le_one (conormalRemOp (by norm_num) hβF haF hgF E b)⟫_ℂ := by
    rw [← inner_add_right]
    change ⟪TF w, CCF E b⟫_ℂ = _
    rw [← boundaryFourier.inner_map_map,
      ← bridge_half_pairing (QF w) (boundaryFourier (TF w)) (boundaryFourier (CCF E b))
        (fun n => by simpa only [sobWeight] using localConformalDiskHalfTrace_apply hR F hFs hL w n),
      localConformalVekuaCoordinateConormalRemainder_eq_conormalRemOp hR F hFs hb hL hhol hinj
        hC hK e he hsource hes E b hbn]
  have hrem_eq : ⟪h1Gradient ΩF 0 w, h1Gradient ΩF 0 (RF (F 1) E b)⟫_ℂ +
      ⟪h1Gradient ΩF 1 w, h1Gradient ΩF 1 (RF (F 1) E b)⟫_ℂ -
      E * ⟪h1Value ΩF w, h1Value ΩF (VF (F 1) E b)⟫_ℂ =
      ⟪QF w, sobolevSmoothing 1 zero_le_one (conormalRemOp (by norm_num) hβF haF hgF E b)⟫_ℂ := by
    calc
      _ = (⟪h1Gradient ΩF 0 w, h1Value ΩF (AF (F 1) E b)⟫_ℂ +
            ⟪h1Gradient ΩF 1 w, Complex.I • h1Value ΩF (AF (F 1) E b)⟫_ℂ +
            ⟪h1Value ΩF w, (2 : ℂ) • h1WirtingerDbar ΩF (AF (F 1) E b)⟫_ℂ) +
          (⟪h1Gradient ΩF 0 w, h1Value ΩF (BF (F 1) E b)⟫_ℂ +
            ⟪h1Gradient ΩF 1 w, (-Complex.I) • h1Value ΩF (BF (F 1) E b)⟫_ℂ +
            ⟪h1Value ΩF w, (2 : ℂ) • h1WirtingerD ΩF (BF (F 1) E b)⟫_ℂ) := by
        rw [← hgx, ← hgy, sub_eq_add_neg, ← hmass]; ring
      _ = _ := (congrArg₂ (· + ·) hA hB).trans hrhs
  have hp := localConformalHardyH1Extension_principal_conormal hR F hFs hb hL hhol hinj hC hK
    e he hsource hes b w
  have hbproj : (1 - posProj) b = b := by
    ext n
    simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply,
      lp.coeFn_sub, Pi.sub_apply, posProj, diagOp_apply]
    by_cases hn : 0 < n
    · simp [hn, hbn n hn]
    · simp [hn]
  rw [hbproj] at hp
  have hsplit : (∑ i : Fin 2, ⟪h1Gradient ΩF i w, h1Gradient ΩF i (VF (F 1) E b)⟫_ℂ) -
      E * ⟪h1Value ΩF w, h1Value ΩF (VF (F 1) E b)⟫_ℂ =
      (∑ i : Fin 2, ⟪h1Gradient ΩF i w, h1Gradient ΩF i (UF b)⟫_ℂ) +
      (⟪h1Gradient ΩF 0 w, h1Gradient ΩF 0 (RF (F 1) E b)⟫_ℂ +
        ⟪h1Gradient ΩF 1 w, h1Gradient ΩF 1 (RF (F 1) E b)⟫_ℂ -
        E * ⟪h1Value ΩF w, h1Value ΩF (VF (F 1) E b)⟫_ℂ) := by
    simp only [Fin.sum_univ_two, localConformalVekuaRemainder_apply, map_sub, inner_sub_right]
    ring
  rw [hsplit, hp, hrem_eq, ← inner_add_right]
  rfl

end PhysicalCoordinates

end PolyaNeumann

end
