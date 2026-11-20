/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.ShiftEquations.Mobius.RepinTilt
/-! # Circle tilt at arbitrary nonnegative real times -/
@[expose] public section
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal
namespace DOZZ.Proofs
private theorem repin_log_radius_origin (m : ℝ) : -Real.log ‖((Real.exp (-m) : ℝ) : ℂ)‖ = m := by
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.log_exp, neg_neg]

section
variable (m : ℝ) (hm : 0 ≤ m)
include hm

/-- On the circle of radius `e^{-m} ≤ 1` the background `log |·|_+` vanishes. -/
theorem reflected_integral_log_normPlus_circle_origin :
    ∫ w, Real.log (normPlus w) ∂circleMeasure 0 m = 0 := by
  have hae : (fun w => Real.log (normPlus w)) =ᵐ[circleMeasure 0 m] fun _ => (0 : ℝ) := by
    filter_upwards [ae_norm_sub_center_circleMeasure 0 m] with w hw
    rw [sub_zero] at hw
    have hle : ‖w‖ ≤ 1 := by
      rw [hw]
      exact Real.exp_le_one_iff.mpr (by
        have := hm
        linarith)
    rw [normPlus, max_eq_left hle, Real.log_one]
  rw [integral_congr_ae hae, integral_zero]

/-- **The potential of the circle at the origin**:
`∫ G(x,u) dσ_{0,e^{-m}}(u) = log |x|_+ - log max(e^{-m}, |x|)`. -/
theorem reflected_repinPotential_origin (x : ℂ) :
    repinPotential ((Real.exp (-m) : ℝ) : ℂ) 0 x =
      Real.log (normPlus x) - Real.log (max (Real.exp (-m)) ‖x‖) := by
  have ha : ((Real.exp (-m) : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.exp_pos _).ne'
  rw [repinPotential_eq _ 0 ha x, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _), zero_sub, norm_neg]
  have hc : repinConst ((Real.exp (-m) : ℝ) : ℂ) 0 = 0 := by
    unfold repinConst
    rw [repin_log_radius_origin]
    exact reflected_integral_log_normPlus_circle_origin m hm
  rw [hc]
  ring

end

section
variable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
include hX

/-- The circle average at the origin at radius `e^{-m}` has variance `m`. -/
theorem reflected_gaussianVariance_circleAverage_origin (Xc : Ω → ℂ → ℝ → ℝ)
    (hXc : IsCircleAverage P X Xc) (m : ℝ) (hm : 0 ≤ m) :
    gaussianVariance P (fun ω => Xc ω 0 m) = m := by
  have _ := circleMeasure_isProbability 0 m
  unfold gaussianVariance
  rw [isCircleAverage_covariance P X hX Xc hXc 0 0 m m]
  have hinner : ∀ u, ∫ v, gffKernel u v ∂circleMeasure 0 m =
      Real.log (normPlus u) - Real.log (max (Real.exp (-m)) ‖u‖) := fun u => by
    rw [← reflected_repinPotential_origin m hm u, repinPotential, repin_log_radius_origin]
  simp_rw [hinner]
  have hae : (fun u : ℂ => Real.log (normPlus u) - Real.log (max (Real.exp (-m)) ‖u‖))
      =ᵐ[circleMeasure 0 m] fun _ => m := by
    filter_upwards [ae_norm_sub_center_circleMeasure 0 m] with u hu
    rw [sub_zero] at hu
    have hle : ‖u‖ ≤ 1 := by
      rw [hu]
      exact Real.exp_le_one_iff.mpr (by
        have := hm
        linarith)
    rw [normPlus, max_eq_left hle, Real.log_one, hu, max_self, Real.log_exp]
    ring
  rw [integral_congr_ae hae, integral_const, probReal_univ, one_smul]

/-- **Cameron–Martin tilt by the circle average at the origin.** For real `a`, nonnegative `m`, and every
measurable functional `H` of the chaos,
`E[e^{a X_m(0) - m a²/2} H(M)] = E[H(e^{γ a Cov(X(·), X_m(0))} M)]`. -/
theorem reflected_lintegral_circleTilt (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2)
    (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M) (Xc : Ω → ℂ → ℝ → ℝ)
    (hXc : IsCircleAverage P X Xc) (a m : ℝ) (hm : 0 ≤ m) (H : Measure ℂ → ℝ≥0∞)
    (hH : Measurable H) :
    ∫⁻ ω, ENNReal.ofReal (Real.exp (a * Xc ω 0 m - m * a ^ 2 / 2)) * H (M ω) ∂P =
      ∫⁻ ω, H ((M ω).withDensity ((fun x : ℂ => ENNReal.ofReal (Real.exp (γ * a * (Real.log (normPlus x) - Real.log (max (Real.exp (-m)) ‖x‖))))))) ∂P := by
  have ha' := Complex.ofReal_ne_zero.mpr (Real.exp_pos (-m)).ne'
  have ht := lintegral_repin_circle_tilt P X hX γ hγ hγ2 M hM Xc hXc _ 0 ha' a H hH
  simpa only [repin_log_radius_origin, reflected_gaussianVariance_circleAverage_origin P X hX Xc hXc m hm,
    reflected_repinPotential_origin m hm, mul_assoc, mul_comm (a ^ 2) m] using ht

end

end DOZZ.Proofs
