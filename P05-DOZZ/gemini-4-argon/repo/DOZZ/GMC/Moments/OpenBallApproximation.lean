/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction
public import Mathlib.MeasureTheory.Measure.Lebesgue.Complex

/-! Compactly supported continuous approximations from below to planar open balls. -/

@[expose] public section

open MeasureTheory Filter Topology Set
open scoped BoundedContinuousFunction

namespace DOZZ.Proofs

/-- A continuous radial cutoff increasing to the indicator of an open ball. -/
noncomputable def openBallApproxFun (z : ℂ) (R : ℝ) (n : ℕ) (x : ℂ) : ℝ :=
  max 0 (min 1 ((n : ℝ) * (R - ‖x - z‖)))

theorem openBallApproxFun_continuous z R n :
    Continuous (openBallApproxFun z R n) := by
  unfold openBallApproxFun
  fun_prop

theorem openBallApproxFun_bounds z R n x :
    0 ≤ openBallApproxFun z R n x ∧ openBallApproxFun z R n x ≤ 1 := by
  unfold openBallApproxFun
  constructor
  · exact le_max_left _ _
  · exact max_le_iff.mpr ⟨by norm_num, min_le_left _ _⟩

/-- The ball approximants as bounded continuous functions. -/
noncomputable def openBallApprox (z : ℂ) (R : ℝ) (n : ℕ) :
    BoundedContinuousFunction ℂ ℝ :=
  BoundedContinuousFunction.mkOfBound
    ⟨openBallApproxFun z R n, openBallApproxFun_continuous z R n⟩ 1 (by
      intro x y
      have hx := openBallApproxFun_bounds z R n x
      have hy := openBallApproxFun_bounds z R n y
      change dist (openBallApproxFun z R n x) (openBallApproxFun z R n y) ≤ 1
      rw [Real.dist_eq]
      rw [abs_le]
      exact ⟨by linarith, by linarith⟩)

theorem openBallApproxFun_tendsto z R x :
    Tendsto (fun n : ℕ => openBallApproxFun z R n x) atTop
      (𝓝 ((Metric.ball z R).indicator (fun _ => (1 : ℝ)) x)) := by
  by_cases hx : dist x z < R
  · have hgap : 0 < R - ‖x - z‖ := by
      rw [dist_eq_norm] at hx
      linarith
    obtain ⟨N, hN⟩ := exists_nat_gt (1 / (R - ‖x - z‖))
    have hEventually : (fun _ : ℕ => (1 : ℝ)) =ᶠ[atTop]
        fun n => openBallApproxFun z R n x := by
      filter_upwards [eventually_ge_atTop N] with n hn
      have hprod : 1 ≤ (n : ℝ) * (R - ‖x - z‖) := by
        have := (div_lt_iff₀ hgap).mp (show 1 / (R - ‖x - z‖) < (n : ℝ) by exact lt_of_lt_of_le hN (by exact_mod_cast hn))
        nlinarith
      simp [openBallApproxFun, min_eq_left hprod]
    convert (Tendsto.congr' hEventually tendsto_const_nhds) using 1
    simpa [dist_eq_norm] using hx
  · have hx' : R ≤ dist x z := le_of_not_gt hx
    have hzero n : openBallApproxFun z R n x = 0 := by
      simp [openBallApproxFun, max_eq_left ((min_le_right _ _).trans (mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg n) (sub_nonpos.mpr (by simpa [dist_eq_norm] using hx'))))]
    convert (Tendsto.congr' (Filter.Eventually.of_forall fun n => (hzero n).symm) tendsto_const_nhds) using 1
    simp [Metric.mem_ball, hx]

/-- The topological support of each cutoff stays inside the closed ball. -/
theorem openBallApprox_tsupport_subset z R (n : ℕ) :
    tsupport (openBallApprox z R n : ℂ → ℝ) ⊆ Metric.closedBall z R := by
  change closure (Function.support (openBallApprox z R n : ℂ → ℝ)) ⊆
    Metric.closedBall z R
  exact closure_minimal (by intro x hx; by_contra hball; change (openBallApprox z R n : ℂ → ℝ) x ≠ 0 at hx; exact hx (by simp [openBallApprox, openBallApproxFun, max_eq_left ((min_le_right _ _).trans (mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg n) (sub_nonpos.mpr (by simpa [dist_eq_norm] using (lt_of_not_ge hball : R < dist x z).le))))])) Metric.isClosed_closedBall

/-- Integrals of the cutoffs converge to the mass of an open ball for every finite measure. -/
theorem openBallApprox_integral_tendsto z R (μ : Measure ℂ)
    [IsFiniteMeasure μ] :
    Tendsto (fun n : ℕ => ∫ x, openBallApprox z R n x ∂μ) atTop
      (𝓝 (μ.real (Metric.ball z R))) := by
  have hdom : ∀ n, ∀ᵐ x ∂μ, ‖openBallApprox z R n x‖ ≤ (1 : ℝ) := by
    intro n
    filter_upwards [] with x
    have hx := openBallApproxFun_bounds z R n x
    simpa [openBallApprox, Real.norm_eq_abs, abs_of_nonneg hx.1] using hx.2
  have hlim : ∀ᵐ x ∂μ,
      Tendsto (fun n => openBallApprox z R n x) atTop
        (𝓝 ((Metric.ball z R).indicator (fun _ => (1 : ℝ)) x)) := ae_of_all _ (fun x => by
      simpa [openBallApprox] using openBallApproxFun_tendsto z R x)
  rw [← integral_indicator_one Metric.isOpen_ball.measurableSet]
  exact (tendsto_integral_of_dominated_convergence (fun _ : ℂ => (1 : ℝ)) (fun n => (openBallApprox z R n).continuous.measurable.aestronglyMeasurable) (integrable_const 1) hdom hlim)

/-- Pulling back the centered cutoff by an affine map gives a cutoff on the target disk. -/
noncomputable def openBallAffineApprox (a : ℂ) (c R : ℝ) (n : ℕ) :
    BoundedContinuousFunction ℂ ℝ :=
  (openBallApprox 0 R n).compContinuous
    ⟨fun y => (c : ℂ)⁻¹ • (y - a), by fun_prop⟩

/-- The affine pullback cutoff has support inside the target closed ball. -/
theorem openBallAffineApprox_tsupport_subset {a} {c R} (hc : 0 < c)
    (n : ℕ) :
    tsupport (openBallAffineApprox a c R n : ℂ → ℝ) ⊆ Metric.closedBall a (c * R) := by
  change closure (Function.support (openBallAffineApprox a c R n : ℂ → ℝ)) ⊆
    Metric.closedBall a (c * R)
  exact closure_minimal (by intro y hy; by_contra hball; change (openBallAffineApprox a c R n : ℂ → ℝ) y ≠ 0 at hy; exact hy (by change (openBallApprox 0 R n : ℂ → ℝ) ((c : ℂ)⁻¹ • (y - a)) = 0; simpa [openBallApprox] using (by simp [openBallApproxFun, abs_of_pos hc, max_eq_left ((min_le_right _ _).trans (mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg n) (sub_nonpos.mpr (show R < c⁻¹ * ‖y - a‖ by simpa [abs_of_pos hc] using (by simpa [abs_of_pos hc, div_eq_mul_inv, mul_comm] using (show R < ‖y - a‖ / c by rw [lt_div_iff₀ hc]; simpa [dist_eq_norm, mul_comm] using (lt_of_not_ge hball : c * R < dist y a)))).le)))]))) Metric.isClosed_closedBall

/-- Applying the affine map to the pulled-back cutoff recovers the source cutoff. -/
theorem openBallAffineApprox_comp_affine a c R (hc : c ≠ 0)
    n x :
    openBallAffineApprox a c R n (a + c • x) = openBallApprox 0 R n x := by
  have hcancel : (c : ℂ)⁻¹ • (a + c • x - a) = x := by
    rw [show a + c • x - a = c • x by abel, (show c • x = (c : ℂ) * x by change (algebraMap ℝ ℂ c) * x = (c : ℂ) * x; simp)]
    simp [show (c : ℂ) ≠ 0 by exact_mod_cast hc]
  change (openBallApprox 0 R n : ℂ → ℝ) ((c : ℂ)⁻¹ • (a + c • x - a)) = _
  rw [hcancel]

/-- Integrals of affine pullback cutoffs converge to the mass of the target open ball. -/
theorem openBallAffineApprox_integral_tendsto {a} {c R} (hc : 0 < c)
    (μ : Measure ℂ) [IsFiniteMeasure μ] :
    Tendsto (fun n : ℕ => ∫ y, openBallAffineApprox a c R n y ∂μ) atTop
      (𝓝 (μ.real (Metric.ball a (c * R)))) := by
  have hbound : Integrable (fun _ : ℂ => (1 : ℝ)) μ := integrable_const 1
  have hdom : ∀ n, ∀ᵐ y ∂μ, ‖openBallAffineApprox a c R n y‖ ≤ (1 : ℝ) := by
    intro n
    have hEq : (openBallAffineApprox a c R n : ℂ → ℝ) =ᵐ[μ]
        fun y => openBallApprox 0 R n ((c : ℂ)⁻¹ • (y - a)) :=
      Filter.Eventually.of_forall fun _ => rfl
    filter_upwards [hEq] with y hy
    rw [hy, Real.norm_eq_abs]
    have hb := openBallApproxFun_bounds 0 R n ((c : ℂ)⁻¹ • (y - a))
    have hcoe : (openBallApprox 0 R n : ℂ → ℝ) ((c : ℂ)⁻¹ • (y - a)) =
        openBallApproxFun 0 R n ((c : ℂ)⁻¹ • (y - a)) := rfl
    rw [hcoe, abs_of_nonneg hb.1]
    exact hb.2
  have hlim : ∀ᵐ y ∂μ,
      Tendsto (fun n => openBallAffineApprox a c R n y) atTop
        (𝓝 ((Metric.ball a (c * R)).indicator (fun _ => (1 : ℝ)) y)) := ae_of_all _ fun y => by
      have hiff : dist y a < c * R ↔ |c|⁻¹ * ‖y - a‖ < R := by
        rw [dist_eq_norm]
        constructor
        · intro h
          have h'' : ‖y - a‖ / c < R := by
            apply (div_lt_iff₀ hc).2
            simpa [mul_comm] using (by simpa [mul_comm] using h)
          simpa [abs_of_pos hc, div_eq_mul_inv, mul_comm] using h''
        · intro h
          simpa [mul_comm] using (by simpa [mul_comm] using (div_lt_iff₀ hc).1 (by simpa [abs_of_pos hc, div_eq_mul_inv, mul_comm] using h))
      rw [(show (fun n => openBallAffineApprox a c R n y) = fun n => openBallApproxFun 0 R n ((c : ℂ)⁻¹ • (y - a)) by funext n; rfl)]
      convert (openBallApproxFun_tendsto 0 R ((c : ℂ)⁻¹ • (y - a))) using 1
      simp [Set.indicator, hiff]
  rw [← integral_indicator_one Metric.isOpen_ball.measurableSet]
  exact (tendsto_integral_of_dominated_convergence (fun _ : ℂ => (1 : ℝ)) (fun n => (openBallAffineApprox a c R n).continuous.measurable.aestronglyMeasurable) hbound hdom hlim)

end DOZZ.Proofs
