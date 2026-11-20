/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.FourPoint.TaylorPairIntegrability
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import DOZZ.GMC.Annulus.PositiveRoot

/-! Planar radial bounds obtained by Haar dilation. -/

@[expose] public section
open MeasureTheory Set
open scoped ENNReal
namespace DOZZ.Proofs

private theorem lintegral_norm_rpow_smul (a ρ : ℝ) (hρ : 0 < ρ) {s : Set ℂ}
    (hs : MeasurableSet s) :
    (∫⁻ x : ℂ in s, ENNReal.ofReal (‖x‖ ^ a)) =
      ENNReal.ofReal (ρ ^ (a + 2)) *
        ∫⁻ x : ℂ in (ρ • · : ℂ → ℂ) ⁻¹' s, ENNReal.ofReal (‖x‖ ^ a) := by
  let F := fun x : ℂ => ENNReal.ofReal (‖x‖ ^ a)
  have hf : Measurable F := by dsimp [F]; fun_prop
  have h := setLIntegral_map (μ := (volume : Measure ℂ)) hs hf (measurable_const_smul ρ)
  rw [Measure.map_addHaar_smul _ hρ.ne', Measure.restrict_smul, lintegral_smul_measure,
    Complex.finrank_real_complex, abs_of_pos (inv_pos.mpr (sq_pos_of_pos hρ))] at h
  have hp (x : ℂ) : F (ρ • x) = ENNReal.ofReal (ρ ^ a) * F x := by
    dsimp [F]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hρ, Real.mul_rpow hρ.le (norm_nonneg _),
      ENNReal.ofReal_mul (Real.rpow_nonneg hρ.le _)]
  simp_rw [hp, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top] at h
  have hcancel : ENNReal.ofReal (ρ ^ 2) * ENNReal.ofReal ((ρ ^ 2)⁻¹) = 1 := by
    rw [← ENNReal.ofReal_mul (sq_nonneg ρ), mul_inv_cancel₀ (pow_ne_zero _ hρ.ne'), ENNReal.ofReal_one]
  have hpow : ENNReal.ofReal (ρ ^ 2) * ENNReal.ofReal (ρ ^ a) = ENNReal.ofReal (ρ ^ (a + 2)) := by
    rw [← ENNReal.ofReal_mul (sq_nonneg ρ), ← Real.rpow_natCast, ← Real.rpow_add hρ, add_comm]
    norm_num
  rw [smul_eq_mul] at h
  have he := congrArg (ENNReal.ofReal (ρ ^ 2) * ·) h
  rwa [← mul_assoc, hcancel, one_mul, ← mul_assoc, hpow] at he

private theorem smul_preimage_ball_zero {ρ : ℝ} (hρ : 0 < ρ) :
    (ρ • · : ℂ → ℂ) ⁻¹' Metric.ball 0 ρ = Metric.ball 0 1 := by
  ext x
  simp only [mem_preimage, Metric.mem_ball, dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_pos hρ]
  constructor <;> intro h <;> nlinarith only [h, hρ]

private theorem planar_radial_bound (a : ℝ) (S : ℝ → Set ℂ) (hS : ∀ ρ, MeasurableSet (S ρ))
    (hpre : ∀ ρ > 0, (ρ • · : ℂ → ℂ) ⁻¹' S ρ = S 1)
    (hfin : IntegrableOn (fun x : ℂ => ‖x‖ ^ a) (S 1)) :
    ∃ C : ℝ, 0 < C ∧ ∀ ρ > 0,
      (∫⁻ x : ℂ in S ρ, ENNReal.ofReal (‖x‖ ^ a)) ≤ ENNReal.ofReal (C * ρ ^ (a + 2)) := by
  let J := ∫⁻ x : ℂ in S 1, ENNReal.ofReal (‖x‖ ^ a)
  have hJ : J < ∞ := (hasFiniteIntegral_iff_ofReal
    (ae_of_all _ fun x => Real.rpow_nonneg (norm_nonneg x) _)).mp hfin.hasFiniteIntegral
  have hj : J ≤ ENNReal.ofReal (J.toReal + 1) := by
    rw [ENNReal.le_ofReal_iff_toReal_le hJ.ne (by positivity)]
    linarith
  refine ⟨J.toReal + 1, by positivity, fun ρ hρ => ?_⟩
  rw [lintegral_norm_rpow_smul a ρ hρ (hS ρ), hpre ρ hρ, mul_comm (J.toReal + 1),
    ENNReal.ofReal_mul (Real.rpow_nonneg hρ.le _)]
  exact mul_le_mul' le_rfl hj

/-- The translated radial disk has its exact integrable power, uniformly before the radius. -/
theorem planar_radial_ball_bound (a : ℝ) (ha : -2 < a) :
    ∃ C : ℝ, 0 < C ∧ ∀ z : ℂ, ∀ ρ : ℝ, 0 < ρ →
      (∫⁻ x : ℂ in Metric.ball z ρ, ENNReal.ofReal (‖x - z‖ ^ a)) ≤ ENNReal.ofReal (C * ρ ^ (a + 2)) := by
  obtain ⟨C, hC, h⟩ := planar_radial_bound a (Metric.ball 0) (fun _ => measurableSet_ball)
    (fun _ hρ => smul_preimage_ball_zero hρ) ((integrableOn_norm_rpow_ball_iff a 1 zero_lt_one).mpr ha)
  refine ⟨C, hC, fun z ρ hρ => ?_⟩
  simp_rw [norm_sub_rev _ z, translated_ball_rpow_integral z ρ a]
  exact h ρ hρ

/-- A finite constant before every positive radius, with the literal tail exponent a+2. -/
theorem planar_radial_tail_bound (a : ℝ) (ha : a < -2) :
    ∃ C : ℝ, 0 < C ∧ ∀ ρ : ℝ, 0 < ρ →
      (∫⁻ x : ℂ in (Metric.ball 0 ρ)ᶜ, ENNReal.ofReal (‖x‖ ^ a)) ≤ ENNReal.ofReal (C * ρ ^ (a + 2)) :=
  planar_radial_bound a (fun ρ => (Metric.ball 0 ρ)ᶜ) (fun _ => measurableSet_ball.compl)
    (fun _ hρ => by rw [preimage_compl, smul_preimage_ball_zero hρ])
    ((integrableOn_norm_rpow_ball_compl_iff a 1 zero_lt_one).mpr ha)

/-- A local radial majorant bounds the reference mass of a kernel in small disks. -/
theorem small_ball_kernel_bound (K : ℂ → ℝ) (a w : ℝ) (ha : -2 < a) (hw : 0 < w)
    (hK : ∀ x : ℂ, ‖x‖ < 1 / 2 → K x ≤ w * ‖x‖ ^ a) :
    ∃ C : ℝ, 0 < C ∧ ∀ r : ℝ, 0 < r → r ≤ 1 / 2 →
      (∫⁻ x in Metric.ball (0 : ℂ) r, ENNReal.ofReal (K x) ∂gmcReferenceMeasure) ≤
        ENNReal.ofReal (C * r ^ (a + 2)) := by
  obtain ⟨C, hC, hb⟩ := planar_radial_ball_bound a ha
  refine ⟨w * C, mul_pos hw hC, fun r hr hr₁ => ?_⟩
  have hn {x : ℂ} (hx : x ∈ Metric.ball 0 r) : ‖x‖ < 1 / 2 := by
    exact (by simpa [Metric.mem_ball] using hx : ‖x‖ < r).trans_le hr₁
  rw [gmcReferenceMeasure_restrict_unit_chart _ measurableSet_ball
    (fun x hx => (hn hx).le.trans (by norm_num))]
  calc
    _ ≤ ∫⁻ x in Metric.ball (0 : ℂ) r, ENNReal.ofReal w * ENNReal.ofReal (‖x‖ ^ a) :=
      setLIntegral_mono' measurableSet_ball fun x hx => by
        rw [← ENNReal.ofReal_mul hw.le]
        exact ENNReal.ofReal_le_ofReal (hK x (hn hx))
    _ = ENNReal.ofReal w * ∫⁻ x in Metric.ball (0 : ℂ) r, ENNReal.ofReal (‖x‖ ^ a) :=
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal w * ENNReal.ofReal (C * r ^ (a + 2)) :=
      mul_le_mul' le_rfl (by simpa only [sub_zero] using hb 0 r hr)
    _ = _ := by rw [← ENNReal.ofReal_mul hw.le, ← mul_assoc]

end DOZZ.Proofs
