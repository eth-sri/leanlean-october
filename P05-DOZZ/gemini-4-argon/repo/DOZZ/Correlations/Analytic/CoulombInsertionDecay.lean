/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Correlations.Analytic.InsertionTailDecay
public import DOZZ.GMC.SharpMoments.SeibergUniform

/-! Uniform small moments of the actual Coulomb mass near a finite insertion. -/

@[expose] public section
open MeasureTheory
open scoped ENNReal
namespace DOZZ.Proofs

/-- Localize the separated-root bound to any smaller disk while keeping its constant at the
fixed separation scale. -/
theorem coulomb_shrinking_root_piece_le
    {N} (μ : Measure ℂ) γ (α : Fin N → ℝ) (z : Fin N → ℂ)
    αinf k {δ ρ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hρδ : ρ ≤ δ)
    (hsep : ∀ j, j ≠ k → 2 * δ ≤ ‖z j - z k‖) (hatom : μ {z k} = 0) :
    (∫⁻ x in Metric.ball (z k) ρ, coulombWeight γ α z αinf x ∂μ) ≤
      ENNReal.ofReal (((2 + 2 * ∑ j, ‖z j‖) / δ) ^ (∑ j, |γ * α j| + |γ * αinf|)) *
        weightedGmcBallMass γ μ (α k) (z k) ρ := by
  have hw : Measurable (fun x => ENNReal.ofReal ‖x - z k‖ ^ (-γ * α k)) :=
    (ENNReal.measurable_ofReal.comp (measurable_id.sub_const _).norm).pow_const _
  unfold weightedGmcBallMass
  simp only [ENNReal.rpow_eq_pow]
  rw [← lintegral_const_mul _ hw]
  apply lintegral_mono_ae
  filter_upwards [(ae_restrict_of_ae (measure_eq_zero_iff_ae_notMem.mp hatom)), ae_restrict_mem Metric.isOpen_ball.measurableSet] with x hxk hx
  exact coulombWeight_le_root γ α z αinf k hδ hδ1 hsep
    (Metric.ball_subset_ball hρδ hx) hxk

/-- Uniform decay near one root for bounded charge vectors with a strict upper charge gap.
The power of the radius is positive even when the first moment is infinite. -/
theorem coulomb_insertion_moment_decay
    {Ω : Type*} [MeasurableSpace Ω] {N}
    (P : Measure Ω) X (hX : IsEquatorGFF P X)
    (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (z : Fin N → ℂ) k δ (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hsep : ∀ j, j ≠ k → 2 * δ ≤ ‖z j - z k‖)
    A a gap m (hgap : 0 < gap) (ha : a + gap < Q γ) (hm : 0 < m)
    (hms : m < min (4 / γ ^ 2) (2 / γ * (Q γ - (a + gap)))) :
    ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ (α : Fin N → ℝ) (αinf : ℝ),
      (∀ i, |α i| ≤ A) → |αinf| ≤ A → α k ≤ a → ∀ ρ : ℝ, 0 < ρ → ρ ≤ δ →
      (∫⁻ ω, (∫⁻ x in Metric.ball (z k) ρ, coulombWeight γ α z αinf x ∂M ω) ^ m ∂P) ≤
        ENNReal.ofReal (ρ ^ (γ * gap * m)) * C := by
  obtain ⟨C, hC, hdec⟩ := weighted_small_ball_moment_decay
    P X hX γ hγ hγ2 M hM a gap hgap ha (z k) δ hδ m hm hms
  let L := (2 + 2 * ∑ j, ‖z j‖) / δ
  have hL : 1 ≤ L := by
    apply (le_div_iff₀ hδ).mpr
    have : 0 ≤ ∑ j, ‖z j‖ := Finset.sum_nonneg (fun j _ => norm_nonneg _)
    linarith
  let B := ENNReal.ofReal (L ^ ((N + 1 : ℝ) * (γ * A)))
  refine ⟨B ^ m * C, ENNReal.mul_lt_top
    (ENNReal.rpow_lt_top_of_nonneg hm.le ENNReal.ofReal_ne_top) hC, ?_⟩
  intro α αinf hα hi hk ρ hρ hρδ
  have he : ∑ j, |γ * α j| + |γ * αinf| ≤ (N + 1 : ℝ) * (γ * A) := by
    have : ∑ j, |γ * α j| ≤ N * (γ * A) := by
      calc
        _ ≤ ∑ j : Fin N, γ * A := Finset.sum_le_sum (fun j _ => by
          rw [abs_mul, abs_of_pos hγ]
          exact mul_le_mul_of_nonneg_left (hα j) hγ.le)
        _ = _ := by simp
    have : |γ * αinf| ≤ γ * A := by
      rw [abs_mul, abs_of_pos hγ]
      exact mul_le_mul_of_nonneg_left hi hγ.le
    linarith
  calc
    _ ≤ ∫⁻ ω, (B * weightedGmcBallMass γ (M ω) (α k) (z k) ρ) ^ m ∂P := by
      apply lintegral_mono_ae
      filter_upwards [(gmc_singleton_mass_eq_zero_ae P X hX γ hγ hγ2 M hM (z k))] with ω hω
      apply ENNReal.rpow_le_rpow _ hm.le
      exact (coulomb_shrinking_root_piece_le (M ω) γ α z αinf k hδ hδ1 hρδ hsep hω).trans
        (mul_le_mul_left (ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow_of_exponent_le hL he)) _)
    _ = B ^ m * weightedGmcBallMoment P M γ (α k) (z k) ρ m := by
      simp_rw [ENNReal.mul_rpow_of_nonneg _ _ hm.le]
      exact lintegral_const_mul'' _ ((gmc_weighted_mass_aemeasurable P X hX γ hγ hγ2 M hM (α k) (z k) ρ).pow_const m)
    _ ≤ B ^ m * (ENNReal.ofReal (ρ ^ (γ * gap * m)) * C) :=
      mul_le_mul_right (hdec (α k) hk ρ hρ (le_min hρδ (hρδ.trans hδ1))) _
    _ = _ := by ring

end DOZZ.Proofs
