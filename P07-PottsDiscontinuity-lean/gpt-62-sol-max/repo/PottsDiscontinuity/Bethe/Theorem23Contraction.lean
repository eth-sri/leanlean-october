module

public import PottsDiscontinuity.Bethe.Prop21Positivity

/-! # Poisson contraction with an explicit mass defect -/

@[expose] public section

open Set MeasureTheory intervalIntegral

namespace PottsDiscontinuity.Bethe

/-- Estimate (2.4), allowing a nonzero integral of the difference. The last
term is indispensable for `ρ_p`, whose mass is `1/2+r/N`. -/
theorem xiConv_abs_le_with_mass_defect {μ m B : ℝ} (hμ : 0 < μ)
    (hm : 0 ≤ m) (hlower : ∀ t : ℝ, m ≤ Xi μ t)
    {f : ℝ → ℝ} (hf : IntervalIntegrable f volume (-Real.pi) Real.pi)
    (hbound : ∀ β ∈ Icc (-Real.pi) Real.pi, |f β| ≤ B) (α : ℝ) :
    |xiConv μ f α| ≤ (1 - m) * B + m * |∫ β in (-Real.pi)..Real.pi, f β| / (2 * Real.pi) := by
  let K : ℝ → ℝ := fun β => Xi μ (α - β) - m
  have hc : Continuous K := ((continuous_Xi hμ).comp (continuous_const.sub continuous_id)).sub
    continuous_const
  have hnonneg (β : ℝ) : 0 ≤ K β := sub_nonneg.mpr (hlower _)
  have hprod :=
    hf.continuousOn_mul hc.continuousOn
  have hmajor : IntervalIntegrable (fun β => K β * B) volume (-Real.pi) Real.pi :=
    (hc.mul continuous_const).intervalIntegrable _ _
  have hfirst : |∫ β in (-Real.pi)..Real.pi, K β * f β| ≤
      (2 * Real.pi) * (1 - m) * B := by
    apply (intervalIntegral.abs_integral_le_integral_abs (by linarith [Real.pi_pos])).trans
    have hi := intervalIntegral.integral_mono_on (by linarith [Real.pi_pos]) hprod.abs hmajor
      (fun β hβ => show |K β * f β| ≤ K β * B from by
        rw [abs_mul, abs_of_nonneg (hnonneg β)]
        exact mul_le_mul_of_nonneg_left (hbound β hβ) (hnonneg β))
    have hKint : (∫ β in (-Real.pi)..Real.pi, K β) = (2 * Real.pi) * (1 - m) := by
      change (∫ β in (-Real.pi)..Real.pi, Xi μ (α - β) - m) = _
      have hiXi : IntervalIntegrable (fun β => Xi μ (α - β)) volume (-Real.pi) Real.pi :=
        ((continuous_Xi hμ).comp (continuous_const.sub continuous_id)).intervalIntegrable _ _
      rw [intervalIntegral.integral_sub hiXi
        intervalIntegrable_const, integral_Xi_shift hμ α, intervalIntegral.integral_const,
        smul_eq_mul]
      ring
    simpa [hKint] using hi
  have hid : (∫ β in (-Real.pi)..Real.pi, Xi μ (α - β) * f β) =
      (∫ β in (-Real.pi)..Real.pi, K β * f β) + m * ∫ β in (-Real.pi)..Real.pi, f β := by
    have heq : (fun β => Xi μ (α - β) * f β) =
        fun β => K β * f β + m * f β := by funext β; ring
    simp [heq, intervalIntegral.integral_add hprod (hf.const_mul m)]
  have htotal : |∫ β in (-Real.pi)..Real.pi, Xi μ (α - β) * f β| ≤
      (2 * Real.pi) * (1 - m) * B + m * |∫ β in (-Real.pi)..Real.pi, f β| := by
    rw [hid]
    apply (abs_add_le _ _).trans
    rw [abs_mul, abs_of_nonneg hm]
    exact add_le_add hfirst le_rfl
  unfold xiConv
  rw [abs_mul, abs_of_pos (inv_pos.mpr (by positivity : (0 : ℝ) < 2 * Real.pi))]
  apply (mul_le_mul_of_nonneg_left htotal (inv_nonneg.mpr (by positivity))).trans_eq
  field_simp

theorem exists_uniform_double_Xi_lower {Δ₀ : ℝ} (hΔ₀ : Δ₀ < -1) :
    ∃ m : ℝ, 0 < m ∧ m < 1 ∧ ∀ Δ ≤ Δ₀, ∀ t : ℝ,
      m ≤ Xi (2 * lamOf Δ) t := by
  obtain ⟨X, hX, hXi⟩ := exists_Xi_uniform_bounds (lamOf_pos hΔ₀)
  refine ⟨X⁻¹, inv_pos.2 (zero_lt_one.trans hX), inv_lt_one_of_one_lt₀ hX, fun Δ hΔ t => ?_⟩
  exact (hXi _ (by linarith [lamOf_mono hΔ₀ hΔ, lamOf_pos hΔ₀]) t).1

end PottsDiscontinuity.Bethe
