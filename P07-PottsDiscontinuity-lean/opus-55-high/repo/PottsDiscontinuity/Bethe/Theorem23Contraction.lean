module

public import PottsDiscontinuity.Bethe.Prop21Positivity

/-! # Poisson contraction with an explicit mass defect -/

public section

open Set MeasureTheory intervalIntegral

namespace PottsDiscontinuity.Bethe

theorem integral_Xi_shift {μ : ℝ} (hμ : 0 < μ) (α : ℝ) :
    (∫ β in (-Real.pi)..Real.pi, Xi μ (α - β)) = 2 * Real.pi := by
  have hd (β : ℝ) : HasDerivAt (fun t => -kMap μ (α - t)) (Xi μ (α - β)) β := by
    have hp : HasDerivAt (fun t : ℝ => α - t) (-1) β := by
      change HasDerivAt ((fun _ : ℝ => α) - id) (-1) β
      simpa using (hasDerivAt_const β α).sub (hasDerivAt_id β)
    have hh := ((hasDerivAt_kMap hμ (α - β)).comp β hp).neg
    aesop
  have hc : Continuous (fun β => Xi μ (α - β)) :=
    (continuous_Xi hμ).comp (continuous_const.sub continuous_id)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun β _ => hd β)
    (hc.intervalIntegrable _ _)]
  have hp := kMap_add_two_pi μ (α - Real.pi)
  grind

/-- Estimate (2.4), allowing a nonzero integral of the difference. The last
term is indispensable for `ρ_p`, whose mass is `1/2+r/N`. -/
theorem xiConv_abs_le_with_mass_defect {μ m B : ℝ} (hμ : 0 < μ)
    (hm : 0 ≤ m) (hlower : ∀ t : ℝ, m ≤ Xi μ t)
    {f : ℝ → ℝ} (hf : IntervalIntegrable f volume (-Real.pi) Real.pi)
    (hbound : ∀ β ∈ Icc (-Real.pi) Real.pi, |f β| ≤ B) (α : ℝ) :
    |xiConv μ f α| ≤ (1 - m) * B + m * |∫ β in (-Real.pi)..Real.pi, f β| / (2 * Real.pi) := by
  let K := fun β => Xi μ (α - β) - m
  have hc : Continuous K := ((continuous_Xi hμ).comp (continuous_const.sub continuous_id)).sub
    continuous_const
  have hnonneg (β : ℝ) : 0 ≤ K β := by grind
  have hprod :=
    hf.continuousOn_mul hc.continuousOn
  have hfirst : |∫ β in (-Real.pi)..Real.pi, K β * f β| ≤
      (2 * Real.pi) * (1 - m) * B := by
    apply (intervalIntegral.abs_integral_le_integral_abs (by linarith [Real.pi_pos])).trans
    have hi := intervalIntegral.integral_mono_on (by linarith [Real.pi_pos]) hprod.abs ((hc.mul continuous_const).intervalIntegrable _ _)
      (fun β hβ => show |K β * f β| ≤ K β * B from by
        rw [abs_mul, abs_of_nonneg (hnonneg β)]
        exact mul_le_mul_of_nonneg_left (hbound β hβ) (hnonneg β))
    have hKint : (∫ β in (-Real.pi)..Real.pi, K β) = (2 * Real.pi) * (1 - m) := by
      have hiXi : IntervalIntegrable (fun β => Xi μ (α - β)) volume (-Real.pi) Real.pi :=
        ((continuous_Xi hμ).comp (continuous_const.sub continuous_id)).intervalIntegrable _ _
      rw [intervalIntegral.integral_sub hiXi
        intervalIntegrable_const, integral_Xi_shift hμ α, intervalIntegral.integral_const,
        smul_eq_mul]
      ring
    simp_all
  have hid : (∫ β in (-Real.pi)..Real.pi, Xi μ (α - β) * f β) =
      (∫ β in (-Real.pi)..Real.pi, K β * f β) + m * ∫ β in (-Real.pi)..Real.pi, f β := by
    have heq : (fun β => Xi μ (α - β) * f β) =
        fun β => K β * f β + m * f β := by grind
    simp_all
  have htotal : |∫ β in (-Real.pi)..Real.pi, Xi μ (α - β) * f β| ≤
      (2 * Real.pi) * (1 - m) * B + m * |∫ β in (-Real.pi)..Real.pi, f β| := by
    rw [hid]
    apply (abs_add_le _ _).trans
    rw [abs_mul, abs_of_nonneg hm]
    linarith
  unfold xiConv
  rw [abs_mul, abs_of_pos (inv_pos.mpr (by positivity : (0 : ℝ) < 2 * Real.pi))]
  apply (mul_le_mul_of_nonneg_left htotal (inv_nonneg.mpr (by positivity))).trans_eq
  field_simp

theorem exists_uniform_double_Xi_lower {Δ₀ : ℝ} (hΔ₀ : Δ₀ < -1) :
    ∃ m : ℝ, 0 < m ∧ m < 1 ∧ ∀ Δ ≤ Δ₀, ∀ t : ℝ,
      m ≤ Xi (2 * lamOf Δ) t := by
  let lam0 := lamOf Δ₀
  let m := (Real.exp lam0 - 1) / (Real.exp lam0 + 1)
  have hlam0 : 0 < lam0 := lamOf_pos hΔ₀
  have hE : 1 < Real.exp lam0 := by simp_all
  have hm1 : m < 1 :=
    (div_lt_one (by linarith)).2 (by linarith)
  refine ⟨m, (by positivity), hm1, fun Δ hΔ t => ?_⟩
  have hmono : lam0 ≤ 2 * lamOf Δ := by
    have hi := lamOf_mono hΔ₀ hΔ
    linarith
  exact (exp_ratio_mono' hlam0 hmono).trans (Xi_ge_exp_ratio (by linarith) t)

end PottsDiscontinuity.Bethe
