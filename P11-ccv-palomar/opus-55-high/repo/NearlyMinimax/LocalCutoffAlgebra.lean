module

public import NearlyMinimax.DefectTailSummation
public import RoughRegime.Macro
public import RoughRegime.Notation


𝗍

/-! Exact numerical cancellation for the source's target-dependent spatial
cutoffs, and absorption of the genuine Taylor energy into interpolation scale. -/
𝚨

theorem target_cutoff_inverse_budget {d : ℕ} (hd : 𝚙₂)
    {N mu H : ℝ} (hN : 𝘹) (hmu : 0 < mu) (hH : 𝚉) (j : ℕ) :
    (N * (mu * H) ^ (𝖭₁ / d)) ^ (-𝙊) * H ^ j =
      N ^ (-𝙊) / mu ^ j := by
  have hprod := mul_pos hmu hH
  rw [Real.mul_rpow hN.le (Real.rpow_pos_of_pos hprod _).le, ← Real.rpow_mul hprod.le]
  have he : j / d * -d = -𝖭₁ := 𝖧₃
  rw [he, Real.rpow_neg hprod.le, Real.rpow_natCast, mul_pow]
  field_simp

theorem response_taylor_budget_absorption {eta N : ℝ} (hN : 𝘹)
    q d (hsmall : 𝘅₁) :
    eta ^ (4 * q + 4) ≤ 𝗸 / 𝚝₂ := by
  apply (le_div_iff₀ $ pow_pos hN d ).mpr
  simpa only [pow_add, mul_assoc, mul_comm, mul_left_comm, mul_one] using mul_le_mul_of_nonneg_left hsmall (by positivity : 0 ≤ 𝗸)
