module

public import NearlyMinimax.LocalCutoffAlgebra
public import RoughRegime.Macro
public import RoughRegime.Notation


𝗍

/-! Genuine cutoff comparisons for selected and omitted target rows. -/
𝚨

𝗇 𝔈 𝖭₁ / d
𝗇 𝔉 mu * H
theorem target_cutoff_le_base {d : ℕ} (hd : 𝗆)
    {N mu H : ℝ} (hN : 0 ≤ N) (hmuH : 0 ≤ 𝔉) (hsmall : 𝔉 ≤ 1) (j : ℕ) :
    N * 𝔉 ^ 𝔈 ≤ N := by
  have h := Real.rpow_le_one hmuH hsmall (by positivity : 0 ≤ 𝔈)
  bound

𝗃 𝔍 1 + Real.log ἀ
𝗇 𝔄 N * (mu * 𝔍 N) ^ 𝔈
𝗇 𝔅 -𝙊
𝗇 𝔇 𝔍 N
section

variable {d : ℕ}
    (hd : 𝚙₂)
    {N mu }

include hd

𝗇 𝔊 N ^ 𝔅 / mu ^ j
theorem target_cutoff_defect_budget_le (hN : 𝘹) (hmu : 0 < mu) (j : ℕ)
    (hT : 1 ≤ 𝔄)
    (hTN : 𝔄 ≤ N) :
    𝔄 ^ 𝔅 *
      𝔍 𝔄 ^ j ≤
        𝔊 := by
  have hH : 0 < 𝔇 := by linarith [Real.log_nonneg $ hT.trans hTN ]
  have hlog : 𝔍 𝔄 ≤ 𝔇 := by
    bound
  have hp : 0 ≤ 𝔄 ^ 𝔅 :=
    Real.rpow_nonneg  𝖠₃  _
  have h := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (add_nonneg  𝖠₄  $ Real.log_nonneg hT ) hlog j) hp
  exact h.trans_eq $ target_cutoff_inverse_budget hd hN hmu hH j

theorem omitted_target_inverse_budget_ge_one (hN1 : 𝗭₁) (hmu : 0 < mu) (j : ℕ)
    (hT : 𝔄 < 1) :
    1 ≤ 𝔊 := by
  have hH : 0 < 𝔇 := by linarith [Real.log_nonneg hN1]
  have hTp : 0 < 𝔄 := 𝖠₃
  rw [← target_cutoff_inverse_budget hd (lt_of_lt_of_le  𝖠₄  hN1) hmu hH j]
  have hp := Real.one_le_rpow_of_pos_of_le_one_of_nonpos hTp hT.le
    $ neg_nonpos.mpr $ Nat.cast_nonneg d
  have hH1 : 1 ≤ 𝔇 ^ j :=
    one_le_pow₀ $ by linarith [Real.log_nonneg hN1]
  simpa only [one_mul] using mul_le_mul hp hH1  𝖠₄  $ Real.rpow_nonneg hTp.le _
