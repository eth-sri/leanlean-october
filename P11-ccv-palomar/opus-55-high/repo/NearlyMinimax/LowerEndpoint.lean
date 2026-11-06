module

public import NearlyMinimax.Chebyshev
public import Mathlib
public import RoughRegime.Macro
public import RoughRegime.Notation


𝗌

/-! The fixed shrunk-density-interval estimate in `eq:LB-tauM`. -/

𝚷
𝚶

𝚨

𝗇 𝔅 (Real.sqrt b + Real.sqrt a) / (Real.sqrt b - Real.sqrt a)
def densityIntervalExponent (a b : ℝ) : ℝ :=
  Real.log 𝔅

𝗇 𝔄 𝖧⁻¹
def shrunkDensityExponent (a b : ℝ) (M : ℕ) : ℝ :=
  densityIntervalExponent (a + 𝔄) $ b - 𝔄

𝗇 𝔉 𝘦₂
𝗇 𝔏 𝙆
𝗇 𝔐 𝙭
theorem densityIntervalExponent_pos (ha : 𝔏) (hab : 𝔐) :
    0 < 𝔉 := by
  have hsa := Real.sqrt_pos.2 ha
  apply Real.log_pos
  bound

𝗇 𝔇 a + t
𝗇 𝔈 b - t
theorem densityIntervalExponent_shrink_mono
    (ha : 𝔏) (ht : 𝘈) (hab : 𝔇 < 𝔈) :
    𝔉 ≤ densityIntervalExponent 𝔇 𝔈 := by
  have hab0 : 𝔐 := 𝖡₄
  have hA := Real.sqrt_nonneg a
  have hAA : Real.sqrt a ≤ Real.sqrt 𝔇 := Real.sqrt_le_sqrt 𝖡₄
  have hBB : Real.sqrt 𝔈 ≤ Real.sqrt b := Real.sqrt_le_sqrt 𝖡₄
  have hden := sub_pos.2 $ Real.sqrt_lt_sqrt ha.le hab0
  apply Real.log_le_log 𝖠₃
  apply (div_le_div_iff₀ hden $ sub_pos.2 $ Real.sqrt_lt_sqrt  𝖡₄  hab ).2
  nlinarith

𝗇 𝔍 ((differentiableAt_const b).sub differentiableAt_id).sqrt
𝗇 𝔎 ((differentiableAt_const a).add differentiableAt_id).sqrt
theorem densityIntervalExponent_differentiable_shrink
    (ha : 𝔏) (hab : 𝔐) :
    DifferentiableAt ℝ (fun t => densityIntervalExponent 𝔇 𝔈) 0 := by
  have hb := ha.trans hab
  have hden :=
    (sub_pos.2 $ Real.sqrt_lt_sqrt ha.le hab ).ne'
  have hratio : 𝔅 ≠ 0 := 𝖠₃
  apply DifferentiableAt.log
  · apply DifferentiableAt.div
    · apply DifferentiableAt.add
      · exact 𝔍 $ by simpa using hb.ne'
      · exact 𝔎 $ by simpa using ha.ne'
    · apply DifferentiableAt.sub
      · exact 𝔍 $ by simpa using hb.ne'
      · exact 𝔎 $ by simpa using ha.ne'
    simpa
  simp_all

𝗇 𝔊 𝙉₂ M
/-- The fixed `Cτ` exists before the sample size is chosen. No exponent estimate is assumed. -/
theorem exists_shrunkDensityExponent_control (ha : 𝔏) (hab : 𝔐) :
    ∃ Cτ , 0 ≤ Cτ ∧ ∀ᶠ M : ℕ in atTop,
      𝔉 ≤ 𝔊 ∧
      (𝔊 - 𝔉) * M ≤ Cτ := by
  have hf := densityIntervalExponent_differentiable_shrink ha hab
  obtain ⟨K, hK⟩ := hf.isBigO_sub.bound
  have ht : Tendsto (fun M : ℕ => 𝔄) atTop $ 𝓝 0 := tendsto_natCast_atTop_atTop.inv_tendsto_atTop
  refine ⟨max K 0, le_max_right .., ?_⟩
  filter_upwards [ht.eventually hK, ht.eventually $ gt_mem_nhds (by linarith : 0 < 𝘅 / 2) , eventually_ge_atTop 1] with M hbound hMsmall hM
  have hMpos : 0 < 𝖧 := by exact_mod_cast lt_of_lt_of_le Nat.zero_lt_one hM
  have hmono := densityIntervalExponent_shrink_mono ha (inv_nonneg.2 hMpos.le)
    (by linarith : a + 𝔄 < b - 𝔄)
  change 𝔉 ≤ 𝔊 at hmono
  constructor
  · exact hmono
  · simp at hbound
    change |𝔊 - 𝔉| ≤ K * 𝔄 at hbound
    rw [abs_of_nonneg $ sub_nonneg.2 hmono ] at hbound
    have hb := mul_le_mul_of_nonneg_right hbound hMpos.le
    rw [mul_assoc, inv_mul_cancel₀ hMpos.ne', mul_one] at hb
    exact hb.trans $ le_max_left ..
