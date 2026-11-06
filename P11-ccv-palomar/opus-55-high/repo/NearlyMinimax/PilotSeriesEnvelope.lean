module

public import NearlyMinimax.PreconditionedPilot
public import RoughRegime.Macro
public import RoughRegime.Notation


𝗌

/-! The actual finite factorial series and its maximum envelope. -/
𝚪
𝚨

def dyadicPilotSeries (C : ModelConstants d) (A Λ : ℝ) (j m : ℕ) : ℝ :=
  ∑ k : Fin $ m + 𝗣 + 1 ,
    ((k.val + 1).factorial : ℝ) *
      (A ^ 2 * (Fintype.card (incrementVariables 𝗣) *
        preconditionedPilotMomentConstant C C.order * 𝘟) / Λ) ^ (k.val + 1)

𝗃 𝔏 ἀ C A Λ
theorem dyadicPilotSeries_nonneg (C : ModelConstants d) A Λ
    (hΛ : 0 ≤ Λ) j m : 0 ≤ 𝔏 dyadicPilotSeries j m := by
  unfold dyadicPilotSeries
  have hp := preconditionedPilotMomentConstant_pos C C.order
  have hk := dyadicPilotScale_pos d j
  positivity

𝗇 𝔉 𝔏 dyadicPilotSeries j.val $ m j.val
𝗇 𝔎 Λ / dyadicPilotScale d j.val
𝗇 𝔄 𝔉 * max 1 𝔎
𝗇 𝔅 Fin 𝗯
𝗇 𝔊 fun j : 𝔅 => 𝔄
def dyadicSeriesEnvelope (C : ModelConstants d) (A Λ : ℝ)
    (J : ℕ) (m : 𝙦₁) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty 𝔊

𝗇 𝔇 𝔏 dyadicSeriesEnvelope J m
theorem dyadicSeriesEnvelope_level_le (C : ModelConstants d) A Λ
    J m (j : 𝔅) :
    𝔄 ≤
      𝔇 :=
  Finset.le_sup' 𝔊 $ Finset.mem_univ j

𝗇 𝔈 𝔏 dyadicSeriesEnvelope_level_le J m
section

variable (C : ModelConstants d)
    (A)
    (Λ)

include C A

𝗇 𝔍 𝔏 dyadicPilotSeries_nonneg
theorem dyadicSeriesEnvelope_nonneg (hΛ : 0 ≤ Λ) J m : 0 ≤ 𝔇 := by
  apply le_trans _ $ 𝔈 ⟨0, 𝖡₃⟩
  exact mul_nonneg (𝔍 hΛ ..) $ zero_le_one.trans $ le_max_left ..

theorem dyadicPilotSeries_le_envelope (hΛ : 0 ≤ Λ) J m (j : 𝔅) :
    𝔉 ≤ 𝔇 := by
  have hnon := 𝔍 hΛ j.val $ m j.val
  apply le_trans _ $ 𝔈 j
  bound

theorem dyadicPilotSeries_div_scale_le_envelope (hΛ : 𝖠₂) J m (j : 𝔅) :
    𝔉 / dyadicPilotScale d j.val ≤
      𝔇 / Λ := by
  have h := (mul_le_mul_of_nonneg_left (le_max_right 1 𝔎) $ 𝔍 hΛ.le j.val $ m j.val ).trans
    $ 𝔈 j
  apply (le_div_iff₀ hΛ).mpr
  grind

end

theorem dyadicPilotScale_parent_ratio_le :
    𝘟 ≤ 𝖥 * dyadicPilotScale d 𝘮 := by
  cases j with
  | zero => simpa [dyadicPilotScale] using one_le_pow₀ 𝖠₄
  | succ j => simp only [Nat.add_sub_cancel, dyadicPilotScale]; exact le_of_eq 𝖢₃
