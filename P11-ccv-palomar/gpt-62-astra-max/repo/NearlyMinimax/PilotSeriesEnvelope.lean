module

public import NearlyMinimax.PreconditionedPilot


@[expose] public section

/-! The actual finite factorial series and its maximum envelope. -/
noncomputable section
open scoped BigOperators
namespace NearlyMinimax

variable {d : ℕ} (C : ModelConstants d) (A Λ : ℝ) (hΛ : 0 ≤ Λ) (J : ℕ) (m : ℕ → ℕ)

include hΛ in
theorem dyadicPilotSeries_nonneg (j m : ℕ) : 0 ≤ dyadicPilotSeries C A Λ j m := by
  unfold dyadicPilotSeries
  have hp := preconditionedPilotMomentConstant_pos C C.order
  have hk := dyadicPilotScale_pos d j
  positivity

def dyadicSeriesEnvelope : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun j : Fin (J + 1) =>
    dyadicPilotSeries C A Λ j.val (m j.val) * max 1 (Λ / dyadicPilotScale d j.val))

theorem dyadicSeriesEnvelope_level_le (j : Fin (J + 1)) :
    dyadicPilotSeries C A Λ j.val (m j.val) * max 1 (Λ / dyadicPilotScale d j.val) ≤
      dyadicSeriesEnvelope C A Λ J m :=
  Finset.le_sup' (fun j : Fin (J + 1) =>
    dyadicPilotSeries C A Λ j.val (m j.val) * max 1 (Λ / dyadicPilotScale d j.val)) (Finset.mem_univ j)

include hΛ in
theorem dyadicSeriesEnvelope_nonneg : 0 ≤ dyadicSeriesEnvelope C A Λ J m := by
  apply le_trans _ (dyadicSeriesEnvelope_level_le C A Λ J m ⟨0, by omega⟩)
  exact mul_nonneg (dyadicPilotSeries_nonneg C A Λ hΛ _ _) (by positivity)

theorem dyadicPilotSeries_div_scale_le_envelope
    (hΛ : 0 < Λ) {J : ℕ} (m : ℕ → ℕ) (j : Fin (J + 1)) :
    dyadicPilotSeries C A Λ j.val (m j.val) / dyadicPilotScale d j.val ≤
      dyadicSeriesEnvelope C A Λ J m / Λ := by
  have hnon := dyadicPilotSeries_nonneg C A Λ hΛ.le j.val (m j.val)
  have h := (mul_le_mul_of_nonneg_left (le_max_right 1 (Λ / dyadicPilotScale d j.val)) hnon).trans
    (dyadicSeriesEnvelope_level_le C A Λ J m j)
  apply (le_div_iff₀ hΛ).mpr
  convert h using 1 <;> ring

theorem dyadicPilotScale_parent_ratio_le {j : ℕ} :
    dyadicPilotScale d j ≤ 2 ^ d * dyadicPilotScale d (j - 1) := by
  cases j with
  | zero => simpa [dyadicPilotScale] using one_le_pow₀ (by norm_num)
  | succ j => simp [dyadicPilotScale]; exact le_of_eq (by ring)

end NearlyMinimax
