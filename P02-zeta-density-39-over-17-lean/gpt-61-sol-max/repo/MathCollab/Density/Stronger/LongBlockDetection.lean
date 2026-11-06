module
import Mathlib
public import MathCollab.Density.Stronger.WeightedCriticalMean
public import MathCollab.Density.Stronger.SmallResidue

@[expose] public section

open Complex MeasureTheory Set Filter
open scoped BigOperators Topology ContDiff

namespace MathCollab.Density.Stronger

theorem negligible_residue_le_detector_height :
    ∀ᶠ T : ℝ in atTop, T^(-100 : ℝ) ≤ 1/(48*Real.log T) := by
  have ht := (isLittleO_log_rpow_atTop (by norm_num : (0:ℝ) < 100)).tendsto_div_nhds_zero
  filter_upwards [eventually_ge_atTop (2 : ℝ),
    ht.eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1/48))] with T hT hh
  have hTp : 0 < T := by linarith
  have hlog : 0 < Real.log T := Real.log_pos (by linarith)
  have hp : 48*Real.log T ≤ T^(100 : ℝ) := by
    have h := (div_lt_iff₀ (Real.rpow_pos_of_pos hTp 100)).mp hh
    linarith
  rw [Real.rpow_neg hTp.le, ← one_div]
  exact one_div_le_one_div_of_le (by positivity) hp

/-- A genuinely large smooth block forces a weighted critical-line mean,
with a positive constant chosen before T and every block parameter. -/
theorem smoothMollifierBlock_eventually_detects_mean {ψ : ℝ → ℝ} {a b : ℝ}
    (hψ : ContDiff ℝ ∞ ψ) (ha : 0 < a) (hb : 0 < b) (hs : tsupport ψ ⊆ Icc a b)
    (A : ℕ) (hA : 3 ≤ A) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ T : ℝ in atTop, ∀ (ρ : ℂ) (X N q : ℝ),
      3/4 ≤ ρ.re → ρ.re < 1 → T ≤ |ρ.im| →
      0 ≤ X → X ≤ T → 1 ≤ N → N ≤ T^2 → 0 ≤ q →
      1/(24*Real.log T) ≤ ‖smoothMollifierBlock ψ ρ X N q‖ →
      1/(48*Real.log T) ≤ C*Real.sqrt X*N^(1/2-ρ.re)*weightedCriticalMean A ρ.im := by
  obtain ⟨C,hC,h⟩ := uniform_smoothMollifierBlock_mean_bound hψ ha hb hs A hA
  refine ⟨C+1,by linarith,?_⟩
  filter_upwards [eventually_ge_atTop (2 : ℝ),
    smoothDetectorResidue_eventually_small hψ ha hb hs, negligible_residue_le_detector_height]
    with T hT hres hsmall
  intro ρ X N q hβ hβ' hγ hX hXT hN hNT hq hlarge
  have hNp : 0 < N := by linarith
  have hr := (hres ρ X N q hβ hβ'.le hγ hX hXT hN hNT hq).trans hsmall
  have hm := h ρ X N q hβ hβ' hX hNp hq
  have hj := weightedCriticalMean_nonneg A ρ.im
  have hh : C*Real.sqrt X*N^(1/2-ρ.re)*weightedCriticalMean A ρ.im ≤
      (C+1)*Real.sqrt X*N^(1/2-ρ.re)*weightedCriticalMean A ρ.im := by gcongr; linarith
  have he : 1/(24*Real.log T) = 2*(1/(48*Real.log T)) := by ring
  grind


