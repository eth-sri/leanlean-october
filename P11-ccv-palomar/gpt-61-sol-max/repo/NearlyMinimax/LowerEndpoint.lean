module

public import NearlyMinimax.Chebyshev
public import Mathlib


@[expose] public section

/-! The fixed shrunk-density-interval estimate in `eq:LB-tauM`. -/

noncomputable section
open Filter
open scoped Topology

namespace NearlyMinimax

def densityIntervalExponent a b  :=
  Real.log ((Real.sqrt b + Real.sqrt a) / (Real.sqrt b - Real.sqrt a))

def shrunkDensityExponent a b (M : ℕ)  :=
  densityIntervalExponent (a + (M : ℝ)⁻¹) (b - (M : ℝ)⁻¹)

theorem densityIntervalExponent_pos {a b } (ha : 0 < a) (hab : a < b) :
    0 < densityIntervalExponent a b := by
  have hsa := Real.sqrt_pos.2 ha
  have hsb := Real.sqrt_lt_sqrt ha.le hab
  apply Real.log_pos
  bound

theorem densityIntervalExponent_shrink_mono {a b t }
    (ha : 0 < a) (ht : 0 ≤ t) (hab : a + t < b - t) :
    densityIntervalExponent a b ≤ densityIntervalExponent (a + t) (b - t) := by
  have hab0 : a < b := by linarith
  have hA := Real.sqrt_nonneg a
  have hB := Real.sqrt_nonneg (b - t)
  have hAA : Real.sqrt a ≤ Real.sqrt (a + t) := Real.sqrt_le_sqrt (by linarith)
  have hBB : Real.sqrt (b - t) ≤ Real.sqrt b := Real.sqrt_le_sqrt (by linarith)
  have hden := sub_pos.2 (Real.sqrt_lt_sqrt ha.le hab0)
  have hden' := sub_pos.2 (Real.sqrt_lt_sqrt (by linarith : 0 ≤ a + t) hab)
  unfold densityIntervalExponent
  apply Real.log_le_log (by positivity)
  apply (div_le_div_iff₀ hden hden').2
  nlinarith

section
variable {a b : ℝ} (ha : 0 < a) (hab : a < b)
include ha hab

theorem densityIntervalExponent_differentiable_shrink  :
    DifferentiableAt ℝ (fun t  => densityIntervalExponent (a + t) (b - t)) 0 := by
  have hb  := ha.trans hab
  have hsa  := (Real.sqrt_pos.2 ha).ne'
  have hden  :=
    (sub_pos.2 (Real.sqrt_lt_sqrt ha.le hab)).ne'
  have hratio : (Real.sqrt b + Real.sqrt a) / (Real.sqrt b - Real.sqrt a) ≠ 0 := by positivity
  unfold densityIntervalExponent
  apply DifferentiableAt.log
  · apply DifferentiableAt.div
    · apply DifferentiableAt.add
      · exact ((differentiableAt_const b).sub differentiableAt_id).sqrt (by simpa using hb.ne')
      · exact ((differentiableAt_const a).add differentiableAt_id).sqrt (by simpa using ha.ne')
    · apply DifferentiableAt.sub
      · exact ((differentiableAt_const b).sub differentiableAt_id).sqrt (by simpa using hb.ne')
      · exact ((differentiableAt_const a).add differentiableAt_id).sqrt (by simpa using ha.ne')
    · simpa using hden
  · simpa using hratio

/-- The fixed `Cτ` exists before the sample size is chosen. No exponent estimate is assumed. -/
theorem exists_shrunkDensityExponent_control  :
    ∃ Cτ : ℝ, 0 ≤ Cτ ∧ ∀ᶠ M : ℕ in atTop,
      densityIntervalExponent a b ≤ shrunkDensityExponent a b M ∧
      (shrunkDensityExponent a b M - densityIntervalExponent a b) * M ≤ Cτ := by
  have hf := densityIntervalExponent_differentiable_shrink ha hab
  obtain ⟨K, hK⟩ := hf.isBigO_sub.bound
  have ht : Tendsto (fun M : ℕ => (M : ℝ)⁻¹) atTop (𝓝 0) := tendsto_natCast_atTop_atTop.inv_tendsto_atTop
  have hsmall := ht.eventually (gt_mem_nhds (by linarith : 0 < (b - a) / 2))
  refine ⟨max K 0, le_max_right _ _, ?_⟩
  filter_upwards [ht.eventually hK, hsmall, eventually_ge_atTop (1 : ℕ)] with M hbound hMsmall hM
  have hMpos : 0 < (M : ℝ) := by positivity
  have hMinv  := inv_nonneg.2 hMpos.le
  have hmono := densityIntervalExponent_shrink_mono ha hMinv
    (by linarith : a + (M : ℝ)⁻¹ < b - (M : ℝ)⁻¹)
  change densityIntervalExponent a b ≤ shrunkDensityExponent a b M at hmono
  constructor
  · exact hmono
  · simp only [Real.norm_eq_abs, sub_zero, add_zero, abs_of_nonneg hMinv] at hbound
    change |shrunkDensityExponent a b M - densityIntervalExponent a b| ≤ K * (M : ℝ)⁻¹ at hbound
    rw [abs_of_nonneg (sub_nonneg.2 hmono)] at hbound
    have hb := mul_le_mul_of_nonneg_right hbound hMpos.le
    rw [mul_assoc, inv_mul_cancel₀ hMpos.ne', mul_one] at hb
    exact hb.trans (le_max_left _ _)
end


end NearlyMinimax
