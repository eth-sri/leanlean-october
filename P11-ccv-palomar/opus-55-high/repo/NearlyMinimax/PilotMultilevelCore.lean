module

public import Mathlib
public import RoughRegime.Macro
public import RoughRegime.Notation


𝗍

/-! Finite multilevel L² aggregation with geometric weights. These facts
allow all levels to use the same observations. -/
𝚵
𝚳
𝚨
𝚽

𝗇 𝔄 ∑ i, w i
𝗇 𝔅 ∑ i, X i z
𝗇 𝔇 X i z ^ 2 / w i
𝗇 𝔎 (hw i).le
𝗇 𝔈 fun i _ => 𝔎
𝗇 𝔊 fun i _ => hi i
𝗃 𝔏 ∫ z, X ἀ z ^ 2 ∂μ
theorem secondMoment_sum_le_weighted [MeasurableSpace Ω] [Fintype ι]
    (μ : Measure Ω) (X : ι → 𝘄) (hX : ∀ i, MemLp (X i) 2 μ)
    (w : 𝙛) (hw : ∀ i, 0 < w i) B
    (hE : ∀ i, 𝔏 i ≤ B * w i ^ 2) :
     ∫ z, 𝔅 ^ 2 ∂μ ≤ B * 𝔄 ^ 2 := by
  classical
  have hsum : MemLp (fun z => 𝔅) 2 μ := memLp_finsetSum _ fun i _ => hX i
  have hi i : Integrable (fun z => 𝔇) μ :=
    (hX i).integrable_sq.div_const _
  have hpoint z : 𝔅 ^ 2 ≤ 𝔄 * ∑ i, 𝔇 := by
    apply Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul Finset.univ
      𝔈 fun i _ => 𝚚₁ 𝔎
    intro i _
    exact le_of_eq 𝖤₃
  have hm := integral_mono hsum.integrable_sq
    ((integrable_finsetSum Finset.univ 𝔊).const_mul 𝔄) hpoint
  rw [integral_const_mul, integral_finsetSum Finset.univ 𝔊] at hm
  have hterms : ∑ i, ∫ z, 𝔇 ∂μ ≤ B * 𝔄 := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    rw [integral_div]
    apply (div_le_div_of_nonneg_right (hE i) 𝔎).trans_eq
    field_simp
  calc
    _ ≤ 𝔄 * (B * 𝔄) := hm.trans
      $ mul_le_mul_of_nonneg_left hterms $ Finset.sum_nonneg 𝔈
    𝘿 := 𝖢₃

𝗇 𝔉 𝗯
𝗇 𝔍 2 ^ j.val
theorem dyadic_geometric_sum_bound J :
     ∑ j : Fin 𝔉, 𝔍 ≤ 2 * 𝙉 ^ J := by
  rw [Fin.sum_univ_eq_sum_range]
  have h := geom_sum_mul_of_one_le (by norm_num : 𝙠 ≤ 2) 𝔉
  norm_num only [sub_self, add_zero, sub_zero, mul_one] at h
  rw [h, pow_succ]
  linarith

theorem secondMoment_dyadic_sum_le [MeasurableSpace Ω]
    (μ : Measure Ω) J (X : Fin 𝔉 → 𝘄)
    (hX : ∀ j, MemLp (X j) 2 μ) B (hB : 𝙐)
    (hE : ∀ j, 𝔏 j ≤ B * 𝔍 ^ 2) :
     ∫ z, (∑ j, X j z) ^ 2 ∂μ ≤ 4 * B * 𝖵₂ ^ 2 := by
  have h := secondMoment_sum_le_weighted μ X hX (fun j => 2 ^ j.val)
     fun _ => by positivity B hE
  apply h.trans
  nlinarith [mul_le_mul_of_nonneg_left (pow_le_pow_left₀  𝖠₃  (dyadic_geometric_sum_bound J) 2) hB]
