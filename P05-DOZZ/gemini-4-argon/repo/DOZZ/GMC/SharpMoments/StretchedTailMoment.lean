/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.MeasureTheory.Integral.Lebesgue.Add
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! # Negative moments from stretched-exponential small-ball tails

If the small-ball probabilities satisfy `P {m ≤ e^{-x}} ≤ C exp (-d x^β)` for every `x ≥ 0` with
`d > 0` and `β > 1`, then every negative moment `∫ m^(-q) dP` is finite, with a bound depending
only on `C, d, β, q`. The proof is a discrete layer cake: `m^(-q)` is dominated by `1` plus the sum
over `n` of `e^{q (n+1)}` times the indicator of `{m ≤ e^{-n}}`, and the resulting series
`∑ e^{q (n+1)} exp (-d n^β)` converges because `β > 1`. -/

@[expose] public section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace DOZZ.Proofs

/-! ### The pointwise layer-cake bound -/

/-- The `n`-th layer of the discrete layer cake: the weight `e^{q (n+1)}` on the level set
`{w ≤ e^{-n}}`. -/
noncomputable def stretchedTail_layer (q : ℝ) (n : ℕ) (v : ℝ≥0∞) : ℝ≥0∞ :=
  {w : ℝ≥0∞ | w ≤ ENNReal.ofReal (Real.exp (-(n : ℝ)))}.indicator
    (fun _ => ENNReal.ofReal (Real.exp (q * ((n : ℝ) + 1)))) v







/-! ### Integration of the layer cake -/



/-- The negative moment is at most `1` plus the weighted small-ball probabilities. -/
theorem stretchedTail_lintegral_le {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (m : Ω → ℝ≥0∞) (hm : AEMeasurable m P) q (hq : 0 < q) :
    ∫⁻ ω, m ω ^ (-q) ∂P ≤ 1 + ∑' n : ℕ, ENNReal.ofReal (Real.exp (q * ((n : ℝ) + 1))) *
      P {ω | m ω ≤ ENNReal.ofReal (Real.exp (-(n : ℝ)))} := by
  have stretchedTail_layer_of_le (n : ℕ) {v : ℝ≥0∞} (hv : v ≤ ENNReal.ofReal (Real.exp (-(n : ℝ)))) : stretchedTail_layer q n v = ENNReal.ofReal (Real.exp (q * ((n : ℝ) + 1))) := Set.indicator_of_mem (s := {w : ℝ≥0∞ | w ≤ ENNReal.ofReal (Real.exp (-(n : ℝ)))}) hv _
  have stretchedTail_aemeasurable_layer n : AEMeasurable (fun ω => stretchedTail_layer q n (m ω)) P := (measurable_const.indicator measurableSet_Iic).comp_aemeasurable hm
  have stretchedTail_lintegral_layer (n : ℕ) : ∫⁻ ω, stretchedTail_layer q n (m ω) ∂P = ENNReal.ofReal (Real.exp (q * ((n : ℝ) + 1))) * P {ω | m ω ≤ ENNReal.ofReal (Real.exp (-(n : ℝ)))} := by
    have hs : NullMeasurableSet {ω | m ω ≤ ENNReal.ofReal (Real.exp (-(n : ℝ)))} P :=
      hm.nullMeasurable measurableSet_Iic
    rw [← lintegral_indicator_const₀ hs]
    rfl
  have stretchedTail_rpow_neg_le (v : ℝ≥0∞) : v ^ (-q) ≤ 1 + ∑' n : ℕ, stretchedTail_layer q n v := by
    have stretchedTail_pos_case (hv0 : v ≠ 0) (hvt : v ≠ ⊤) : v ^ (-q) ≤ 1 + ∑' n : ℕ, stretchedTail_layer q n v := by
      have stretchedTail_exists_level r (hr : 0 < r) (hr1 : r ≤ 1) : ∃ n : ℕ, r ≤ Real.exp (-(n : ℝ)) ∧ r ^ (-q) ≤ Real.exp (q * ((n : ℝ) + 1)) := by
        have ht0 : 0 ≤ -Real.log r := by
          have := Real.log_nonpos hr.le hr1
          linarith
        refine ⟨⌊-Real.log r⌋₊, ?_, ?_⟩
        · have h1 : ((⌊-Real.log r⌋₊ : ℕ) : ℝ) ≤ -Real.log r := Nat.floor_le ht0
          calc r = Real.exp (-(-Real.log r)) := by rw [neg_neg, Real.exp_log hr]
            _ ≤ Real.exp (-(⌊-Real.log r⌋₊ : ℝ)) := Real.exp_le_exp.2 (neg_le_neg h1)
        · have h2 : -Real.log r < (⌊-Real.log r⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one _
          calc r ^ (-q) = Real.exp (-Real.log r * q) := by
                rw [Real.rpow_def_of_pos hr]; congr 1; ring
            _ ≤ Real.exp (q * ((⌊-Real.log r⌋₊ : ℝ) + 1)) := by
                apply Real.exp_le_exp.2
                rw [mul_comm q]
                exact mul_le_mul_of_nonneg_right h2.le hq.le
      by_cases hv1 : 1 ≤ v
      · exact (ENNReal.rpow_le_one_of_one_le_of_neg hv1 (neg_lt_zero.2 hq)).trans le_self_add
      · obtain ⟨r, hr, rfl⟩ : ∃ r : ℝ, 0 < r ∧ ENNReal.ofReal r = v :=
          ⟨v.toReal, ENNReal.toReal_pos hv0 hvt, ENNReal.ofReal_toReal hvt⟩
        obtain ⟨n, hn1, hn2⟩ := stretchedTail_exists_level r hr ((ENNReal.ofReal_lt_one.1 (not_le.1 hv1)).le)
        calc ENNReal.ofReal r ^ (-q) = ENNReal.ofReal (r ^ (-q)) := ENNReal.ofReal_rpow_of_pos hr
          _ ≤ ENNReal.ofReal (Real.exp (q * ((n : ℝ) + 1))) := ENNReal.ofReal_le_ofReal hn2
          _ = stretchedTail_layer q n (ENNReal.ofReal r) :=
              (stretchedTail_layer_of_le n (ENNReal.ofReal_le_ofReal hn1)).symm
          _ ≤ ∑' k : ℕ, stretchedTail_layer q k (ENNReal.ofReal r) :=
              ENNReal.le_tsum (f := fun k => stretchedTail_layer q k (ENNReal.ofReal r)) n
          _ ≤ _ := le_add_self
    have stretchedTail_zero_case : (0 : ℝ≥0∞) ^ (-q) ≤ 1 + ∑' n : ℕ, stretchedTail_layer q n 0 := by
      have hsum : ∑' n : ℕ, stretchedTail_layer q n 0 = ⊤ := by
        refine top_le_iff.1 ?_
        rw [← ENNReal.tsum_const_eq_top_of_ne_zero (α := ℕ) (c := 1) one_ne_zero]
        refine ENNReal.tsum_le_tsum fun n => ?_
        rw [stretchedTail_layer_of_le n zero_le]
        exact (fun n => by rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal (Real.one_le_exp (by positivity))) n
      rw [hsum, ENNReal.zero_rpow_of_neg (neg_lt_zero.2 hq)]
      simp
    rcases eq_or_ne v 0 with rfl | hv0
    · exact stretchedTail_zero_case
    rcases eq_or_ne v ⊤ with rfl | hvt
    · rw [ENNReal.top_rpow_of_neg (neg_lt_zero.2 hq)]
      exact zero_le
    · exact stretchedTail_pos_case hv0 hvt
  calc ∫⁻ ω, m ω ^ (-q) ∂P
      ≤ ∫⁻ ω, (1 + ∑' n : ℕ, stretchedTail_layer q n (m ω)) ∂P :=
        lintegral_mono fun ω => stretchedTail_rpow_neg_le (m ω)
    _ = 1 + ∑' n : ℕ, ∫⁻ ω, stretchedTail_layer q n (m ω) ∂P := by
        rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one,
          lintegral_tsum (stretchedTail_aemeasurable_layer)]
    _ = _ := by
        simp_rw [stretchedTail_lintegral_layer]

/-! ### Summability of the stretched-exponential series -/

/-- The `n`-th term of the dominating series: `e^{q (n+1)} * (max C 0 * exp (-d n^β))`. -/
noncomputable def stretchedTail_term (C d β q : ℝ) (n : ℕ) : ℝ :=
  Real.exp (q * ((n : ℝ) + 1)) * (max C 0 * Real.exp (-d * (n : ℝ) ^ β))




/-! ### The main bound -/


/-- A stretched-exponential bound on small-ball probabilities gives every negative moment, with a
bound depending only on the tail constants and the order. -/
theorem lintegral_rpow_neg_le_of_stretched_tail
    (C d β q : ℝ) (hd : 0 < d) (hβ : 1 < β) (hq : 0 < q) :
    ∃ K : ℝ, ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (m : Ω → ℝ≥0∞), AEMeasurable m P →
      (∀ x : ℝ, 0 ≤ x → P {ω | m ω ≤ ENNReal.ofReal (Real.exp (-x))} ≤
        ENNReal.ofReal (C * Real.exp (-d * x ^ β))) →
      ∫⁻ ω, m ω ^ (-q) ∂P ≤ ENNReal.ofReal K := by
  have stretchedTail_term_nonneg n : 0 ≤ stretchedTail_term C d β q n := mul_nonneg (Real.exp_pos _).le (mul_nonneg (le_max_right _ _) (Real.exp_pos _).le)
  have stretchedTail_term_le (n : ℕ) {p : ℝ≥0∞} (hp : p ≤ ENNReal.ofReal (C * Real.exp (-d * (n : ℝ) ^ β))) : ENNReal.ofReal (Real.exp (q * ((n : ℝ) + 1))) * p ≤ ENNReal.ofReal (stretchedTail_term C d β q n) := by
    calc ENNReal.ofReal (Real.exp (q * ((n : ℝ) + 1))) * p
        ≤ ENNReal.ofReal (Real.exp (q * ((n : ℝ) + 1))) *
            ENNReal.ofReal (C * Real.exp (-d * (n : ℝ) ^ β)) := mul_le_mul_right hp _
      _ = ENNReal.ofReal (Real.exp (q * ((n : ℝ) + 1)) * (C * Real.exp (-d * (n : ℝ) ^ β))) :=
          (ENNReal.ofReal_mul (Real.exp_pos _).le).symm
      _ ≤ ENNReal.ofReal (stretchedTail_term C d β q n) := by
          refine ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le)
          exact mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le
  have stretchedTail_summable : Summable (stretchedTail_term C d β q) := by
    have stretchedTail_eventually_exponent_le : ∀ᶠ n : ℕ in atTop, q * ((n : ℝ) + 1) + -d * (n : ℝ) ^ β ≤ -(n : ℝ) := by
      have hpow : Tendsto (fun n : ℕ => (n : ℝ) ^ (β - 1)) atTop atTop :=
        (tendsto_rpow_atTop (sub_pos.2 hβ)).comp tendsto_natCast_atTop_atTop
      filter_upwards [hpow.eventually_ge_atTop ((2 * q + 1) / d), eventually_ge_atTop 1] with n hn hn1
      have hn1' : (1 : ℝ) ≤ n := by exact_mod_cast hn1
      have hn0 : (0 : ℝ) < n := lt_of_lt_of_le one_pos hn1'
      have hsplit : (n : ℝ) ^ β = (n : ℝ) ^ (β - 1) * n := by
        have h := Real.rpow_add_one hn0.ne' (β - 1)
        rwa [sub_add_cancel] at h
      have h1 : 2 * q + 1 ≤ d * (n : ℝ) ^ (β - 1) := by
        rw [div_le_iff₀ hd] at hn
        linarith
      have h2 : (2 * q + 1) * n ≤ d * (n : ℝ) ^ β := by
        rw [hsplit, ← mul_assoc]
        exact mul_le_mul_of_nonneg_right h1 hn0.le
      have h3 : q ≤ q * n := le_mul_of_one_le_right hq.le hn1'
      linarith
    refine Summable.of_norm_bounded_eventually_nat
      (g := fun n : ℕ => max C 0 * Real.exp (-(n : ℝ))) (Real.summable_exp_neg_nat.mul_left _) ?_
    filter_upwards [stretchedTail_eventually_exponent_le] with n hn
    rw [Real.norm_of_nonneg (stretchedTail_term_nonneg n)]
    calc stretchedTail_term C d β q n
        = max C 0 * Real.exp (q * ((n : ℝ) + 1) + -d * (n : ℝ) ^ β) := by
          rw [stretchedTail_term, Real.exp_add]
          ring
      _ ≤ max C 0 * Real.exp (-(n : ℝ)) :=
          mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 hn) (le_max_right _ _)
  refine ⟨1 + ∑' n : ℕ, stretchedTail_term C d β q n, ?_⟩
  intro Ω _ P _ m hm htail
  calc ∫⁻ ω, m ω ^ (-q) ∂P
      ≤ 1 + ∑' n : ℕ, ENNReal.ofReal (Real.exp (q * ((n : ℝ) + 1))) *
          P {ω | m ω ≤ ENNReal.ofReal (Real.exp (-(n : ℝ)))} :=
        stretchedTail_lintegral_le P m hm q hq
    _ ≤ 1 + ∑' n : ℕ, ENNReal.ofReal (stretchedTail_term C d β q n) :=
        add_le_add_right (ENNReal.tsum_le_tsum fun n =>
          stretchedTail_term_le n (htail (n : ℝ) (Nat.cast_nonneg n))) _
    _ = ENNReal.ofReal (1 + ∑' n : ℕ, stretchedTail_term C d β q n) := by
        rw [ENNReal.ofReal_add zero_le_one (tsum_nonneg (stretchedTail_term_nonneg)),
          ENNReal.ofReal_tsum_of_nonneg (stretchedTail_term_nonneg) (stretchedTail_summable),
          ENNReal.ofReal_one]

end DOZZ.Proofs
