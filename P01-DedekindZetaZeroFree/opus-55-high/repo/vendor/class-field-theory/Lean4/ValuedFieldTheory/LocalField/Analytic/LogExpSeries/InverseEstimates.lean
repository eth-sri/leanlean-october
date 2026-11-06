module

public import ValuedFieldTheory.LocalField.Analytic.LogExpSeries.LogConvergence

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-!
Develops the valuation estimates showing that logarithm and exponential series are inverse on
their common principal-unit domain.
-/

open Filter
open Polynomial
open scoped Topology
open scoped PowerSeries.WithPiTopology
noncomputable section

attribute [local instance] Classical.propDecidable

universe u

open ValuationTheory.DiscreteValuationField
open LocalFieldTheory.DiscreteValuationField

namespace LocalFieldTheory.DiscreteValuationField
namespace MultiplicativeIntegerValuation

variable {K : Type u} [Field K]

/-- The positive-degree exponential tail partial sums converge to
`expSeries - 1`. -/
theorem tendsto_expSeriesTailPartialSumField_ofWithZeroValuation_of_lt_exp_neg_one
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    {p : ℕ} [Fact p.Prime] (x : K)
    (hnK : ∀ n : ℕ, (((n.factorial : ℕ) : K) ≠ 0))
    (hnval : ∀ n : ℕ,
      v (((n.factorial : ℕ) : K)) =
        WithZero.exp (-(padicValNat p n.factorial : ℤ)))
    (hvx : v x < WithZero.exp (-1 : ℤ))
    (hcomplete :
      letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
      CompleteSpace K) :
    letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
    Tendsto
      (fun N : ℕ =>
        ∑ n ∈ Finset.range N, expSeriesTermField x hnK (n + 1))
      atTop
      (𝓝 (expSeriesFieldOfWithZeroValuation v x hnK - 1)) := by
  let : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
  have hfull :
      Tendsto
        (fun N : ℕ => expSeriesPartialSumField x hnK (N + 1))
        atTop (𝓝 (expSeriesFieldOfWithZeroValuation v x hnK)) := by
    exact
      (tendsto_expSeriesPartialSumField_ofWithZeroValuation_of_lt_exp_neg_one
        (v := v) (p := p) x hnK hnval hvx hcomplete).comp
          (tendsto_add_atTop_nat 1)
  have hsub :
      Tendsto
        (fun N : ℕ => expSeriesPartialSumField x hnK (N + 1) - 1)
        atTop (𝓝 (expSeriesFieldOfWithZeroValuation v x hnK - 1)) :=
    hfull.sub tendsto_const_nhds
  have htail :
      (fun N : ℕ => expSeriesPartialSumField x hnK (N + 1) - 1) =
        fun N : ℕ =>
          ∑ n ∈ Finset.range N, expSeriesTermField x hnK (n + 1) := by
    funext N
    rw [expSeriesPartialSumField_succ_eq_one_add_tail]
    abel
  simpa [htail] using hsub

/-- The positive-degree exponential tail partial sums converge to
`expSeries - 1` under the sharp ramified threshold. -/
theorem tendsto_expSeriesTailPartialSumField_ofWithZeroValuation_scaled_of_threshold
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    {p : ℕ} [Fact p.Prime] (e : ℕ) (x : K)
    (hnK : ∀ n : ℕ, (((n.factorial : ℕ) : K) ≠ 0))
    (hnval : ∀ n : ℕ,
      v (((n.factorial : ℕ) : K)) =
        WithZero.exp (-((e : ℤ) * (padicValNat p n.factorial : ℤ))))
    (hxthreshold : ∀ hx : x ≠ 0,
      (e : ℚ) / ((p : ℚ) - 1) <
        ((ofWithZeroValuation v).val (Units.mk0 x hx) : ℚ))
    (hcomplete :
      letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
      CompleteSpace K) :
    letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
    Tendsto
      (fun N : ℕ =>
        ∑ n ∈ Finset.range N, expSeriesTermField x hnK (n + 1))
      atTop
      (𝓝 (expSeriesFieldOfWithZeroValuation v x hnK - 1)) := by
  let : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
  have hfull :
      Tendsto
        (fun N : ℕ => expSeriesPartialSumField x hnK (N + 1))
        atTop (𝓝 (expSeriesFieldOfWithZeroValuation v x hnK)) := by
    exact
      (tendsto_expSeriesPartialSumField_ofWithZeroValuation_scaled_of_threshold
        (v := v) (p := p) e x hnK hnval
        (fun hx => by exact_mod_cast hxthreshold hx) hcomplete).comp
          (tendsto_add_atTop_nat 1)
  have hsub :
      Tendsto
        (fun N : ℕ => expSeriesPartialSumField x hnK (N + 1) - 1)
        atTop (𝓝 (expSeriesFieldOfWithZeroValuation v x hnK - 1)) :=
    hfull.sub tendsto_const_nhds
  have htail :
      (fun N : ℕ => expSeriesPartialSumField x hnK (N + 1) - 1) =
        fun N : ℕ =>
          ∑ n ∈ Finset.range N, expSeriesTermField x hnK (n + 1) := by
    funext N
    rw [expSeriesPartialSumField_succ_eq_one_add_tail]
    abel
  simpa [htail] using hsub

/-- Above the sharp ramified `e/(p-1)` threshold, every exponential term of
degree at least two has strictly smaller `ℤᵐ⁰`-value than the linear term. -/
theorem valuation_expSeriesTermField_lt_self_of_scaled_inv_sub_one_lt
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    {p : ℕ} [Fact p.Prime] (e : ℕ) {x : K} (hx : x ≠ 0)
    (hnK : ∀ n : ℕ, (((n.factorial : ℕ) : K) ≠ 0))
    (hnval : ∀ n : ℕ,
      v (((n.factorial : ℕ) : K)) =
        WithZero.exp (-((e : ℤ) * (padicValNat p n.factorial : ℤ))))
    (hthreshold :
      (e : ℚ) / ((p : ℚ) - 1) <
        ((ofWithZeroValuation v).val (Units.mk0 x hx) : ℚ))
    {n : ℕ} (hn : 2 ≤ n) :
    v (expSeriesTermField x hnK n) < v x := by
  let xu : Kˣ := Units.mk0 x hx
  let denom : Kˣ :=
    Units.mk0 (((n.factorial : ℕ) : K)) (hnK n)
  have hval :
      (ofWithZeroValuation v).val xu <
        (ofWithZeroValuation v).val (xu ^ n / denom) := by
    change
      (ofWithZeroValuation v).val xu <
        (ofWithZeroValuation v).val
          (xu ^ n /
            Units.mk0 (((n.factorial : ℕ) : K)) (hnK n))
    rw [ofWithZeroValuation_val_pow_div_natCast_factorial_scaled
      (v := v) (p := p) (e := e) (n := n) xu (hnK n) (hnval n)]
    exact
      exp_higher_term_integer_valuation_gt_scaled
        (p := p) (e := e) (n := n) hn hthreshold
  have hlt :=
    valuation_lt_of_ofWithZeroValuation_val_lt
      (v := v) (x := xu) (y := xu ^ n / denom) hval
  simpa [xu, denom, expSeriesTermField] using hlt

/-- Every finite higher-degree exponential tail has valuation strictly smaller
than the linear term above the sharp ramified `e/(p-1)` threshold. -/
theorem valuation_expSeriesHigherTailPartialSumField_lt_self_of_scaled_inv_sub_one_lt
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    {p : ℕ} [Fact p.Prime] (e : ℕ) {x : K} (hx : x ≠ 0)
    (hnK : ∀ n : ℕ, (((n.factorial : ℕ) : K) ≠ 0))
    (hnval : ∀ n : ℕ,
      v (((n.factorial : ℕ) : K)) =
        WithZero.exp (-((e : ℤ) * (padicValNat p n.factorial : ℤ))))
    (hthreshold :
      (e : ℚ) / ((p : ℚ) - 1) <
        ((ofWithZeroValuation v).val (Units.mk0 x hx) : ℚ))
    (N : ℕ) :
    v (∑ n ∈ Finset.range N, expSeriesTermField x hnK (n + 2)) <
      v x := by
  exact
    v.map_sum_lt ((_root_.Valuation.ne_zero_iff v).2 hx)
      (fun n _hn =>
        valuation_expSeriesTermField_lt_self_of_scaled_inv_sub_one_lt
          (v := v) (p := p) e (x := x) hx hnK hnval hthreshold
          (by omega))

/-- The higher-degree exponential tail partial sums converge to
`expSeries - 1 - x` under the sharp ramified threshold. -/
theorem tendsto_expSeriesHigherTailPartialSumField_ofWithZeroValuation_scaled_of_threshold
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    {p : ℕ} [Fact p.Prime] (e : ℕ) (x : K)
    (hnK : ∀ n : ℕ, (((n.factorial : ℕ) : K) ≠ 0))
    (hnval : ∀ n : ℕ,
      v (((n.factorial : ℕ) : K)) =
        WithZero.exp (-((e : ℤ) * (padicValNat p n.factorial : ℤ))))
    (hxthreshold : ∀ hx : x ≠ 0,
      (e : ℚ) / ((p : ℚ) - 1) <
        ((ofWithZeroValuation v).val (Units.mk0 x hx) : ℚ))
    (hcomplete :
      letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
      CompleteSpace K) :
    letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
    Tendsto
      (fun N : ℕ =>
        ∑ n ∈ Finset.range N, expSeriesTermField x hnK (n + 2))
      atTop
      (𝓝 (expSeriesFieldOfWithZeroValuation v x hnK - 1 - x)) := by
  let : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
  have hfull :
      Tendsto
        (fun N : ℕ =>
          ∑ n ∈ Finset.range (N + 1),
            expSeriesTermField x hnK (n + 1))
        atTop
        (𝓝 (expSeriesFieldOfWithZeroValuation v x hnK - 1)) := by
    exact
      (tendsto_expSeriesTailPartialSumField_ofWithZeroValuation_scaled_of_threshold
        (v := v) (p := p) e x hnK hnval hxthreshold hcomplete).comp
          (tendsto_add_atTop_nat 1)
  have hsub :
      Tendsto
        (fun N : ℕ =>
          (∑ n ∈ Finset.range (N + 1),
            expSeriesTermField x hnK (n + 1)) - x)
        atTop
        (𝓝 (expSeriesFieldOfWithZeroValuation v x hnK - 1 - x)) :=
    hfull.sub tendsto_const_nhds
  have htail :
      (fun N : ℕ =>
        (∑ n ∈ Finset.range (N + 1),
          expSeriesTermField x hnK (n + 1)) - x) =
      fun N : ℕ =>
        ∑ n ∈ Finset.range N, expSeriesTermField x hnK (n + 2) := by
    funext N
    rw [Finset.sum_range_succ']
    simp [expSeriesTermField]
  simpa [htail] using hsub

/-- The full higher-degree exponential tail has valuation strictly smaller
than the linear term above the sharp ramified `e/(p-1)` threshold. -/
theorem valuation_expSeriesHigherTailField_lt_self_of_scaled_inv_sub_one_lt
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    {p : ℕ} [Fact p.Prime] (e : ℕ) {x : K} (hx : x ≠ 0)
    (hnK : ∀ n : ℕ, (((n.factorial : ℕ) : K) ≠ 0))
    (hnval : ∀ n : ℕ,
      v (((n.factorial : ℕ) : K)) =
        WithZero.exp (-((e : ℤ) * (padicValNat p n.factorial : ℤ))))
    (hthreshold :
      (e : ℚ) / ((p : ℚ) - 1) <
        ((ofWithZeroValuation v).val (Units.mk0 x hx) : ℚ))
    (hcomplete :
      letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
      CompleteSpace K) :
    v (expSeriesFieldOfWithZeroValuation v x hnK - 1 - x) <
      v x := by
  exact
    valuation_limit_lt_of_tendsto_of_eventually_lt
      (v := v) (γ := v x) ((_root_.Valuation.ne_zero_iff v).2 hx)
      (tendsto_expSeriesHigherTailPartialSumField_ofWithZeroValuation_scaled_of_threshold
        (v := v) (p := p) e x hnK hnval
        (fun hx' => by
          simp_all)
        hcomplete)
      (Eventually.of_forall fun N =>
        valuation_expSeriesHigherTailPartialSumField_lt_self_of_scaled_inv_sub_one_lt
          (v := v) (p := p) e (x := x) hx hnK hnval hthreshold N)

/-- The exponential-series value is a first principal unit on the normalized
convergence radius: after subtracting the constant term, it lies in the open
unit ball. -/
theorem valuation_expSeriesField_sub_one_lt_one_ofWithZeroValuation_of_lt_exp_neg_one
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    {p : ℕ} [Fact p.Prime] (x : K)
    (hnK : ∀ n : ℕ, (((n.factorial : ℕ) : K) ≠ 0))
    (hnval : ∀ n : ℕ,
      v (((n.factorial : ℕ) : K)) =
        WithZero.exp (-(padicValNat p n.factorial : ℤ)))
    (hvx : v x < WithZero.exp (-1 : ℤ))
    (hcomplete :
      letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
      CompleteSpace K) :
    v (expSeriesFieldOfWithZeroValuation v x hnK - 1) <
      (1 : WithZero (Multiplicative ℤ)) := by
  let : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
  exact
    valuation_limit_lt_one_of_tendsto_of_eventually_lt_one
      (v := v)
      (u := fun N : ℕ =>
        ∑ n ∈ Finset.range N, expSeriesTermField x hnK (n + 1))
      (z := expSeriesFieldOfWithZeroValuation v x hnK - 1)
      (tendsto_expSeriesTailPartialSumField_ofWithZeroValuation_of_lt_exp_neg_one
        (v := v) (p := p) x hnK hnval hvx hcomplete)
      (Eventually.of_forall fun N =>
        valuation_expSeriesTailPartialSumField_lt_one_of_lt_exp_neg_one
          (v := v) (p := p) x hnK hnval hvx N)

/-- On the sharp ramified exponential convergence ball,
`exp(x) - 1` has the same valuation as the linear term `x`. -/
theorem valuation_expSeriesField_sub_one_eq_self_ofWithZeroValuation_scaled_of_threshold
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    {p : ℕ} [Fact p.Prime] (e : ℕ) {x : K} (hx : x ≠ 0)
    (hnK : ∀ n : ℕ, (((n.factorial : ℕ) : K) ≠ 0))
    (hnval : ∀ n : ℕ,
      v (((n.factorial : ℕ) : K)) =
        WithZero.exp (-((e : ℤ) * (padicValNat p n.factorial : ℤ))))
    (hthreshold :
      (e : ℚ) / ((p : ℚ) - 1) <
        ((ofWithZeroValuation v).val (Units.mk0 x hx) : ℚ))
    (hcomplete :
      letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
      CompleteSpace K) :
    v (expSeriesFieldOfWithZeroValuation v x hnK - 1) = v x := by
  have htail :
      v (expSeriesFieldOfWithZeroValuation v x hnK - 1 - x) <
        v x :=
    valuation_expSeriesHigherTailField_lt_self_of_scaled_inv_sub_one_lt
      (v := v) (p := p) e (x := x) hx hnK hnval hthreshold hcomplete
  have hsplit :
      expSeriesFieldOfWithZeroValuation v x hnK - 1 =
        x + (expSeriesFieldOfWithZeroValuation v x hnK - 1 - x) := by
    abel
  rw [hsplit]
  exact v.map_add_eq_of_lt_left htail

/-- The complete-DVF package attached to a standard `ℤᵐ⁰`-valued complete
discrete valuation. -/
def completeDVFOfWithZeroValuation
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    [ValuationTheory.DiscreteValuationField.Valuation.IsCompleteDiscrete v] :
    CompleteDVF.{u, 0} K where
  ValueGroup := WithZero (Multiplicative ℤ)
  valuation := v
  instCompleteDiscrete := inferInstance

/-- For a normalized `ℤᵐ⁰`-valued complete DVF, an integer-valuation lower
bound gives membership in the corresponding maximal-ideal power. -/
theorem mem_maximalIdeal_pow_ofWithZeroValuation_val_ge
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    [ValuationTheory.DiscreteValuationField.Valuation.IsCompleteDiscrete v]
    {π : (completeDVFOfWithZeroValuation v).valuationSubring}
    (hπ : v.IsUniformizer (π : K))
    (hπval : v (π : K) = WithZero.exp (-1 : ℤ))
    (n : ℕ) (a : (completeDVFOfWithZeroValuation v).valuationSubring)
    (hval : ∀ ha : (a : K) ≠ 0,
      (n : ℤ) ≤
        (ofWithZeroValuation v).val (Units.mk0 (a : K) ha)) :
    a ∈ (completeDVFOfWithZeroValuation v).maximalIdeal ^ n := by
  by_cases ha0 : (a : K) = 0
  · simp_all
  · have hπpow :
        v (π : K) ^ n =
          WithZero.exp (-(n : ℤ)) := by
      simp_all
    have hlog :
        WithZero.log (v (a : K)) ≤ -(n : ℤ) := by
      have hNlog :
          (n : ℤ) ≤ -WithZero.log (v (a : K)) := by
        simpa [ofWithZeroValuation_val] using hval ha0
      linarith
    have hva :
        v (a : K) ≤ WithZero.exp (-(n : ℤ)) :=
      WithZero.le_exp_of_log_le hlog
    exact
      (ValuationTheory.DiscreteValuationField.Valuation.mem_maximalIdeal_pow_iff_valuation_le_uniformizer_pow
        (val := v) hπ n (x := a)).2 (by
          change v (a : K) ≤ v ((π : K) ^ n)
          simp_all)

/-- Conversely, membership in `m^n` gives the expected lower bound for the
attached integer valuation. -/
theorem ofWithZeroValuation_val_ge_of_mem_maximalIdeal_pow
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    [ValuationTheory.DiscreteValuationField.Valuation.IsCompleteDiscrete v]
    {π : (completeDVFOfWithZeroValuation v).valuationSubring}
    (hπ : v.IsUniformizer (π : K))
    (hπval : v (π : K) = WithZero.exp (-1 : ℤ))
    (n : ℕ) (a : (completeDVFOfWithZeroValuation v).valuationSubring)
    (ha : a ∈ (completeDVFOfWithZeroValuation v).maximalIdeal ^ n)
    (ha_ne : (a : K) ≠ 0) :
    (n : ℤ) ≤
      (ofWithZeroValuation v).val (Units.mk0 (a : K) ha_ne) := by
  have hπpow :
      v (π : K) ^ n =
        WithZero.exp (-(n : ℤ)) := by
    simp_all
  have hva :
      v (a : K) ≤ WithZero.exp (-(n : ℤ)) := by
    have h :=
      (ValuationTheory.DiscreteValuationField.Valuation.mem_maximalIdeal_pow_iff_valuation_le_uniformizer_pow
        (val := v) hπ n (x := a)).1 ha
    change v (a : K) ≤ v ((π : K) ^ n) at h
    simp_all
  have hv_ne : v (a : K) ≠ 0 :=
    (_root_.Valuation.ne_zero_iff v).2 ha_ne
  have hlog :
      WithZero.log (v (a : K)) ≤ -(n : ℤ) :=
    (WithZero.log_le_iff_le_exp hv_ne).2 hva
  have hneg :
      (n : ℤ) ≤ -WithZero.log (v (a : K)) := by
    omega
  simpa [ofWithZeroValuation_val] using hneg
