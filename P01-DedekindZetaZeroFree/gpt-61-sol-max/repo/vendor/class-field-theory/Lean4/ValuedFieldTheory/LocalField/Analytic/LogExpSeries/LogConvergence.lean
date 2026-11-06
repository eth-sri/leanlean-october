module

public import Mathlib.Topology.Algebra.InfiniteSum.Nonarchimedean
public import ValuedFieldTheory.LocalField.Analytic.LogExpSeries.ExpConvergence

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/




set_option autoImplicit false
/-!
Establishes convergence and summability of the logarithm series on the nonarchimedean open unit
ball.
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
















































/-- Establishes the identity `logSeriesTermField x hnK n = 0`. -/
theorem logSeriesTermField_eq_zero_of_eq_zero
    {x : K} (hx : x = 0)
    (hnK : ∀ n : ℕ, (((n + 1 : ℕ) : K) ≠ 0)) (n : ℕ) :
    logSeriesTermField x hnK n = 0 := by
  have hpow : (0 : K) ^ (n + 1) = 0 := by
    cases n with
    | zero => simp
    | succ n => simp
  simp [logSeriesTermField, hx, hpow]

/-- Establishes the identity `signedLogSeriesTermField x hnK n = 0`. -/
theorem signedLogSeriesTermField_eq_zero_of_eq_zero
    {x : K} (hx : x = 0)
    (hnK : ∀ n : ℕ, (((n + 1 : ℕ) : K) ≠ 0)) (n : ℕ) :
    signedLogSeriesTermField x hnK n = 0 := by
  simp [signedLogSeriesTermField,
    logSeriesTermField_eq_zero_of_eq_zero hx hnK n]

/-- Establishes the identity `logOnePlusSeriesFieldOfWithZeroValuation v 0 hnK = 0`. -/
@[simp] theorem logOnePlusSeriesField_zero_ofWithZeroValuation
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    (hnK : ∀ n : ℕ, (((n + 1 : ℕ) : K) ≠ 0)) :
    logOnePlusSeriesFieldOfWithZeroValuation v 0 hnK = 0 := by
  let : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
  have hzero :
      (fun n : ℕ => signedLogSeriesTermField (0 : K) hnK n) =
        fun _ : ℕ => (0 : K) := by
    funext n
    exact signedLogSeriesTermField_eq_zero_of_eq_zero rfl hnK n
  simp [logOnePlusSeriesFieldOfWithZeroValuation, hzero]































/-- Signed field-element logarithm-series terms tend to zero when `v x < 1`. -/
theorem tendsto_zero_signedLogSeriesTermField_ofWithZeroValuation_of_lt_one
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    {p : ℕ} [Fact p.Prime] (x : K)
    (hnK : ∀ n : ℕ, (((n + 1 : ℕ) : K) ≠ 0))
    (hnval : ∀ n : ℕ,
      v (((n + 1 : ℕ) : K)) =
        WithZero.exp (-(padicValNat p (n + 1) : ℤ)))
    (hvx : v x < (1 : WithZero (Multiplicative ℤ))) :
    letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
    Tendsto (fun n : ℕ => signedLogSeriesTermField x hnK n) atTop
      (𝓝 (0 : K)) := by
  let : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
  by_cases hx : x = 0
  · have hconst :
        (fun n : ℕ => signedLogSeriesTermField x hnK n) =
          fun _ : ℕ => (0 : K) := by
      funext n
      exact signedLogSeriesTermField_eq_zero_of_eq_zero hx hnK n
    simp [hconst]
  · have hxpos :
        0 < (ofWithZeroValuation v).val (Units.mk0 x hx) :=
      ofWithZeroValuation_val_mk0_pos_of_lt_one (v := v) hx hvx
    have hunit :=
      tendsto_zero_signed_log_term_ofWithZeroValuation_of_pos
        (v := v) (p := p) (Units.mk0 x hx) hnK hnval hxpos
    simpa [signedLogSeriesTermField, logSeriesTermField] using hunit
































/-- Summability of the signed field-element logarithm series under the
principal-unit condition `v x < 1`. -/
theorem summable_signedLogSeriesTermField_ofWithZeroValuation_of_lt_one
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    {p : ℕ} [Fact p.Prime] (x : K)
    (hnK : ∀ n : ℕ, (((n + 1 : ℕ) : K) ≠ 0))
    (hnval : ∀ n : ℕ,
      v (((n + 1 : ℕ) : K)) =
        WithZero.exp (-(padicValNat p (n + 1) : ℤ)))
    (hvx : v x < (1 : WithZero (Multiplicative ℤ)))
    (hcomplete :
      letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
      CompleteSpace K) :
    letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
    Summable (fun n : ℕ => signedLogSeriesTermField x hnK n) := by
  let : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
  let : CompleteSpace K := hcomplete
  have : NonarchimedeanRing K := nonarchimedeanRing_ofWithZeroValuation v
  have hzero :
      Tendsto (fun n : ℕ => signedLogSeriesTermField x hnK n) atTop
        (𝓝 (0 : K)) :=
    tendsto_zero_signedLogSeriesTermField_ofWithZeroValuation_of_lt_one
      (v := v) (p := p) x hnK hnval hvx
  have hcofinite :
      Tendsto (fun n : ℕ => signedLogSeriesTermField x hnK n) cofinite
        (𝓝 (0 : K)) := by
    simpa [Nat.cofinite_eq_atTop] using hzero
  rw [NonarchimedeanAddGroup.summable_iff_tendsto_cofinite_zero]
  exact hcofinite

/-- Field-element principal-unit logarithm series: the signed series has the
value supplied by `logOnePlusSeriesFieldOfWithZeroValuation`. -/
theorem hasSum_signedLogSeriesTermField_logOnePlusSeriesField_ofWithZeroValuation_of_lt_one
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    {p : ℕ} [Fact p.Prime] (x : K)
    (hnK : ∀ n : ℕ, (((n + 1 : ℕ) : K) ≠ 0))
    (hnval : ∀ n : ℕ,
      v (((n + 1 : ℕ) : K)) =
        WithZero.exp (-(padicValNat p (n + 1) : ℤ)))
    (hvx : v x < (1 : WithZero (Multiplicative ℤ)))
    (hcomplete :
      letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
      CompleteSpace K) :
    letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
    HasSum (fun n : ℕ => signedLogSeriesTermField x hnK n)
      (logOnePlusSeriesFieldOfWithZeroValuation v x hnK) := by
  let : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
  have hs :
      Summable (fun n : ℕ => signedLogSeriesTermField x hnK n) :=
    summable_signedLogSeriesTermField_ofWithZeroValuation_of_lt_one
      (v := v) (p := p) x hnK hnval hvx hcomplete
  simpa [logOnePlusSeriesFieldOfWithZeroValuation] using hs.hasSum



































































































































































































/-- The field-element finite logarithm polynomials converge to the
principal-unit logarithm-series value. -/
theorem tendsto_logOnePlusPartialSumField_ofWithZeroValuation_of_lt_one
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    {p : ℕ} [Fact p.Prime] (x : K)
    (hnK : ∀ n : ℕ, (((n + 1 : ℕ) : K) ≠ 0))
    (hnval : ∀ n : ℕ,
      v (((n + 1 : ℕ) : K)) =
        WithZero.exp (-(padicValNat p (n + 1) : ℤ)))
    (hvx : v x < (1 : WithZero (Multiplicative ℤ)))
    (hcomplete :
      letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
      CompleteSpace K) :
    letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
    Tendsto (fun N : ℕ => logOnePlusPartialSumField x hnK N) atTop
      (𝓝 (logOnePlusSeriesFieldOfWithZeroValuation v x hnK)) := by
  let : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
  have hsum :=
    hasSum_signedLogSeriesTermField_logOnePlusSeriesField_ofWithZeroValuation_of_lt_one
      (v := v) (p := p) x hnK hnval hvx hcomplete
  simpa [logOnePlusPartialSumField] using hsum.tendsto_sum_nat

section
variable (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    {p : ℕ} [Fact p.Prime] (e : ℕ) (x : K)
    (hnK : ∀ n : ℕ, (((n + 1 : ℕ) : K) ≠ 0))
    (hnval : ∀ n : ℕ,
      v (((n + 1 : ℕ) : K)) =
        WithZero.exp (-((e : ℤ) * (padicValNat p (n + 1) : ℤ))))
    (hvx : v x < (1 : WithZero (Multiplicative ℤ)))
include v p e x hnK hnval hvx in
/-- Signed field-element logarithm-series terms tend to zero under a
ramified denominator valuation hypothesis. -/
theorem tendsto_zero_signedLogSeriesTermField_ofWithZeroValuation_scaled_of_lt_one
      :
    letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
    Tendsto (fun n : ℕ => signedLogSeriesTermField x hnK n) atTop
      (𝓝 (0 : K)) := by
  let : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
  by_cases hx : x = 0
  · have hconst :
        (fun n : ℕ => signedLogSeriesTermField x hnK n) =
          fun _ : ℕ => (0 : K) := by
      funext n
      exact signedLogSeriesTermField_eq_zero_of_eq_zero hx hnK n
    simp [hconst]
  · have hxpos :
        0 < (ofWithZeroValuation v).val (Units.mk0 x hx) :=
      ofWithZeroValuation_val_mk0_pos_of_lt_one (v := v) hx hvx
    have hunit :=
      tendsto_zero_signed_log_term_ofWithZeroValuation_scaled_of_pos
        (v := v) (p := p) e (Units.mk0 x hx) hnK hnval hxpos
    simpa [signedLogSeriesTermField, logSeriesTermField] using hunit

include v p e x hnK hnval hvx in
/-- Summability of the signed field-element logarithm series under a
ramified denominator valuation hypothesis. -/
theorem summable_signedLogSeriesTermField_ofWithZeroValuation_scaled_of_lt_one
     
    (hcomplete :
      letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
      CompleteSpace K) :
    letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
    Summable (fun n : ℕ => signedLogSeriesTermField x hnK n) := by
  let : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
  let : CompleteSpace K := hcomplete
  have : NonarchimedeanRing K := nonarchimedeanRing_ofWithZeroValuation v
  have hzero :
      Tendsto (fun n : ℕ => signedLogSeriesTermField x hnK n) atTop
        (𝓝 (0 : K)) :=
    tendsto_zero_signedLogSeriesTermField_ofWithZeroValuation_scaled_of_lt_one
      (v := v) (p := p) e x hnK hnval hvx
  have hcofinite :
      Tendsto (fun n : ℕ => signedLogSeriesTermField x hnK n) cofinite
        (𝓝 (0 : K)) := by
    simpa [Nat.cofinite_eq_atTop] using hzero
  rw [NonarchimedeanAddGroup.summable_iff_tendsto_cofinite_zero]
  exact hcofinite

include v p e x hnK hnval hvx in
/-- Field-element logarithm series has the same `tsum` value under a
ramified denominator valuation hypothesis. -/
theorem hasSum_signedLogSeriesTermField_logOnePlusSeriesField_ofWithZeroValuation_scaled_of_lt_one
     
    (hcomplete :
      letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
      CompleteSpace K) :
    letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
    HasSum (fun n : ℕ => signedLogSeriesTermField x hnK n)
      (logOnePlusSeriesFieldOfWithZeroValuation v x hnK) := by
  let : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
  have hs :
      Summable (fun n : ℕ => signedLogSeriesTermField x hnK n) :=
    summable_signedLogSeriesTermField_ofWithZeroValuation_scaled_of_lt_one
      (v := v) (p := p) e x hnK hnval hvx hcomplete
  simpa [logOnePlusSeriesFieldOfWithZeroValuation] using hs.hasSum

include v p e x hnK hnval hvx in
/-- Field-element finite logarithm polynomials converge to the logarithm
series under a ramified denominator valuation hypothesis. -/
theorem tendsto_logOnePlusPartialSumField_ofWithZeroValuation_scaled_of_lt_one
     
    (hcomplete :
      letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
      CompleteSpace K) :
    letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
    Tendsto (fun N : ℕ => logOnePlusPartialSumField x hnK N) atTop
      (𝓝 (logOnePlusSeriesFieldOfWithZeroValuation v x hnK)) := by
  let : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
  have hsum :=
    hasSum_signedLogSeriesTermField_logOnePlusSeriesField_ofWithZeroValuation_scaled_of_lt_one
      (v := v) (p := p) e x hnK hnval hvx hcomplete
  simpa [logOnePlusPartialSumField] using hsum.tendsto_sum_nat





















































































































































































































































































































































/-- Above the ramified threshold `e/(p-1)`, each higher logarithm term has
strictly smaller `ℤᵐ⁰`-value than the linear term. -/
theorem valuation_logSeriesTermField_lt_self_of_scaled_inv_sub_one_lt
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    {p : ℕ} [Fact p.Prime] (e : ℕ) {x : K} (hx : x ≠ 0)
    (hnK : ∀ n : ℕ, (((n + 1 : ℕ) : K) ≠ 0))
    (hnval : ∀ n : ℕ,
      v (((n + 1 : ℕ) : K)) =
        WithZero.exp (-((e : ℤ) * (padicValNat p (n + 1) : ℤ))))
    (hthreshold :
      (e : ℚ) / ((p : ℚ) - 1) <
        ((ofWithZeroValuation v).val (Units.mk0 x hx) : ℚ))
    {n : ℕ} (hn : n ≠ 0) :
    v (logSeriesTermField x hnK n) < v x := by
  let xu : Kˣ := Units.mk0 x hx
  let denom : Kˣ :=
    Units.mk0 (((n + 1 : ℕ) : K)) (hnK n)
  have hval :
      (ofWithZeroValuation v).val xu <
        (ofWithZeroValuation v).val (xu ^ (n + 1) / denom) := by
    change
      (ofWithZeroValuation v).val xu <
        (ofWithZeroValuation v).val
          (xu ^ (n + 1) /
            Units.mk0 (((n + 1 : ℕ) : K)) (hnK n))
    rw [ofWithZeroValuation_val_pow_div_natCast_scaled
      (v := v) (p := p) (e := e) (n := n + 1) xu (hnK n) (hnval n)]
    exact
      log_higher_term_integer_valuation_gt_scaled
        (p := p) (e := e) (n := n + 1) (by omega) hthreshold
  have hlt :=
    valuation_lt_of_ofWithZeroValuation_val_lt
      (v := v) (x := xu) (y := xu ^ (n + 1) / denom) hval
  simpa [xu, denom, logSeriesTermField] using hlt

/-- The signed higher logarithm terms have the same ramified valuation
estimate as the unsigned terms. -/
theorem valuation_signedLogSeriesTermField_lt_self_of_scaled_inv_sub_one_lt
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    {p : ℕ} [Fact p.Prime] (e : ℕ) {x : K} (hx : x ≠ 0)
    (hnK : ∀ n : ℕ, (((n + 1 : ℕ) : K) ≠ 0))
    (hnval : ∀ n : ℕ,
      v (((n + 1 : ℕ) : K)) =
        WithZero.exp (-((e : ℤ) * (padicValNat p (n + 1) : ℤ))))
    (hthreshold :
      (e : ℚ) / ((p : ℚ) - 1) <
        ((ofWithZeroValuation v).val (Units.mk0 x hx) : ℚ))
    {n : ℕ} (hn : n ≠ 0) :
    v (signedLogSeriesTermField x hnK n) < v x := by
  have hlog :
      v (logSeriesTermField x hnK n) < v x :=
    valuation_logSeriesTermField_lt_self_of_scaled_inv_sub_one_lt
      (v := v) (p := p) e (x := x) hx hnK hnval hthreshold hn
  have hval :
      v (signedLogSeriesTermField x hnK n) =
        v (logSeriesTermField x hnK n) := by
    rw [signedLogSeriesTermField, v.map_mul]
    simp
  rw [hval]
  exact hlog

/-- Every finite higher-degree logarithm tail has valuation strictly smaller
than the linear term above the ramified `e/(p-1)` threshold. -/
theorem valuation_logHigherTailPartialSumField_lt_self_of_scaled_inv_sub_one_lt
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    {p : ℕ} [Fact p.Prime] (e : ℕ) {x : K} (hx : x ≠ 0)
    (hnK : ∀ n : ℕ, (((n + 1 : ℕ) : K) ≠ 0))
    (hnval : ∀ n : ℕ,
      v (((n + 1 : ℕ) : K)) =
        WithZero.exp (-((e : ℤ) * (padicValNat p (n + 1) : ℤ))))
    (hthreshold :
      (e : ℚ) / ((p : ℚ) - 1) <
        ((ofWithZeroValuation v).val (Units.mk0 x hx) : ℚ))
    (N : ℕ) :
    v (∑ n ∈ Finset.range N, signedLogSeriesTermField x hnK (n + 1)) <
      v x := by
  exact
    v.map_sum_lt ((_root_.Valuation.ne_zero_iff v).2 hx)
      (fun n _hn =>
        valuation_signedLogSeriesTermField_lt_self_of_scaled_inv_sub_one_lt
          (v := v) (p := p) e (x := x) hx hnK hnval hthreshold
          (Nat.succ_ne_zero n))

include v p e x hnK hnval hvx in
/-- The higher-degree logarithm tail partial sums converge to
`log(1+x) - x` under a ramified denominator valuation hypothesis. -/
theorem tendsto_logHigherTailPartialSumField_ofWithZeroValuation_scaled_of_lt_one
     
    (hcomplete :
      letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
      CompleteSpace K) :
    letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
    Tendsto
      (fun N : ℕ =>
        ∑ n ∈ Finset.range N, signedLogSeriesTermField x hnK (n + 1))
      atTop
      (𝓝 (logOnePlusSeriesFieldOfWithZeroValuation v x hnK - x)) := by
  let : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
  have hfull :
      Tendsto
        (fun N : ℕ => logOnePlusPartialSumField x hnK (N + 1))
        atTop (𝓝 (logOnePlusSeriesFieldOfWithZeroValuation v x hnK)) := by
    exact
      (tendsto_logOnePlusPartialSumField_ofWithZeroValuation_scaled_of_lt_one
        (v := v) (p := p) e x hnK hnval hvx hcomplete).comp
          (tendsto_add_atTop_nat 1)
  have hsub :
      Tendsto
        (fun N : ℕ => logOnePlusPartialSumField x hnK (N + 1) - x)
        atTop
        (𝓝 (logOnePlusSeriesFieldOfWithZeroValuation v x hnK - x)) :=
    hfull.sub tendsto_const_nhds
  have htail :
      (fun N : ℕ => logOnePlusPartialSumField x hnK (N + 1) - x) =
      fun N : ℕ =>
        ∑ n ∈ Finset.range N, signedLogSeriesTermField x hnK (n + 1) := by
    funext N
    rw [logOnePlusPartialSumField, Finset.sum_range_succ']
    simp
  simpa [htail] using hsub
end


/-- The full higher-degree logarithm tail has valuation strictly smaller than
the linear term above the ramified `e/(p-1)` threshold. -/
theorem valuation_logHigherTailField_lt_self_of_scaled_inv_sub_one_lt
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    {p : ℕ} [Fact p.Prime] (e : ℕ) {x : K} (hx : x ≠ 0)
    (hnK : ∀ n : ℕ, (((n + 1 : ℕ) : K) ≠ 0))
    (hnval : ∀ n : ℕ,
      v (((n + 1 : ℕ) : K)) =
        WithZero.exp (-((e : ℤ) * (padicValNat p (n + 1) : ℤ))))
    (hvx : v x < (1 : WithZero (Multiplicative ℤ)))
    (hthreshold :
      (e : ℚ) / ((p : ℚ) - 1) <
        ((ofWithZeroValuation v).val (Units.mk0 x hx) : ℚ))
    (hcomplete :
      letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
      CompleteSpace K) :
    v (logOnePlusSeriesFieldOfWithZeroValuation v x hnK - x) <
      v x := by
  exact
    valuation_limit_lt_of_tendsto_of_eventually_lt
      (v := v) (γ := v x) ((_root_.Valuation.ne_zero_iff v).2 hx)
      (tendsto_logHigherTailPartialSumField_ofWithZeroValuation_scaled_of_lt_one
        (v := v) (p := p) e x hnK hnval hvx hcomplete)
      (Eventually.of_forall fun N =>
        valuation_logHigherTailPartialSumField_lt_self_of_scaled_inv_sub_one_lt
          (v := v) (p := p) e (x := x) hx hnK hnval hthreshold N)

/-- Above the ramified `e/(p-1)` threshold, `log(1+x)` has the same valuation
as the linear term `x`. -/
theorem valuation_logOnePlusSeriesField_eq_self_of_scaled_inv_sub_one_lt
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    {p : ℕ} [Fact p.Prime] (e : ℕ) {x : K} (hx : x ≠ 0)
    (hnK : ∀ n : ℕ, (((n + 1 : ℕ) : K) ≠ 0))
    (hnval : ∀ n : ℕ,
      v (((n + 1 : ℕ) : K)) =
        WithZero.exp (-((e : ℤ) * (padicValNat p (n + 1) : ℤ))))
    (hvx : v x < (1 : WithZero (Multiplicative ℤ)))
    (hthreshold :
      (e : ℚ) / ((p : ℚ) - 1) <
        ((ofWithZeroValuation v).val (Units.mk0 x hx) : ℚ))
    (hcomplete :
      letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
      CompleteSpace K) :
    v (logOnePlusSeriesFieldOfWithZeroValuation v x hnK) = v x := by
  have htail :
      v (logOnePlusSeriesFieldOfWithZeroValuation v x hnK - x) <
        v x :=
    valuation_logHigherTailField_lt_self_of_scaled_inv_sub_one_lt
      (v := v) (p := p) e (x := x) hx hnK hnval hvx hthreshold hcomplete
  have hsplit :
      logOnePlusSeriesFieldOfWithZeroValuation v x hnK =
        x + (logOnePlusSeriesFieldOfWithZeroValuation v x hnK - x) := by
    abel
  rw [hsplit]
  exact v.map_add_eq_of_lt_left htail






















































end MultiplicativeIntegerValuation
end LocalFieldTheory.DiscreteValuationField

end
