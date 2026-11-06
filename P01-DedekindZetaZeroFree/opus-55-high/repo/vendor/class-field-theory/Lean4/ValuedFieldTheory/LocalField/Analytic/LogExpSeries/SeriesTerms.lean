module

public import Mathlib.Topology.Algebra.InfiniteSum.Nonarchimedean
public import Mathlib.Topology.Algebra.Valued.WithZeroMulInt
public import ValuedFieldTheory.LocalField.Analytic.LogExpSeries.FormalProduct
public import ValuedFieldTheory.LocalField.DiscreteValuationField.FieldUnitDecomposition

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-!
Defines the logarithm and exponential series terms and proves the valuation estimates used in
their convergence arguments.
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

/-- The unsigned `n`-th term `x^(n+1)/(n+1)` in the logarithm series. -/
def logSeriesTerm
    (x : Kˣ) (hnK : ∀ n : ℕ, (((n + 1 : ℕ) : K) ≠ 0)) (n : ℕ) : K :=
  ((x ^ (n + 1) /
    Units.mk0 (((n + 1 : ℕ) : K)) (hnK n) : Kˣ) : K)

/-- The signed `n`-th term `(-1)^n x^(n+1)/(n+1)` in the series for
`log (1 + x)`. -/
def signedLogSeriesTerm
    (x : Kˣ) (hnK : ∀ n : ℕ, (((n + 1 : ℕ) : K) ≠ 0)) (n : ℕ) : K :=
  (-1 : K) ^ n * logSeriesTerm x hnK n

/-- The value of the principal-unit logarithm series, formed as a topological
sum in the topology attached to `v`. -/
def logOnePlusSeriesOfWithZeroValuation
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    (x : Kˣ) (hnK : ∀ n : ℕ, (((n + 1 : ℕ) : K) ≠ 0)) : K := by
  letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
  exact ∑' n : ℕ, signedLogSeriesTerm x hnK n

/-- The unsigned logarithm-series term for a field element.  This is the form
needed for principal units `1 + x`, where `x` may be zero. -/
def logSeriesTermField
    (x : K) (hnK : ∀ n : ℕ, (((n + 1 : ℕ) : K) ≠ 0)) (n : ℕ) : K :=
  x ^ (n + 1) /
    ((Units.mk0 (((n + 1 : ℕ) : K)) (hnK n) : Kˣ) : K)

/-- Establishes the identity `logSeriesTermField x hnK 0 = x`. -/
@[simp] theorem logSeriesTermField_zero
    (x : K) (hnK : ∀ n : ℕ, (((n + 1 : ℕ) : K) ≠ 0)) :
    logSeriesTermField x hnK 0 = x := by
  simp [logSeriesTermField]

/-- The signed logarithm-series term for a field element. -/
def signedLogSeriesTermField
    (x : K) (hnK : ∀ n : ℕ, (((n + 1 : ℕ) : K) ≠ 0)) (n : ℕ) : K :=
  (-1 : K) ^ n * logSeriesTermField x hnK n

/-- Establishes the identity `signedLogSeriesTermField x hnK 0 = x`. -/
@[simp] theorem signedLogSeriesTermField_zero
    (x : K) (hnK : ∀ n : ℕ, (((n + 1 : ℕ) : K) ≠ 0)) :
    signedLogSeriesTermField x hnK 0 = x := by
  simp [signedLogSeriesTermField]

/-- The `n`-th field logarithm-series term is the evaluation of the
`(n+1)`-st coefficient of the formal series `log(1+X)` at `x`. -/
theorem powerSeries_log_coeff_mul_pow_eq_signedLogSeriesTermField
    [Algebra ℚ K] (x : K)
    (hnK : ∀ n : ℕ, (((n + 1 : ℕ) : K) ≠ 0)) (n : ℕ) :
    PowerSeries.coeff (n + 1) (PowerSeries.log K) *
        x ^ (n + 1) =
      signedLogSeriesTermField x hnK n := by
  have hcoeff :
      algebraMap ℚ K (((-1 : ℚ) ^ n) / (((n + 1 : ℕ) : ℚ))) =
        (-1 : K) ^ n / (((n + 1 : ℕ) : K)) := by
    rw [map_div₀, map_pow, map_neg]
    rw [(algebraMap ℚ K).map_one]
    congr 1
    exact map_natCast (algebraMap ℚ K) (n + 1)
  have hsign : (-1 : ℚ) ^ (n + 1 + 1) = (-1 : ℚ) ^ n := by
    rw [show n + 1 + 1 = n + 2 by omega, pow_add]
    norm_num
  rw [PowerSeries.coeff_log, ite_eq_right (Nat.succ_ne_zero n), hsign, hcoeff]
  simp [signedLogSeriesTermField, logSeriesTermField, div_eq_mul_inv,
    mul_assoc, mul_left_comm, mul_comm]

/-- Field-element finite partial sums of the principal-unit logarithm series. -/
def logOnePlusPartialSumField
    (x : K) (hnK : ∀ n : ℕ, (((n + 1 : ℕ) : K) ≠ 0)) (N : ℕ) : K :=
  ∑ n ∈ Finset.range N, signedLogSeriesTermField x hnK n

/-- Field-element value of the principal-unit logarithm series. -/
def logOnePlusSeriesFieldOfWithZeroValuation
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    (x : K) (hnK : ∀ n : ℕ, (((n + 1 : ℕ) : K) ≠ 0)) : K := by
  letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
  exact ∑' n : ℕ, signedLogSeriesTermField x hnK n

/-! ### Exponential-series terms -/

/-- The `n`-th term `x^n / n!` in the exponential series, for nonzero `x`. -/
def expSeriesTerm
    (x : Kˣ) (hnK : ∀ n : ℕ, (((n.factorial : ℕ) : K) ≠ 0))
    (n : ℕ) : K :=
  ((x ^ n /
    Units.mk0 (((n.factorial : ℕ) : K)) (hnK n) : Kˣ) : K)

/-- The `n`-th exponential-series term for a field element.  This covers
`x = 0`, which is needed for the eventual principal-ideal domain of the
exponential map. -/
def expSeriesTermField
    (x : K) (hnK : ∀ n : ℕ, (((n.factorial : ℕ) : K) ≠ 0))
    (n : ℕ) : K :=
  x ^ n / ((Units.mk0 (((n.factorial : ℕ) : K)) (hnK n) : Kˣ) : K)

/-- Establishes the identity `expSeriesTermField x hnK 0 = 1`. -/
@[simp] theorem expSeriesTermField_zero
    (x : K) (hnK : ∀ n : ℕ, (((n.factorial : ℕ) : K) ≠ 0)) :
    expSeriesTermField x hnK 0 = 1 := by
  simp [expSeriesTermField]

/-- The `n`-th field exponential-series term is the evaluation of the
`n`-th coefficient of mathlib's formal exponential series at `x`. -/
theorem formalExpPowerSeries_coeff_mul_pow_eq_expSeriesTermField
    [Algebra ℚ K] (x : K)
    (hnK : ∀ n : ℕ, (((n.factorial : ℕ) : K) ≠ 0)) (n : ℕ) :
    PowerSeries.coeff n (PowerSeries.exp K) * x ^ n =
      expSeriesTermField x hnK n := by
  rw [PowerSeries.coeff_exp]
  simp [expSeriesTermField, div_eq_mul_inv, mul_comm]

/-- Field-element finite partial sums of the exponential series. -/
def expSeriesPartialSumField
    (x : K) (hnK : ∀ n : ℕ, (((n.factorial : ℕ) : K) ≠ 0))
    (N : ℕ) : K :=
  ∑ n ∈ Finset.range N, expSeriesTermField x hnK n

/-- Coefficientwise Cauchy product for the local exponential terms, inherited
from mathlib's formal identity `exp(xX) * exp(yX) = exp((x+y)X)`. -/
theorem expSeriesTermField_add_eq_sum_antidiagonal
    [Algebra ℚ K] (x y : K)
    (hnK : ∀ n : ℕ, (((n.factorial : ℕ) : K) ≠ 0)) (n : ℕ) :
    expSeriesTermField (x + y) hnK n =
      ∑ ij ∈ Finset.antidiagonal n,
        expSeriesTermField x hnK ij.1 *
          expSeriesTermField y hnK ij.2 := by
  symm
  calc
    (∑ ij ∈ Finset.antidiagonal n,
        expSeriesTermField x hnK ij.1 *
          expSeriesTermField y hnK ij.2) =
        ∑ ij ∈ Finset.antidiagonal n,
          (PowerSeries.coeff ij.1 (PowerSeries.exp K) * x ^ ij.1) *
            (PowerSeries.coeff ij.2 (PowerSeries.exp K) * y ^ ij.2) := 
      Finset.sum_congr rfl fun ij _ => by
        rw [formalExpPowerSeries_coeff_mul_pow_eq_expSeriesTermField
          (K := K) x hnK ij.1,
          formalExpPowerSeries_coeff_mul_pow_eq_expSeriesTermField
          (K := K) y hnK ij.2]
    _ = ∑ ij ∈ Finset.antidiagonal n,
          PowerSeries.coeff ij.1
              (PowerSeries.rescale x (PowerSeries.exp K)) *
            PowerSeries.coeff ij.2
              (PowerSeries.rescale y (PowerSeries.exp K)) := 
      Finset.sum_congr rfl fun ij _ => by
        simp [mul_assoc, mul_left_comm, mul_comm]
    _ = PowerSeries.coeff n
          (PowerSeries.rescale x (PowerSeries.exp K) *
            PowerSeries.rescale y (PowerSeries.exp K)) := by
      rw [PowerSeries.coeff_mul]
    _ = PowerSeries.coeff n
          (PowerSeries.rescale (x + y) (PowerSeries.exp K)) := by
      rw [PowerSeries.exp_mul_exp_eq_exp_add]
    _ = PowerSeries.coeff n (PowerSeries.exp K) * (x + y) ^ n := by
      simp [mul_comm]
    _ = expSeriesTermField (x + y) hnK n :=
      formalExpPowerSeries_coeff_mul_pow_eq_expSeriesTermField
        (K := K) (x + y) hnK n

/-- Field-element value of the exponential series. -/
def expSeriesFieldOfWithZeroValuation
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    (x : K) (hnK : ∀ n : ℕ, (((n.factorial : ℕ) : K) ≠ 0)) : K := by
  letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
  exact ∑' n : ℕ, expSeriesTermField x hnK n

/-- The topology attached to a valued field is nonarchimedean.  This is the
topological input needed before applying mathlib's nonarchimedean infinite-sum
criterion. -/
theorem nonarchimedeanRing_ofWithZeroValuation
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ))) :
    letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
    NonarchimedeanRing K := by
  let : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
  simpa [Valued.mk'] using v.subgroups_basis.nonarchimedean

/-- If a nonzero field element has valuation strictly below one, then its
attached integer valuation as a field unit is positive. -/
theorem ofWithZeroValuation_val_mk0_pos_of_lt_one
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    {x : K} (hx : x ≠ 0)
    (hvx : v x < (1 : WithZero (Multiplicative ℤ))) :
    0 < (ofWithZeroValuation v).val (Units.mk0 x hx) := by
  have hxv_ne : v x ≠ 0 := (_root_.Valuation.ne_zero_iff v).2 hx
  have hlogneg : WithZero.log (v x) < (0 : ℤ) := by
    have hloglt :
        WithZero.log (v x) <
          WithZero.log (1 : WithZero (Multiplicative ℤ)) := by
      rw [WithZero.log_lt_log hxv_ne one_ne_zero]
      exact hvx
    simpa using hloglt
  simp_all

/-- If a nonzero element lies below `exp (-1)` in the normalized
`ℤᵐ⁰`-valuation, then its attached integer valuation is strictly bigger than
one.  This is the field-element radius used for the exponential series. -/
theorem ofWithZeroValuation_val_mk0_one_lt_of_lt_exp_neg_one
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    {x : K} (hx : x ≠ 0)
    (hvx : v x < WithZero.exp (-1 : ℤ)) :
    1 < ((ofWithZeroValuation v).val (Units.mk0 x hx) : ℝ) := by
  have hxv_ne : v x ≠ 0 := (_root_.Valuation.ne_zero_iff v).2 hx
  have hloglt : WithZero.log (v x) < (-1 : ℤ) := by
    simpa using
      ((WithZero.log_lt_log hxv_ne
        (WithZero.exp_ne_zero (a := (-1 : ℤ)))).2 hvx)
  have hint : (1 : ℤ) < -WithZero.log (v x) := by
    linarith
  have hreal : (1 : ℝ) < ((-WithZero.log (v x) : ℤ) : ℝ) := by
    exact_mod_cast hint
  simpa [ofWithZeroValuation_val] using hreal

/-- Positive attached integer valuation is the same direction as lying in the
open unit ball for the original `ℤᵐ⁰`-valued valuation. -/
theorem valuation_lt_one_of_ofWithZeroValuation_val_pos
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ))) (x : Kˣ)
    (hpos : 0 < (ofWithZeroValuation v).val x) :
    v (x : K) < (1 : WithZero (Multiplicative ℤ)) := by
  have hxv_ne : v (x : K) ≠ 0 :=
    (_root_.Valuation.ne_zero_iff v).2 x.ne_zero
  have hlogneg : WithZero.log (v (x : K)) < (0 : ℤ) := by
    rw [ofWithZeroValuation_val] at hpos
    linarith
  rw [← WithZero.log_lt_log hxv_ne one_ne_zero]
  simpa using hlogneg

/-- Integer-valued valuation comparison, translated back to the original
`ℤᵐ⁰`-valued valuation.  Larger integer value means smaller `WithZero` value. -/
theorem valuation_lt_of_ofWithZeroValuation_val_lt
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ))) {x y : Kˣ}
    (hxy : (ofWithZeroValuation v).val x <
      (ofWithZeroValuation v).val y) :
    v (y : K) < v (x : K) := by
  simp_all

/-- Equal `ℤᵐ⁰`-valued valuations give equal integer valuations after passing
to `ofWithZeroValuation`. -/
theorem ofWithZeroValuation_val_eq_of_valuation_eq
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ))) {x y : Kˣ}
    (hxy : v (x : K) = v (y : K)) :
    (ofWithZeroValuation v).val x = (ofWithZeroValuation v).val y := by
  simp [ofWithZeroValuation_val, hxy]

/-- The integer valuation attached to a nonarchimedean `ℤᵐ⁰`-valuation is
bounded below by the minimum under addition. -/
theorem ofWithZeroValuation_val_add_ge_min
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    {x y : K} (hx : x ≠ 0) (hy : y ≠ 0) (hxy : x + y ≠ 0) :
    min ((ofWithZeroValuation v).val (Units.mk0 x hx))
        ((ofWithZeroValuation v).val (Units.mk0 y hy)) ≤
      (ofWithZeroValuation v).val (Units.mk0 (x + y) hxy) := by
  simp_all

/-- In the topology attached to a discrete `ℤᵐ⁰`-valued valuation, every open
valuation ball of nonzero radius is sequentially closed for convergent
sequences. -/
theorem valuation_limit_lt_of_tendsto_of_eventually_lt
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    {γ : WithZero (Multiplicative ℤ)} (hγ : γ ≠ 0)
    {u : ℕ → K} {z : K}
    (hu :
      letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
      Tendsto u atTop (𝓝 z))
    (hsmall : ∀ᶠ n : ℕ in atTop, v (u n) < γ) :
    v z < γ := by
  let : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
  by_contra hznot
  have hzle : γ ≤ v z := le_of_not_gt hznot
  have hvz0 : v z ≠ 0 := by
    intro hvz
    apply hγ
    simp_all
  have hdiff :
      Tendsto (fun n : ℕ => z - u n) atTop (𝓝 (0 : K)) := by
    have hz : Tendsto (fun _ : ℕ => z) atTop (𝓝 z) := tendsto_const_nhds
    simpa using hz.sub hu
  have hball : {w : K | v w < v z} ∈ 𝓝 (0 : K) := by
    rw [Valued.mem_nhds_zero]
    refine ⟨Units.mk0 (v.restrict z) (by simpa using hvz0), ?_⟩
    intro w hw
    change v.restrict w < v.restrict z at hw
    exact v.restrict_lt_iff.mp hw
  have hdiff_small : ∀ᶠ n : ℕ in atTop, v (z - u n) < v z :=
    hdiff.eventually hball
  have hcontra : ∀ᶠ n : ℕ in atTop, False := by
    filter_upwards [hsmall, hdiff_small] with n hun hdiffn
    have hun_lt_z : v (u n) < v z := lt_of_lt_of_le hun hzle
    have hsub : v (z - u n) = v z :=
      v.map_sub_eq_of_lt_left hun_lt_z
    simp_all
  rcases hcontra.exists with ⟨_, hfalse⟩
  exact hfalse

/-- In the topology attached to a discrete `ℤᵐ⁰`-valued valuation, the open
unit ball is sequentially closed for convergent sequences. -/
theorem valuation_limit_lt_one_of_tendsto_of_eventually_lt_one
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    {u : ℕ → K} {z : K}
    (hu :
      letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
      Tendsto u atTop (𝓝 z))
    (hsmall :
      ∀ᶠ n : ℕ in atTop,
        v (u n) < (1 : WithZero (Multiplicative ℤ))) :
    v z < (1 : WithZero (Multiplicative ℤ)) := by
  exact
    valuation_limit_lt_of_tendsto_of_eventually_lt
      (v := v) (γ := (1 : WithZero (Multiplicative ℤ))) one_ne_zero
      hu hsmall

/-- The product of two elements of valuation strictly below one again has
valuation strictly below one. -/
theorem valuation_mul_lt_one_of_lt_one
    {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]
    (v : _root_.Valuation K Γ₀) {x y : K}
    (hx : v x < 1) (hy : v y < 1) :
    v (x * y) < 1 := by
  rw [v.map_mul]
  exact _root_.Left.mul_lt_one' hx hy

/-- The logarithm product argument `(1+x)(1+y)-1 = x+y+xy` stays in the
open unit ball of a valuation. -/
theorem valuation_log_mul_argument_lt_one_of_lt_one
    {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]
    (v : _root_.Valuation K Γ₀) {x y : K}
    (hx : v x < 1) (hy : v y < 1) :
    v (x + y + x * y) < 1 := by
  have hxy : v (x * y) < 1 :=
    valuation_mul_lt_one_of_lt_one v hx hy
  have hsum_le : v (x + y) ≤ max (v x) (v y) :=
    map_add_le_max v x y
  have hsum_lt : v (x + y) < 1 :=
    lt_of_le_of_lt hsum_le (max_lt hx hy)
  have htotal_le : v ((x + y) + x * y) ≤ max (v (x + y)) (v (x * y)) :=
    map_add_le_max v (x + y) (x * y)
  exact lt_of_le_of_lt htotal_le (max_lt hsum_lt hxy)

/-- Ramified-denominator version of the logarithm-series valuation estimate:
if integer denominators have value `e * v_p(n)`, positive valuation of `x`
still forces `x^(n+1)/(n+1)` to tend to zero. -/
theorem ofWithZeroValuation_val_log_term_scaled_tendsto_atTop_of_pos
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    {p : ℕ} [Fact p.Prime] (e : ℕ) (x : Kˣ)
    (hnK : ∀ n : ℕ, (((n + 1 : ℕ) : K) ≠ 0))
    (hnval : ∀ n : ℕ,
      v (((n + 1 : ℕ) : K)) =
        WithZero.exp (-((e : ℤ) * (padicValNat p (n + 1) : ℤ))))
    (hxpos : 0 < (ofWithZeroValuation v).val x) :
    Tendsto
      (fun n : ℕ =>
        ((ofWithZeroValuation v).val
          (x ^ (n + 1) /
            Units.mk0 (((n + 1 : ℕ) : K)) (hnK n)) : ℝ))
      atTop atTop := by
  have hxone : (1 : ℤ) ≤ (ofWithZeroValuation v).val x := by
    omega
  have hxoneReal : (1 : ℝ) ≤ ((ofWithZeroValuation v).val x : ℝ) := by
    exact_mod_cast hxone
  exact
    ofWithZeroValuation_val_pow_succ_div_natCast_scaled_tendsto_atTop
      (v := v) (p := p) e x hnK hnval
      (hcpos := by norm_num)
      (hc := hxoneReal)

/-- Eventually the ramified-denominator logarithm-series terms have valuation
at least any prescribed integer bound. -/
theorem eventually_le_ofWithZeroValuation_val_log_term_scaled_of_pos
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    {p : ℕ} [Fact p.Prime] (e : ℕ) (x : Kˣ)
    (hnK : ∀ n : ℕ, (((n + 1 : ℕ) : K) ≠ 0))
    (hnval : ∀ n : ℕ,
      v (((n + 1 : ℕ) : K)) =
        WithZero.exp (-((e : ℤ) * (padicValNat p (n + 1) : ℤ))))
    (hxpos : 0 < (ofWithZeroValuation v).val x)
    (N : ℤ) :
    ∀ᶠ n : ℕ in atTop,
      N ≤
        (ofWithZeroValuation v).val
          (x ^ (n + 1) /
            Units.mk0 (((n + 1 : ℕ) : K)) (hnK n)) := by
  have htendsto :=
    ofWithZeroValuation_val_log_term_scaled_tendsto_atTop_of_pos
      (v := v) (p := p) e x hnK hnval hxpos
  have hreal :
      ∀ᶠ n : ℕ in atTop,
        (N : ℝ) ≤
          ((ofWithZeroValuation v).val
            (x ^ (n + 1) /
              Units.mk0 (((n + 1 : ℕ) : K)) (hnK n)) : ℝ) :=
    tendsto_atTop.1 htendsto (N : ℝ)
  filter_upwards [hreal] with n hn
  exact_mod_cast hn

/-- The signed logarithm-series terms tend to zero under the ramified
denominator valuation hypothesis. -/
theorem tendsto_zero_signed_log_term_ofWithZeroValuation_scaled_of_pos
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    {p : ℕ} [Fact p.Prime] (e : ℕ) (x : Kˣ)
    (hnK : ∀ n : ℕ, (((n + 1 : ℕ) : K) ≠ 0))
    (hnval : ∀ n : ℕ,
      v (((n + 1 : ℕ) : K)) =
        WithZero.exp (-((e : ℤ) * (padicValNat p (n + 1) : ℤ))))
    (hxpos : 0 < (ofWithZeroValuation v).val x) :
    letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
    Tendsto
      (fun n : ℕ =>
        (-1 : K) ^ n *
          ((x ^ (n + 1) /
            Units.mk0 (((n + 1 : ℕ) : K)) (hnK n) : Kˣ) : K))
      atTop (𝓝 (0 : K)) := by
  let : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
  rw [tendsto_iff_forall_eventually_mem]
  intro s hs
  rw [Valued.mem_nhds_zero] at hs
  rcases hs with ⟨γ, hγs⟩
  let γ' : (WithZero (Multiplicative ℤ))ˣ :=
    Units.map (MonoidWithZeroHom.ValueGroup₀.embedding
      (f := (v : K →*₀ WithZero (Multiplicative ℤ)))) γ
  rcases WithZero.exists_exp_neg_natCast_lt γ'.ne_zero with ⟨N, hNγ⟩
  have hterm :=
    eventually_le_ofWithZeroValuation_val_log_term_scaled_of_pos
      (v := v) (p := p) e x hnK hnval hxpos (N : ℤ)
  filter_upwards [hterm] with n hn
  apply hγs
  let y : Kˣ :=
    x ^ (n + 1) /
      Units.mk0 (((n + 1 : ℕ) : K)) (hnK n)
  have hlog :
      WithZero.log (v (y : K)) ≤ -(N : ℤ) := by
    have hNlog : (N : ℤ) ≤ -WithZero.log (v (y : K)) := by
      simpa [y, ofWithZeroValuation_val] using hn
    linarith
  have hvle : v (y : K) ≤ WithZero.exp (-(N : ℤ)) :=
    WithZero.le_exp_of_log_le hlog
  have hsign : v ((-1 : K) ^ n) = 1 := by
    simp
  have hvsigned :
      v ((-1 : K) ^ n * (y : K)) ≤ WithZero.exp (-(N : ℤ)) := by
    rw [v.map_mul, hsign, one_mul]
    exact hvle
  change v.restrict ((-1 : K) ^ n * (y : K)) < γ.1
  rw [Valuation.restrict_lt_iff_lt_embedding]
  exact lt_of_le_of_lt hvsigned (by simpa [γ'] using hNγ)
