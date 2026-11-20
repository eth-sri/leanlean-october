module

public import ValuedFieldTheory.LocalField.DiscreteValuationField.ValuationSubringUnits.IntegerValuation
public import Mathlib.Order.Filter.AtTopBot.Tendsto

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

set_option autoImplicit false

/-!
# Valuation estimates for logarithm and exponential series

This file proves lower bounds and divergence-to-infinity statements for the
integer valuations of the logarithm and exponential series terms.
-/

noncomputable section

universe u

open Filter WithZero
open scoped NNReal Filter WithZero

namespace LocalFieldTheory.DiscreteValuationField
namespace MultiplicativeIntegerValuation

variable {K : Type u} [Field K]

section

variable (v : _root_.Valuation K (WithZero (Multiplicative ℤ))) {p n : ℕ}

/-- Positive-degree exponential terms have positive integer valuation when
the input has valuation strictly bigger than one. -/
theorem ofWithZeroValuation_val_pow_div_natCast_factorial_pos_of_one_lt [Fact p.Prime] (x : Kˣ)
    (hnK : (((n.factorial : ℕ) : K) ≠ 0))
    (hnval :
      v (((n.factorial : ℕ) : K)) =
        WithZero.exp (-(padicValNat p n.factorial : ℤ)))
    (hxone : 1 < (ofWithZeroValuation v).val x)
    (hn : n ≠ 0) :
    0 <
      (ofWithZeroValuation v).val
        (x ^ n /
          Units.mk0 (((n.factorial : ℕ) : K)) hnK) := by
  have hterm :=
    ofWithZeroValuation_val_pow_div_natCast_factorial
      (v := v) (p := p) x hnK hnval
  have hxge : (2 : ℤ) ≤ (ofWithZeroValuation v).val x := by
    omega
  have hnnonneg : (0 : ℤ) ≤ (n : ℤ) := by
    exact_mod_cast Nat.zero_le n
  have hlin :=
    mul_le_mul_of_nonneg_left hxge hnnonneg
  have hden :
      (padicValNat p n.factorial : ℤ) ≤ (n : ℤ) := by
    exact_mod_cast padicValNat_factorial_le (p := p) n
  have hnpos : (0 : ℤ) < (n : ℤ) := by
    exact_mod_cast Nat.pos_of_ne_zero hn
  rw [hterm]
  linarith

/-- Real lower bound for the valuation of the exponential-series term
`x^n / n!`. -/
theorem ofWithZeroValuation_val_pow_div_natCast_factorial_real_lower_bound (x : Kˣ)
    (hnK : (((n.factorial : ℕ) : K) ≠ 0))
    (hnval :
      v (((n.factorial : ℕ) : K)) =
        WithZero.exp (-(padicValNat p n.factorial : ℤ)))
    {c : ℝ} (hc : c ≤ ((ofWithZeroValuation v).val x : ℝ)) :
    (n : ℝ) * c - (padicValNat p n.factorial : ℝ) ≤
      ((ofWithZeroValuation v).val
        (x ^ n /
          Units.mk0 (((n.factorial : ℕ) : K)) hnK) : ℝ) := by
  have hterm :=
    ofWithZeroValuation_val_pow_div_natCast_factorial
      (v := v) (p := p) x hnK hnval
  have hlin :=
    mul_le_mul_of_nonneg_left hc (Nat.cast_nonneg n)
  calc
    (n : ℝ) * c - (padicValNat p n.factorial : ℝ) ≤
        (n : ℝ) * ((ofWithZeroValuation v).val x : ℝ) -
          (padicValNat p n.factorial : ℝ) := by
      linarith
    _ =
        ((ofWithZeroValuation v).val
          (x ^ n /
            Units.mk0 (((n.factorial : ℕ) : K)) hnK) : ℝ) := by
      simp_all [hterm]

end

/-- Real lower bound for the valuation of the exponential-series term
`x^n / n!`, with a ramification-index scale in the denominator valuation. -/
theorem ofWithZeroValuation_val_pow_div_natCast_factorial_scaled_real_lower_bound
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    {p n : ℕ} (e : ℕ) (x : Kˣ)
    (hnK : (((n.factorial : ℕ) : K) ≠ 0))
    (hnval :
      v (((n.factorial : ℕ) : K)) =
        WithZero.exp (-((e : ℤ) * (padicValNat p n.factorial : ℤ))))
    {c : ℝ} (hc : c ≤ ((ofWithZeroValuation v).val x : ℝ)) :
    (n : ℝ) * c - (e : ℝ) * (padicValNat p n.factorial : ℝ) ≤
      ((ofWithZeroValuation v).val
        (x ^ n /
          Units.mk0 (((n.factorial : ℕ) : K)) hnK) : ℝ) := by
  have hterm :=
    ofWithZeroValuation_val_pow_div_natCast_factorial_scaled
      (v := v) (p := p) e x hnK hnval
  have hlin :=
    mul_le_mul_of_nonneg_left hc (Nat.cast_nonneg n)
  calc
    (n : ℝ) * c - (e : ℝ) * (padicValNat p n.factorial : ℝ) ≤
        (n : ℝ) * ((ofWithZeroValuation v).val x : ℝ) -
          (e : ℝ) * (padicValNat p n.factorial : ℝ) := by
      linarith
    _ =
        ((ofWithZeroValuation v).val
          (x ^ n /
            Units.mk0 (((n.factorial : ℕ) : K)) hnK) : ℝ) := by
      simp_all [hterm]

section

variable (v : _root_.Valuation K (WithZero (Multiplicative ℤ))) {p : ℕ} [Fact p.Prime]

/-- The valuations of the exponential-series terms `x^n / n!` tend to `+∞`
when the value of `x` is strictly larger than one.  This is the convergence
estimate used for the exponential half of the field-unit logarithm theorem. -/
theorem ofWithZeroValuation_val_pow_div_natCast_factorial_tendsto_atTop (x : Kˣ)
    (hnK : ∀ n : ℕ, (((n.factorial : ℕ) : K) ≠ 0))
    (hnval : ∀ n : ℕ,
      v (((n.factorial : ℕ) : K)) =
        WithZero.exp (-(padicValNat p n.factorial : ℤ)))
    {c : ℝ} (hcOne : 1 < c)
    (hc : c ≤ ((ofWithZeroValuation v).val x : ℝ)) :
    Tendsto
      (fun n : ℕ =>
        ((ofWithZeroValuation v).val
          (x ^ n /
            Units.mk0 (((n.factorial : ℕ) : K)) (hnK n)) : ℝ))
      atTop atTop := by
  exact tendsto_atTop_mono' atTop (Eventually.of_forall fun n ↦ ofWithZeroValuation_val_pow_div_natCast_factorial_real_lower_bound v x (hnK n) (hnval n) hc) (tendsto_nat_mul_const_sub_padicValNat_factorial_atTop hcOne)

/-- Sharp ramified convergence estimate for the exponential-series terms
`x^n / n!`: a value of `x` strictly above `e/(p-1)` dominates the scaled
factorial denominator contribution `e * v_p(n!)`. -/
theorem ofWithZeroValuation_val_pow_div_natCast_factorial_scaled_tendsto_atTop (e : ℕ) (x : Kˣ)
    (hnK : ∀ n : ℕ, (((n.factorial : ℕ) : K) ≠ 0))
    (hnval : ∀ n : ℕ,
      v (((n.factorial : ℕ) : K)) =
        WithZero.exp (-((e : ℤ) * (padicValNat p n.factorial : ℤ))))
    {c : ℝ}
    (hcThreshold : (e : ℝ) / ((p : ℝ) - 1) < c)
    (hc : c ≤ ((ofWithZeroValuation v).val x : ℝ)) :
    Tendsto
      (fun n : ℕ =>
        ((ofWithZeroValuation v).val
          (x ^ n /
            Units.mk0 (((n.factorial : ℕ) : K)) (hnK n)) : ℝ))
      atTop atTop := by
  exact tendsto_atTop_mono' atTop (Eventually.of_forall fun n ↦ ofWithZeroValuation_val_pow_div_natCast_factorial_scaled_real_lower_bound v e x (hnK n) (hnval n) hc) (tendsto_nat_mul_const_sub_const_mul_padicValNat_factorial_atTop (Nat.cast_nonneg e) hcThreshold)

end

/-- Real lower bound for the valuation of `x^n / n`, in the form used to prove
that the logarithm-series terms tend to zero. -/
theorem ofWithZeroValuation_val_pow_div_natCast_real_lower_bound
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    {p n : ℕ} [Fact p.Prime] (x : Kˣ) (hnK : (n : K) ≠ 0)
    (hnval : v (n : K) = WithZero.exp (-(padicValNat p n : ℤ)))
    {c : ℝ} (hc : c ≤ ((ofWithZeroValuation v).val x : ℝ)) :
    (n : ℝ) * c - Real.logb p n ≤
      ((ofWithZeroValuation v).val
        (x ^ n / Units.mk0 (n : K) hnK) : ℝ) := by
  have hterm :=
    ofWithZeroValuation_val_pow_div_natCast
      (v := v) (p := p) x hnK hnval
  have hlin :=
    mul_le_mul_of_nonneg_left hc (Nat.cast_nonneg n)
  have hden :
      (padicValNat p n : ℝ) ≤ Real.logb p n :=
    padicValNat_le_real_logb n
  have hmain :
      (n : ℝ) * c - Real.logb p n ≤
        (n : ℝ) * ((ofWithZeroValuation v).val x : ℝ) -
          (padicValNat p n : ℝ) := by
    linarith
  calc
    (n : ℝ) * c - Real.logb p n ≤
        (n : ℝ) * ((ofWithZeroValuation v).val x : ℝ) -
          (padicValNat p n : ℝ) := hmain
    _ =
        ((ofWithZeroValuation v).val
          (x ^ n / Units.mk0 (n : K) hnK) : ℝ) := by
      simp_all [hterm]

/-- Real lower bound for the valuation of `x^n / n`, with a fixed
ramification-index scale in the denominator valuation. -/
theorem ofWithZeroValuation_val_pow_div_natCast_scaled_real_lower_bound
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    {p n : ℕ} [Fact p.Prime] (e : ℕ) (x : Kˣ)
    (hnK : (n : K) ≠ 0)
    (hnval :
      v (n : K) =
        WithZero.exp (-((e : ℤ) * (padicValNat p n : ℤ))))
    {c : ℝ} (hc : c ≤ ((ofWithZeroValuation v).val x : ℝ)) :
    (n : ℝ) * c - (e : ℝ) * Real.logb (p : ℝ) (n : ℝ) ≤
      ((ofWithZeroValuation v).val
        (x ^ n / Units.mk0 (n : K) hnK) : ℝ) := by
  have hterm :=
    ofWithZeroValuation_val_pow_div_natCast_scaled
      (v := v) (p := p) e x hnK hnval
  have hlin :=
    mul_le_mul_of_nonneg_left hc (Nat.cast_nonneg n)
  let logb₀ := Real.logb (p : ℝ) (n : ℝ)
  have hden_base :
      (padicValNat p n : ℝ) ≤ logb₀ :=
    padicValNat_le_real_logb n
  have hden :
      (e : ℝ) * (padicValNat p n : ℝ) ≤
        (e : ℝ) * logb₀ :=
    mul_le_mul_of_nonneg_left hden_base (Nat.cast_nonneg e)
  have hmain :
      (n : ℝ) * c - (e : ℝ) * logb₀ ≤
        (n : ℝ) * ((ofWithZeroValuation v).val x : ℝ) -
          (e : ℝ) * (padicValNat p n : ℝ) := by
    linarith
  calc
    (n : ℝ) * c - (e : ℝ) * logb₀ ≤
        (n : ℝ) * ((ofWithZeroValuation v).val x : ℝ) -
          (e : ℝ) * (padicValNat p n : ℝ) := hmain
    _ =
        ((ofWithZeroValuation v).val
          (x ^ n / Units.mk0 (n : K) hnK) : ℝ) := by
      simp_all [hterm]

/-- The valuations of the logarithm-series terms `x^(n+1)/(n+1)` tend to
`+∞`, assuming the natural-number denominators have their expected `p`-adic
values and `x` has positive valuation. -/
theorem ofWithZeroValuation_val_pow_succ_div_natCast_tendsto_atTop
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    {p : ℕ} [Fact p.Prime] (x : Kˣ)
    (hnK : ∀ n : ℕ, (((n + 1 : ℕ) : K) ≠ 0))
    (hnval : ∀ n : ℕ,
      v (((n + 1 : ℕ) : K)) =
        WithZero.exp (-(padicValNat p (n + 1) : ℤ)))
    {c : ℝ} (hcpos : 0 < c)
    (hc : c ≤ ((ofWithZeroValuation v).val x : ℝ)) :
    Tendsto
      (fun n : ℕ =>
        ((ofWithZeroValuation v).val
          (x ^ (n + 1) /
            Units.mk0 (((n + 1 : ℕ) : K)) (hnK n)) : ℝ))
      atTop atTop := by
  have hsource :
      Tendsto
        (fun n : ℕ =>
          ((n + 1 : ℕ) : ℝ) * c - Real.logb p (n + 1))
        atTop atTop :=
    tendsto_nat_succ_mul_const_sub_logb_atTop hcpos
  have hle :
      (fun n : ℕ =>
        ((n + 1 : ℕ) : ℝ) * c - Real.logb p (n + 1)) ≤ᶠ[atTop]
      (fun n : ℕ =>
        ((ofWithZeroValuation v).val
          (x ^ (n + 1) /
            Units.mk0 (((n + 1 : ℕ) : K)) (hnK n)) : ℝ)) := Eventually.of_forall fun n => by
      simpa [Nat.cast_add, Nat.cast_one] using
        ofWithZeroValuation_val_pow_div_natCast_real_lower_bound
          (v := v) (p := p) x (hnK n) (hnval n) hc
  exact tendsto_atTop_mono' atTop hle hsource

/-- The valuations of the logarithm-series terms `x^(n+1)/(n+1)` tend to
`+∞` when the natural-number denominators have a fixed ramification-index
scale in their `p`-adic valuation. -/
theorem ofWithZeroValuation_val_pow_succ_div_natCast_scaled_tendsto_atTop
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    {p : ℕ} [Fact p.Prime] (e : ℕ) (x : Kˣ)
    (hnK : ∀ n : ℕ, (((n + 1 : ℕ) : K) ≠ 0))
    (hnval : ∀ n : ℕ,
      v (((n + 1 : ℕ) : K)) =
        WithZero.exp (-((e : ℤ) * (padicValNat p (n + 1) : ℤ))))
    {c : ℝ} (hcpos : 0 < c)
    (hc : c ≤ ((ofWithZeroValuation v).val x : ℝ)) :
    Tendsto
      (fun n : ℕ =>
        ((ofWithZeroValuation v).val
          (x ^ (n + 1) /
            Units.mk0 (((n + 1 : ℕ) : K)) (hnK n)) : ℝ))
      atTop atTop := by
  have hsource :
      Tendsto
        (fun n : ℕ =>
          ((n + 1 : ℕ) : ℝ) * c -
            (e : ℝ) * Real.logb (p : ℝ) ((n + 1 : ℕ) : ℝ))
        atTop atTop :=
    tendsto_nat_succ_mul_const_sub_const_mul_logb_atTop hcpos
  have hle :
      (fun n : ℕ =>
        ((n + 1 : ℕ) : ℝ) * c -
          (e : ℝ) * Real.logb (p : ℝ) ((n + 1 : ℕ) : ℝ)) ≤ᶠ[atTop]
      (fun n : ℕ =>
        ((ofWithZeroValuation v).val
          (x ^ (n + 1) /
            Units.mk0 (((n + 1 : ℕ) : K)) (hnK n)) : ℝ)) := Eventually.of_forall fun n => by
      simpa [Nat.cast_add, Nat.cast_one] using
        ofWithZeroValuation_val_pow_div_natCast_scaled_real_lower_bound
          (v := v) (p := p) (e := e) x
          (hnK n) (hnval n) hc
  exact tendsto_atTop_mono' atTop hle hsource

end MultiplicativeIntegerValuation
end LocalFieldTheory.DiscreteValuationField

end
