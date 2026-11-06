module

public import Mathlib.Data.Nat.Factorization.Basic
public import Mathlib.Data.Nat.Prime.Basic
public import Mathlib.Algebra.EuclideanDomain.Basic
public import Mathlib.Algebra.Order.Field.Power
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.NumberTheory.Padics.PadicVal.Basic
public import Mathlib.Topology.Algebra.Order.Field
public import Mathlib.Tactic

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/


/-!
# Arithmetic lemmas for local-field index calculations

This file contains the pure natural-number cancellation steps used after local-field
norm and value-group arguments have produced an lcm divisibility.

It also contains the elementary `p`-adic valuation estimates used in the local-field structure development,
the logarithm and exponential estimates for the convergence and valuation behavior of the
logarithm and exponential series.
-/

namespace LocalFieldTheory.DiscreteValuationField

open Filter

section PadicLogArithmetic

variable {p n : ℕ}

/-- Arithmetic estimate for the field-unit logarithm in real logarithmic
form: `v_p(n) <= log_p(n)`. -/
theorem padicValNat_le_real_logb
    [Fact p.Prime] (n : ℕ) :
    (padicValNat p n : ℝ) ≤ Real.logb p n := by
  exact
    (Nat.cast_le.mpr (padicValNat_le_nat_log (p := p) n)).trans
      (Real.natLog_le_logb n p)

/-- Variant of the logarithmic domination estimate with a fixed real multiple
of the logarithmic term.  This is the form needed after inserting the
ramification index into the valuation of integer denominators. -/
theorem tendsto_nat_succ_mul_const_sub_const_mul_logb_atTop
    {c C : ℝ} (hc : 0 < c) :
    Tendsto
      (fun n : ℕ =>
        ((n + 1 : ℕ) : ℝ) * c -
          C * Real.logb (p : ℝ) ((n + 1 : ℕ) : ℝ))
      atTop atTop := by
  have hhalf : 0 < c / 2 := by positivity
  have htend :
      Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
  have hsmall :
      (fun n : ℕ => C * Real.logb (p : ℝ) ((n + 1 : ℕ) : ℝ)) =o[atTop]
        (fun n : ℕ => ((n + 1 : ℕ) : ℝ)) := by
    have hlog :
        (fun n : ℕ => Real.logb (p : ℝ) ((n + 1 : ℕ) : ℝ)) =o[atTop]
          (fun n : ℕ => ((n + 1 : ℕ) : ℝ)) := by
      simpa [Function.comp_def] using
        (Real.isLittleO_logb_id_atTop (b := (p : ℝ))).comp_tendsto
          htend
    simpa using hlog.const_mul_left C
  have hbound :
      ∀ᶠ n : ℕ in atTop,
        ‖C * Real.logb (p : ℝ) ((n + 1 : ℕ) : ℝ)‖ ≤
          (c / 2) * ‖((n + 1 : ℕ) : ℝ)‖ :=
    hsmall.def hhalf
  have hle :
      (fun n : ℕ => (c / 2) * ((n + 1 : ℕ) : ℝ)) ≤ᶠ[atTop]
        (fun n : ℕ =>
          ((n + 1 : ℕ) : ℝ) * c -
            C * Real.logb (p : ℝ) ((n + 1 : ℕ) : ℝ)) := by
    filter_upwards [hbound] with n hn
    have hnnonneg : 0 ≤ ((n + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
    have hlog_le :
        C * Real.logb (p : ℝ) ((n + 1 : ℕ) : ℝ) ≤
          (c / 2) * ((n + 1 : ℕ) : ℝ) := by
      calc
        C * Real.logb (p : ℝ) ((n + 1 : ℕ) : ℝ) ≤
            ‖C * Real.logb (p : ℝ) ((n + 1 : ℕ) : ℝ)‖ :=
          le_abs_self _
        _ ≤ (c / 2) * ‖((n + 1 : ℕ) : ℝ)‖ := hn
        _ = (c / 2) * ((n + 1 : ℕ) : ℝ) := by
          rw [Real.norm_eq_abs, abs_of_nonneg hnnonneg]
    calc
      (c / 2) * ((n + 1 : ℕ) : ℝ) =
          ((n + 1 : ℕ) : ℝ) * c -
            (c / 2) * ((n + 1 : ℕ) : ℝ) := by
        ring
      _ ≤ ((n + 1 : ℕ) : ℝ) * c -
          C * Real.logb (p : ℝ) ((n + 1 : ℕ) : ℝ) :=
        sub_le_sub_left hlog_le (((n + 1 : ℕ) : ℝ) * c)
  have hlin :
      Tendsto (fun n : ℕ => (c / 2) * ((n + 1 : ℕ) : ℝ)) atTop atTop :=
    Tendsto.const_mul_atTop hhalf htend
  exact tendsto_atTop_mono' atTop hle hlin

/-- Exponential-series estimate for the field-unit logarithm:
for every slope `c > 1`, the linear term `n * c` dominates the factorial
denominator contribution `v_p(n!)`.  The proof uses mathlib's Legendre-bound
`padicValNat_factorial_le`; no factorial valuation formula is reproved here. -/
theorem tendsto_nat_mul_const_sub_padicValNat_factorial_atTop
    [Fact p.Prime] {c : ℝ} (hc : 1 < c) :
    Tendsto
      (fun n : ℕ => (n : ℝ) * c - (padicValNat p n.factorial : ℝ))
      atTop atTop := by
  have hpos : 0 < c - 1 := sub_pos.mpr hc
  have hsource :
      Tendsto (fun n : ℕ => (n : ℝ) * (c - 1)) atTop atTop := by
    simpa [mul_comm] using
      Tendsto.const_mul_atTop hpos tendsto_natCast_atTop_atTop
  have hle :
      (fun n : ℕ => (n : ℝ) * (c - 1)) ≤ᶠ[atTop]
        (fun n : ℕ =>
          (n : ℝ) * c - (padicValNat p n.factorial : ℝ)) := 
    Eventually.of_forall fun n => by
      have hdenNat : padicValNat p n.factorial ≤ n :=
        padicValNat_factorial_le (p := p) n
      have hden : (padicValNat p n.factorial : ℝ) ≤ (n : ℝ) :=
        Nat.cast_le.mpr hdenNat
      nlinarith
  exact tendsto_atTop_mono' atTop hle hsource

/-- Legendre's factorial-valuation formula, Legendre's formula in digit form:
if `n = a_0 + a_1 p + ... + a_r p^r`, then multiplying the displayed digit formula by `p - 1` gives
`(p - 1) v_p(n!) = (a_0 p^0 + ... + a_r p^r) - (a_0 + ... + a_r)`. -/
theorem padicValNat_factorial_digits
    [Fact p.Prime] (n : ℕ) :
    (p - 1) * padicValNat p n.factorial =
      Nat.ofDigits p (p.digits n) - (p.digits n).sum := by
  simpa [Nat.ofDigits_digits] using
    (sub_one_mul_padicValNat_factorial (p := p) n)

/-- A nonzero natural number has positive sum of base-`p` digits. -/
theorem digits_sum_pos_of_ne_zero (hn : n ≠ 0) :
    0 < (p.digits n).sum := by
  by_contra hnot
  have hsum0 : (p.digits n).sum = 0 :=
    by omega
  have hall : ∀ a ∈ p.digits n, a = 0 :=
    List.sum_eq_zero_iff.mp hsum0
  have hmapZero :
      (List.mapIdx (fun i a => a * p ^ i) (p.digits n)).sum = 0 := by
    apply List.sum_eq_zero
    intro b hb
    rw [List.mem_mapIdx] at hb
    rcases hb with ⟨i, hi, rfl⟩
    have hdigit : (p.digits n)[i] = 0 :=
      hall _ (List.getElem_mem hi)
    simp [hdigit]
  have hof : Nat.ofDigits p (p.digits n) = 0 := by
    simpa [Nat.ofDigits_eq_sum_mapIdx] using hmapZero
  have hn0 : n = 0 := by
    simpa [Nat.ofDigits_digits] using hof
  omega

/-- Legendre's formula gives the sharp bound
`(p - 1) * v_p(n!) <= n - 1` for nonzero `n`. -/
theorem sub_one_mul_padicValNat_factorial_le_sub_one
    [Fact p.Prime] (hn : n ≠ 0) :
    (p - 1) * padicValNat p n.factorial ≤ n - 1 := by
  rw [padicValNat_factorial_digits, Nat.ofDigits_digits]
  have hsumpos : 1 ≤ (p.digits n).sum :=
    Nat.succ_le_of_lt (digits_sum_pos_of_ne_zero (p := p) hn)
  omega

/-- Factorial-denominator analogue of the factorial quotient estimate:
`v_p(n!) / (n-1) <= 1/(p-1)`. -/
theorem padicValNat_factorial_div_sub_one_le_inv_sub_one
    [Fact p.Prime] (hn : 1 < n) :
    (padicValNat p n.factorial : ℚ) / ((n : ℚ) - 1) ≤
      1 / ((p : ℚ) - 1) := by
  have hpNat : Nat.Prime p := Fact.out
  have hp : (1 : ℚ) < p := by
    exact_mod_cast hpNat.one_lt
  have hpden : 0 < (p : ℚ) - 1 := by
    linarith
  have hnden : 0 < (n : ℚ) - 1 := by
    simp_all
  have hNat :
      (p - 1) * padicValNat p n.factorial ≤ n - 1 :=
    sub_one_mul_padicValNat_factorial_le_sub_one
      (p := p) (n := n) (by omega)
  have hmul :
      ((p : ℚ) - 1) * (padicValNat p n.factorial : ℚ) ≤
        (n : ℚ) - 1 := by
    have hcast :
        (((p - 1) * padicValNat p n.factorial : ℕ) : ℚ) ≤
          ((n - 1 : ℕ) : ℚ) := by
      exact_mod_cast hNat
    have hpone : 1 ≤ p := hpNat.one_lt.le
    have hnone : 1 ≤ n := by omega
    simp_all
  field_simp [hnden.ne', hpden.ne']
  nlinarith

/-- Real factorial-denominator bound used for the sharp convergence radius of
the exponential series. -/
theorem padicValNat_factorial_le_sub_one_div_sub_one_real
    [Fact p.Prime] (hn : n ≠ 0) :
    (padicValNat p n.factorial : ℝ) ≤
      ((n : ℝ) - 1) / ((p : ℝ) - 1) := by
  have hpNat : Nat.Prime p := Fact.out
  have hp : (1 : ℝ) < p := by
    exact_mod_cast hpNat.one_lt
  have hpden : 0 < (p : ℝ) - 1 := by
    linarith
  have hNat :
      (p - 1) * padicValNat p n.factorial ≤ n - 1 :=
    sub_one_mul_padicValNat_factorial_le_sub_one
      (p := p) (n := n) hn
  have hmul :
      ((p : ℝ) - 1) * (padicValNat p n.factorial : ℝ) ≤
        (n : ℝ) - 1 := by
    have hcast :
        (((p - 1) * padicValNat p n.factorial : ℕ) : ℝ) ≤
          ((n - 1 : ℕ) : ℝ) := by
      exact_mod_cast hNat
    have hpone : 1 ≤ p := hpNat.one_lt.le
    have hnone : 1 ≤ n := by omega
    simp_all
  exact (le_div_iff₀ hpden).2 (by simpa [mul_comm] using hmul)

/-- Sharp asymptotic estimate for the exponential series denominator:
any real slope strictly above `C/(p-1)` dominates
`C * v_p(n!)`. -/
theorem tendsto_nat_mul_const_sub_const_mul_padicValNat_factorial_atTop
    [Fact p.Prime] {c C : ℝ} (hC : 0 ≤ C)
    (hc : C / ((p : ℝ) - 1) < c) :
    Tendsto
      (fun n : ℕ =>
        (n : ℝ) * c - C * (padicValNat p n.factorial : ℝ))
      atTop atTop := by
  have hpNat : Nat.Prime p := Fact.out
  have hp : (1 : ℝ) < p := by
    exact_mod_cast hpNat.one_lt
  have hpden : 0 < (p : ℝ) - 1 := by
    linarith
  have hdelta : 0 < c - C / ((p : ℝ) - 1) := sub_pos.mpr hc
  have hsource :
      Tendsto
        (fun n : ℕ => (n : ℝ) * (c - C / ((p : ℝ) - 1)))
        atTop atTop := by
    simpa [mul_comm] using
      Tendsto.const_mul_atTop hdelta tendsto_natCast_atTop_atTop
  have hle :
      (fun n : ℕ => (n : ℝ) * (c - C / ((p : ℝ) - 1))) ≤ᶠ[atTop]
        (fun n : ℕ =>
          (n : ℝ) * c - C * (padicValNat p n.factorial : ℝ)) := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hn0 : n ≠ 0 := by omega
    have hfac :=
      padicValNat_factorial_le_sub_one_div_sub_one_real
        (p := p) (n := n) hn0
    have hCfac :
        C * (padicValNat p n.factorial : ℝ) ≤
          C * (((n : ℝ) - 1) / ((p : ℝ) - 1)) :=
      mul_le_mul_of_nonneg_left hfac hC
    have hCp_nonneg : 0 ≤ C / ((p : ℝ) - 1) :=
      div_nonneg hC hpden.le
    have hden_bound :
        C * (((n : ℝ) - 1) / ((p : ℝ) - 1)) ≤
          (n : ℝ) * (C / ((p : ℝ) - 1)) := by
      calc
        C * (((n : ℝ) - 1) / ((p : ℝ) - 1)) =
            ((n : ℝ) - 1) * (C / ((p : ℝ) - 1)) := by
          ring
        _ ≤ (n : ℝ) * (C / ((p : ℝ) - 1)) :=
          mul_le_mul_of_nonneg_right (by linarith) hCp_nonneg
    calc
      (n : ℝ) * (c - C / ((p : ℝ) - 1)) =
          (n : ℝ) * c - (n : ℝ) * (C / ((p : ℝ) - 1)) := by
        ring
      _ ≤ (n : ℝ) * c - C * (padicValNat p n.factorial : ℝ) := by
        linarith [hCfac.trans hden_bound]
  exact tendsto_atTop_mono' atTop hle hsource

/-- Ramified sharp-threshold version of
`exp_higher_term_integer_valuation_gt`: if the factorial denominator
contributes `e * v_p(n!)`, then every higher exponential term has larger
integer valuation than the linear term above `e/(p-1)`. -/
theorem exp_higher_term_integer_valuation_gt_scaled
    [Fact p.Prime] {n e : ℕ} (hn : 2 ≤ n) {m : ℤ}
    (hm : (e : ℚ) / ((p : ℚ) - 1) < (m : ℚ)) :
    m < (n : ℤ) * m - (e : ℤ) * (padicValNat p n.factorial : ℤ) := by
  have hquot :=
    padicValNat_factorial_div_sub_one_le_inv_sub_one
      (p := p) (n := n) (by omega)
  have hnden : 0 < (n : ℚ) - 1 := by
    have hnq : (1 : ℚ) < n := by
      exact_mod_cast (by omega : 1 < n)
    linarith
  have he_nonneg : 0 ≤ (e : ℚ) := by
    positivity
  have hscaled_div :
      ((e : ℚ) * (padicValNat p n.factorial : ℚ)) /
          ((n : ℚ) - 1) ≤
        (e : ℚ) / ((p : ℚ) - 1) := by
    calc
      ((e : ℚ) * (padicValNat p n.factorial : ℚ)) /
          ((n : ℚ) - 1) =
          (e : ℚ) *
            ((padicValNat p n.factorial : ℚ) / ((n : ℚ) - 1)) := by
        ring
      _ ≤ (e : ℚ) * (1 / ((p : ℚ) - 1)) :=
        mul_le_mul_of_nonneg_left hquot he_nonneg
      _ = (e : ℚ) / ((p : ℚ) - 1) := by
        ring
  have hstrict :
      ((e : ℚ) * (padicValNat p n.factorial : ℚ)) /
          ((n : ℚ) - 1) < (m : ℚ) :=
    lt_of_le_of_lt hscaled_div hm
  have hdenlt :
      (e : ℚ) * (padicValNat p n.factorial : ℚ) <
        ((n : ℚ) - 1) * (m : ℚ) := by
    calc
      (e : ℚ) * (padicValNat p n.factorial : ℚ) =
          (((e : ℚ) * (padicValNat p n.factorial : ℚ)) /
              ((n : ℚ) - 1)) *
            ((n : ℚ) - 1) := by
        field_simp [hnden.ne']
      _ < (m : ℚ) * ((n : ℚ) - 1) :=
        mul_lt_mul_of_pos_right hstrict hnden
      _ = ((n : ℚ) - 1) * (m : ℚ) := by
        ring
  have hgoal :
      (m : ℚ) <
        (n : ℚ) * (m : ℚ) -
          (e : ℚ) * (padicValNat p n.factorial : ℚ) := by
    nlinarith
  have hgoal' :
      (m : ℚ) <
        (((n : ℤ) * m -
          (e : ℤ) * (padicValNat p n.factorial : ℤ) : ℤ) : ℚ) := by
    simp_all
  exact_mod_cast hgoal'

/-- Arithmetic estimate at the deep exponential–logarithm threshold:
for `n > 1`, the quotient `v_p(n)/(n-1)` is at most `1/(p-1)`.

This is the exact numerical inequality used later to show that, above the
threshold `1/(p-1)`, the linear term of the logarithm or exponential series
has strictly smaller valuation than every higher term. -/
theorem padicValNat_div_sub_one_le_inv_sub_one
    [Fact p.Prime] (hn : 1 < n) :
    (padicValNat p n : ℚ) / ((n : ℚ) - 1) ≤
      1 / ((p : ℚ) - 1) := by
  let a := padicValNat p n
  have hpNat : Nat.Prime p := Fact.out
  have hp : (1 : ℚ) < p := by
    exact_mod_cast hpNat.one_lt
  have hpden : 0 < (p : ℚ) - 1 := by
    linarith
  have hnden : 0 < (n : ℚ) - 1 := by
    simp_all
  have hpowNat : p ^ a ≤ n :=
    Nat.le_of_dvd (lt_trans Nat.zero_lt_one hn) pow_padicValNat_dvd
  have hpow : (p : ℚ) ^ a ≤ (n : ℚ) := by
    exact_mod_cast hpowNat
  have hbern :
      (a : ℚ) ≤ (((p : ℚ) ^ a - 1) / ((p : ℚ) - 1)) :=
    Nat.cast_le_pow_sub_div_sub (α := ℚ) (a := (p : ℚ)) hp a
  have hsub :
      ((p : ℚ) ^ a - 1) / ((p : ℚ) - 1) ≤
        ((n : ℚ) - 1) / ((p : ℚ) - 1) :=
    div_le_div_of_nonneg_right (sub_le_sub_right hpow 1) hpden.le
  have hbound :
      (a : ℚ) ≤ ((n : ℚ) - 1) / ((p : ℚ) - 1) :=
    hbern.trans hsub
  calc
    (padicValNat p n : ℚ) / ((n : ℚ) - 1) =
        (a : ℚ) / ((n : ℚ) - 1) := rfl
    _ ≤ (((n : ℚ) - 1) / ((p : ℚ) - 1)) /
        ((n : ℚ) - 1) :=
      div_le_div_of_nonneg_right hbound hnden.le
    _ = 1 / ((p : ℚ) - 1) := by
      field_simp [hnden.ne', hpden.ne']

/-- Ramified-denominator version of
`log_higher_term_integer_valuation_gt`: if the denominator contributes
`e * v_p(n)`, then the sharp comparison threshold is `e/(p-1)`. -/
theorem log_higher_term_integer_valuation_gt_scaled
    [Fact p.Prime] {n e : ℕ} (hn : 2 ≤ n) {m : ℤ}
    (hm : (e : ℚ) / ((p : ℚ) - 1) < (m : ℚ)) :
    m < (n : ℤ) * m - (e : ℤ) * (padicValNat p n : ℤ) := by
  have hquot :=
    padicValNat_div_sub_one_le_inv_sub_one
      (p := p) (n := n) (by omega)
  have hnden : 0 < (n : ℚ) - 1 := by
    have hnq : (1 : ℚ) < n := by
      exact_mod_cast (by omega : 1 < n)
    linarith
  have he_nonneg : 0 ≤ (e : ℚ) := by
    positivity
  have hscaled_div :
      ((e : ℚ) * (padicValNat p n : ℚ)) / ((n : ℚ) - 1) ≤
        (e : ℚ) / ((p : ℚ) - 1) := by
    calc
      ((e : ℚ) * (padicValNat p n : ℚ)) / ((n : ℚ) - 1) =
          (e : ℚ) * ((padicValNat p n : ℚ) / ((n : ℚ) - 1)) := by
        ring
      _ ≤ (e : ℚ) * (1 / ((p : ℚ) - 1)) :=
        mul_le_mul_of_nonneg_left hquot he_nonneg
      _ = (e : ℚ) / ((p : ℚ) - 1) := by
        ring
  have hstrict :
      ((e : ℚ) * (padicValNat p n : ℚ)) / ((n : ℚ) - 1) < (m : ℚ) :=
    lt_of_le_of_lt hscaled_div hm
  have hdenlt :
      (e : ℚ) * (padicValNat p n : ℚ) <
        ((n : ℚ) - 1) * (m : ℚ) := by
    calc
      (e : ℚ) * (padicValNat p n : ℚ) =
          (((e : ℚ) * (padicValNat p n : ℚ)) / ((n : ℚ) - 1)) *
            ((n : ℚ) - 1) := by
        field_simp [hnden.ne']
      _ < (m : ℚ) * ((n : ℚ) - 1) :=
        mul_lt_mul_of_pos_right hstrict hnden
      _ = ((n : ℚ) - 1) * (m : ℚ) := by
        ring
  have hgoal :
      (m : ℚ) <
        (n : ℚ) * (m : ℚ) -
          (e : ℚ) * (padicValNat p n : ℚ) := by
    nlinarith
  have hgoal' :
      (m : ℚ) <
        (((n : ℤ) * m -
          (e : ℤ) * (padicValNat p n : ℤ) : ℤ) : ℚ) := by
    simp_all
  exact_mod_cast hgoal'
