/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import Mathlib.Tactic
public import ThreeSumApsp.Util.RamArith
public import ThreeSumApsp.Util.Asymptotics.PowPolylog
public import ThreeSumApsp.Util.Asymptotics.Scale

/-!
# Bounds of the form "a polylogarithm times a power of √n"

`SoftOSqrtPow F i` says that `F n ≤ K (⌊log₂ n⌋ + 1)^e (⌊√n⌋ + 1)^i` for all `n ≥ 2`, for some
constants `K` and `e`.  In the notation of the paper this is `F(n) = Õ((√n)^i) = Õ(n^{i/2})`
(`SoftOSqrtPow.isPowPolylog`): the index 0 stands for a polylogarithm, 2 for `Õ(n)`, 3 for
`Õ(n^{3/2})`.

It is the calculus `Scale.SoftO` on the scale `sqrtScale`, which counts the powers of `⌊√n⌋ + 1` and
not those of `⌊log₂ n⌋ + 1`.  The logarithm of a function with such a bound is polylogarithmic
(`SoftOSqrtPow.natLog_comp`).  The tactic `growth_sqrt` proves a bound for an explicit expression
in `n`, `⌊√n⌋` and logarithms by following the expression, and no constant is ever written out.
-/

@[expose] public section

namespace ThreeSumApsp

/-- `⌊log₂ n⌋ + 1 ≤ 4 ln n` for `n ≥ 2`. -/
theorem natLog_succ_le {n} (hn : 2 ≤ n) : ((Nat.log 2 n + 1 : ℕ) : ℝ) ≤ 4 * Real.log n := by
  have hhalf := Real.one_half_lt_log_two.le
  have  : Real.log 2 ≤ Real.log n := Real.log_le_log (by norm_num) (mod_cast hn)
  have  :=
    calc Nat.log 2 n * Real.log 2 = Real.log ((2 ^ Nat.log 2 n : ℕ) : ℝ) := by
          simp_all
      _ ≤ Real.log n := Real.log_le_log (by positivity)
          (mod_cast Nat.pow_log_le_self 2 (by omega))
  have  := mul_le_mul_of_nonneg_left hhalf (Nat.cast_nonneg (α := ℝ) (Nat.log 2 n))
  grind

/-- `⌊√n⌋ + 1 ≤ 2 √n` for `n ≥ 1`. -/
theorem natSqrt_succ_le {n} (hn : 1 ≤ n) : ((Nat.sqrt n + 1 : ℕ) : ℝ) ≤ 2 * √(n : ℝ) := by

  push_cast
  linarith [Real.nat_sqrt_le_real_sqrt (a := n), (Real.one_le_sqrt.mpr (mod_cast hn) : 1 ≤ √(n : ℝ))]

/-- The scale of the bounds `Õ(n^{i/2})`, for `n ≥ 2`: powers of `⌊√n⌋ + 1` are counted, powers of
`⌊log₂ n⌋ + 1` are not. -/
noncomputable def sqrtScale : Scale ℕ (Fin 1) where
  dom n := 2 ≤ n
  hidden n := (Nat.log 2 n + 1 : ℕ)
  base _ n := (Nat.sqrt n + 1 : ℕ)
  one_le_hidden _ _ := Nat.one_le_cast.2 (Nat.le_add_left 1 _)
  one_le_base _ _ _ := Nat.one_le_cast.2 (Nat.le_add_left 1 _)

/-- `F(n) ≤ K (⌊log₂ n⌋ + 1)^e (⌊√n⌋ + 1)^i` for all `n ≥ 2`, for some `K` and `e`. -/
abbrev SoftOSqrtPow F i := sqrtScale.SoftO F ![i]

namespace SoftOSqrtPow

variable {F : ℕ → ℕ} {i : ℕ}

/-- The function `⌊log₂ n⌋` is a polylogarithm. -/
theorem natLog : SoftOSqrtPow (fun n => Nat.log 2 n) 0 :=
  (Scale.SoftO.of_le_hidden fun _ _ => Nat.cast_le.2 (Nat.le_succ _)).mono (by decide)

/-- The function `⌊√n⌋` has the first power of `√n`. -/
theorem natSqrt : SoftOSqrtPow (fun n => Nat.sqrt n) 1 :=
  (Scale.SoftO.of_le_base 0 fun _ _ => Nat.cast_le.2 (Nat.le_succ _)).mono (by decide)

/-- `n` itself is at most `(⌊√n⌋ + 1)²`. -/
def self :=
  (by growth [natSqrt] : SoftOSqrtPow (fun n => (Nat.sqrt n + 1) ^ 2) 2).of_le fun n _ =>
    (Nat.lt_succ_sqrt n).le.trans (sq _).ge

/-- The logarithm of a function with such a bound is a polylogarithm. -/
theorem natLog_comp {e} (hF : sqrtScale.SoftO F e) :
    SoftOSqrtPow (fun n => Nat.log 2 (F n)) 0 := by
  refine (Scale.SoftO.log2 (fun _ n _ => ?_) hF).mono (by decide)

  simp only [sqrtScale, Real.rpow_natCast]
  exact_mod_cast by
    grind [Nat.lt_pow_succ_log_self, Nat.sqrt_le_self]

/-- In the notation of the paper: `F(n) = Õ(n^{i/2})`. -/
theorem isPowPolylog (hF : SoftOSqrtPow F i) {a : ℝ} (ha : a = i / 2) :
    IsPowPolylog (fun n => (F n : ℝ)) a := by
  obtain ⟨K, e, hK0, hK⟩ := hF.exists_le
  refine .of_abs_le (K * 4 ^ e * 2 ^ i) e 2 fun n hn => ?_
  have  : √(n : ℝ) ^ i = (n : ℝ) ^ a := by
    rw [ha, Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg n)]
    congr 1
    ring
  rw [abs_of_nonneg (Nat.cast_nonneg _)]
  calc (F n : ℝ)
      ≤ K * (((Nat.log 2 n + 1 : ℕ) : ℝ) ^ e * ((Nat.sqrt n + 1 : ℕ) : ℝ) ^ i) := by
        ram_arith [sqrtScale, Scale.mon]
    _ ≤ K * ((4 * Real.log n) ^ e * (2 * √(n : ℝ)) ^ i) := by
        gcongr
        exacts [natLog_succ_le hn, natSqrt_succ_le (by omega)]
    _ = K * 4 ^ e * 2 ^ i * ((n : ℝ) ^ a * Real.log n ^ e) := by
        ram_arith [mul_pow]

end SoftOSqrtPow

/-- Proves `SoftOSqrtPow F i` as `growth` does.  The given facts bound the quantities that occur,
other than `n`, `⌊√n⌋` and binary logarithms. -/
macro "growth_sqrt" "[" hs:term,* "]" : tactic =>
  `(tactic| growth [SoftOSqrtPow.self, SoftOSqrtPow.natLog, SoftOSqrtPow.natSqrt,
    SoftOSqrtPow.natLog_comp, $hs,*])

end ThreeSumApsp
