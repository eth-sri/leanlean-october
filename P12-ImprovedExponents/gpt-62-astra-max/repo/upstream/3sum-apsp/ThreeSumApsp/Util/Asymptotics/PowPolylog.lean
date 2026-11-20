/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import PaperStatements
public import ThreeSumApsp.Util.Asymptotics.Dominated
public import ThreeSumApsp.Util.Asymptotics.Powers
public import ThreeSumApsp.Util.Log

/-!
# Calculating with `O(n^a)` and `Õ(n^a)`

Closure properties of the two classes `IsBigOPow f a`, that is `f(n) = O(n^a)`, and
`IsPowPolylog f a`, that is `f(n) = O(n^a (log n)^{O(1)})`, which the paper writes `Õ(n^a)`.

A bound enters by `of_abs_le`, by `of_isBigO`, or from the model functions (`isBigOPow_rpow`,
`isBigOPow_natCast_pow`, `isBigOPow_const`, `isPowPolylog_rpow_mul_log_pow`, `isPowPolylog_log_pow`,
and for rounded powers `isBigOPow_ceil_rpow`, `isBigOPow_floor_rpow` and their inverses;
`IsBigOPow.natCeil` for rounding in general). Both classes are closed under sums, constant factors
and passing to a smaller function (`mono_left`). A product has the exponent `a + b` and a power the
exponent `a * k` (`pow`, `rpow`), to be brought to the wanted form by `mono`, which asks only for an
inequality between exponents. Substituting `n ↦ size n` multiplies nonnegative exponents
(`IsBigOPow.comp`, `IsPowPolylog.comp`), for `size n = O(n^μ)`, and then `log (size n) = Õ(1)`
(`IsBigOPow.isPowPolylog_log_natCast`). The classes are related by `IsBigOPow.isPowPolylog` and,
with a loss in the exponent, `IsPowPolylog.isBigOPow`; `eventually_abs_le` absorbs the constant as
well.
-/

public section

open Filter Asymptotics

namespace ThreeSumApsp

variable {f g : ℕ → ℝ} {a b : ℝ}

/-! ### `O(n^a)` -/

/-- `n ^ a = O(n^a)`. -/
theorem isBigOPow_rpow (a : ℝ) : IsBigOPow (fun n : ℕ => n ^ a) a :=
  isBigO_refl _ _

/-- `n ^ k = O(n^k)` for a natural number `k`. -/
theorem isBigOPow_natCast_pow (k : ℕ) : IsBigOPow (fun n : ℕ => n ^ k) k := by
  simpa only [Real.rpow_natCast] using isBigOPow_rpow k

/-- A constant is `O(n^0)`. -/
theorem isBigOPow_const (c : ℝ) : IsBigOPow (fun _ => c) 0 :=
  isBigO_of_abs_le |c| 0 fun n _ => by simp

namespace IsBigOPow

/-- If `g = O(n^a)` and `f = O(g)`, then `f = O(n^a)`. -/
theorem of_isBigO (hg : IsBigOPow g a) (hfg : f =O[atTop] g) : IsBigOPow f a :=
  hfg.trans hg

/-- If `|f n| ≤ |g n|` for all large `n` and `g = O(n^a)`, then `f = O(n^a)`. -/
theorem mono_left (hg : IsBigOPow g a) (h : ∀ᶠ n in atTop, |f n| ≤ |g n|) : IsBigOPow f a :=
  hg.of_isBigO (IsBigO.of_bound' h)

section
variable (hf : IsBigOPow f a)
include hf

/-- The exponent may be raised. -/
protected theorem mono (hab : a ≤ b) : IsBigOPow f b :=
  hf.trans (isBigO_rpow_rpow_of_le hab)

/-- `O(n^a) + O(n^a) = O(n^a)`. -/
protected theorem add (hg : IsBigOPow g a) :
    IsBigOPow (fun n => f n + g n) a :=
  IsBigO.add hf hg

/-- `O(n^a) · O(n^b) = O(n^(a+b))`. -/
protected theorem mul (hg : IsBigOPow g b) :
    IsBigOPow (fun n => f n * g n) (a + b) :=
  (IsBigO.mul hf hg).congr' EventuallyEq.rfl (rpow_mul_rpow_eventuallyEq a b)

/-- `O(n^a) ^ r = O(n^(a r))` for a real exponent `r ≥ 0`. -/
protected theorem rpow {r : ℝ} (hr : 0 ≤ r) :
    IsBigOPow (fun n => f n ^ r) (a * r) := by
  have h := IsBigO.rpow hr (Eventually.of_forall fun n : ℕ => by positivity) hf
  exact h.congr_right fun n => (Real.rpow_mul n.cast_nonneg a r).symm

/-- The constant is absorbed: if `f = O(n^a)` and `a < b`, then `|f n| ≤ n ^ b` for all large `n`.
-/
theorem eventually_abs_le (hab : a < b) :
    ∀ᶠ n : ℕ in atTop, |f n| ≤ n ^ b := by
  obtain ⟨C, hC⟩ := IsBigO.bound hf
  filter_upwards [hC, eventually_mul_rpow_le C hab] with n hn hCn
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg n.cast_nonneg a)] at hn
  grind

/-- `O(n^a) ⊆ Õ(n^a)`. -/
theorem isPowPolylog : IsPowPolylog f a :=
  ⟨0, by aesop⟩

end

end IsBigOPow

/-! ### `Õ(n^a)` -/

/-- `n ^ a * (log n) ^ e = Õ(n^a)`. -/
theorem isPowPolylog_rpow_mul_log_pow (a : ℝ) (e : ℕ) :
    IsPowPolylog (fun n : ℕ => n ^ a * Real.log n ^ e) a :=
  ⟨e, isBigO_refl _ _⟩

/-- `(log n) ^ e = Õ(1)`. -/
theorem isPowPolylog_log_pow (e : ℕ) : IsPowPolylog (fun n : ℕ => Real.log n ^ e) 0 :=
  ⟨e, by aesop⟩

/-- `log n = Õ(1)`. -/
theorem isPowPolylog_log : IsPowPolylog (fun n : ℕ => Real.log n) 0 := by
  simpa only [pow_one] using isPowPolylog_log_pow 1

/-- A constant is `Õ(1)`. -/
theorem isPowPolylog_const (c : ℝ) : IsPowPolylog (fun _ => c) 0 :=
  (isBigOPow_const c).isPowPolylog

namespace IsPowPolylog

/-- A bound `|f n| ≤ C * (n ^ a * (log n) ^ e)` from some `n₀` on gives `f = Õ(n^a)`. -/
theorem of_abs_le (C : ℝ) (e n₀ : ℕ)
    (h : ∀ n, n₀ ≤ n → |f n| ≤ C * (n ^ a * Real.log n ^ e)) : IsPowPolylog f a :=
  ⟨e, isBigO_of_abs_le C n₀ h⟩

section
variable (hg : IsPowPolylog g a)
include hg

/-- If `g = Õ(n^a)` and `f = O(g)`, then `f = Õ(n^a)`. -/
theorem of_isBigO (hfg : f =O[atTop] g) : IsPowPolylog f a := by
  obtain ⟨e, hg⟩ := hg
  exact ⟨e, hfg.trans hg⟩

/-- If `|f n| ≤ |g n|` for all large `n` and `g = Õ(n^a)`, then `f = Õ(n^a)`. -/
theorem mono_left (h : ∀ᶠ n in atTop, |f n| ≤ |g n|) : IsPowPolylog f a :=
  hg.of_isBigO (IsBigO.of_bound' h)

/-- If `0 ≤ f n ≤ g n` for all large `n` and `g = Õ(n^a)`, then `f = Õ(n^a)`. -/
theorem mono_left_of_nonneg (h0 : ∀ᶠ n in atTop, 0 ≤ f n)
    (h : ∀ᶠ n in atTop, f n ≤ g n) : IsPowPolylog f a :=
  hg.mono_left ((h0.and h).mono fun _ hn => abs_le_abs_of_nonneg hn.1 hn.2)

end

section
variable (hf : IsPowPolylog f a)
include hf

/-- The exponent may be raised. -/
protected theorem mono (hab : a ≤ b) : IsPowPolylog f b := by
  obtain ⟨e, hf⟩ := hf
  exact ⟨e, hf.trans (isBigO_rpow_mul_log_pow_of_le hab le_rfl)⟩

/-- `Õ(n^a) + Õ(n^a) = Õ(n^a)`. -/
protected theorem add (hg : IsPowPolylog g a) :
    IsPowPolylog (fun n => f n + g n) a := by
  obtain ⟨e₁, hf⟩ := hf
  obtain ⟨e₂, hg⟩ := hg
  exact ⟨max e₁ e₂, (hf.trans (isBigO_rpow_mul_log_pow_of_le le_rfl (le_max_left _ _))).add
    (hg.trans (isBigO_rpow_mul_log_pow_of_le le_rfl (le_max_right _ _)))⟩

/-- Constant factors are absorbed. -/
theorem const_mul (c : ℝ) : IsPowPolylog (fun n => c * f n) a := by
  obtain ⟨e, hf⟩ := hf
  exact ⟨e, hf.const_mul_left c⟩

/-- `Õ(n^a) · Õ(n^b) = Õ(n^(a+b))`. -/
protected theorem mul (hg : IsPowPolylog g b) :
    IsPowPolylog (fun n => f n * g n) (a + b) := by
  obtain ⟨e₁, hf⟩ := hf
  obtain ⟨e₂, hg⟩ := hg
  refine ⟨e₁ + e₂, (hf.mul hg).congr' EventuallyEq.rfl ?_⟩
  filter_upwards [rpow_mul_rpow_eventuallyEq a b] with n hn
  rw [← hn, pow_add, mul_mul_mul_comm]

/-- If `f = Õ(n^a)` then `|f| = Õ(n^a)`. -/
protected theorem abs : IsPowPolylog (fun n => |f n|) a := by
  obtain ⟨e, hf⟩ := hf
  exact ⟨e, hf.norm_left⟩

/-- If `f = Õ(n^a)` and `g n = f n` for all large `n`, then `g = Õ(n^a)`. -/
protected theorem congr (h : f =ᶠ[atTop] g) : IsPowPolylog g a := by
  obtain ⟨e, hf⟩ := hf
  exact ⟨e, hf.congr' h EventuallyEq.rfl⟩

/-- Logarithms are absorbed: `Õ(n^a) ⊆ O(n^b)` for `a < b`. -/
theorem isBigOPow (hab : a < b) : IsBigOPow f b := by
  obtain ⟨e, hf⟩ := hf
  exact hf.trans (isBigO_rpow_mul_log_pow_rpow hab e)

end

end IsPowPolylog

/-- Substituting a size: if `G(s) = O(s^a)` and `size n = O(n^μ)` with `a, μ ≥ 0`, then
`G(size n) = O(n^(a μ))`. The sizes need not tend to infinity. -/
protected theorem IsBigOPow.comp {G} {size : ℕ → ℕ} {μ} (hG : IsBigOPow G a)
    (hsize : IsBigOPow (fun n => (size n)) μ) (ha : 0 ≤ a) (hμ : 0 ≤ μ) :
    IsBigOPow (fun n => G (size n)) (a * μ) := by
  have hmodel :=
    ((hsize.rpow ha).mono (mul_comm μ a).le).add ((isBigOPow_const 1).mono (mul_nonneg ha hμ))
  exact hmodel.of_isBigO
    (isBigO_comp_add_one hG (fun s => by positivity) size)

/-- `log (c * n ^ κ) = Õ(1)`. -/
theorem isPowPolylog_log_mul_rpow (c κ : ℝ) :
    IsPowPolylog (fun n : ℕ => Real.log (c * n ^ κ)) 0 := by
  obtain rfl | hc := eq_or_ne c 0
  · simpa only [zero_mul, Real.log_zero] using isPowPolylog_const 0
  · refine ((isPowPolylog_const (Real.log c)).add (isPowPolylog_log.const_mul κ)).congr ?_
    filter_upwards [eventually_gt_atTop 0] with n hn
    have hpos : (0 : ℝ) < n := Nat.cast_pos.2 hn
    rw [Real.log_mul hc (Real.rpow_pos_of_pos hpos κ).ne', Real.log_rpow hpos]

end ThreeSumApsp
