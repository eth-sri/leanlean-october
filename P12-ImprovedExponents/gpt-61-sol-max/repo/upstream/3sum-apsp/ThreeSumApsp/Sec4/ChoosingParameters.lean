/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import Mathlib.Tactic
public import PaperStatements
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Order.Ring.Abs
public import Mathlib.Algebra.Order.Ring.Int
public import Mathlib.Data.Int.Cast.Lemmas
public import Mathlib.Data.Nat.Cast.Order.Ring
public import Mathlib.Tactic.GCongr
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import ThreeSumApsp.Util.Choose
public import ThreeSumApsp.Util.Log
public import Mathlib.Analysis.SpecialFunctions.BinaryEntropy

/-!
# 4.4 Choosing the parameters: the entropy function, the exponents `γ` and `q`, equation (11)

Section 4.4 chooses the parameters `L` and `t` of Theorem 30. This file has the facts that its
proofs use about `D = 4^m` and about the notions with which Corollary 31 is stated ("Other choices
of the parameters"). The notation of the paper: `entropy` is `H`, `rhoC c` is `ρ_c = 9/(c-1)`,
`gammaOf c θ` is `γ = θ ln(1/ρ_c)/ln 4`, `qOf θ` is `q = (H(θ) + θ ln 9)/ln 4`, `lnΛ c γ` is the
denominator `ln Λ` of (11), `Rc c γ` is `R_c(γ) = ln 4/ln Λ`, and `D m` is `D = 4^m`.

* The entropy function `H` is Mathlib's `Real.binEntropy` (`entropy_eq_binEntropy`); continuity,
  concavity and the derivative come from there.
* Powers and logarithms of `D = 4^m` (`cast_D_pos`, `one_le_cast_D`, `log_cast_D`,
  `cast_le_log_cast_D`, `cast_D_rpow`).
* The bound `binom(n, k) ≥ e^{n H(k/n)}/(n+1)` (`exp_entropy_div_le_choose`): it is the standard
  bound `binom(n, k) ≥ 1/(n+1) · n^n/(k^k (n-k)^{n-k})`, as `e^{n H(k/n)} = n^n/(k^k (n-k)^{n-k})`.
* One section for each of `ρ_c`, `γ`, `q`, and `ln Λ` with `R_c(γ)`: signs, monotonicity and
  continuity, and the three facts that tie them to the costs: `ρ_c^{θm} = D^{-γ}`
  (`rhoC_rpow_eq_D_rpow`), `e^{m(H(θ) + θ ln 9)} = D^q` (`exp_entropy_eq_D_rpow_qOf`), and
  `Λ < 4^{1/ε}` if and only if `ε < R_c(γ)` (`eq_11_iff`).
-/

public section



namespace ThreeSumApsp

/-! ### The entropy function: the link with Mathlib's `Real.binEntropy` -/

/-- The entropy function of Section 4.4 is Mathlib's binary entropy function. -/
theorem entropy_eq_binEntropy : entropy = Real.binEntropy := by
  grind [Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub, entropy, Real.negMulLog]

/-- `H(x) ≥ 0` for `0 ≤ x ≤ 1`. -/
theorem entropy_nonneg {x} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) : 0 ≤ entropy x := by
  rw [entropy_eq_binEntropy]
  exact Real.binEntropy_nonneg hx0 hx1

/-! ### Powers and logarithms of `D = 4^m` -/

/-- `ln 4 > 0`. -/
theorem log_four_pos : 0 < Real.log 4 := Real.log_pos (by norm_num)

/-- `D = 4^m` as a real number. -/
theorem cast_D_eq m : (D m : ℝ) = (4 : ℝ) ^ m := by
  simp [D]

/-- `D > 0`. -/
theorem cast_D_pos m : (0 : ℝ) < (D m : ℝ) := by
  rw [cast_D_eq]
  positivity

/-- `D ≥ 1`. -/
theorem one_le_cast_D m : (1 : ℝ) ≤ (D m : ℝ) := by
  grind [cast_D_eq, one_le_pow₀]

/-- `ln D = m ln 4`. -/
theorem log_cast_D m : Real.log (D m) = (m : ℝ) * Real.log 4 := by
  rw [cast_D_eq, Real.log_pow]

/-- `m ≤ ln D`. -/
theorem cast_le_log_cast_D (m : ℕ) : (m : ℝ) ≤ Real.log (D m) := by
  grind [log_cast_D, le_mul_of_one_le_right, Real.one_le_log_four]

/-- `D^x = e^{x m ln 4}`. -/
theorem cast_D_rpow m x :
    (D m : ℝ) ^ x = Real.exp (x * (m * Real.log 4)) := by
  grind [Real.rpow_def_of_pos, cast_D_pos, log_cast_D]

/-! ### The lower bound on binomial coefficients by the entropy function -/

/-! ### The decay rate `ρ_c` -/

/-- `ρ_c = 9/(c-1) < 1` for `c > 10`. -/
theorem rhoC_lt_one {c} (hc : 10 < c) : rhoC c < 1 :=
  (div_lt_one (by linarith)).2 (by linarith)

/-! ### The exponent `γ` -/

/-! ### The exponent `q` -/

/-- The exponent `q` is not negative for `0 < θ < 0.9`. -/
theorem qOf_nonneg θ (hθ0 : 0 < θ) (hθ1 : θ < 0.9) : 0 ≤ qOf θ :=
  div_nonneg (add_nonneg (entropy_nonneg hθ0.le (by linarith))
    (mul_nonneg hθ0.le (Real.log_nonneg (by norm_num)))) log_four_pos.le

/-- `e^{m(H(θ) + θ ln 9)} = D^q` with `D = 4^m` and `q = (H(θ) + θ ln 9)/ln 4`. -/
theorem exp_entropy_eq_D_rpow_qOf θ (m : ℕ) :
    Real.exp (m * (entropy θ + θ * Real.log 9)) = (D m : ℝ) ^ qOf θ := by
  rw [cast_D_rpow]
  congr 1
  unfold qOf
  field_simp

/-! ### The denominator `ln Λ` of equation (11), and `R_c(γ)` -/

end ThreeSumApsp
