/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import PaperStatements
public import ThreeSumApsp.Util.Basic
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

open Finset

namespace ThreeSumApsp

/-! ### The entropy function: the link with Mathlib's `Real.binEntropy` -/

/-- The entropy function of Section 4.4 is Mathlib's binary entropy function. -/
theorem entropy_eq_binEntropy : entropy = Real.binEntropy := by
  funext x
  rw [Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub, entropy, Real.negMulLog, Real.negMulLog]
  ring

/-- The entropy function is continuous on the whole real line. -/
theorem entropy_continuous : Continuous entropy := by
  rw [entropy_eq_binEntropy]
  exact Real.binEntropy_continuous

/-- `H(x) ≥ 0` for `0 ≤ x ≤ 1`. -/
theorem entropy_nonneg {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) : 0 ≤ entropy x := by
  rw [entropy_eq_binEntropy]
  exact Real.binEntropy_nonneg hx0 hx1

/-- The derivative of the entropy function, `H'(x) = ln((1-x)/x)` for `0 < x < 1`. -/
theorem hasDerivAt_entropy (x : ℝ) (hx0 : 0 < x) (hx1 : x < 1) :
    HasDerivAt entropy (Real.log ((1 - x) / x)) x := by
  rw [entropy_eq_binEntropy, Real.log_div (by linarith) hx0.ne']
  exact Real.hasDerivAt_binEntropy hx0.ne' hx1.ne

/-! ### Powers and logarithms of `D = 4^m` -/

/-- `ln 4 > 0`. -/
theorem log_four_pos : 0 < Real.log 4 := Real.log_pos (by norm_num)

/-- `D = 4^m` as a real number. -/
theorem cast_D_eq (m : ℕ) : (D m : ℝ) = (4 : ℝ) ^ m := by
  simp [D]

/-- `D > 0`. -/
theorem cast_D_pos (m : ℕ) : (0 : ℝ) < (D m : ℝ) := by
  rw [cast_D_eq]
  positivity

/-- `D ≥ 1`. -/
theorem one_le_cast_D (m : ℕ) : (1 : ℝ) ≤ (D m : ℝ) := by
  rw [cast_D_eq]
  exact one_le_pow₀ (by norm_num)

/-- `ln D = m ln 4`. -/
theorem log_cast_D (m : ℕ) : Real.log (D m : ℝ) = (m : ℝ) * Real.log 4 := by
  rw [cast_D_eq, Real.log_pow]

/-- `m ≤ ln D`. -/
theorem cast_le_log_cast_D (m : ℕ) : (m : ℝ) ≤ Real.log (D m : ℝ) := by
  rw [log_cast_D]
  exact le_mul_of_one_le_right (Nat.cast_nonneg m) Real.one_le_log_four

/-- `D^x = e^{x m ln 4}`. -/
theorem cast_D_rpow (m : ℕ) (x : ℝ) :
    (D m : ℝ) ^ x = Real.exp (x * ((m : ℝ) * Real.log 4)) := by
  rw [Real.rpow_def_of_pos (cast_D_pos m), log_cast_D]
  ring_nf

/-! ### The lower bound on binomial coefficients by the entropy function -/

/-! ### The decay rate `ρ_c` -/

/-- `ρ_c = 9/(c-1) < 1` for `c > 10`. -/
theorem rhoC_lt_one {c : ℝ} (hc : 10 < c) : rhoC c < 1 :=
  (div_lt_one (by linarith)).2 (by linarith)

/-! ### The exponent `γ` -/

/-! ### The exponent `q` -/

/-- `q` is a continuous function of `θ`. -/
theorem continuous_qOf : Continuous qOf :=
  (entropy_continuous.add (continuous_id.mul continuous_const)).div_const _

/-- The exponent `q` is strictly increasing in `θ` on `[0, 0.9]`: the derivative of `H(θ) + θ ln 9`
is `ln(9(1-θ)/θ)`, which is positive for `0 < θ < 0.9`. -/
theorem qOf_strictMonoOn : StrictMonoOn qOf (Set.Icc 0 0.9) := by
  have hnum : StrictMonoOn (fun θ : ℝ => entropy θ + θ * Real.log 9) (Set.Icc 0 0.9) := by
    refine strictMonoOn_of_deriv_pos (convex_Icc 0 0.9)
      (entropy_continuous.add (continuous_id.mul continuous_const)).continuousOn fun θ hθ => ?_
    rw [interior_Icc] at hθ
    obtain ⟨hθ0, hθ1⟩ : 0 < θ ∧ θ < 0.9 := hθ
    have hderiv : HasDerivAt (fun θ : ℝ => entropy θ + θ * Real.log 9)
        (Real.log ((1 - θ) / θ) + 1 * Real.log 9) θ :=
      (hasDerivAt_entropy θ hθ0 (by linarith)).add ((hasDerivAt_id θ).mul_const (Real.log 9))
    rw [hderiv.deriv, one_mul, ← Real.log_mul (div_pos (by linarith) hθ0).ne' (by norm_num)]
    refine Real.log_pos ?_
    rw [div_mul_eq_mul_div, lt_div_iff₀ hθ0]
    linarith
  exact fun x hx y hy hxy => div_lt_div_of_pos_right (hnum hx hy hxy) log_four_pos

/-- The exponent `q` is not negative for `0 < θ < 0.9`. -/
theorem qOf_nonneg (θ : ℝ) (hθ0 : 0 < θ) (hθ1 : θ < 0.9) : 0 ≤ qOf θ :=
  div_nonneg (add_nonneg (entropy_nonneg hθ0.le (by linarith))
    (mul_nonneg hθ0.le (Real.log_nonneg (by norm_num)))) log_four_pos.le

/-- `q` increases with `θ` from 0 to `log_4 10` on `(0, 0.9)`: the value at `θ = 0`. That `q`
increases is `qOf_strictMonoOn`. -/
theorem qOf_zero : qOf 0 = 0 := by
  simp [qOf, entropy]

/-- `q` increases with `θ` from 0 to `log_4 10` on `(0, 0.9)`: the value at `θ = 0.9`. Indeed
`H(0.9) + 0.9 ln 9 = ln 10`, because `ln 0.9 = ln 9 - ln 10` and `ln 0.1 = -ln 10`. -/
theorem qOf_nine_tenths : qOf 0.9 = Real.logb 4 10 := by
  have hnine : Real.log 0.9 = Real.log 9 - Real.log 10 := by
    rw [← Real.log_div (by norm_num) (by norm_num)]
    norm_num
  have htenth : Real.log (1 - 0.9) = -Real.log 10 := by
    rw [← Real.log_inv]
    norm_num
  rw [qOf, entropy, Real.logb, hnine, htenth]
  congr 1
  ring

/-- `e^{m(H(θ) + θ ln 9)} = D^q` with `D = 4^m` and `q = (H(θ) + θ ln 9)/ln 4`. -/
theorem exp_entropy_eq_D_rpow_qOf (θ : ℝ) (m : ℕ) :
    Real.exp ((m : ℝ) * (entropy θ + θ * Real.log 9)) = (D m : ℝ) ^ qOf θ := by
  rw [cast_D_rpow]
  congr 1
  have hfour := log_four_pos.ne'
  unfold qOf
  field_simp

/-! ### The denominator `ln Λ` of equation (11), and `R_c(γ)` -/

end ThreeSumApsp
