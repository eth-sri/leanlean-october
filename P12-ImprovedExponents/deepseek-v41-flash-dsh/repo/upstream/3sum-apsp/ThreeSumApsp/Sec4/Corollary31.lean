/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Sec4.ParameterSteps

/-!
# Corollary 31: the costs of Theorem 30 as powers of `D`

"We repeat the proof of Corollary 26 with L := ⌈cm⌉ and t := ⌈θm⌉". Here `L` is `levelsOf c m` and
`t` is `switchOf θ m`, for constants `c > 10` and `0 < θ < 0.9`; the inner dimension satisfies
`2 ≤ D ≤ N^ε` with `ε < R_c(γ)`, and `m = ⌈log_4 D⌉`. The main result is `Corollary31.costs`: for
all `m` from some `m₀` on, the preprocessing cost (8) of Theorem 30 (`cost8`, the sum of a first
term for the boxes and a last term for the encodings) is `O(N² log² D / D^γ)`, and its query cost
`L ∑_{d ≤ t} α_d` (`costQuery`) is `O(D^q log D)`. What the paper says of the finitely many smaller
`m` is `Corollary31.small_m`; nothing else rests on that lemma.

The steps are those of the proof of Corollary 26. What does not depend on `c` and `θ` is proved
before, for both corollaries; the rest is what the paper says of each step.

* Setting up. As for Corollary 26, the inner dimension is padded to `D = 4^m`
  (`Corollary26.setting_up`, `Corollary26.padding`); this changes the bounds by a constant factor
  (`padded_le`). The hypothesis reads `N ≥ 4^{(m-1)/ε}` (`Corollary31.hypothesis`).
* Boxes. `ρ < ρ_c` and `ρ^t ≤ D^{-γ}` (`Corollary31.rho_lt`, `Corollary31.rho_pow_le`), which bounds
  the first term of (8) (`Corollary31.first_term`).
* Queries. The calculation of Corollary 26, `∑_{d ≤ t} α_d ≤ (9x)^t (1 + 1/x)^m` (`sum_alpha_le`),
  with `x = (1-θ)/θ` in place of 8 gives `O(D^q)` (`Corollary31.sum_alpha`) and so
  `Corollary31.query_cost`.
* Encodings. As for Corollary 26, inequality (10) (`eq_10`) bounds the last term of (8)
  (`Equation10.last_term`) and gives the hypothesis `N ≥ √K N₀` of Theorem 30
  (`Equation10.tile_fits`). Its left-hand side is `O(√m · Λ^m)` (`Corollary31.lhs10_le`), and the
  base `Λ` is smaller than the base `4^{1/ε}` (`eq_11_iff`). This `Λ` is the general form of the `Λ`
  of Corollary 26 (`exp_lnΛ`, `baseLambda_eq_exp_lnΛ`).

The last sentence of the corollary, on `R_c(0)`, is `sec4_Rc_strictAntiOn` and
`sec4_Rc_zero_tendsto`. Bounds "up to a constant" are written with `Dominated`, in the one parameter
`m` or in the record `Sizes` of the given `D`, of `N` and of `m`.
-/

@[expose] public section

open Finset

namespace ThreeSumApsp

/-! ### Setting up -/

/-- The hypotheses of Corollary 31 on its parameters: "Let c > 10 and 0 < θ < 0.9", and "ε <
R_c(γ)". -/
structure Admissible (c θ ε : ℝ) : Prop where
  c_gt : 10 < c
  θ_pos : 0 < θ
  θ_lt : θ < 0.9
  thin : ε < Rc c (gammaOf c θ)

/-- With "L := ⌈cm⌉" (proof of Corollary 31) the hypothesis `L ≥ 10m` of Theorem 30 holds. -/
theorem ten_mul_le_levelsOf {c : ℝ} (hc : 10 < c) (m : ℕ) : 10 * m ≤ levelsOf c m := by
  have h : ((10 * m : ℕ) : ℝ) ≤ c * m := by
    push_cast
    exact mul_le_mul_of_nonneg_right hc.le (Nat.cast_nonneg m)
  exact_mod_cast h.trans (Nat.le_ceil _)

/-- `L = ⌈cm⌉ ≤ (c + 1) m` for `m ≥ 1`. -/
private lemma levelsOf_le {c : ℝ} (hc : 10 < c) {m : ℕ} (hm : 1 ≤ m) :
    (levelsOf c m : ℝ) ≤ (c + 1) * m := by
  have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hL : (levelsOf c m : ℝ) < c * m + 1 := Nat.ceil_lt_add_one (by positivity)
  linarith

/-- `m = O(log D)` for `D = 4^m`. -/
private lemma dominated_cast_log_D :
    Dominated (fun m : ℕ => 1 ≤ m) (fun m => (m : ℝ)) fun m => Real.log (D m) :=
  .of_le fun m _ => cast_le_log_cast_D m

/-- `L = ⌈cm⌉ = O(log D)` for `D = 4^m`. -/
private lemma dominated_levelsOf_log_D {c : ℝ} (hc : 10 < c) :
    Dominated (fun m : ℕ => 1 ≤ m) (fun m => (levelsOf c m : ℝ)) fun m => Real.log (D m) :=
  (Dominated.of_le_const_mul (C := c + 1) (by linarith) fun _ hm => levelsOf_le hc hm).trans
    dominated_cast_log_D

/-- Proof of Corollary 31: "After the padding, the assumption D ≤ N^ε now reads N ≥ 4^{(m-1)/ε}",
because `4^{m-1} < D ≤ N^ε` for the original `D`. -/
theorem Corollary31.hypothesis {m D₀ N : ℕ} {ε : ℝ} (hm : 1 ≤ m) (hε : 0 < ε)
    (hgt : 4 ^ (m - 1) < D₀) (hthin : (D₀ : ℝ) ≤ (N : ℝ) ^ ε) :
    (4 : ℝ) ^ (((m : ℝ) - 1) / ε) ≤ (N : ℝ) := by
  have hle : (4 : ℝ) ^ ((m : ℝ) - 1) ≤ (N : ℝ) ^ ε := by
    rw [← Nat.cast_one, ← Nat.cast_sub hm, Real.rpow_natCast]
    exact le_trans (by exact_mod_cast hgt.le) hthin
  calc (4 : ℝ) ^ (((m : ℝ) - 1) / ε) = ((4 : ℝ) ^ ((m : ℝ) - 1)) ^ (1 / ε) := by
        rw [← Real.rpow_mul (by norm_num), mul_one_div]
    _ ≤ ((N : ℝ) ^ ε) ^ (1 / ε) := Real.rpow_le_rpow (by positivity) hle (by positivity)
    _ = (N : ℝ) := by
        rw [← Real.rpow_mul N.cast_nonneg, mul_one_div_cancel hε.ne', Real.rpow_one]

/-! ### Boxes -/

/-- Proof of Corollary 31: "ρ < ρ_c", where `ρ = 9m/(L-m+1)` and `L = ⌈cm⌉ ≥ cm`. -/
theorem Corollary31.rho_lt {c : ℝ} (hc : 10 < c) (m : ℕ) : rho (levelsOf c m) m < rhoC c := by
  have hL : c * m ≤ levelsOf c m := Nat.le_ceil _
  have hm : (m : ℝ) ≤ c * m := le_mul_of_one_le_left (Nat.cast_nonneg m) (by linarith)
  unfold rho rhoC
  -- after clearing denominators: `9m (c - 1) < 9 (L - m + 1)`, from `cm ≤ L`
  rw [div_lt_div_iff₀ (by linarith) (by linarith)]
  linarith

/-! ### Queries -/

/-- Proof of Corollary 31: "the same calculation with x := (1-θ)/θ in place of 8, where 9x > 1
because θ < 0.9, gives ∑_{d≤t} α_d ≤ (9x)^t (1+1/x)^m = O(D^q)". The constant is `9x`, because
`t = ⌈θm⌉ < θm + 1`. -/
theorem Corollary31.sum_alpha {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 0.9) :
    Dominated (fun m : ℕ => 1 ≤ m) (fun m => ∑ d ∈ range (switchOf θ m + 1), (alpha m d : ℝ))
      fun m => (D m : ℝ) ^ qOf θ := by
  have hx : 0 < (1 - θ) / θ := div_pos (by linarith) hθ0
  have h9x : 1 < 9 * ((1 - θ) / θ) := by
    rw [← mul_div_assoc, lt_div_iff₀ hθ0]
    linarith
  refine .of_le_const_mul (C := 9 * ((1 - θ) / θ)) (by positivity) fun m _ => ?_
  have ht : ((switchOf θ m : ℕ) : ℝ) ≤ θ * m + 1 := (Nat.ceil_lt_add_one (by positivity)).le
  calc ∑ d ∈ range (switchOf θ m + 1), (alpha m d : ℝ)
      ≤ (9 * ((1 - θ) / θ)) ^ switchOf θ m * (1 + 1 / ((1 - θ) / θ)) ^ m :=
        sum_alpha_le hx h9x.le (switchOf_le (by linarith) m)
    _ ≤ (9 * ((1 - θ) / θ)) ^ (θ * (m : ℝ) + 1) * (1 + 1 / ((1 - θ) / θ)) ^ m := by
        gcongr
        rw [← Real.rpow_natCast]
        exact Real.rpow_le_rpow_of_exponent_le h9x.le ht
    _ = 9 * ((1 - θ) / θ) * (D m : ℝ) ^ qOf θ := by
        rw [← rpow_mul_pow_eq_D_rpow_qOf hθ0 (by linarith) m, Real.rpow_add (by positivity),
          Real.rpow_one]
        ring

/-- The query cost `L ∑_{d ≤ t} α_d` of Theorem 30 is `O(L D^q) = O(D^q log D)`, for `D = 4^m`. (In
the proof of Corollary 26: "Hence a query takes O(L D^q) = O(m D^q) time".) -/
theorem Corollary31.query_cost {c θ : ℝ} (hc : 10 < c) (hθ0 : 0 < θ) (hθ1 : θ < 0.9) :
    Dominated (fun m : ℕ => 1 ≤ m) (fun m => costQuery (levelsOf c m) m (switchOf θ m))
      fun m => (D m : ℝ) ^ qOf θ * Real.log (D m) :=
  ((dominated_levelsOf_log_D hc).mul (Corollary31.sum_alpha hθ0 hθ1) (fun _ _ => by positivity)
    fun _ _ => by positivity).congr (fun _ _ => rfl) fun m _ => by ring

/-! ### Encodings

As in the proof of Corollary 26, `m`-th powers are compared by comparing their bases. The paper's
sentences are one lemma each: the bound on the binomial coefficient (`Corollary31.le_K`, for which
`Corollary31.mul_entropy_monotoneOn` passes from `L` to `cm`), the bound `O(√m · Λ^m)` on the
left-hand side (`Corollary31.lhs10_le`), where `Λ` is `Real.exp (lnΛ c γ)` (`exp_lnΛ`), and
`Λ < 4^{1/ε}` (`eq_11_iff`); `eq_10` puts them together with `Corollary31.hypothesis`. Throughout,
`L = ⌈cm⌉`, and `D₀` is the inner dimension before padding. -/

/-! ### The corollary -/

/-- The instances of Corollary 31 from a threshold `m₀` on: `2 ≤ D ≤ N^ε` and `m = ⌈log_4 D⌉ ≥ m₀`.
-/
structure Sizes.Corollary31 (ε : ℝ) (m₀ : ℕ) (p : Sizes) : Prop where
  setUp : p.SetUp
  thin : (p.D₀ : ℝ) ≤ (p.N : ℝ) ^ ε
  large : m₀ ≤ p.m

end ThreeSumApsp
