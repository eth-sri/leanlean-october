module

public import Chazelle.Golf

public import Chazelle.Cost.Analytic

/-!
# The up-phase arithmetic (Chazelle §4.1, Lemma 4.1 and p. 518)

Notation: `n = 2^p + 1`, grades `g = 0, …, p` (the paper's `λ`), `β = 1/5`, and the granularity
of a canonical submap of a grade-`g` chain is `γ = 2^⌈βg⌉` (`ceilBeta g = ⌈βg⌉`).

## Exponent bookkeeping
* `lemma41_exponent`: `1 - β/3 + 4β²/3 = 74/75` (Lemma 4.1).
* `upPhase_exponent`: `β(4β/3 - 1/3) = -1/75` (p. 518).
* `downPhase_exponent`: `β²(4β/3 - 1/3) = -1/375` (p. 520).
* `mergeCost_exponent`: `-β + β²/3 + 2β/3 + β² = -1/75`.

## Lemma 4.1's internal arithmetic (proof on pp. 517–518)
* `resetCost_le`: the granularity-reset cost `Σ_{0 ≤ k < λ} 2^(k - ⌈βk⌉) ≤ 10 · 2^((1-β)λ)`.
* `mergeCost_le`: a single merge of `m ≤ 2^(λ+1)` vertices costs
  `λ² (m / 2^(βλ)) 2^(β²λ/3 + 2βλ/3) (2^(β²λ) + ⌈log₂ m⌉) ≤ 52 λ² m 2^(-λ/75)`.
* `mergeTree_le`: summing merges over `L` levels with at most `2^(λ+1)` vertices per level gives
  at most `104 L λ² 2^((74/75)λ)`.
* `mergeCostFull_le`, `mergeTreeFull_le`: the same keeping Lemma 3.5's `+1` term (dropped in the
  paper), with at most `2λ` merges: `≤ 104 L λ² 2^((74/75)λ) + 416 λ² 2^((74/75)λ)`.
* `clog_le_one_add_clog`: a balanced tree on `j ≤ 2λ` leaves has `≤ 1 + ⌈log₂ λ⌉` levels.
* `lemma41_assembly`: for `λ ≥ 2`, partition + reset + merge tree cost
  `≤ (c_p + 10 c_r + 624 c_m) · λ² ⌈log₂ λ⌉ 2^((74/75)λ)` (Lemma 4.1 with explicit constant).

## Processing a grade and the whole up phase (p. 518)
* `upGradeCost c₀ c₁ c₂ p g`: `2^(p-g)` chains, each costing `c₀` (naive/constant overhead)
  `+ c₁ · λ² ⌈log₂ λ⌉ 2^((1 - β/3 + 4β²/3)λ)` (Lemma 4.1) `+ c₂ · (m ⌈log₂ m⌉ / γ + 1)`
  (Lemma 3.6 preprocessing, `m = 2^λ + 1`, `γ = 2^⌈βλ⌉`).
* `upGradeCost_le_slack`: the paper's "preprocessing grade `λ` takes `O(n 2^(-λ/76))`":
  `upGradeCost c₀ c₁ c₂ p g ≤ (c₀ + 34200³ c₁ + 27 c₂) · 2^p · 2^(-g/76)`.
* `upPhaseCost_le`: `Σ_{g ≤ p} upGradeCost c₀ c₁ c₂ p g ≤ 304 (c₀ + 34200³ c₁ + 27 c₂) · 2^p`.
* `upPhase_series_le`: `Σ_{g ≤ p} 2^(p-g) · λ²⌈log₂ λ⌉2^((74/75)λ) ≤ 900³ · 600 · 2^p`
  (the up-phase series bounded via `Σ λ³ 2^(-λ/75)`).
* `paper_upGrade_slack`: `n λ² ⌈log₂ λ⌉ 2^(βλ(4β/3 - 1/3)) + n λ 2^(-βλ) ≤ (34200³ + 12) n 2^(-λ/76)`.
-/

namespace Chazelle.Cost

public section

open Finset

/-! ### `β = 1/5` and exponents -/

/-- Chazelle's granularity exponent `β = 1/5` (p. 516). -/
@[expose] noncomputable def beta : ℝ := 1 / 5

theorem beta_eq : beta = 1 / 5 := rfl

/-- `⌈βg⌉` (a natural number): the granularity exponent of a canonical submap of a grade-`g`
chain is `γ = 2^⌈βg⌉`. -/
@[expose] noncomputable def ceilBeta (g : ℕ) : ℕ := ⌈beta * g⌉₊

/-- Lemma 4.1's exponent: `1 - β/3 + 4β²/3 = 74/75`. -/
theorem lemma41_exponent : 1 - beta / 3 + 4 * beta ^ 2 / 3 = 74 / 75 := by
  rw [beta_eq]; norm_num

/-- Down-phase exponent (p. 520): `β²(4β/3 - 1/3) = -1/375`. -/
theorem downPhase_exponent : beta ^ 2 * (4 * beta / 3 - 1 / 3) = -1 / 375 := by
  rw [beta_eq]; norm_num

/-- `βg ≤ ⌈βg⌉`. -/
theorem beta_mul_le_ceilBeta (g : ℕ) : beta * g ≤ ceilBeta g := Nat.le_ceil _

/-- `⌈βg⌉ ≤ g`. -/
theorem ceilBeta_le (g : ℕ) : ceilBeta g ≤ g := by
  unfold ceilBeta
  Ξ Nat.ceil_le, beta_eq
  have : (0 : ℝ) ≤ g := Nat.cast_nonneg g
  linarith

/-- `⌈βg⌉ ≥ 1` for `g ≥ 1`. -/
theorem one_le_ceilBeta {g : ℕ} (hg : 1 ≤ g) : 1 ≤ ceilBeta g := by
  unfold ceilBeta
  apply Nat.one_le_iff_ne_zero.mpr
  apply Nat.pos_iff_ne_zero.mp
  Ξ Nat.ceil_pos, beta_eq
  have : (1 : ℝ) ≤ g := by exact_mod_cast hg
  linarith

/-- `1 / 2^⌈βg⌉ ≤ 2^(-g/5)`. -/
theorem inv_two_pow_ceilBeta_le (g : ℕ) :
    1 / (2 : ℝ) ^ (ceilBeta g) ≤ (2 : ℝ) ^ (-(g : ℝ) / 5) := by
  rw [one_div, ← Real.rpow_natCast, ← Real.rpow_neg (⊛)]
  apply two_rpow_le_two_rpow
  have := beta_mul_le_ceilBeta g
  rw [beta_eq] at this
  linarith

/-! ### Two slack inequalities with explicit constants -/

/-- `λ³ 2^(-λ/75) ≤ 34200³ · 2^(-λ/76)` (the `−1/76` slack of p. 518; `34200 = 2·3·5700`,
`1/75 - 1/76 = 1/5700`). -/
theorem slack76_cubic (g : ℕ) :
    (g : ℝ) ^ 3 * (2 : ℝ) ^ (-(g : ℝ) / 75) ≤ 34200 ^ 3 * (2 : ℝ) ^ (-(g : ℝ) / 76) := by
  have h := natPow_le_two_rpow 3 5700 (⊛) g
  have hpos : 0 ≤ (2 : ℝ) ^ (-(g : ℝ) / 75) := (two_rpow_pos _).le
  have h' : (g : ℝ) ^ 3 ≤ 34200 ^ 3 * (2 : ℝ) ^ ((g : ℝ) / 5700) := by
    have e : (2 * ((3 : ℕ) : ℝ) * ((5700 : ℕ) : ℝ)) = 34200 := ⊛
    rw [e] at h
    exact_mod_cast h
  calc (g : ℝ) ^ 3 * (2 : ℝ) ^ (-(g : ℝ) / 75)
      ≤ (34200 ^ 3 * (2 : ℝ) ^ ((g : ℝ) / 5700)) * (2 : ℝ) ^ (-(g : ℝ) / 75) :=
        mul_le_mul_of_nonneg_right h' hpos
    _ = 34200 ^ 3 * ((2 : ℝ) ^ ((g : ℝ) / 5700) * (2 : ℝ) ^ (-(g : ℝ) / 75)) := ⋆
    _ = 34200 ^ 3 * (2 : ℝ) ^ (-(g : ℝ) / 76) := by
        Ξ two_rpow_mul_two_rpow
        congr 2
        ring

/-- `λ · 2^(-λ/5) ≤ 12 · 2^(-λ/76)`. -/
theorem slack76_linear (g : ℕ) :
    (g : ℝ) * (2 : ℝ) ^ (-(g : ℝ) / 5) ≤ 12 * (2 : ℝ) ^ (-(g : ℝ) / 76) := by
  have h := nat_le_two_rpow 6 (⊛) g
  have hpos : 0 ≤ (2 : ℝ) ^ (-(g : ℝ) / 5) := (two_rpow_pos _).le
  have hg : (0 : ℝ) ≤ g := Nat.cast_nonneg g
  calc (g : ℝ) * (2 : ℝ) ^ (-(g : ℝ) / 5)
      ≤ (2 * ((6 : ℕ) : ℝ) * (2 : ℝ) ^ ((g : ℝ) / ((6 : ℕ) : ℝ))) * (2 : ℝ) ^ (-(g : ℝ) / 5) :=
        mul_le_mul_of_nonneg_right h hpos
    _ = 12 * ((2 : ℝ) ^ ((g : ℝ) / 6) * (2 : ℝ) ^ (-(g : ℝ) / 5)) := by push_cast; ring
    _ = 12 * (2 : ℝ) ^ (-(g : ℝ) / 30) := by
        Ξ two_rpow_mul_two_rpow
        congr 2
        ring
    _ ≤ 12 * (2 : ℝ) ^ (-(g : ℝ) / 76) := by
        apply mul_le_mul_of_nonneg_left _ (⊛)
        apply two_rpow_le_two_rpow
        linarith

/-- `2^(-λ/5) ≤ 2^(-λ/76)` and `2^(-λ) ≤ 2^(-λ/76)`. -/
theorem two_rpow_neg_div5_le (g : ℕ) : (2 : ℝ) ^ (-(g : ℝ) / 5) ≤ (2 : ℝ) ^ (-(g : ℝ) / 76) := by
  apply two_rpow_le_two_rpow
  have : (0 : ℝ) ≤ g := Nat.cast_nonneg g
  linarith

/-! ### Per-chain cost bounds -/

/-- Lemma 4.1's per-chain time bound (without its constant): `λ² ⌈log₂ λ⌉ 2^(λ(1 - β/3 + 4β²/3))`,
i.e. `λ² ⌈log₂ λ⌉ 2^((74/75)λ)`. -/
@[expose] noncomputable def lemma41Bound (g : ℕ) : ℝ :=
  (g : ℝ) ^ 2 * (Nat.clog 2 g : ℝ) * (2 : ℝ) ^ ((1 - beta / 3 + 4 * beta ^ 2 / 3) * g)

/-- Lemma 3.6's preprocessing bound (without its constant) for a grade-`g` chain:
`m ⌈log₂ m⌉ / γ + 1` with `m = 2^g + 1` vertices and `γ = 2^⌈βg⌉`. -/
@[expose] noncomputable def lemma36PrepBound (g : ℕ) : ℝ :=
  ((2 : ℝ) ^ g + 1) * (Nat.clog 2 (2 ^ g + 1) : ℝ) / (2 : ℝ) ^ (ceilBeta g) + 1

theorem lemma41Bound_eq (g : ℕ) :
    lemma41Bound g = (g : ℝ) ^ 2 * (Nat.clog 2 g : ℝ) * (2 : ℝ) ^ ((74 / 75 : ℝ) * g) := by
  unfold lemma41Bound
  Ξ lemma41_exponent

theorem lemma41Bound_nonneg (g : ℕ) : 0 ≤ lemma41Bound g := by
  Ξ lemma41Bound_eq
  have := two_rpow_pos ((74 / 75 : ℝ) * g)
  positivity

/-! ### Processing a grade; the whole up phase -/

/-- Time to process grade `g` (Chazelle p. 516–518), for `n = 2^p + 1`: there are `2^(p-g)`
chains in grade `g`; for each we pay a constant `c₀` (naive processing of the early grades and
bookkeeping), `c₁` times Lemma 4.1's bound (computing its canonical submap), and `c₂` times
Lemma 3.6's preprocessing bound (with `γ = 2^⌈βg⌉`). -/
@[expose] noncomputable def upGradeCost (c₀ c₁ c₂ : ℝ) (p g : ℕ) : ℝ :=
  (2 : ℝ) ^ (p - g) * (c₀ + c₁ * lemma41Bound g + c₂ * lemma36PrepBound g)

/-- Total up-phase time: processing grades `0, 1, …, p`. -/
@[expose] noncomputable def upPhaseCost (c₀ c₁ c₂ : ℝ) (p : ℕ) : ℝ :=
  ∑ g ∈ range (p + 1), upGradeCost c₀ c₁ c₂ p g

/-- The explicit up-phase per-grade constant `c₀ + 34200³ c₁ + 27 c₂`. -/
@[expose] noncomputable def upSlackConst (c₀ c₁ c₂ : ℝ) : ℝ := c₀ + 34200 ^ 3 * c₁ + 27 * c₂

/-! ### Lemma 4.1's internal arithmetic -/

/-- **Granularity reset cost in Lemma 4.1 (p. 517).**
`Σ_{0 ≤ k < λ} 2^(k - ⌈βk⌉) ≤ 10 · 2^((1-β)λ)` (the paper: `O(2^(λ(1-β)))`). -/
theorem resetCost_le (lam : ℕ) :
    ∑ k ∈ range lam, (2 : ℝ) ^ (k - ceilBeta k) ≤ 10 * (2 : ℝ) ^ ((1 - beta) * lam) := by
  set r := (2 : ℝ) ^ ((4 : ℝ) / 5) with hr
  have hterm : ∀ k ∈ range lam, (2 : ℝ) ^ (k - ceilBeta k) ≤ r ^ k := by
    intro k _
    rw [← Real.rpow_natCast, hr, ← Real.rpow_mul_natCast (⊛)]
    apply two_rpow_le_two_rpow
    Ξ Nat.cast_sub (ceilBeta_le k)
    have := beta_mul_le_ceilBeta k
    rw [beta_eq] at this
    linarith
  refine le_trans (Finset.sum_le_sum hterm) ?_
  -- r ≥ 2^(1/5) ≥ 1 + 1/10
  have hu := sub_one_ge_of_pow_eq_two (N := 5) (⊛) (Real.rpow_nonneg (⊛) _)
    (two_rpow_one_div_pow 5 (⊛))
  have hr1 : (2 : ℝ) ^ ((1 : ℝ) / ((5 : ℕ) : ℝ)) ≤ r := by
    rw [hr]; apply two_rpow_le_two_rpow; norm_num
  have hr11 : 1 + 1 / 10 ≤ r := by push_cast at hu hr1 ⊢; linarith
  have hr0 : 1 < r := ⟡
  Ξ geom_sum_eq hr0.ne'
  have hrl : r ^ lam = (2 : ℝ) ^ ((1 - beta) * lam) := by
    rw [hr, ← Real.rpow_mul_natCast (⊛), beta_eq]
    congr 1
    ring
  Ξ hrl
  have hpos : 0 < r - 1 := ⟡
  Ξ div_le_iff₀ hpos
  have h2 : 0 < (2 : ℝ) ^ ((1 - beta) * lam) := two_rpow_pos _
  nlinarith

/-- The time of one merge at grade `λ` (Lemma 3.5 with `f(γ) = λ2^(β²λ/3 + 2βλ/3)`,
`g(γ) = λ`, `h(γ) = 2^(β²λ)`, input curves with `m` vertices in total; p. 518):
`λ² (m / 2^(βλ)) 2^(β²λ/3 + 2βλ/3) (2^(β²λ) + ⌈log₂ m⌉)`. -/
@[expose] noncomputable def mergeCost (lam m : ℕ) : ℝ :=
  (lam : ℝ) ^ 2 * ((m : ℝ) / (2 : ℝ) ^ (beta * lam)) *
    (2 : ℝ) ^ (beta ^ 2 * lam / 3 + 2 * beta * lam / 3) *
      ((2 : ℝ) ^ (beta ^ 2 * lam) + (Nat.clog 2 m : ℝ))

/-! ### Lemma 4.1 with the `+1` terms of Lemma 3.5, and the assembled per-chain bound -/

/-- Lemma 3.5's bound for one merge at grade `λ`, keeping the `+1` of `(n₁/γ₁ + n₂/γ₂ + 1)`:
`λ² (m / 2^(βλ) + 1) 2^(β²λ/3 + 2βλ/3) (2^(β²λ) + ⌈log₂ m⌉)` (the paper drops the `+1`). -/
@[expose] noncomputable def mergeCostFull (lam m : ℕ) : ℝ :=
  (lam : ℝ) ^ 2 * ((m : ℝ) / (2 : ℝ) ^ (beta * lam) + 1) *
    (2 : ℝ) ^ (beta ^ 2 * lam / 3 + 2 * beta * lam / 3) *
      ((2 : ℝ) ^ (beta ^ 2 * lam) + (Nat.clog 2 m : ℝ))

end

end Chazelle.Cost
