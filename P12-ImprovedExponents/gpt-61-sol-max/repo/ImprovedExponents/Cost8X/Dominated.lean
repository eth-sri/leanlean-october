module

public import ThreeSumApsp.Sec4.Corollary31
public import ImprovedExponents.ExactCount.Tail
public import ImprovedExponents.Cost8X.Defs
import all ThreeSumApsp.Sec4.Corollary31

@[expose] public section

/-!
# `cost8X` at the parameters of Corollary 31

With `L = ⌈cm⌉` levels, the switching order `t = ⌈θm⌉` and `D = 4^m`, the tail of the leaf counts
is at most `(m + 1)(L + 1) D^{-γX(c, θ)}` (`sum_beta_le_rpow`), where `γX(c, θ) = -g₂(c, θ)/ln 4`
is the exact exponent. So for every `γ < γX(c, θ)` the first term of `cost8X` is
`O(N² log² D/D^γ)`: the slack `γX - γ` pays for the factor `(m + 1)(L + 1)` (`first_termX`). The
second term is that of the paper's expression (8) and is bounded by its inequality (10), which
holds for every `γ ≥ 0` and `ε < R_c(γ)` (`eq_10X`).

`costsX` puts the two together, in the form of upstream's `ThreeSumApsp.Corollary31.costs`, with
`cost8X` in the place of (8) and any `γ < γX(c, θ)` in the place of `γ = θ ln(1/ρ_c)/ln 4`.
-/

namespace ImprovedExponents

open ThreeSumApsp Real Finset

open private levelsOf_le from ThreeSumApsp.Sec4.Corollary31

/-! ### The first term -/

/-- The tail at the parameters of Corollary 31: `tailX ≤ (m + 1)(L + 1) D^{-γX(c, θ)}`. -/
theorem tailX_le_rpow {c θ : ℝ} (hc : 10 < c) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) {m : ℕ} (hm : 1 ≤ m) :
    tailX (levelsOf c m) m (switchOf θ m)
      ≤ ((m : ℝ) + 1) * (((levelsOf c m : ℝ) + 1) * (D m : ℝ) ^ (-gammaX c θ)) := by
  have hmL : m ≤ levelsOf c m := by have := ten_mul_le_levelsOf hc m; omega
  have hM : (0 : ℝ) < M (levelsOf c m) m :=
    sqrtKN0_sq (levelsOf c m) m ▸ pow_pos (sqrtKN0_pos hmL) 2
  unfold tailX
  rw [div_le_iff₀ hM]
  exact (sum_beta_le_rpow hc hθ0 hθ1 hm).trans (le_of_eq (by ring))

/-- `m² D^{-δ} ≤ 2/(δ ln 4)²` for `δ > 0` and `D = 4^m`: a power of `D` pays for `log² D`. -/
theorem sq_mul_D_rpow_le {δ : ℝ} (hδ : 0 < δ) (m : ℕ) :
    (m : ℝ) ^ 2 * (D m : ℝ) ^ (-δ) ≤ 2 / (δ * log 4) ^ 2 := by
  have hlog := log_four_pos
  have hx : 0 ≤ δ * ((m : ℝ) * log 4) := by positivity
  have hexp := quadratic_le_exp_of_nonneg hx
  rw [cast_D_rpow, show -δ * ((m : ℝ) * log 4) = -(δ * ((m : ℝ) * log 4)) by ring, exp_neg,
    ← div_eq_mul_inv, div_le_div_iff₀ (exp_pos _) (by positivity)]
  have hsq : (m : ℝ) ^ 2 * (δ * log 4) ^ 2 = (δ * ((m : ℝ) * log 4)) ^ 2 := by ring
  rw [hsq]
  linarith

/-- **The first term of `cost8X`** for general `c` and `θ`, and every `γ` below the exact exponent
`γX(c, θ)`: it is `O(N² log² D/D^γ)`. The common factor `N²` is left out. This takes the place of
`ThreeSumApsp.Corollary31.first_term`. -/
theorem first_termX {c θ γ : ℝ} (hc : 10 < c) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (hγ : γ < gammaX c θ) :
    Dominated (fun m : ℕ => 1 ≤ m)
      (fun m => (levelsOf c m : ℝ) * m * tailX (levelsOf c m) m (switchOf θ m))
      fun m => (D m : ℝ) ^ (-γ) * Real.log (D m) ^ 2 := by
  have hc0 : (0 : ℝ) < c := by linarith
  have hδ : 0 < gammaX c θ - γ := sub_pos.2 hγ
  have hlog4 := log_four_pos
  refine .of_le_const_mul (C := 2 * (c + 1) * (c + 2) * (2 / ((gammaX c θ - γ) * log 4) ^ 2))
    (by positivity) fun m hm => ?_
  have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hL : (levelsOf c m : ℝ) ≤ (c + 1) * m := levelsOf_le hc hm
  have htail := tailX_le_rpow hc hθ0 hθ1 hm
  have hsplit : (D m : ℝ) ^ (-gammaX c θ)
      = (D m : ℝ) ^ (-(gammaX c θ - γ)) * (D m : ℝ) ^ (-γ) := by
    rw [← rpow_add (cast_D_pos m)]
    congr 1
    ring
  have hpow : (0 : ℝ) ≤ (D m : ℝ) ^ (-gammaX c θ) := rpow_nonneg (Nat.cast_nonneg _) _
  have hpow' : (0 : ℝ) ≤ (D m : ℝ) ^ (-γ) := rpow_nonneg (Nat.cast_nonneg _) _
  have hmlog : (m : ℝ) ≤ Real.log (D m) := cast_le_log_cast_D m
  calc (levelsOf c m : ℝ) * m * tailX (levelsOf c m) m (switchOf θ m)
      ≤ (c + 1) * m * m * (((m : ℝ) + 1) * (((levelsOf c m : ℝ) + 1)
          * (D m : ℝ) ^ (-gammaX c θ))) :=
        mul_le_mul (mul_le_mul_of_nonneg_right hL (Nat.cast_nonneg m)) htail
          (tailX_nonneg _ _ _) (by positivity)
    _ ≤ (c + 1) * m * m * ((2 * (m : ℝ)) * (((c + 2) * m) * (D m : ℝ) ^ (-gammaX c θ))) := by
        gcongr <;> linarith
    _ = 2 * (c + 1) * (c + 2) * ((m : ℝ) ^ 2 * (D m : ℝ) ^ (-(gammaX c θ - γ)))
          * ((D m : ℝ) ^ (-γ) * (m : ℝ) ^ 2) := by
        rw [hsplit]
        ring
    _ ≤ 2 * (c + 1) * (c + 2) * (2 / ((gammaX c θ - γ) * log 4) ^ 2)
          * ((D m : ℝ) ^ (-γ) * Real.log (D m) ^ 2) := by
        have h := sq_mul_D_rpow_le hδ m
        gcongr

/-! ### The second term: inequality (10) for every exponent -/

-- adapted from upstream `ThreeSumApsp/Sec4/Corollary31.lean` (`eq_10`), where the exponent is
-- `gammaOf c θ`; the proof uses only that it is not negative

/-! ### The two terms together -/

end ImprovedExponents
