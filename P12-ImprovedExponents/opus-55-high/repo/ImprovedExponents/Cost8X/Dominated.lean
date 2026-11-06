
import ThreeSumApsp.Sec4.Corollary31
import ImprovedExponents.ExactCount.Tail
import ImprovedExponents.Cost8X.Defs
import ThreeSumApsp.Sec4.Corollary31


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

open ThreeSumApsp Real

variable {c θ : ℝ}


/-! ### The first term -/

/-- The tail at the parameters of Corollary 31: `tailX ≤ (m + 1)(L + 1) D^{-γX(c, θ)}`. -/
theorem tailX_le_rpow (hc : 10 < c) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) {m : ℕ} (hm : 1 ≤ m) :
    tailX (levelsOf c m) m (switchOf θ m)
      ≤ ((m : ℝ) + 1) * (((levelsOf c m : ℝ) + 1) * (D m : ℝ) ^ (-gammaX c θ)) := by
  have hmL : m ≤ levelsOf c m := by grind [ten_mul_le_levelsOf]
  unfold tailX
  rw [div_le_iff₀ (sqrtKN0_sq _ m ▸ pow_pos (sqrtKN0_pos hmL) 2)]
  exact (sum_beta_le_rpow hc hθ0 hθ1 hm).trans (by grind)

/-- `m² D^{-δ} ≤ 2/(δ ln 4)²` for `δ > 0` and `D = 4^m`: a power of `D` pays for `log² D`. -/
theorem sq_mul_D_rpow_le {δ : ℝ} (hδ : 0 < δ) (m : ℕ) :
    (m : ℝ) ^ 2 * (D m : ℝ) ^ (-δ) ≤ 2 / (δ * log 4) ^ 2 := by
  have hx : 0 ≤ δ * (m * log 4) := by positivity
  have hexp := quadratic_le_exp_of_nonneg hx
  rw [cast_D_rpow, show -δ * (m * log 4) = -(δ * (m * log 4)) by ring, exp_neg,
    ← div_eq_mul_inv, div_le_div_iff₀ (exp_pos _) (by positivity)]
  linarith

/-- **The first term of `cost8X`** for general `c` and `θ`, and every `γ` below the exact exponent
`γX(c, θ)`: it is `O(N² log² D/D^γ)`. The common factor `N²` is left out. This takes the place of
`ThreeSumApsp.Corollary31.first_term`. -/
theorem first_termX {γ : ℝ} (hc : 10 < c) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (hγ : γ < gammaX c θ) :
    Dominated (fun m : ℕ => 1 ≤ m)
      (fun m => (levelsOf c m : ℝ) * m * tailX (levelsOf c m) m (switchOf θ m))
      fun m => (D m : ℝ) ^ (-γ) * Real.log (D m) ^ 2 := by
  refine .of_le_const_mul (C := 2 * (c + 1) * (c + 2) * (2 / ((gammaX c θ - γ) * log 4) ^ 2))
    (by positivity) fun m hm => ?_
  have hm' : (1 : ℝ) ≤ m := by simp_all
  have hL := levelsOf_le hc hm
  have hsplit : D m ^ (-gammaX c θ)
      = D m ^ (-(gammaX c θ - γ)) * (D m : ℝ) ^ (-γ) := by
    rw [← rpow_add (cast_D_pos m)]
    ring
  have hmlog := cast_le_log_cast_D m
  calc levelsOf c m * m * tailX _ m _
      ≤ (c + 1) * m * m * ((m + 1) * (((levelsOf c m) + 1)
          * (D m) ^ (-gammaX c θ))) :=
        mul_le_mul (mul_le_mul_of_nonneg_right hL (Nat.cast_nonneg m)) (tailX_le_rpow hc hθ0 hθ1 hm)
          (tailX_nonneg _ _ _) (by positivity)
    _ ≤ (c + 1) * m * m * ((2 * m) * (((c + 2) * m) * (D m) ^ (-gammaX c θ))) := by
        gcongr <;> linarith
    _ = 2 * (c + 1) * (c + 2) * (m ^ 2 * (D m) ^ (-(gammaX c θ - γ)))
          * ((D m) ^ (-γ) * m ^ 2) := by
        grind
    _ ≤ 2 * (c + 1) * (c + 2) * (2 / ((gammaX c θ - γ) * log 4) ^ 2)
          * ((D m) ^ (-γ) * Real.log _ ^ 2) := by
        have h := sq_mul_D_rpow_le (sub_pos.2 hγ) m
        gcongr

/-! ### The second term: inequality (10) for every exponent -/

-- adapted from upstream `ThreeSumApsp/Sec4/Corollary31.lean` (`eq_10`), where the exponent is
-- `gammaOf c θ`; the proof uses only that it is not negative

/-! ### The two terms together -/
