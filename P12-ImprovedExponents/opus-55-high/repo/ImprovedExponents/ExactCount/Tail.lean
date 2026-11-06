
import ThreeSumApsp.Sec4.Corollary31
import ImprovedExponents.ExactCount.G2


/-!
# The tail of the leaf counts, exactly

Section 4 of the paper bounds the number of leaves of order at least `t` in a tile by the geometric
estimate `∑_{d ≥ t} β_d ≤ M ρ^t/(1 - ρ)` (`ThreeSumApsp.Theorem30.sum_beta`). Here it is bounded by
its true exponential rate:

  `∑_{d=t}^{m} β_d ≤ (m + 1)(L + 1) M e^{m g₂(L/m, t/m)}`   (`sum_beta_le_exp`).

The proof compares integers. For `d ≥ t`,

  `β_d (m-t)^{m-t} (L-m+t)^{L-m+t} ≤ (L + 1) M 9^t m^m (L-m)^{L-m}`   (`beta_mul_le`),

because binomial coefficients `binom(L, j)` grow by a factor of at least 9 per step for `j ≤ L/10`,
one term of the expansion of `L^L = ((m-t) + (L-m+t))^L` is at most the sum, and the term with
`binom(L, m)` is the largest of the `L + 1` terms of `L^L = (m + (L-m))^L`.

With `L = ⌈cm⌉` and `t = ⌈θm⌉` the rate is at most `g₂(c, θ)`, so the tail is at most
`(m + 1)(L + 1) M D^{-γX(c, θ)}` with `γX(c, θ) := -g₂(c, θ)/ln 4` (`sum_beta_le_rpow`). The paper's
exponent `γ = θ ln(1/ρ_c)/ln 4` is smaller (`gammaOf_le_gammaX`), strictly for `θ > 0`
(`gammaOf_lt_gammaX`).
-/

namespace ImprovedExponents

open ThreeSumApsp Real Finset

variable {L : ℕ}

/-! ### Integers -/

/-- For `j ≤ j₀ ≤ L/10`, binomial coefficients grow by a factor of at least 9 per step. -/
theorem choose_mul_nine_pow_le {j j₀ : ℕ} (hj : j ≤ j₀) (hL : 10 * j₀ ≤ L) :
    L.choose j * 9 ^ (j₀ - j) ≤ L.choose j₀ := by
  induction hj using Nat.decreasingInduction with
  | self => simp
  | of_succ k hk ih =>
    have hstep : L.choose k * 9 ≤ L.choose (k + 1) := by
      refine Nat.le_of_mul_le_mul_right ?_ (Nat.succ_pos k)
      rw [Nat.choose_succ_right_eq]
      calc L.choose k * 9 * (k + 1) = L.choose k * (9 * (k + 1)) := by ring
        _ ≤ L.choose k * (L - k) := Nat.mul_le_mul_left _ (by omega)
    calc L.choose k * 9 ^ (j₀ - k) = L.choose k * 9 * 9 ^ (j₀ - (k + 1)) := by
          rw [show j₀ - k = j₀ - (k + 1) + 1 by omega]
          ring
      _ ≤ L.choose _ * 9 ^ (j₀ - (k + 1)) := by simp_all
      _ ≤ L.choose j₀ := ih

/-- `M = binom(L, m) 9^{L-m}`. -/
theorem M_eq (L m : ℕ) : M L m = L.choose m * 9 ^ (L - m) := by
  rw [← beta_zero_eq_M, beta_zero]

variable {m t d : ℕ}

/-- The leaves of order `d ≥ t`, without fractions:
`β_d (m-t)^{m-t} (L-m+t)^{L-m+t} ≤ (L + 1) M 9^t m^m (L-m)^{L-m}`. -/
theorem beta_mul_le (hL : 10 * m ≤ L) (htd : t ≤ d) (hdm : d ≤ m) :
    beta L m d * ((m - t) ^ (m - t) * (L - m + t) ^ (L - m + t))
      ≤ (L + 1) * (M L m * (9 ^ t * (m ^ m * (L - m) ^ (L - m)))) := by
  have hmL : m ≤ L := by omega
  have h1 : L.choose (m - d) * 9 ^ (d - t) ≤ L.choose (m - t) := by
    have h := choose_mul_nine_pow_le (L := L) (j := m - d) (j₀ := m - t) (by omega) (by omega)
    grind
  have h2 : L.choose (m - t) * (m - t) ^ (m - t) * (L - m + t) ^ (L - m + t) ≤ L ^ L := by
    have h := Nat.choose_mul_pow_mul_pow_le (m - t) (L - m + t) L (m - t)
    grind
  have h3 := Nat.pow_self_le_mul_choose_mul_pow_mul_pow hmL
  have hb : beta L m d = L.choose (m - d) * 9 ^ (d - t) * (9 ^ t * 9 ^ (L - m)) := by
    rw [beta, mul_assoc, ← pow_add, ← pow_add]
    grind
  calc beta L m d * ((m - t) ^ (m - t) * (L - m + t) ^ (L - m + t))
      = L.choose _ * 9 ^ (d - t) * ((m - t) ^ (m - t) * (L - m + t) ^ (L - m + t)
          * (9 ^ t * 9 ^ (L - m))) := by
        grind
    _ ≤ L.choose _ * ((m - t) ^ (m - t) * (L - m + t) ^ (L - m + t)
          * (9 ^ t * 9 ^ (L - m))) := Nat.mul_le_mul_right _ h1
    _ = L.choose _ * (m - t) ^ (m - t) * (L - m + t) ^ (L - m + t)
          * (9 ^ t * 9 ^ (L - m)) := by ring
    _ ≤ L ^ L * (9 ^ t * 9 ^ (L - m)) := by simp_all
    _ ≤ (L + 1) * (L.choose m * m ^ m * (L - m) ^ (L - m)) * (9 ^ t * 9 ^ (L - m)) :=
        by simp_all
    _ = (L + 1) * (M L m * (9 ^ t * (m ^ m * (L - m) ^ (L - m)))) := by
        grind [M_eq]

/-! ### The exponential rate -/

/-- The leaves of order `d ≥ t`: `β_d ≤ (L + 1) M e^{m g₂(L/m, t/m)}`. -/
theorem beta_le_exp (hm : 1 ≤ m) (hL : 10 * m ≤ L) (htd : t ≤ d) (hdm : d ≤ m) :
    (beta L m d : ℝ) ≤ ((L : ℝ) + 1) * (M L m : ℝ) * exp ((m : ℝ) * g2 (L / m) (t / m)) := by
  have hmL : m ≤ L := by omega
  have hX : 0 < (m - t : ℕ) ^ (m - t) * ((L - m + t : ℕ) : ℝ) ^ (L - m + t) := by
    have h : 0 < (m - t) ^ (m - t) * (L - m + t) ^ (L - m + t) :=
      by simp_all [Nat.pow_self_pos]
    exact_mod_cast h
  have hcast : beta L m d
      * ((m - t : ℕ) ^ (m - t) * (L - m + t : ℕ) ^ (L - m + t))
      ≤ (L + 1) * (M L m
        * (9 ^ t * (m ^ m * ((L - m : ℕ) : ℝ) ^ (L - m)))) := by
    exact_mod_cast beta_mul_le hL htd hdm
  rw [exp_mul_g2_div hm hmL (htd.trans hdm)]
  calc beta L m d
      = beta L m d * ((m - t : ℕ) ^ (m - t) * (L - m + t : ℕ) ^ (L - m + t))
          / ((m - t : ℕ) ^ (m - t) * ((L - m + t : ℕ) : ℝ) ^ (L - m + t)) :=
        by grind
    _ ≤ (L + 1) * (M L m * (9 ^ t * (m ^ m * (L - m : ℕ) ^ (L - m))))
          / ((m - t : ℕ) ^ (m - t) * (L - m + t : ℕ) ^ (L - m + t)) :=
        div_le_div_of_nonneg_right hcast hX.le
    _ = _ := by ring

/-- **The tail of the leaf counts**: `∑_{d=t}^{m} β_d ≤ (m + 1)(L + 1) M e^{m g₂(L/m, t/m)}`. -/
theorem sum_beta_le_exp (hm : 1 ≤ m) (hL : 10 * m ≤ L) :
    ∑ d ∈ Finset.Icc t m, (beta L m d : ℝ)
      ≤ ((m : ℝ) + 1) * (((L : ℝ) + 1) * (M L m : ℝ) * exp ((m : ℝ) * g2 (L / m) (t / m))) := by
  have hnonneg : 0 ≤ (L + 1) * M L m * exp (m * g2 (L / m) (t / m)) := by
    positivity
  calc ∑ d ∈ Finset.Icc t m, (beta L m d : ℝ)
      ≤ ∑ _d ∈ Finset.Icc t m, (L + 1) * M L m * exp (m * g2 (L / m) (t / m)) :=
        by grind [sum_le_sum, beta_le_exp]
    _ = (m + 1 - t : ℕ)
          * ((L + 1) * M L m * exp (m * g2 (L / m) (t / m))) := by
        simp
    _ ≤ (m + 1) * ((L + 1) * (M L m) * exp _) := by
        refine mul_le_mul_of_nonneg_right ?_ hnonneg
        exact_mod_cast by omega

/-! ### The exponent `γX` -/

/-- The exact exponent of the boxes: `γX(c, θ) := -g₂(c, θ)/ln 4`. It takes the place of the paper's
`γ = θ ln(1/ρ_c)/ln 4` (`ThreeSumApsp.gammaOf`). -/
noncomputable def gammaX (c θ : ℝ) : ℝ := -g2 c θ / log 4

variable {θ c : ℝ}

@[simp] theorem gammaX_zero (c : ℝ) : gammaX c 0 = 0 := by simp [gammaX]

/-- `γX(c, θ) > 0` for `c > 10` and `0 < θ ≤ 1`. -/
theorem gammaX_pos (hc : 10 < c) (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) : 0 < gammaX c θ :=
  div_pos (neg_pos.2 (g2_neg hc hθ0 hθ1)) log_four_pos

/-- `γX(c, ·)` increases strictly on `[0, 1]`, for `c > 10`. -/
theorem gammaX_strictMonoOn (hc : 10 < c) : StrictMonoOn (gammaX c) (Set.Icc 0 1) :=
  fun _ hx _ hy hxy =>
    div_lt_div_of_pos_right (neg_lt_neg (g2_strictAntiOn_right hc hx hy hxy)) log_four_pos

/-- `e^{m g₂(c, θ)} = D^{-γX(c, θ)}` with `D = 4^m`. -/
theorem exp_mul_g2_eq_D_rpow (c θ : ℝ) (m : ℕ) :
    exp ((m : ℝ) * g2 c θ) = (D m : ℝ) ^ (-gammaX c θ) := by
  rw [cast_D_rpow]
  unfold gammaX
  field_simp

/-- With `L = ⌈cm⌉ ≥ cm` and `t = ⌈θm⌉ ≥ θm`, the rate is at most `g₂(c, θ)`:
`e^{m g₂(L/m, t/m)} ≤ D^{-γX(c, θ)}`. -/
theorem exp_mul_g2_le_D_rpow (hc : 10 < c) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (hm : 1 ≤ m) :
    exp ((m : ℝ) * g2 (levelsOf c m / m) (switchOf θ m / m)) ≤ (D m : ℝ) ^ (-gammaX c θ) := by
  have hm0 : (0 : ℝ) < m := by positivity
  have hL : c ≤ levelsOf c m / m := by
    rw [le_div_iff₀ hm0]
    exact Nat.le_ceil _
  have ht : θ ≤ switchOf θ m / m := by
    rw [le_div_iff₀ hm0]
    exact Nat.le_ceil _
  have ht1 : (switchOf θ m : ℝ) / m ≤ 1 := by
    simp_all [div_le_one, switchOf_le]
  have ht0 : 0 ≤ (switchOf θ m : ℝ) / m := by positivity
  have hstep1 :=
    g2_antitoneOn_left ht0 (by grind) (by grind) hL
  have hstep2 :=
    g2_antitoneOn_right hc.le ⟨hθ0, hθ1⟩ ⟨ht0, ht1⟩ ht
  rw [← exp_mul_g2_eq_D_rpow]
  grind [exp_le_exp, mul_le_mul_of_nonneg_left]

/-- **The tail at the parameters of Corollary 31**: with `L = ⌈cm⌉` and `t = ⌈θm⌉`,
`∑_{d=t}^{m} β_d ≤ (m + 1)(L + 1) M D^{-γX(c, θ)}`. -/
theorem sum_beta_le_rpow (hc : 10 < c) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (hm : 1 ≤ m) :
    ∑ d ∈ Finset.Icc (switchOf θ m) m, (beta (levelsOf c m) m d : ℝ)
      ≤ ((m : ℝ) + 1) * (((levelsOf c m : ℝ) + 1) * (M (levelsOf c m) m : ℝ)
        * (D m : ℝ) ^ (-gammaX c θ)) := by
  apply (sum_beta_le_exp hm (ten_mul_le_levelsOf hc m)).trans
  have h := exp_mul_g2_le_D_rpow hc hθ0 hθ1 hm
  gcongr
