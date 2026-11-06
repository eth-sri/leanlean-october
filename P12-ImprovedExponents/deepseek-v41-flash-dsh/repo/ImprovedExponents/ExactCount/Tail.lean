module

public import ThreeSumApsp.Sec4.Corollary31
public import ImprovedExponents.ExactCount.G2
public import ThreeSumApsp.TacticsShort

@[expose] public section

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

/-! ### Integers -/

/-- For `j ≤ j₀ ≤ L/10`, binomial coefficients grow by a factor of at least 9 per step. -/
theorem choose_mul_nine_pow_le {L j j₀ : ℕ} (hj : j ≤ j₀) (hL : 10 * j₀ ≤ L) :
    L.choose j * 9 ^ (j₀ - j) ≤ L.choose j₀ := by
  induction hj using Nat.decreasingInduction with
  | self => simp
  | of_succ k hk ih =>
    have hstep : L.choose k * 9 ≤ L.choose (k + 1) := by
      refine Nat.le_of_mul_le_mul_right ?_ (Nat.succ_pos k)
      rw [Nat.choose_succ_right_eq]
      calc L.choose k * 9 * (k + 1) = L.choose k * (9 * (k + 1)) := by ring
        _ ≤ L.choose k * (L - k) := Nat.mul_le_mul_left _ tac_omega
    calc L.choose k * 9 ^ (j₀ - k) = L.choose k * 9 * 9 ^ (j₀ - (k + 1)) := by
          rw [show j₀ - k = j₀ - (k + 1) + 1 by omega, pow_succ]
          ring
      _ ≤ L.choose (k + 1) * 9 ^ (j₀ - (k + 1)) := Nat.mul_le_mul_right _ hstep
      _ ≤ L.choose j₀ := ih

/-- `M = binom(L, m) 9^{L-m}`. -/
theorem M_eq (L m : ℕ) : M L m = L.choose m * 9 ^ (L - m) := by
  rw [← beta_zero_eq_M, beta_zero]

/-- The leaves of order `d ≥ t`, without fractions:
`β_d (m-t)^{m-t} (L-m+t)^{L-m+t} ≤ (L + 1) M 9^t m^m (L-m)^{L-m}`. -/
theorem beta_mul_le {L m t d : ℕ} (hL : 10 * m ≤ L) (htd : t ≤ d) (hdm : d ≤ m) :
    beta L m d * ((m - t) ^ (m - t) * (L - m + t) ^ (L - m + t))
      ≤ (L + 1) * (M L m * (9 ^ t * (m ^ m * (L - m) ^ (L - m)))) := by
  have hmL : m ≤ L := by omega
  have h1 : L.choose (m - d) * 9 ^ (d - t) ≤ L.choose (m - t) := by
    have h := choose_mul_nine_pow_le (L := L) (j := m - d) (j₀ := m - t) tac_omega tac_omega
    rwa [show m - t - (m - d) = d - t by omega] at h
  have h2 : L.choose (m - t) * (m - t) ^ (m - t) * (L - m + t) ^ (L - m + t) ≤ L ^ L := by
    have h := Nat.choose_mul_pow_mul_pow_le (m - t) (L - m + t) L (m - t)
    rwa [show L - (m - t) = L - m + t by omega, show m - t + (L - m + t) = L by omega] at h
  have h3 := Nat.pow_self_le_mul_choose_mul_pow_mul_pow hmL
  have hb : beta L m d = L.choose (m - d) * 9 ^ (d - t) * (9 ^ t * 9 ^ (L - m)) := by
    rw [beta, mul_assoc, ← pow_add, ← pow_add]
    congr 2
    omega
  calc beta L m d * ((m - t) ^ (m - t) * (L - m + t) ^ (L - m + t))
      = L.choose (m - d) * 9 ^ (d - t) * ((m - t) ^ (m - t) * (L - m + t) ^ (L - m + t)
          * (9 ^ t * 9 ^ (L - m))) := by
        rw [hb]
        ring
    _ ≤ L.choose (m - t) * ((m - t) ^ (m - t) * (L - m + t) ^ (L - m + t)
          * (9 ^ t * 9 ^ (L - m))) := Nat.mul_le_mul_right _ h1
    _ = L.choose (m - t) * (m - t) ^ (m - t) * (L - m + t) ^ (L - m + t)
          * (9 ^ t * 9 ^ (L - m)) := by ring
    _ ≤ L ^ L * (9 ^ t * 9 ^ (L - m)) := Nat.mul_le_mul_right _ h2
    _ ≤ (L + 1) * (L.choose m * m ^ m * (L - m) ^ (L - m)) * (9 ^ t * 9 ^ (L - m)) :=
        Nat.mul_le_mul_right _ h3
    _ = (L + 1) * (M L m * (9 ^ t * (m ^ m * (L - m) ^ (L - m)))) := by
        rw [M_eq]
        ring

/-! ### The exponential rate -/

/-- The leaves of order `d ≥ t`: `β_d ≤ (L + 1) M e^{m g₂(L/m, t/m)}`. -/
theorem beta_le_exp {L m t d : ℕ} (hm : 1 ≤ m) (hL : 10 * m ≤ L) (htd : t ≤ d) (hdm : d ≤ m) :
    (beta L m d : ℝ) ≤ ((L : ℝ) + 1) * (M L m : ℝ) * exp ((m : ℝ) * g2 (L / m) (t / m)) := by
  have hmL : m ≤ L := by omega
  have ht := htd.trans hdm
  have hX : (0 : ℝ) < ((m - t : ℕ) : ℝ) ^ (m - t) * ((L - m + t : ℕ) : ℝ) ^ (L - m + t) := by
    have h : 0 < (m - t) ^ (m - t) * (L - m + t) ^ (L - m + t) :=
      Nat.mul_pos (Nat.pow_self_pos) (Nat.pow_pos tac_omega)
    exact_mod_cast h
  have hcast : (beta L m d : ℝ)
      * (((m - t : ℕ) : ℝ) ^ (m - t) * ((L - m + t : ℕ) : ℝ) ^ (L - m + t))
      ≤ ((L : ℝ) + 1) * ((M L m : ℝ)
        * ((9 : ℝ) ^ t * ((m : ℝ) ^ m * ((L - m : ℕ) : ℝ) ^ (L - m)))) := by
    exact_mod_cast beta_mul_le hL htd hdm
  rw [exp_mul_g2_div hm hmL ht]
  calc (beta L m d : ℝ)
      = (beta L m d : ℝ) * (((m - t : ℕ) : ℝ) ^ (m - t) * ((L - m + t : ℕ) : ℝ) ^ (L - m + t))
          / (((m - t : ℕ) : ℝ) ^ (m - t) * ((L - m + t : ℕ) : ℝ) ^ (L - m + t)) :=
        (mul_div_cancel_right₀ _ hX.ne').symm
    _ ≤ ((L : ℝ) + 1) * ((M L m : ℝ) * ((9 : ℝ) ^ t * ((m : ℝ) ^ m * ((L - m : ℕ) : ℝ) ^ (L - m))))
          / (((m - t : ℕ) : ℝ) ^ (m - t) * ((L - m + t : ℕ) : ℝ) ^ (L - m + t)) :=
        div_le_div_of_nonneg_right hcast hX.le
    _ = _ := by ring

/-- **The tail of the leaf counts**: `∑_{d=t}^{m} β_d ≤ (m + 1)(L + 1) M e^{m g₂(L/m, t/m)}`. -/
theorem sum_beta_le_exp {L m t : ℕ} (hm : 1 ≤ m) (hL : 10 * m ≤ L) :
    ∑ d ∈ Finset.Icc t m, (beta L m d : ℝ)
      ≤ ((m : ℝ) + 1) * (((L : ℝ) + 1) * (M L m : ℝ) * exp ((m : ℝ) * g2 (L / m) (t / m))) := by
  have hnonneg : 0 ≤ ((L : ℝ) + 1) * (M L m : ℝ) * exp ((m : ℝ) * g2 (L / m) (t / m)) := by
    positivity
  calc ∑ d ∈ Finset.Icc t m, (beta L m d : ℝ)
      ≤ ∑ _d ∈ Finset.Icc t m, ((L : ℝ) + 1) * (M L m : ℝ) * exp ((m : ℝ) * g2 (L / m) (t / m)) :=
        sum_le_sum fun d hd => beta_le_exp hm hL (mem_Icc.1 hd).1 (mem_Icc.1 hd).2
    _ = ((m + 1 - t : ℕ) : ℝ)
          * (((L : ℝ) + 1) * (M L m : ℝ) * exp ((m : ℝ) * g2 (L / m) (t / m))) := by
        rw [sum_const, Nat.card_Icc, nsmul_eq_mul]
    _ ≤ ((m : ℝ) + 1) * (((L : ℝ) + 1) * (M L m : ℝ) * exp ((m : ℝ) * g2 (L / m) (t / m))) := by
        refine mul_le_mul_of_nonneg_right ?_ hnonneg
        exact_mod_cast Nat.sub_le (m + 1) t

/-! ### The exponent `γX` -/

/-- The exact exponent of the boxes: `γX(c, θ) := -g₂(c, θ)/ln 4`. It takes the place of the paper's
`γ = θ ln(1/ρ_c)/ln 4` (`ThreeSumApsp.gammaOf`). -/
noncomputable def gammaX (c θ : ℝ) : ℝ := -g2 c θ / log 4

@[simp] theorem gammaX_zero (c : ℝ) : gammaX c 0 = 0 := by simp [gammaX]

/-- `γX(c, θ) > 0` for `c > 10` and `0 < θ ≤ 1`. -/
theorem gammaX_pos {c θ : ℝ} (hc : 10 < c) (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) : 0 < gammaX c θ :=
  div_pos (neg_pos.2 (g2_neg hc hθ0 hθ1)) log_four_pos

/-- `γX(c, ·)` increases strictly on `[0, 1]`, for `c > 10`. -/
theorem gammaX_strictMonoOn {c : ℝ} (hc : 10 < c) : StrictMonoOn (gammaX c) (Set.Icc 0 1) :=
  fun _ hx _ hy hxy =>
    div_lt_div_of_pos_right (neg_lt_neg (g2_strictAntiOn_right hc hx hy hxy)) log_four_pos

/-- `e^{m g₂(c, θ)} = D^{-γX(c, θ)}` with `D = 4^m`. -/
theorem exp_mul_g2_eq_D_rpow (c θ : ℝ) (m : ℕ) :
    exp ((m : ℝ) * g2 c θ) = (D m : ℝ) ^ (-gammaX c θ) := by
  rw [cast_D_rpow]
  congr 1
  unfold gammaX
  field_simp

/-- With `L = ⌈cm⌉ ≥ cm` and `t = ⌈θm⌉ ≥ θm`, the rate is at most `g₂(c, θ)`:
`e^{m g₂(L/m, t/m)} ≤ D^{-γX(c, θ)}`. -/
theorem exp_mul_g2_le_D_rpow {c θ : ℝ} (hc : 10 < c) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) {m : ℕ}
    (hm : 1 ≤ m) :
    exp ((m : ℝ) * g2 (levelsOf c m / m) (switchOf θ m / m)) ≤ (D m : ℝ) ^ (-gammaX c θ) := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hL : c ≤ (levelsOf c m : ℝ) / m := by
    rw [le_div_iff₀ hm0]
    exact Nat.le_ceil _
  have ht : θ ≤ (switchOf θ m : ℝ) / m := by
    rw [le_div_iff₀ hm0]
    exact Nat.le_ceil _
  have ht1 : (switchOf θ m : ℝ) / m ≤ 1 := by
    rw [div_le_one hm0]
    exact_mod_cast switchOf_le hθ1 m
  have ht0 : 0 ≤ (switchOf θ m : ℝ) / m := by positivity
  have hstep1 : g2 (levelsOf c m / m) (switchOf θ m / m) ≤ g2 c (switchOf θ m / m) :=
    g2_antitoneOn_left ht0 (Set.mem_Ici.2 tac_linarith) (Set.mem_Ici.2 tac_linarith) hL
  have hstep2 : g2 c (switchOf θ m / m) ≤ g2 c θ :=
    g2_antitoneOn_right hc.le ⟨hθ0, hθ1⟩ ⟨ht0, ht1⟩ ht
  rw [← exp_mul_g2_eq_D_rpow]
  exact exp_le_exp.2 (mul_le_mul_of_nonneg_left (hstep1.trans hstep2) hm0.le)

/-- **The tail at the parameters of Corollary 31**: with `L = ⌈cm⌉` and `t = ⌈θm⌉`,
`∑_{d=t}^{m} β_d ≤ (m + 1)(L + 1) M D^{-γX(c, θ)}`. -/
theorem sum_beta_le_rpow {c θ : ℝ} (hc : 10 < c) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) {m : ℕ}
    (hm : 1 ≤ m) :
    ∑ d ∈ Finset.Icc (switchOf θ m) m, (beta (levelsOf c m) m d : ℝ)
      ≤ ((m : ℝ) + 1) * (((levelsOf c m : ℝ) + 1) * (M (levelsOf c m) m : ℝ)
        * (D m : ℝ) ^ (-gammaX c θ)) := by
  refine (sum_beta_le_exp hm (ten_mul_le_levelsOf hc m)).trans ?_
  have h := exp_mul_g2_le_D_rpow hc hθ0 hθ1 hm
  gcongr

end ImprovedExponents