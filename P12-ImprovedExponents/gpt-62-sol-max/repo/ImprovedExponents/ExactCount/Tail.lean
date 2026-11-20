module

import ImprovedExponents.PrunedEncoding.Counts

public import ThreeSumApsp.Sec4.Corollary31
public import ImprovedExponents.ExactCount.G2

@[expose] public section

/-!
# The tail of the leaf counts, exactly

Section 4 of the paper bounds the number of leaves of order at least `t` in a tile by the geometric
estimate `∑_{d ≥ t} β_d ≤ M ρ^t/(1 - ρ)` (`ThreeSumApsp.Theorem30.sum_beta`). Here it is bounded by
its true exponential rate:

  `∑_{d=t}^{m} β_d ≤ (m + 1)(L + 1) M e^{m g₂(L/m, t/m)}`   (`sum_beta_le_exp`).

Binomial coefficients `binom(L, j)` grow by a factor of at least 9 per step for `j ≤ L/10`.
Thus the largest summand is at `d = t`. The entropy bounds for the coefficients at `m - t`
and `m` bound its ratio to `M` (`beta_le_exp`).

With `L = ⌈cm⌉` and `t = ⌈θm⌉` the rate is at most `g₂(c, θ)`, so the tail is at most
`(m + 1)(L + 1) M D^{-γX(c, θ)}` with `γX(c, θ) := -g₂(c, θ)/ln 4` (`sum_beta_le_rpow`). The paper's
exponent `γ = θ ln(1/ρ_c)/ln 4` does not use this sharper count.
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
        _ ≤ L.choose k * (L - k) := Nat.mul_le_mul_left _ (by omega)
    calc L.choose k * 9 ^ (j₀ - k) = L.choose k * 9 * 9 ^ (j₀ - (k + 1)) := by
          rw [show j₀ - k = j₀ - (k + 1) + 1 by omega, pow_succ]
          ring
      _ ≤ L.choose (k + 1) * 9 ^ (j₀ - (k + 1)) := Nat.mul_le_mul_right _ hstep
      _ ≤ L.choose j₀ := ih

/-- The largest leaf count of the tail occurs at its first order; apply the entropy
sandwich to the coefficients at `m - t` and `m`. -/
theorem beta_le_exp {L m t d : ℕ} (hm : 1 ≤ m) (hL : 10 * m ≤ L) (htd : t ≤ d) (hdm : d ≤ m) :
    (beta L m d : ℝ) ≤ ((L : ℝ) + 1) * (M L m : ℝ) * exp ((m : ℝ) * g2 (L / m) (t / m)) := by
  have hd : L.choose (m - d) * 9 ^ (d - t) ≤ L.choose (m - t) := by
    simpa [show (m - t) - (m - d) = d - t by omega] using
      choose_mul_nine_pow_le (L := L) (j := m - d) (j₀ := m - t) (by omega) (by omega)
  have ht : t ≤ m := htd.trans hdm
  calc
    _ ≤ (L.choose (m - t) : ℝ) * 9 ^ t * 9 ^ (L - m) := by
      have h := Nat.mul_le_mul_right (9 ^ t * 9 ^ (L - m)) hd
      rw [mul_assoc, ← pow_add, ← pow_add, show d - t + (t + (L - m)) = L - m + d by omega,
        ← beta] at h
      exact_mod_cast (by simpa [pow_add, mul_assoc] using h : beta L m d ≤ _)
    _ ≤ exp (chooseEntropy L (m - t)) * 9 ^ t * 9 ^ (L - m) := by
      gcongr
      exact (choose_entropyBounds (by omega : m - t ≤ L)).1
    _ ≤ _ := by
      rw [entropy_drop hm (by omega) ht, M_eq_choose_mul, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
      have h := mul_le_mul_of_nonneg_left (choose_entropyBounds (by omega : m ≤ L)).2
        (exp_pos ((m : ℝ) * g2 (L / m) (t / m))).le
      convert mul_le_mul_of_nonneg_right h (by positivity : 0 ≤ (9 : ℝ) ^ (L - m)) using 1 <;> ring

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
        simp
    _ ≤ ((m : ℝ) + 1) * (((L : ℝ) + 1) * (M L m : ℝ) * exp ((m : ℝ) * g2 (L / m) (t / m))) := by
        refine mul_le_mul_of_nonneg_right ?_ hnonneg
        exact_mod_cast Nat.sub_le (m + 1) t

/-! ### The exponent `γX` -/

/-- The exact exponent of the boxes: `γX(c, θ) := -g₂(c, θ)/ln 4`. It takes the place of the paper's
`γ = θ ln(1/ρ_c)/ln 4` (`ThreeSumApsp.gammaOf`). -/
noncomputable def gammaX (c θ : ℝ) : ℝ := -g2 c θ / log 4

/-- `e^{m g₂(c, θ)} = D^{-γX(c, θ)}` with `D = 4^m`. -/
theorem exp_mul_g2_eq_D_rpow (c θ : ℝ) (m : ℕ) :
    exp ((m : ℝ) * g2 c θ) = (D m : ℝ) ^ (-gammaX c θ) := by
  rw [cast_D_rpow]
  congr 1
  have hfour := log_four_pos.ne'
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
    g2_antitoneOn_left ht0 (Set.mem_Ici.2 (by linarith)) (Set.mem_Ici.2 (by linarith)) hL
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
