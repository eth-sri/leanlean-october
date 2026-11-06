
import ImprovedExponents.Pipeline.ThinClaim
import ImprovedExponents.Optimum.PerCBasic


/-!
# Choosing parameters below a saving

Small facts used when the parameters of the programs are fitted to a target saving `δ`.

* A thin-product claim stays true for a smaller exponent `γ` (`ThinClaim.mono_gamma`).
* A nonnegative rational is the quotient of two natural numbers (`rat_eq_div`), which is how
  rational exponents enter the program text.
* If `δ` is below the saving `ε min(u, min(γ, s) - u)`, it is still below it after `γ` is lowered a
  little and `ε` is replaced by a suitable smaller rational (`exists_gamma_rat_of_lt`).
* `min(2σ - 1, 1 - σ) ≤ 1/3`, which bounds every saving by `ε/3` (`min_le_third`).
-/

namespace ImprovedExponents

open ThreeSumApsp Light.Sec4

variable {ε : ℝ}

/-- A thin-product claim with the exponent `γ` gives the claim with every smaller exponent. -/
theorem ThinClaim.mono_gamma {M : DetTimeModel} {γ γ' q : ℝ} (h : ThinClaim M ε γ q)
    (hγ : γ' ≤ γ := by simp) : ThinClaim M ε γ' q := by
  obtain ⟨C, T, hT, hb⟩ := h
  refine ⟨max C 0, T, hT, fun N D w u hN hD hDN => ?_⟩
  have hDR : (1 : ℝ) ≤ D := by simp_all
  have hpre : preBound31 γ N D ≤ preBound31 γ' N D := by
    exact div_le_div_of_nonneg_left (by positivity) (by positivity)
      (Real.rpow_le_rpow_of_exponent_le hDR hγ)
  have hpre0 : 0 ≤ preBound31 γ N D := by unfold preBound31; positivity
  have hq0 : 0 ≤ w * queryBound31 q D := by unfold queryBound31; positivity
  calc T N D w u ≤ C * (preBound31 γ N D + w * queryBound31 q D) := by simp_all
    _ ≤ max C 0 * (preBound31 γ N D + w * queryBound31 q D) :=
        by grind [mul_le_mul_of_nonneg_right]
    _ ≤ max C 0 * (preBound31 γ' N D + w * queryBound31 q D) :=
        by grind [mul_le_mul_of_nonneg_left]

variable {r : ℚ}

/-- A nonnegative rational number is the quotient of two natural numbers. -/
theorem rat_eq_div (hr : 0 ≤ r) : (r : ℝ) = (r.num.toNat : ℝ) / (r.den : ℝ) := by
  have hnum : r.num.toNat = (r.num : ℝ) := by
    exact_mod_cast by simp_all
  grind [Rat.cast_def]

/-- The numerator of a positive rational number, as a natural number, is positive. -/
theorem one_le_num_toNat (hr : 0 < r) : 1 ≤ r.num.toNat := by
  have h := Rat.num_pos.2 hr
  omega

variable {k : ℕ}

/-- The numerator and the denominator of a rational number between two bounds given by natural
numbers: `k < r` gives `k · den < num`. -/
theorem mul_den_lt_num (hr : 0 ≤ r) (h : (k : ℝ) < (r : ℝ)) :
    k * r.den < r.num.toNat := by
  have hden : (0 : ℝ) < r.den := by positivity
  rw [rat_eq_div hr, lt_div_iff₀ hden] at h
  exact_mod_cast h

/-- `r < k/l` for natural `k`, `l` gives `l · num < k · den`. -/
theorem mul_num_lt_mul_den (hr : 0 ≤ r) {l : ℕ} (hl : 0 < l)
    (h : (r : ℝ) < (k : ℝ) / l) : l * r.num.toNat < k * r.den := by
  have hden : (0 : ℝ) < r.den := by positivity
  have hlR : (0 : ℝ) < l := by positivity
  rw [rat_eq_div hr, div_lt_div_iff₀ hden hlR] at h
  have h' : l * r.num.toNat < k * (r.den : ℝ) := by linarith
  exact_mod_cast h'



/-- **Lowering the parameters a little.** If `0 ≤ δ < ε min(u, min(γ₀, s) - u)`, there are a
smaller exponent `γ < γ₀` and a positive rational `e < ε` with `δ < e min(u, min(γ, s) - u)`. -/
theorem exists_gamma_rat_of_lt {δ u s γ₀ : ℝ} (hδ0 : 0 ≤ δ) (hε : 0 < ε)
    (hδ : δ < ε * min u (min γ₀ s - u)) :
    ∃ (γ : ℝ) (e : ℚ), γ < γ₀ ∧ 0 < (e : ℝ) ∧ (e : ℝ) < ε ∧
      δ < (e : ℝ) * min u (min γ s - u) := by
  set m₀ := min u _ with hm₀
  set τ := (ε * m₀ - δ) / (2 * ε) with hτ
  have hτpos : 0 < τ := by simp_all
  set m := min u (min (γ₀ - τ) s - u) with hm
  have hmge : m₀ - τ ≤ m := by grind
  have hετ : ε * τ = (ε * m₀ - δ) / 2 := by
    grind
  have hεm : δ < ε * m := by
    nlinarith
  have hmpos : 0 < m := by
    by_contra hneg
    have := mul_nonpos_of_nonneg_of_nonpos hε.le (not_lt.1 hneg)
    linarith
  have hlt : δ / m < ε := by simp_all [div_lt_iff₀]
  obtain ⟨e, he1, he2⟩ := exists_rat_btwn hlt
  refine ⟨γ₀ - τ, e, by linarith, lt_of_le_of_lt (by positivity) he1, he2, ?_⟩
  simp_all [div_lt_iff₀]
