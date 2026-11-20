module

public import ImprovedExponents.Cost8P.Costs

@[expose] public section

/-!
# The pruned offline routine of Section 4 with the exact exponent

`ImprovedExponents.Cost8X.Offline` shows that upstream's offline routine at the ratios `c = a/b`
and `θ = p/q` runs within

  `N² (log D + 1)²/D^γ + w D^q (log D + 1)`

steps for every `γ` below the exact exponent `γX(c, θ)`, on the instances with `D ≤ N^ε`,
`ε < R_c(γ)` (`offlineWithinX`). Here the same is shown for the pruned offline routine, whose time
is `tOffline32P c₀ G` with the constant `c₀` of the pruned shared stage, on the instances with
`ε < R'_c(γ)` (`offlineWithinP`): the cost of the encodings is `cost8P` and the thinness bound is
that of pruned encodings (`costsP`). The conclusion is spelled out; it is
`ImprovedExponents.OfflineWithin` with `tOffline32P c₀ G` in the place of
`tOffline32 cShared30 G`.

Adapted from `ImprovedExponents/Cost8X/Offline.lean`.
-/

namespace ImprovedExponents

open ThreeSumApsp Real Light Light.Sec4

/-- `ε γ ≤ 1` for `0 < γ` and `ε < R'_c(γ)`; this is upstream's `eps_mul_gamma_le` for the
thinness bound of pruned encodings. -/
theorem eps_mul_gamma_le_P {c γ ε } (hc : 10 < c) (hγ : 0 < γ) (hε : ε < RcP c γ) :
    ε * γ ≤ 1 := by
  have hA := basePruned_pos (by linarith : 1 < c)
  have hden := thinR_den_pos hA hγ.le
  have h1 : RcP c γ * γ ≤ 1 := by
    unfold RcP thinR
    rw [div_mul_eq_mul_div, div_le_one hden]
    linarith
  nlinarith

/-- If the two bounds dominate `cost8P` and the cost of a query on the instances with `D ≤ N^ε`,
the pruned offline routine stays within them. `c₀` is the constant of the pruned shared stage. -/
-- adapted from ImprovedExponents/Cost8X/Offline.lean (OfflineWithin.of_costsWithinX)
theorem offlineWithinP_of_costsWithinP (c₀ : ℕ) {G } {ε γ q C : ℝ} (hC : 0 ≤ C)
    (h : ∀ N D₀ : ℕ, 1 ≤ N → 1 ≤ D₀ → (D₀ : ℝ) ≤ (N : ℝ) ^ ε →
      CostsWithinP G C N D₀ (preBound31 γ N D₀) (queryBound31 q D₀)) :
    ∃ A : ℝ, ∀ N D₀ w : ℕ, 1 ≤ N → 1 ≤ D₀ → (D₀ : ℝ) ≤ (N : ℝ) ^ ε →
      (tOffline32P c₀ G N D₀ w : ℝ) + 400
        ≤ A * (preBound31 γ N D₀ + (w : ℝ) * queryBound31 q D₀) := by
  obtain ⟨A, hA⟩ := exists_tOffline32P_le G hC c₀ 400
  exact ⟨A, by grind⟩

/-- **The pruned offline routine with the exact exponent**, at given ratios `c = a/b` and
`θ = p/q`, with the constant `c₀` of the pruned shared stage: for every `0 < γ < γX(c, θ)`, every
`ε < R'_c(γ)` and every large enough threshold `m₀`, it stays within the bounds with the exponents
`γ` and `q = (H(θ) + θ ln 9)/ln 4`. -/
-- adapted from ImprovedExponents/Cost8X/Offline.lean (offlineWithinX)
theorem offlineWithinP (c₀ : ℕ) {a b p q : ℕ} (hb : 1 ≤ b) (hq : 1 ≤ q) (hc : 10 * b < a)
    (hp : 1 ≤ p) (hθ : 10 * p < 9 * q) {γ ε } (hγ0 : 0 < γ)
    (hγ : γ < gammaX ((a : ℝ) / b) ((p : ℝ) / q)) (hε : ε < RcP ((a : ℝ) / b) γ) :
    ∃ m₁ : ℕ, ∀ (m₀ : ℕ) (hm₀ : 1 ≤ m₀), m₁ ≤ m₀ →
      ∃ A : ℝ, ∀ N D₀ w : ℕ, 1 ≤ N → 1 ≤ D₀ → (D₀ : ℝ) ≤ (N : ℝ) ^ ε →
        (tOffline32P c₀ ⟨a, b, p, q, m₀, hb, hq, hc, hp, hθ, hm₀⟩ N D₀ w : ℝ) + 400
          ≤ A * (preBound31 γ N D₀ + (w : ℝ) * queryBound31 (qOf ((p : ℝ) / q)) D₀) := by
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hcR : (10 : ℝ) < (a : ℝ) / b := by
    rw [lt_div_iff₀ hbR]
    exact_mod_cast hc
  have hθ0 : (0 : ℝ) < (p : ℝ) / q := by positivity
  have hθ1 : (p : ℝ) / q < 0.9 := by
    rw [div_lt_iff₀ hqR]
    have h : (10 : ℝ) * p < 9 * q := by exact_mod_cast hθ
    linarith
  -- a positive thinness exponent at least `ε` and below `R'_c(γ)`: `costsP` wants `ε > 0`
  have hR0 : 0 < RcP ((a : ℝ) / b) γ := thinR_pos (basePruned_pos (by linarith)) hγ0.le
  set ε₁ := max ε (RcP ((a : ℝ) / b) γ / 2) with hε₁
  have hε₁0 : 0 < ε₁ := by positivity
  have hε₁R : ε₁ < RcP ((a : ℝ) / b) γ := by grind
  have hεε₁ : ε ≤ ε₁ := le_max_left _ _
  obtain ⟨C, m₁, hC, hcost⟩ := costsP hcR hθ0 hθ1 hγ0.le hγ hε₁0 hε₁R
  have hεγ := eps_mul_gamma_le_P hcR hγ0 hε₁R
  refine ⟨m₁, fun m₀ hm₀ hm₁ => offlineWithinP_of_costsWithinP c₀ hC fun N D₀ hN hD hDN => ?_⟩
  have hDN₁ : (D₀ : ℝ) ≤ (N : ℝ) ^ ε₁ :=
    hDN.trans (rpow_le_rpow_of_exponent_le (by simp [*]) hεε₁)
  refine ⟨hN,
    one_le_preBound31 hD (rpow_le_sq hN hγ0.le hεγ hDN₁),
    one_le_queryBound31 hD (qOf_nonneg _ hθ0 hθ1), fun hm => ?_⟩
  have hm1 := le_trans hm₀ hm
  obtain ⟨hfit, hpre, hquery⟩ := hcost D₀ N (logFour D₀) (two_le_of_clog hm1) hDN₁
    (ceil_logb_four D₀).symm (le_trans hm₁ hm)
  rw [levelsOf_div a _ hb] at hfit hpre hquery
  rw [switchOf_div p _ hq] at hpre hquery
  exact ⟨⟨hm1, RatParams.ten_le_L _ _, RatParams.t_le _ _, hfit⟩,
    hpre.trans (mul_le_mul_of_nonneg_left (le_preBound31 hD le_rfl) hC),
    hquery.trans (mul_le_mul_of_nonneg_left (le_queryBound31 hD le_rfl) hC)⟩

end ImprovedExponents
