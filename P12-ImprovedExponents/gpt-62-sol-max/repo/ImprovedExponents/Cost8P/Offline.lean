module

public import ImprovedExponents.Pipeline.Ratios

public import ImprovedExponents.Pipeline.OfflineWithin
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

open ThreeSumApsp Real Light.Sec4

/-- `ε γ ≤ 1` for `0 < γ` and `ε < R'_c(γ)`; this is upstream's `eps_mul_gamma_le` for the
thinness bound of pruned encodings. -/
theorem eps_mul_gamma_le_P {c γ ε : ℝ} (hc : 10 < c) (hγ : 0 < γ) (hε : ε < RcP c γ) :
    ε * γ ≤ 1 := by
  have hA := basePruned_pos (by linarith : 1 < c)
  have hden := thinR_den_pos hA hγ.le
  have h1 : RcP c γ * γ ≤ 1 := by
    unfold RcP thinR
    rw [div_mul_eq_mul_div, div_le_one hden]
    linarith
  nlinarith

/-- **The pruned offline routine with the exact exponent**, at given ratios `c = a/b` and
`θ = p/q`, with the constant `c₀` of the pruned shared stage: for every `0 < γ < γX(c, θ)`, every
`ε < R'_c(γ)` and every large enough threshold `m₀`, it stays within the bounds with the exponents
`γ` and `q = (H(θ) + θ ln 9)/ln 4`. -/
-- adapted from ImprovedExponents/Cost8X/Offline.lean (offlineWithinX)
theorem offlineWithinP (c₀ : ℕ) (G : RatParams) {γ ε : ℝ} (hγ0 : 0 < γ)
    (hγ : γ < gammaX G.realC G.realTheta) (hε : ε < RcP G.realC γ) :
    ∃ m₁ : ℕ, ∀ (m₀ : ℕ) (hm₀ : 1 ≤ m₀), m₁ ≤ m₀ →
      ∃ A : ℝ, ∀ N D₀ w : ℕ, 1 ≤ N → 1 ≤ D₀ → (D₀ : ℝ) ≤ (N : ℝ) ^ ε →
        (tOffline32P c₀ (G.withThreshold m₀ hm₀) N D₀ w : ℝ) + 400
          ≤ A * (preBound31 γ N D₀ + (w : ℝ) * queryBound31 (qOf G.realTheta) D₀) := by
  have hcR := G.ten_lt_realC
  obtain ⟨hθ0, hθ1⟩ := G.realTheta_bounds
  -- a positive thinness exponent at least `ε` and below `R'_c(γ)`: `costsP` wants `ε > 0`
  have hR0 : 0 < RcP G.realC γ := thinR_pos (basePruned_pos (by linarith)) hγ0.le
  let ε₁ := max ε (RcP G.realC γ / 2)
  have hε₁0 : 0 < ε₁ := lt_max_of_lt_right (by positivity)
  have hε₁R : ε₁ < RcP G.realC γ := max_lt hε (by linarith)
  have hεε₁ : ε ≤ ε₁ := le_max_left _ _
  obtain ⟨C, m₁, hC, hcost⟩ := costsP hcR hθ0 hθ1 hγ0.le hγ hε₁0 hε₁R
  have hεγ : ε₁ * γ ≤ 1 := eps_mul_gamma_le_P hcR hγ0 hε₁R
  refine ⟨m₁, fun m₀ hm₀ hm₁ => ?_⟩
  let H := G.withThreshold m₀ hm₀
  obtain ⟨K, hK0, hK⟩ := exists_tPre31P_le_cost8P H c₀
  obtain ⟨Ap, -, hAp⟩ := exists_le_of_small_of_large H hC
    (S := ((20 * H.m₀ + 50 : ℕ) : ℝ)) (by positivity) hK0
  obtain ⟨Aq, -, hAq⟩ := exists_tQuery31_le H hC
  let A : ℝ := max (Ap + 420) (Aq + 30)
  refine ⟨A, fun N D₀ w hN hD hDN => ?_⟩
  let tp := preBound31 γ N D₀
  let tq := queryBound31 (qOf G.realTheta) D₀
  have hDN₁ : (D₀ : ℝ) ≤ (N : ℝ) ^ ε₁ :=
    hDN.trans (rpow_le_rpow_of_exponent_le (by exact_mod_cast hN) hεε₁)
  have htp : 1 ≤ tp := one_le_preBound31 hD (rpow_le_sq hN hγ0.le hεγ hDN₁)
  have htq : 1 ≤ tq := one_le_queryBound31 hD (qOf_nonneg _ hθ0 hθ1)
  have bounds (hm : H.m₀ ≤ logFour D₀) : H.Hyp N D₀ ∧
      preCostP H N D₀ ≤ C * tp ∧ H.queryCost D₀ ≤ C * tq := by
    have hm1 : 1 ≤ logFour D₀ := le_trans hm₀ hm
    obtain ⟨hfit, hpre, hquery⟩ := hcost D₀ N (logFour D₀) (two_le_of_clog hm1) hDN₁
      (ceil_logb_four D₀).symm (le_trans hm₁ hm)
    rw [levelsOf_div G.a _ G.hb] at hfit hpre hquery
    rw [switchOf_div G.p _ G.hq] at hpre hquery
    exact ⟨⟨hm1, H.ten_le_L _, H.t_le _, hfit⟩,
      hpre.trans (mul_le_mul_of_nonneg_left (le_preBound31 hD le_rfl) hC),
      hquery.trans (mul_le_mul_of_nonneg_left (le_queryBound31 hD le_rfl) hC)⟩
  have hsmall (hm : logFour D₀ < H.m₀) : (tPre31P c₀ H N D₀ : ℝ) ≤ (20 * H.m₀ + 50 : ℕ) := by
    exact_mod_cast (show tPre31P c₀ H N D₀ ≤ 20 * H.m₀ + 50 by unfold tPre31P tLog4; lia)
  have hpre := hAp D₀ _ tp _ htp (fun hm => (bounds hm).2.1) hsmall
    (fun hm => (hK N D₀ hN hm (bounds hm).1).trans (le_add_of_nonneg_right (by positivity)))
  have hquery := hAq htq (fun hm => (bounds hm).1) (fun hm => (bounds hm).2.2)
  have hpA := mul_le_mul_of_nonneg_right (le_max_left (Ap + 420) (Aq + 30)) (by linarith : 0 ≤ tp)
  have hqA := mul_le_mul_of_nonneg_right (le_max_right (Ap + 420) (Aq + 30)) (by linarith : 0 ≤ tq)
  have hqW := mul_le_mul_of_nonneg_left (show (tQuery31 H D₀ : ℝ) + 30 ≤ A * tq by
    change _ ≤ max (Ap + 420) (Aq + 30) * tq
    linarith) (Nat.cast_nonneg w)
  change (tOffline32P c₀ H N D₀ w : ℝ) + 400 ≤ A * (tp + w * tq)
  dsimp only [A]
  simp only [tOffline32P, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
  nlinarith only [hpre, hpA, hqW, htp]


end ImprovedExponents
