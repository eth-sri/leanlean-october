module

public import RequestProject.FourierLipschitz

/-!
# Fractional Sobolev regularity from difference estimates (Lemma 6.6, fractional part)

The proof of Lemma 6.6 obtains the fractional gain `H^{1+δ}`, `0 < δ < 1/2`, from an `L²`
estimate on differences: a derivative which is Lipschitz away from finitely many jumps has
`‖v(· + h) - v‖²_{L²} ≤ C |h|`, and the difference-quotient seminorm is then finite for
`δ < 1/2`. This file formalizes this step on the circle `ℝ / 2πℤ`, in Fourier form.

* `summable_rpow_mul_of_block_bound`: if the dyadic blocks of a nonnegative sequence satisfy
  `∑_{N ≤ |n| ≤ 2N} aₙ ≤ C N^{-β}`, then `∑ₙ |n|^{2s} aₙ < ∞` for `2s < β`.
* `block_bound_of_diff_bound`: a bound `∑ₙ |e^{inh} - 1|^{2k} aₙ ≤ C h^β` for small `h > 0`
  gives such dyadic block bounds.
* `summable_rpow_mul_fourierCoeff_of_diff_bound`, `summable_rpow_mul_fourierCoeff_of_second_diff`:
  for a continuous `2π`-periodic `φ`, `∫₀^{2π} |φ(θ+h) - φ(θ)|² ≤ C h^β` gives
  `∑ₙ |n|^{2s} |φ̂(n)|² < ∞` for `2s < β`; the same holds with the second difference
  `φ(θ+2h) - 2φ(θ+h) + φ(θ)` in place of the first.
* `second_diff_bound_of_lipschitz_deriv`: if `φ` is Lipschitz on `ℝ`, and on the cut
  interval `[0, 2π]` it is differentiable with Lipschitz derivative (the derivative may jump at
  the cut), then `∫₀^{2π} |φ(θ+2h) - 2φ(θ+h) + φ(θ)|² ≤ C h³`.
* `summable_fourierCoeff_three_halves`: hence `∑ₙ |n|^{2+2δ} |φ̂(n)|² < ∞` for every
  `δ < 1/2`, i.e. `φ ∈ H^{1+δ}(𝕋)`.
-/

@[expose] public section

noncomputable section

namespace PolyaNeumann

open Real Filter MeasureTheory
open scoped InnerProductSpace

variable {φ : ℝ → ℂ}

/-- **Dyadic summation, quantitative form.** If a nonnegative sequence on `ℤ` has dyadic block
sums `∑_{N ≤ |n| ≤ 2N} aₙ ≤ C N^{-β}` for every `N ≥ 1` and `0 ≤ 2s < β`, then every finite
partial sum of `∑ₙ |n|^{2s} aₙ` is at most `0^{2s} a₀ + |C| 2^{2s} / (1 - 2^{2s-β})`. -/
theorem sum_rpow_mul_le_of_block_bound {a : ℤ → ℝ} (ha : ∀ n, 0 ≤ a n) {C β s : ℝ}
    (hs : 0 ≤ s) (hsβ : 2 * s < β)
    (hblock : ∀ N : ℕ, 1 ≤ N → ∀ u : Finset ℤ, (∀ n ∈ u, (N : ℝ) ≤ |(n : ℝ)| ∧
      |(n : ℝ)| ≤ 2 * N) → ∑ n ∈ u, a n ≤ C * (N : ℝ) ^ (-β)) (u : Finset ℤ) :
    ∑ n ∈ u, |(n : ℝ)| ^ (2 * s) * a n ≤
      0 ^ (2 * s) * a 0 + |C| * 2 ^ (2 * s) * (1 - 2 ^ (2 * s - β))⁻¹ := by
  classical
  set f : ℤ → ℝ := fun n => |(n : ℝ)| ^ (2 * s) * a n with hf
  set r := (2 : ℝ) ^ (2 * s - β) with hr
  have hr0 : 0 ≤ r := by positivity
  have hr1 : r < 1 := Real.rpow_lt_one_of_one_lt_of_neg one_lt_two (by linarith)
  set b : ℕ → ℝ := fun j => |C| * 2 ^ (2 * s) * r ^ j with hbdef
  have hb0 : ∀ j, 0 ≤ b j := fun j => by positivity
  have hpow : ∀ (j : ℕ) (x : ℝ), ((2 : ℝ) ^ j) ^ x = ((2 : ℝ) ^ x) ^ j := by
    intro j x
    rw [← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num),
      ← Real.rpow_mul (by norm_num), mul_comm]
  set g : ℤ → ℕ := fun n => Nat.log 2 n.natAbs with hg
  -- the block estimate on a fiber
  rw [← (show ∑' j, b j = |C| * 2 ^ (2 * s) * (1 - 2 ^ (2 * s - β))⁻¹ by
    rw [hbdef, tsum_mul_left, tsum_geometric_of_lt_one hr0 hr1]), ← Finset.sum_filter_add_sum_filter_not u (fun n => n = 0)]
  gcongr
  · calc ∑ n ∈ u with n = 0, f n ≤ ∑ n ∈ {0}, f n := by
          refine Finset.sum_le_sum_of_subset_of_nonneg (fun n hn => ?_) fun n _ _ => (fun n => mul_nonneg (by positivity) (ha n)) n
          rw [Finset.mem_filter] at hn
          simp [hn.2]
      _ = (0 : ℝ) ^ (2 * s) * a 0 := by
          simp [hf]
  · rw [← Finset.sum_fiberwise_of_maps_to (g := g) (t := (u.filter fun n => ¬n = 0).image g)
      (fun n hn => Finset.mem_image_of_mem g hn)]
    calc ∑ j ∈ (u.filter fun n => ¬n = 0).image g,
          ∑ n ∈ (u.filter fun n => ¬n = 0) with g n = j, f n
        ≤ ∑ j ∈ (u.filter fun n => ¬n = 0).image g, b j := by
          refine Finset.sum_le_sum fun j _ => (show ∀ j v, (∀ n ∈ v, n ≠ 0 ∧ g n = j) → ∑ n ∈ v, f n ≤ b j by
            intro j v hv
            have hrange : ∀ n ∈ v, 2 ^ j ≤ |(n : ℝ)| ∧ |(n : ℝ)| ≤ 2 * 2 ^ j := by
              intro n hn
              obtain ⟨hn0, hgn⟩ := hv n hn
              rw [show |(n : ℝ)| = (n.natAbs : ℝ) by
                rw [Nat.cast_natAbs, Int.cast_abs]]
              constructor
              · exact_mod_cast (hgn ▸ Nat.pow_log_le_self 2 (Int.natAbs_ne_zero.2 hn0) : 2 ^ j ≤ n.natAbs)
              · have : (n.natAbs : ℝ) < 2 ^ (j + 1) := by exact_mod_cast (hgn ▸ Nat.lt_pow_succ_log_self one_lt_two _ : n.natAbs < 2 ^ (j + 1))
                rw [pow_succ] at this
                linarith
            have hblk := hblock (2 ^ j) Nat.one_le_two_pow v (by
              intro n hn; push_cast; exact hrange n hn)
            push_cast at hblk
            calc ∑ n ∈ v, f n ≤ ∑ n ∈ v, (2 * 2 ^ j) ^ (2 * s) * a n := by
                  refine Finset.sum_le_sum fun n hn => mul_le_mul_of_nonneg_right ?_ (ha n)
                  exact Real.rpow_le_rpow (abs_nonneg _) (hrange n hn).2 (by linarith)
              _ = (2 * 2 ^ j) ^ (2 * s) * ∑ n ∈ v, a n := by rw [Finset.mul_sum]
              _ ≤ (2 * 2 ^ j) ^ (2 * s) * (|C| * (2 ^ j) ^ (-β)) := by
                  refine mul_le_mul_of_nonneg_left (hblk.trans ?_) (by positivity)
                  exact mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity)
              _ = _ := by
                  rw [Real.mul_rpow (by norm_num) (by positivity), hpow, hpow, hbdef, hr]
                  simp only
                  rw [show (2 : ℝ) ^ (2 * s - β) = 2 ^ (2 * s) * 2 ^ (-β) by
                    rw [sub_eq_add_neg, Real.rpow_add two_pos], mul_pow]
                  ring) j _ fun n hn => ?_
          simp at hn
          exact ⟨hn.1.2, hn.2⟩
      _ ≤ _ := ((summable_geometric_of_lt_one hr0 hr1).mul_left _).sum_le_tsum _ fun j _ => hb0 j

/-- **Dyadic block bounds from a difference estimate.** If `aₙ ≥ 0` is summable and
`∑ₙ |e^{inh} - 1|^{2k} aₙ ≤ C h^β` for all `0 < h ≤ π/2`, then
`∑_{N ≤ |n| ≤ 2N} aₙ ≤ C (π/2)^β N^{-β}`. -/
theorem block_bound_of_diff_bound  (ha : ∀ n, 0 ≤ a n) (hsum : Summable a)
    k {C β : ℝ}
    (hdiff : ∀ h : ℝ, 0 < h → h ≤ π / 2 →
      ∑' n : ℤ, ‖Complex.exp (n * h * Complex.I) - 1‖ ^ (2 * k) * a n ≤ C * h ^ β)
    (N : ℕ) (hN : 1 ≤ N) (u : Finset ℤ)
    (hu : ∀ n ∈ u, N ≤ |(n : ℝ)| ∧ |(n : ℝ)| ≤ 2 * N) :
    ∑ n ∈ u, a n ≤ C * (π / 2) ^ β * (N : ℝ) ^ (-β) := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  set h := π / (2 * N) with hh
  have hhpos : 0 < h := by positivity
  set w : ℤ → ℝ := fun n => ‖Complex.exp (n * h * Complex.I) - 1‖ ^ (2 * k) * a n with hw
  have hwsum : Summable w := by
    refine Summable.of_nonneg_of_le (fun n => mul_nonneg (by positivity) (ha n)) (fun n => ?_)
      (hsum.mul_left (2 ^ (2 * k)))
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) ((show ∀ n : ℤ, ‖Complex.exp (n * h * Complex.I) - 1‖ ≤ 2 by
      intro n
      refine (norm_sub_le _ _).trans ?_
      rw [show (n : ℂ) * h * Complex.I = (n * h : ℝ) * Complex.I from (by push_cast; ring),
        Complex.norm_exp_ofReal_mul_I]
      norm_num) n) _) (ha n)
  calc _ ≤ _ := Finset.sum_le_sum (by
    intro n hn
    obtain ⟨h1, h2⟩ := hu n hn
    have hk := sq_le_norm_exp_sub_one_sq (show |(n : ℝ) * h| ≤ π by
      rw [abs_mul, abs_of_pos hhpos, hh]
      calc |(n : ℝ)| * (π / (2 * N)) ≤ 2 * N * (π / (2 * N)) := by gcongr
        _ = π := by field_simp)
    rw [show (n * h : ℝ) * Complex.I = (n : ℂ) * h * Complex.I by push_cast; ring] at hk
    have : 1 ≤ ‖Complex.exp (n * h * Complex.I) - 1‖ ^ (2 * k) := by
      rw [pow_mul]; exact one_le_pow₀ (by
        have hsq : (π / 2) ^ 2 ≤ ((n : ℝ) * h) ^ 2 := by
          rw [← sq_abs ((n : ℝ) * h)]
          exact pow_le_pow_left₀ (by positivity) (by
            rw [abs_mul, abs_of_pos hhpos, hh]
            calc π / 2 = N * (π / (2 * N)) := by field_simp
              _ ≤ _ := by gcongr) 2
        have : 4 / π ^ 2 * (π / 2) ^ 2 = 1 := by field_simp; ring
        nlinarith [div_pos (by norm_num : (0:ℝ) < 4) (pow_pos pi_pos 2)])
    simpa [hw] using mul_le_mul_of_nonneg_right this (ha n))
    _ ≤ _ := hwsum.sum_le_tsum _ fun n _ => mul_nonneg (by positivity) (ha n)
    _ ≤ _ := hdiff h hhpos (by
      rw [hh, div_le_div_iff₀ (by positivity) two_pos]
      have : (1 : ℝ) ≤ N := by exact_mod_cast hN
      nlinarith [pi_pos])
    _ = _ := by
      rw [hh, show π / (2 * N) = π / 2 * (N : ℝ)⁻¹ by field_simp,
        Real.mul_rpow (by positivity) (by positivity), Real.inv_rpow hNpos.le,
        Real.rpow_neg hNpos.le]
      ring

/-- Fourier coefficients of the `k`-th forward difference `Δ_h^k φ`. -/
lemma fourierCoeffOn_diff  (hφ : Continuous φ) (hper : Function.Periodic φ (2 * π))
    h n :
    fourierCoeffOn two_pi_pos (fun θ => φ (θ + h) - φ θ) n =
      (Complex.exp (n * h * Complex.I) - 1) * fourierCoeffOn two_pi_pos φ n := by
  rw [fourierCoeffOn_sub_of_continuous (f := fun θ => φ (θ + h)) (g := φ) (hφ.comp (continuous_id.add continuous_const)) hφ n, fourierCoeffOn_comp_add hper h n]
  ring

/-- Parseval for the first difference. -/
lemma tsum_diff_eq_integral  (hφ : Continuous φ) (hper : Function.Periodic φ (2 * π))
    (h : ℝ) :
    ∑' n : ℤ, ‖Complex.exp (n * h * Complex.I) - 1‖ ^ (2 * 1) *
        ‖fourierCoeffOn two_pi_pos φ n‖ ^ 2 =
      (2 * π)⁻¹ * ∫ θ in 0..(2 * π), ‖φ (θ + h) - φ θ‖ ^ 2 := by
  have hc : Continuous fun θ => φ (θ + h) - φ θ := (hφ.comp (continuous_id.add continuous_const)).sub hφ
  rw [← (hasSum_sq_fourierCoeffOn_of_continuous hc).tsum_eq]
  congr 1
  funext n
  rw [fourierCoeffOn_diff hφ hper, norm_mul, mul_pow, mul_one]

/-- Parseval for the second difference. -/
lemma tsum_second_diff_eq_integral  (hφ : Continuous φ)
    (hper : Function.Periodic φ (2 * π)) (h : ℝ) :
    ∑' n : ℤ, ‖Complex.exp (n * h * Complex.I) - 1‖ ^ (2 * 2) *
        ‖fourierCoeffOn two_pi_pos φ n‖ ^ 2 =
      (2 * π)⁻¹ * ∫ θ in 0..(2 * π), ‖φ (θ + 2 * h) - 2 * φ (θ + h) + φ θ‖ ^ 2 := by
  set ψ : ℝ → ℂ := fun θ => φ (θ + h) - φ θ with hψ
  have hψc : Continuous ψ := (hφ.comp (continuous_id.add continuous_const)).sub hφ
  have hψp : Function.Periodic ψ (2 * π) := fun θ => by
    simp [hψ, show θ + 2 * π + h = θ + h + 2 * π by ring, hper (θ + h), hper θ]
  have heq : ∀ θ, φ (θ + 2 * h) - 2 * φ (θ + h) + φ θ = ψ (θ + h) - ψ θ := by
    intro θ
    simp [hψ, show θ + h + h = θ + 2 * h by ring]
    ring
  simp_rw [heq]
  rw [← tsum_diff_eq_integral hψc hψp h]
  congr 1
  funext n
  rw [fourierCoeffOn_diff hφ hper, norm_mul]
  ring

end PolyaNeumann
