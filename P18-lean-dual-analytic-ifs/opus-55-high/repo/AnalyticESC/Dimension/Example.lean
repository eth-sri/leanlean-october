module

public import AnalyticESC.Dimension.Rapaport

public section

/-!
# Dimensions in the polynomial example of Section 1.2.2

The example satisfies the SESC, hence the ESC, and its attractor is not a singleton, since `f₁`
fixes `0` and `f₃` fixes `1`. By Theorem 1.6, `dim_H Λ = s(Φ)` and `dim μ_p = H(p)/χ` for every
positive probability vector `p`; here `s(Φ) < 1` and `H(p) < χ`, so the minima with `1` in (1.6)
are not attained. Both inequalities follow from `3 c_max < 1`.
-/

namespace AnalyticESC

open Metric Filter Topology

namespace IFS

variable (Φ : IFS N ε)

/-- If `N c_max < 1`, then `H(p) < -log c_max` for every positive probability vector `p`: by
`log x ≤ x - 1`, `∑ p_i log (c_max / p_i) ≤ N c_max - 1 < 0`. -/
theorem exdim_entropy_lt (hN : 0 < N) (hc : N * Φ.cmax < 1) {p : Fin N → ℝ}
    (hp : IsProbVec p) : entropy p < -Real.log Φ.cmax := by
  have hc0 := Φ.cmax_pos hN
  have hsum := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) =>
    show p i * Real.log Φ.cmax - p i * Real.log (p i) ≤ Φ.cmax - p i by
    have := mul_le_mul_of_nonneg_left (Real.log_le_sub_one_of_pos (div_pos hc0 (hp.1 i))) (hp.1 i).le
    rw [Real.log_div hc0.ne' (hp.1 i).ne', mul_sub_one, mul_div_cancel₀ _ (hp.1 i).ne'] at this
    linarith
  simp [← Finset.sum_mul, hp.2] at hsum
  rw [entropy]
  linarith

/-- If `N c_max < 1`, then every zero `s` of the pressure satisfies `s < 1`: for `s ≥ 1`,
`∑_{w ∈ Σ_n} ‖f_w'‖^s ≤ (N c_max)^n`. -/
theorem exdim_lt_one (hN : 0 < N) (hc : N * Φ.cmax < 1)
    (hs : Tendsto (fun n => Real.log (Φ.pressureSum s n) / n) atTop (𝓝 0)) : s < 1 := by
  refine lt_of_not_ge fun h1 => ?_
  have hc0 := Φ.cmax_pos hN
  refine (Real.log_neg (mul_pos (Nat.cast_pos.2 hN) hc0) hc).not_ge
    (le_of_tendsto hs (eventually_atTop.2 ⟨1, fun n hn => ?_⟩))
  rw [div_le_iff₀ (Nat.cast_pos.2 hn), mul_comm, ← Real.log_pow]
  refine Real.log_le_log (Φ.pressureSum_pos hN s n) ?_
  calc Φ.pressureSum s n ≤ ∑ _w : Fin n → Fin N, Φ.cmax ^ n := Finset.sum_le_sum fun w _ => by
        have h := Φ.supDeriv_le (List.ofFn w)
        exact (Real.rpow_le_rpow_of_exponent_ge ((Φ.supDeriv_pos hN) _)
          (h.trans (pow_le_one₀ hc0.le Φ.cmax_lt_one.le)) h1).trans (by simp_all)
    _ = (N * Φ.cmax) ^ n := by simp [mul_pow]

end IFS

/-- The maps of the example have no common fixed point in `I`: `f₁` fixes only `0`, and
`f₃(0) = 29/32`. -/
theorem exdim_no_common_fixed_point :
    ¬ ∃ x ∈ I, ∀ i, exampleIFS.realMap i x = x := by
  rintro ⟨x, -, hx⟩
  have h0 := hx 0
  have h2 := hx 2
  simp only [IFS.realMap, exampleIFS, exampleMaps_zero_ofReal, exampleMaps_two_ofReal,
    Complex.ofReal_re] at h0 h2
  nlinarith

/-- The polynomial example of Section 1.2.2: `dim_H Λ = s(Φ) < 1`, and `dim μ_p = H(p)/χ < 1` for every
positive probability vector `p`. -/
theorem example_dim (hM : RapaportMeasureStatement) (hS : RapaportSetStatement) :
    ∃ s,
      exampleIFS.PressureZero s ∧
      s < 1 ∧ dimH exampleIFS.attractor = ENNReal.ofReal s ∧
      ∀ p, IsProbVec p → ∀ μ, exampleIFS.IsSelfConformal p μ →
        entropy p < exampleIFS.lyapunov p μ ∧
        ∀ᵐ x ∂μ, Tendsto (fun δ => Real.log (μ.real (closedBall x δ)) / Real.log δ) (𝓝[>] 0)
          (𝓝 (entropy p / exampleIFS.lyapunov p μ)) := by
  have hN : 0 < 3 := by norm_num
  obtain ⟨⟨s, hs, hdim⟩, hloc⟩ := exampleIFS.theorem_1_6 hN hM hS
    ((exampleIFS.exists_attractor_eq_singleton_iff hN).not.2 exdim_no_common_fixed_point)
    (exampleIFS.esc_of_sesc exampleIFS_sesc)
  have hs1 := exampleIFS.exdim_lt_one hN (by linarith [exampleIFS_cmax_lt]) ((hs s).2 rfl)
  refine ⟨s, hs, hs1, by grind, fun p hp μ hμ => ?_⟩
  have hl := exampleIFS.neg_log_cmax_le_lyapunov hN hp hμ
  have hH := (exampleIFS.exdim_entropy_lt hN (by linarith [exampleIFS_cmax_lt]) hp).trans_le hl
  exact ⟨hH, min_eq_right ((div_lt_one ((neg_pos.2 (Real.log_neg ((exampleIFS.cmin_pos hN).trans_le (exampleIFS.cmin_le_cmax hN)) exampleIFS.cmax_lt_one)).trans_le hl)).2 hH).le ▸ hloc p hp μ hμ⟩

end AnalyticESC
