module

public import AnalyticESC.Dimension.Rapaport

@[expose] public section

/-!
# Dimensions in the polynomial example of Section 1.2.2

The example satisfies the SESC, hence the ESC, and its attractor is not a singleton, since `f₁`
fixes `0` and `f₃` fixes `1`. By Theorem 1.6, `dim_H Λ = s(Φ)` and `dim μ_p = H(p)/χ` for every
positive probability vector `p`; here `s(Φ) < 1` and `H(p) < χ`, so the minima with `1` in (1.6)
are not attained. Both inequalities follow from `3 c_max < 1`.
-/

namespace AnalyticESC

open Set Metric Filter Topology MeasureTheory

namespace IFS

variable {N : ℕ} {ε : ℝ} (Φ : IFS N ε)

/-- If `N c_max < 1`, then `H(p) < -log c_max` for every positive probability vector `p`: by
`log x ≤ x - 1`, `∑ p_i log (c_max / p_i) ≤ N c_max - 1 < 0`. -/
private theorem exdim_entropy_lt (hN : 0 < N) (hc : N * Φ.cmax < 1) {p : Fin N → ℝ}
    (hp : IsProbVec p) : entropy p < -Real.log Φ.cmax := by
  have hc0 := Φ.cmax_pos hN
  have hsum := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => by
    have hpi := hp.1 i
    have hl := Real.log_le_sub_one_of_pos (div_pos hc0 hpi)
    rw [Real.log_div hc0.ne' hpi.ne', sub_le_iff_le_add] at hl
    exact (mul_le_mul_of_nonneg_left hl hpi.le).trans_eq
      (by rw [mul_add, mul_sub_one, mul_div_cancel₀ _ hpi.ne'])
  rw [← Finset.sum_mul, hp.2, one_mul, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hp.2] at hsum
  rw [entropy]; linarith

/-- If `N c_max < 1`, then every zero `s` of the pressure satisfies `s < 1`: for `s ≥ 1`,
`∑_{w ∈ Σ_n} ‖f_w'‖^s ≤ (N c_max)^n`. -/
private theorem exdim_lt_one (hN : 0 < N) (hc : N * Φ.cmax < 1) {s : ℝ}
    (hs : Tendsto (fun n : ℕ => Real.log (Φ.pressureSum s n) / n) atTop (𝓝 0)) : s < 1 := by
  refine lt_of_not_ge fun h1 => ?_
  have hc0 := Φ.cmax_pos hN
  have hb (n : ℕ) (hn : 1 ≤ n) : Real.log (Φ.pressureSum s n) / n ≤ Real.log (N * Φ.cmax) := by
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    have hle : Φ.pressureSum s n ≤ (N * Φ.cmax) ^ n := by
      refine (Finset.sum_le_sum (g := fun _ => Φ.cmax ^ n) fun w _ => ?_).trans_eq (by simp [mul_pow])
      have h : Φ.supDeriv (List.ofFn w) ≤ Φ.cmax ^ n := by simpa using Φ.supDeriv_le (List.ofFn w)
      exact (Real.rpow_le_rpow_of_exponent_ge (Φ.supDeriv_pos hN _)
        (h.trans (pow_le_one₀ hc0.le Φ.cmax_lt_one.le)) h1).trans (by rwa [Real.rpow_one])
    rw [div_le_iff₀ hn']
    exact (Real.log_le_log (Φ.pressureSum_pos hN s n) hle).trans_eq (by rw [Real.log_pow]; ring)
  have h0 := le_of_tendsto hs (eventually_atTop.2 ⟨1, hb⟩)
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  linarith [Real.log_neg (by positivity) hc]

end IFS

/-- The polynomial example of Section 1.2.2: `dim_H Λ = s(Φ) < 1`, and `dim μ_p = H(p)/χ < 1` for every
positive probability vector `p`. -/
theorem example_dim (hM : RapaportMeasureStatement) (hS : RapaportSetStatement) :
    ∃ s : ℝ,
      (∀ t, Tendsto (fun n : ℕ => Real.log (exampleIFS.pressureSum t n) / n) atTop (𝓝 0) ↔
        t = s) ∧
      s < 1 ∧ dimH exampleIFS.attractor = ENNReal.ofReal s ∧
      ∀ p : Fin 3 → ℝ, IsProbVec p → ∀ μ : Measure ℝ, exampleIFS.IsSelfConformal p μ →
        entropy p < exampleIFS.lyapunov p μ ∧
        ∀ᵐ x ∂μ, Tendsto (fun δ => Real.log (μ.real (closedBall x δ)) / Real.log δ) (𝓝[>] 0)
          (𝓝 (entropy p / exampleIFS.lyapunov p μ)) := by
  have hN : (0 : ℕ) < 3 := by norm_num
  have hc : ((3 : ℕ) : ℝ) * exampleIFS.cmax < 1 := by
    have := exampleIFS_cmax_lt; push_cast; linarith
  have hnd : ¬ ∃ x, exampleIFS.attractor = {x} := by
    rw [exampleIFS.exists_attractor_eq_singleton_iff hN]
    rintro ⟨x, -, hx⟩
    have h0 : ((x : ℂ) / 8).re = x := hx 0
    have h2 : ((x : ℂ) / 16 + (x : ℂ) ^ 2 / 32 + 29 / 32).re = x := hx 2
    simp only [Complex.div_ofNat_re, Complex.ofReal_re] at h0
    obtain rfl : x = 0 := by linarith
    norm_num at h2
  obtain ⟨⟨s, hs, hdim⟩, hloc⟩ :=
    exampleIFS.theorem_1_6 hM hS hN hnd (exampleIFS.esc_of_sesc exampleIFS_sesc)
  have hs1 : s < 1 := exampleIFS.exdim_lt_one hN hc ((hs s).2 rfl)
  refine ⟨s, hs, hs1, by rw [hdim, min_eq_right hs1.le], fun p hp μ hμ => ?_⟩
  have hlyap := exampleIFS.neg_log_cmax_le_lyapunov hN hp hμ
  have hH : entropy p < exampleIFS.lyapunov p μ :=
    (exampleIFS.exdim_entropy_lt hN hc hp).trans_le hlyap
  have hχ : 0 < exampleIFS.lyapunov p μ :=
    (neg_pos.2 (Real.log_neg (exampleIFS.cmax_pos hN) exampleIFS.cmax_lt_one)).trans_le hlyap
  refine ⟨hH, ?_⟩
  have h := hloc p hp μ hμ
  rwa [min_eq_right ((div_lt_one hχ).2 hH).le] at h

end AnalyticESC
