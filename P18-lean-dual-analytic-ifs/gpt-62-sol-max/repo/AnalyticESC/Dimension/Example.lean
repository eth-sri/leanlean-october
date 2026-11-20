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

/-- Jensen's inequality gives the entropy bound by the uniform distribution. -/
private theorem entropy_le_log_card {N : ℕ} {p : Fin N → ℝ} (hp : IsProbVec p) :
    entropy p ≤ Real.log N := by
  have h := strictConcaveOn_log_Ioi.concaveOn.le_map_sum (p := fun i => (p i)⁻¹)
    (fun i _ => (hp.1 i).le) hp.2 (fun i _ => inv_pos.2 (hp.1 i))
  simpa [entropy, smul_eq_mul, Real.log_inv, ← Finset.sum_neg_distrib, (hp.1 _).ne'] using h

/-- The maps of the example have no common fixed point in `I`: `f₁` fixes only `0`, and
`f₃(0) = 29/32`. -/
private theorem exdim_no_common_fixed_point :
    ¬ ∃ x ∈ I, ∀ i, exampleIFS.realMaps i x = x := by
  rintro ⟨x, -, hx⟩
  have h0 := hx 0
  have h2 := hx 2
  change ((x : ℂ) / 8).re = x at h0
  change ((x : ℂ) / 16 + (x : ℂ) ^ 2 / 32 + 29 / 32).re = x at h2
  simp only [Complex.div_ofNat_re, Complex.ofReal_re] at h0
  obtain rfl : x = 0 := by linarith
  simp_all

end AnalyticESC

namespace Challenge

open AnalyticESC Set Metric Filter Topology MeasureTheory

/-- The polynomial example of Section 1.2.2, from Rapaport's Theorem 1.2 and Corollary 1.3:
`dim_H Λ = s(Φ) < 1`, where `s(Φ)` is the unique zero of the pressure, and `dim μ_p = H(p)/χ < 1` at
`μ_p`-almost every point, for every positive probability vector `p`, by Theorem 1.6. -/
theorem audit_example_dim (hM : RapaportMeasureStatement) (hS : RapaportSetStatement) :
    ∃ s : ℝ,
      (∀ t, Tendsto (pressureRatio exampleMaps t) atTop (𝓝 0) ↔ t = s) ∧
      s < 1 ∧ dimH (attractor exampleMaps) = ENNReal.ofReal s ∧
      ∀ p : Fin 3 → ℝ, IsProbVec p → ∀ μ : Measure ℝ, IsSelfConformal exampleMaps p μ →
        ∀ hχ : lyapunov exampleMaps p μ ≠ 0,
        entropy p < lyapunov exampleMaps p μ ∧
        ∀ᵐ x ∂μ, Tendsto (fun r : Scale => logRatio (μ.real (closedBall x r)) r) scaleZero
          (𝓝 (divide (entropy p) (lyapunov exampleMaps p μ) hχ)) := by
  have hN : (0 : ℕ) < 3 := by norm_num
  have hc : Real.log (3 : ℝ) + Real.log exampleIFS.cmax < 0 := by
    rw [← Real.log_mul (by norm_num) (exampleIFS.cmax_pos hN).ne']
    exact Real.log_neg (by positivity [exampleIFS.cmax_pos hN]) (by linarith [exampleIFS_cmax_lt])
  have hnd : ¬ ∃ x, exampleIFS.attractor = {x} := by
    rw [exampleIFS.exists_attractor_eq_singleton_iff hN]
    exact AnalyticESC.exdim_no_common_fixed_point
  obtain ⟨⟨s, hs, hdim⟩, hloc⟩ :=
    exampleIFS.theorem_1_6 hM hS hN hnd (exampleIFS.esc_of_sesc exampleIFS_sesc)
  have hs1  := exampleIFS.pressure_zero_lt_one hN hc ((hs s).2 rfl)
  refine ⟨s, hs, hs1, by grind [exampleIFS], fun p hp μ hμ hχne => ?_⟩
  have hχ := exampleIFS.neg_log_cmax_le_lyapunov hp hμ
  have hH  :=
    ((AnalyticESC.entropy_le_log_card hp).trans_lt (by linarith)).trans_le hχ
  have hpos : 0 < exampleIFS.lyapunov p μ := by
    grind [Real.log_nonneg]
  refine ⟨hH, ?_⟩
  have hb : entropy p / lyapunov exampleMaps p μ ≤ 1 := (by bound)
  simpa only [divide, exampleIFS, min_eq_right hb] using (hloc p hp μ hμ hχne)

end Challenge
