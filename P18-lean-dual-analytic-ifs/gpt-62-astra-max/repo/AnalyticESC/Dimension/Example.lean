module

public import AnalyticESC.Dimension.Rapaport
public import AnalyticESC.Main.Example

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

/-- Jensen's inequality for the logarithm bounds the entropy by `log N`. -/
private lemma entropy_le {N} {p : Fin N → ℝ} (hp : IsProbVec p) : entropy p ≤ Real.log N := by
  simpa [entropy,smul_eq_mul,fun i => (hp.1 i).ne'] using strictConcaveOn_log_Ioi.concaveOn.le_map_sum
     (fun i _ => (hp.1 i).le) hp.2 (fun i _ => inv_pos.mpr (hp.1 i))

/-- The maps of the example have no common fixed point in `I`: `f₁` fixes only `0`, and
`f₃(0) = 29/32`. -/
private theorem exdim_no_common_fixed_point :
    ¬ ∃ x ∈ I, ∀ i, exampleIFS.realMap i x = x := by
  rintro ⟨x, -, hx⟩
  have h0 := hx 0; have h2 := hx 2
  simp [IFS.realMap,exampleIFS,Example.real] at h0 h2
  obtain rfl : x = 0 := by linarith
  norm_num at h2

/-- The polynomial example of Section 1.2.2: `dim_H Λ = s(Φ) < 1`, and `dim μ_p = H(p)/χ < 1` for every
positive probability vector `p`. -/
theorem example_dim (hM : RapaportMeasureStatement) (hS : RapaportSetStatement) :
    ∃ s : ℝ,
      exampleIFS.UniqueRoot s ∧
      s < 1 ∧ dimH exampleIFS.attractor = ENNReal.ofReal s ∧
      ∀ p : Fin 3 → ℝ, IsProbVec p → ∀ μ : Measure ℝ, exampleIFS.IsSelfConformal p μ →
        ∀ _ : exampleIFS.lyapunov p μ ≠ 0, entropy p < exampleIFS.lyapunov p μ ∧
        ∀ᵐ x ∂μ, LocalDim μ x (entropy p / exampleIFS.lyapunov p μ) := by
  have hN : 0 < 3 := by norm_num
  have hc : 3 * exampleIFS.cmax < 1 := by
    have := exampleIFS_cmax_lt
    linarith
  have hnd : ¬ ∃ x, exampleIFS.attractor = {x} := by
    rw [exampleIFS.exists_attractor_eq_singleton_iff hN]
    exact exdim_no_common_fixed_point
  obtain ⟨⟨s, hs, hdim⟩, hloc⟩ :=
    exampleIFS.theorem_1_6 hM hS hN hnd (exampleIFS.esc_of_sesc exampleIFS_sesc)
  have pos := exampleIFS.cmax_pos
  have neg := Real.log_neg pos exampleIFS.cmax_lt_one
  have gap : Real.log 3 < -Real.log exampleIFS.cmax := by
    have h := Real.log_neg (by positivity : 0 < 3 * exampleIFS.cmax) hc
    rw [Real.log_mul (by norm_num) (exampleIFS.cmax_pos).ne'] at h; linarith
  have hs1 : s < 1 := by
    by_contra! e
    have := (exampleIFS.slopes (by linarith : 0 ≤ s) exampleIFS.lim_zero ((exampleIFS.ratio_limit _).mp ((hs s).2 rfl))).2
    norm_num at this; nlinarith
  refine ⟨s,hs,hs1,by grind,fun p hp μ hμ hχ => ?_⟩
  have l := exampleIFS.neg_log_cmax_le_lyapunov hp hμ
  have he := (entropy_le hp).trans_lt (gap.trans_le l)
  simpa [Challenge.divide,min_eq_right ((div_lt_one (by linarith)).2 he).le] using And.intro he (hloc p hp μ hμ hχ)

end AnalyticESC
