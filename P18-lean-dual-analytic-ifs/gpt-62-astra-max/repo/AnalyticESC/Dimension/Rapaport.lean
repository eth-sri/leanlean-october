module

public import AnalyticESC.Dimension.Pressure

@[expose] public section

/-!
# Theorem 1.6

Rapaport's theorem, as stated in Theorem 1.6 for the class `𝔖_N`: an analytic IFS with a
non-singleton attractor that satisfies the ESC has equality in (1.6). It follows from Rapaport's
Theorem 1.2 and Corollary 1.3 (`RapaportMeasureStatement`, `RapaportSetStatement`), stated for real
analytic maps of `I`, and from the remark after Theorem 1.6: the attractor is a singleton exactly
when the maps have a common fixed point.
-/

namespace AnalyticESC

open Set Metric Filter Topology MeasureTheory

namespace IFS

variable {N : ℕ} (Φ : IFS N)

/-! ### The real maps in Rapaport's setting -/

private lemma real_weight (w : Letters N) {x} (hx : x ∈ I) : |deriv (realComp Φ.realMap w) x| = Φ.weight w x := by
  have h : realComp Φ.realMap w =ᶠ[𝓝 x] Φ.R w := by
    filter_upwards [near_real (isOpen_nbhd _) (Φ.real_mem hx)] with t ht using congrArg Complex.re (Φ.real_comp w ht).symm
  rw [h.deriv_eq,Φ.weight_eq w hx]

/-- `sup_{x ∈ I} |f_u(x) - f_v(x)|` is the same for the real maps. -/
theorem supDist_eq_iSup_realComp (u v : Letters N) :
    Φ.supDist u v = ⨆ x : I, |realComp Φ.realMap u x - realComp Φ.realMap v x| := by
  refine iSup_congr fun x => ?_
  change ‖Φ.comp u x - Φ.comp v x‖ = _
  rw [Φ.real_comp u (Φ.real_mem x.2),Φ.real_comp v (Φ.real_mem x.2),← Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs]

/-- `‖f_w'‖ = sup_{x ∈ I} |φ_w'(x)|`. -/
theorem supDeriv_eq_iSup_realComp (w : Letters N) :
    Φ.supDeriv w = ⨆ x : I, |deriv (realComp Φ.realMap w) x| :=
  iSup_congr fun x => (Φ.real_weight w x.2).symm

/-- An analytic IFS with a non-singleton attractor that satisfies the ESC satisfies the
hypotheses of Rapaport's Theorem 1.2 and Corollary 1.3. -/
theorem rapaportHyp (hN : 0 < N) (hnd : ¬ ∃ x, Φ.attractor = {x}) (hesc : Φ.ESC) :
    RapaportHyp Φ.realMap where
  mapsTo i x hx := (Φ.inClass i).re_mem_I x hx
  analytic i := (Φ.regular_R [i]).1
  deriv_pos i x hx := abs_pos.mpr ((Φ.regular_R [i]).2 x hx)
  deriv_lt_one i x hx := Φ.deriv_R_lt (a := [i]) (by simp) hx
  no_common_fixed_point h := hnd ((Φ.exists_attractor_eq_singleton_iff hN).2 h)
  exp_separated := by simpa only [ESC,Challenge.ESC,← Φ.supDist_eq_iSup_realComp,supDist] using hesc

/-- Integrate the pointwise contraction bound on the compact support. -/
private lemma dim_integral_le (i : Fin N) {μ : Measure ℝ} [IsProbabilityMeasure μ] (hμ : μ Iᶜ = 0) :
    ∫ x, Real.log |deriv (Φ.realMap i) x| ∂μ ≤ Real.log Φ.cmax := by
  have reg := Φ.regular_R [i]
  have hI := ae_iff.2 hμ
  have hint := (reg.1.deriv.continuousOn.abs.log (fun x hx => abs_ne_zero.mpr (reg.2 x hx))).integrableOn_Icc (μ := μ)
  rw [IntegrableOn,Measure.restrict_eq_self_of_ae_mem hI] at hint
  refine (integral_mono_ae hint (integrable_const (Real.log Φ.cmax)) (hI.mono fun x hx => ?_)).trans_eq (by simp)
  exact Real.log_le_log (abs_pos.mpr (reg.2 x hx)) (by simpa using (Φ.R_bounds [i] hx).2)

/-- The Lyapunov exponent of a self-conformal measure satisfies `χ ≥ -log c_max`. -/
theorem neg_log_cmax_le_lyapunov {p : Fin N → ℝ} (hp : IsProbVec p)
    {μ : Measure ℝ} (hμ : Φ.IsSelfConformal p μ) : -Real.log Φ.cmax ≤ Φ.lyapunov p μ := by
  obtain ⟨hμ1, hμ2, -⟩ := hμ
  rw [lyapunov,Challenge.lyapunov,neg_le_neg_iff]
  calc ∑ i, p i * ∫ x, Real.log |deriv (Φ.realMap i) x| ∂μ ≤ ∑ i, p i * Real.log Φ.cmax :=
        Finset.sum_le_sum fun i _ =>
          mul_le_mul_of_nonneg_left (Φ.dim_integral_le i hμ2) (hp.1 i).le
    _ = Real.log Φ.cmax := by rw [← Finset.sum_mul, hp.2, one_mul]

/-- Theorem 1.6 (Rapaport). An analytic IFS whose attractor is not a singleton and which
satisfies the ESC has equality in (1.6). -/
theorem theorem_1_6 (hM : RapaportMeasureStatement) (hS : RapaportSetStatement) (hN : 0 < N)
    (hnd : ¬ ∃ x, Φ.attractor = {x}) (hesc : Φ.ESC) : Challenge.DimEquality Φ.f := by
  have hφ := Φ.rapaportHyp hN hnd hesc
  have : NeZero N := ⟨hN.ne'⟩
  obtain ⟨s, -, hs⟩ := Φ.exists_pressure_zero
  refine ⟨⟨s, hs, ?_⟩, ?_⟩
  · apply hS Φ.realMap hφ Φ.attractor (range_nonempty _) (isCompact_range Φ.continuous_natProj)
      Φ.attractor_subset_I Φ.attractor_eq_iUnion s
    simp only [← Φ.supDeriv_eq_iSup_realComp]
    exact (hs s).2 rfl
  · exact fun p hp μ hμ => hM Φ.realMap hφ p hp.1 hp.2 μ hμ.1 hμ.2.1 hμ.2.2

end IFS
end AnalyticESC
