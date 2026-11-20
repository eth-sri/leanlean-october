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

variable {N : ℕ} {ε : ℝ} (Φ : IFS N ε)

/-! ### The natural projection and the attractor -/

/-- The attractor is invariant: `Λ = ⋃_i f_i(Λ)`. -/
theorem attractor_eq_iUnion : Φ.attractor = ⋃ i, Φ.realMaps i '' Φ.attractor := by
  ext x
  simp only [mem_iUnion, mem_image]
  constructor
  · rintro ⟨ω, rfl⟩
    exact ⟨ω 0, _, ⟨_, rfl⟩, (Φ.natProj_eq_realMap ω).symm⟩
  · rintro ⟨i, _, ⟨ω, rfl⟩, rfl⟩
    let ω'  := fun j => match j with
      | 0 => i
      | j + 1 => ω j
    exact ⟨ω', Φ.natProj_eq_realMap ω'⟩

/-- `|(φ_w)'(x)| = |f_w'(x)|` on the interval. -/
theorem abs_deriv_realComp (w : List (Fin N)) {x : ℝ} (hx : x ∈ I) :
    |deriv (realComp Φ.realMaps w) x| = ‖deriv (Φ.comp w) x‖ := by
  have h := (Φ.hasDerivAt_re_comp w hx).congr_of_eventuallyEq
    (eventuallyEq_of_mem (real_mem_nhds (isOpen_nbhd ε) (Φ.real_mem_open hx))
      fun _ hy => (congrArg Complex.re (Φ.comp_eq_realComp w (subset_closure hy))).symm)
  simp only [Complex.ofReal_re] at h
  rw [h.deriv]
  exact Φ.abs_re_deriv_comp w hx

private theorem real_deriv_pos (i : Fin N) {x : ℝ} (hx : x ∈ I) :
    0 < |deriv (Φ.realMaps i) x| :=
  (Φ.abs_deriv_realComp [i] hx).symm ▸ norm_pos_iff.2
    ((Φ.inClass i).deriv_ne_zero _ (Φ.real_mem_closed hx))

/-- `‖f_w'‖ = sup_{x ∈ I} |φ_w'(x)|`. -/
theorem supDeriv_eq_iSup_realComp (w : List (Fin N)) :
    Φ.supDeriv w = ⨆ x : I, |deriv (realComp Φ.realMaps w) x| :=
  iSup_congr fun x => (Φ.abs_deriv_realComp w x.2).symm

/-- The Lyapunov exponent of a self-conformal measure satisfies `χ ≥ -log c_max`. -/
theorem neg_log_cmax_le_lyapunov {p : Fin N → ℝ} (hp : IsProbVec p)
    {μ : Measure ℝ} (hμ : Φ.IsSelfConformal p μ) : -Real.log Φ.cmax ≤ Φ.lyapunov p μ := by
  obtain ⟨hμ1, hμ2, -⟩ := hμ
  rw [lyapunov, Challenge.lyapunov, neg_le_neg_iff]
  calc ∑ i, p i * ∫ x, Real.log |deriv (Φ.realMaps i) x| ∂μ ≤ ∑ i, p i * Real.log Φ.cmax :=
        Finset.sum_le_sum fun i _ =>
          mul_le_mul_of_nonneg_left (by
              have hI : ∀ᵐ x ∂μ, x ∈ I := ae_iff.2 hμ2
              let f x := Real.log |deriv (Φ.realMaps i) x|
              have hc : ContinuousOn f I := fun x hx =>
                (((Φ.analyticAt_f i (Φ.real_mem_closed hx)).re_ofReal.deriv.continuousAt.abs).log
                  (Φ.real_deriv_pos i hx).ne').continuousWithinAt
              have hi := hc.integrableOn_compact (μ := μ) isCompact_Icc
              rw [IntegrableOn, Measure.restrict_eq_self_of_ae_mem hI] at hi
              have he : f ≤ᵐ[μ] fun _ => Real.log Φ.cmax := hI.mono fun x hx => by
                refine Real.log_le_log (Φ.real_deriv_pos i hx) ?_
                change |deriv (realComp Φ.realMaps [i]) x| ≤ _
                rw [Φ.abs_deriv_realComp [i] hx]
                exact Φ.norm_deriv_le_cmax i (Φ.real_mem_closed hx)
              simpa [f] using integral_mono_ae hi (integrable_const _) he) (hp.1 i).le
    _ = Real.log Φ.cmax := by rw [← Finset.sum_mul, hp.2, one_mul]

/-- Theorem 1.6 (Rapaport). An analytic IFS whose attractor is not a singleton and which
satisfies the ESC has equality in (1.6). -/
theorem theorem_1_6 (hM : RapaportMeasureStatement) (hS : RapaportSetStatement) (hN : 0 < N)
    (hnd : ¬ ∃ x, Φ.attractor = {x}) (hesc : Φ.ESC) : Challenge.DimEquality Φ.f := by
  have hφ : RapaportHyp Φ.realMaps := by
    refine ⟨fun i => (Φ.inClass i).re_mem_I, fun i _ hx => (Φ.analyticAt_f i (Φ.real_mem_closed hx)).re_ofReal,
      fun i _ hx => Φ.real_deriv_pos i hx, fun i _ hx => (Φ.abs_deriv_realComp [i] hx).symm ▸
        (Φ.inClass i).norm_deriv_lt_one _ (Φ.real_mem_closed hx),
      fun h => hnd ((Φ.exists_attractor_eq_singleton_iff hN).2 h), ?_⟩
    have he (u v : List (Fin N)) : Φ.supDist u v = ⨆ x : I, |realComp Φ.realMaps u x - realComp Φ.realMaps v x| := by
      refine iSup_congr fun x => ?_
      change ‖Φ.comp u (x : ℝ) - Φ.comp v (x : ℝ)‖ = _
      rw [Φ.comp_eq_realComp u (Φ.real_mem_closed x.2), Φ.comp_eq_realComp v (Φ.real_mem_closed x.2),
        ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    simpa only [IFS.ESC, Challenge.ESC, he] using hesc
  obtain ⟨s, -, hs⟩ := Φ.exists_pressure_zero hN
  refine ⟨⟨s, hs, ?_⟩, ?_⟩
  · apply hS Φ.realMaps hφ Φ.attractor (Φ.attractor_nonempty hN) Φ.isCompact_attractor
      Φ.attractor_subset_I Φ.attractor_eq_iUnion s
    simpa only [← supDeriv_eq_iSup_realComp, supDeriv] using! (hs s).2 rfl
  · intro p hp μ hμ hχ
    exact hM Φ.realMaps hφ p hp.1 hp.2 μ hμ.1 hμ.2.1 hμ.2.2 hχ

end IFS

end AnalyticESC
