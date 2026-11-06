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

/-- The natural projection is continuous. -/
private theorem continuous_natProj : Continuous Φ.natProj := by
  refine TendstoUniformly.continuous
    (F := fun n ω => (Φ.comp (List.ofFn fun k : Fin n => ω k) 0).re) (p := atTop)
    (Metric.tendstoUniformly_iff.2 fun δ hδ => ?_) (Frequently.of_forall fun n =>
      (continuous_of_discreteTopology (f := fun v : Fin n → Fin N =>
        (Φ.comp (List.ofFn v) 0).re)).comp (continuous_pi fun k => continuous_apply (k : ℕ)))
  filter_upwards [(tendsto_pow_atTop_nhds_zero_of_lt_one Φ.cmax_nonneg
    Φ.cmax_lt_one).eventually (gt_mem_nhds hδ)] with n hn ω
  have h := Φ.abs_re_comp_sub_le (List.ofFn fun k : Fin n => ω k)
    (Φ.attractor_subset_I ⟨fun j => ω (j + n), rfl⟩) (left_mem_Icc.2 zero_le_one)
  rw [List.length_ofFn, Complex.ofReal_zero, ← Φ.natProj_eq_comp_prefix] at h
  exact ((Real.dist_eq _ _).trans_le h).trans_lt hn

/-- The attractor is invariant: `Λ = ⋃_i f_i(Λ)`. -/
private theorem attractor_eq_iUnion : Φ.attractor = ⋃ i, Φ.realMap i '' Φ.attractor := by
  ext x
  simp only [mem_iUnion, mem_image]
  exact ⟨by rintro ⟨ω, rfl⟩; exact ⟨ω 0, _, ⟨_, rfl⟩, (Φ.natProj_eq_realMap ω).symm⟩,
    by rintro ⟨i, _, ⟨ω, rfl⟩, rfl⟩; exact ⟨fun | 0 => i | j + 1 => ω j, Φ.natProj_eq_realMap _⟩⟩

/-- The remark after Theorem 1.6: the attractor is a singleton exactly when the maps have a
common fixed point in `I`. -/
theorem exists_attractor_eq_singleton_iff (hN : 0 < N) :
    (∃ x, Φ.attractor = {x}) ↔ ∃ x ∈ I, ∀ i, Φ.realMap i x = x := by
  constructor
  · rintro ⟨x, hx⟩
    refine ⟨x, Φ.attractor_subset_I (hx ▸ mem_singleton x), fun i => ?_⟩
    have h1 : Φ.natProj (fun _ => i) = x := mem_singleton_iff.1 (hx ▸ ⟨_, rfl⟩)
    exact ((h1.symm.trans (Φ.natProj_eq_realMap _)).trans (congrArg _ h1)).symm
  · rintro ⟨p, hp, hfix⟩
    have hf (i : Fin N) : Φ.f i p = p :=
      (Φ.comp_ofReal [i] hp).trans (congrArg _ (hfix i))
    have hc (w : List (Fin N)) : Φ.comp w p = p := by
      induction w with
      | nil => rfl
      | cons i w ih => rw [comp_cons, Function.comp_apply, ih, hf]
    have hπ (ω : ℕ → Fin N) : Φ.natProj ω = p := by
      refine sub_eq_zero.1 (abs_nonpos_iff.1 (ge_of_tendsto'
        (tendsto_pow_atTop_nhds_zero_of_lt_one Φ.cmax_nonneg Φ.cmax_lt_one) fun n => ?_))
      have h := Φ.abs_re_comp_sub_le (List.ofFn fun k : Fin n => ω k)
        (Φ.attractor_subset_I ⟨fun j => ω (j + n), rfl⟩) hp
      rwa [List.length_ofFn, hc, Complex.ofReal_re, ← Φ.natProj_eq_comp_prefix] at h
    exact ⟨p, Set.ext fun x => ⟨by rintro ⟨ω, rfl⟩; exact hπ ω,
      by rintro rfl; exact ⟨fun _ => ⟨0, hN⟩, hπ _⟩⟩⟩

/-! ### The real maps in Rapaport's setting -/

/-- The compositions of the real maps are the real restrictions of the compositions. -/
theorem realComp_realMap (w : List (Fin N)) {x : ℝ} (hx : (x : ℂ) ∈ nbhd ε) :
    realComp Φ.realMap w x = (Φ.comp w x).re := by
  induction w with
  | nil => rfl
  | cons i w ih =>
    have h : ((Φ.comp w x).re : ℂ) = Φ.comp w x :=
      Complex.ext (by simp) (by simp [Φ.im_comp_ofReal w hx])
    show Φ.realMap i (realComp Φ.realMap w x) = (Φ.f i (Φ.comp w x)).re
    rw [ih, realMap, h]

/-- `|(φ_w)'(x)| = |f_w'(x)|` at the real points of `B_ε`. -/
private theorem abs_deriv_realComp_realMap (w : List (Fin N)) {x : ℝ} (hx : (x : ℂ) ∈ nbhd ε) :
    |deriv (realComp Φ.realMap w) x| = ‖deriv (Φ.comp w) x‖ := by
  have heq : realComp Φ.realMap w =ᶠ[𝓝 x] fun t : ℝ => (Φ.comp w t).re := by
    filter_upwards [(isOpen_setOf_ofReal_mem (isOpen_nbhd ε)).mem_nhds hx] with _ using
      Φ.realComp_realMap w
  rw [heq.deriv_eq, (hasDerivAt_re_ofReal (Φ.differentiableAt_comp w (subset_closure hx))).deriv]
  exact Complex.abs_re_eq_norm.2 (Φ.im_deriv_comp_ofReal w hx)

/-- `|φ_i'(x)| = |f_i'(x)|` at the real points of `B_ε`. -/
private theorem abs_deriv_realMap (i : Fin N) {x : ℝ} (hx : (x : ℂ) ∈ nbhd ε) :
    |deriv (Φ.realMap i) x| = ‖deriv (Φ.f i) x‖ :=
  Φ.abs_deriv_realComp_realMap [i] hx

/-- `sup_{x ∈ I} |f_u(x) - f_v(x)|` is the same for the real maps. -/
private theorem supDist_eq_iSup_realComp (u v : List (Fin N)) :
    Φ.supDist u v = ⨆ x : I, |realComp Φ.realMap u x - realComp Φ.realMap v x| := by
  refine iSup_congr fun x => ?_
  have hx := ofReal_mem_nbhd Φ.ε_pos x.2
  change ‖Φ.comp u x - Φ.comp v x‖ = _
  rw [Φ.comp_ofReal u x.2, Φ.comp_ofReal v x.2, ← Complex.ofReal_sub, Complex.norm_real,
    Real.norm_eq_abs, Φ.realComp_realMap u hx, Φ.realComp_realMap v hx]

/-- `‖f_w'‖ = sup_{x ∈ I} |φ_w'(x)|`. -/
private theorem supDeriv_eq_iSup_realComp (w : List (Fin N)) :
    Φ.supDeriv w = ⨆ x : I, |deriv (realComp Φ.realMap w) x| :=
  iSup_congr fun x => (Φ.abs_deriv_realComp_realMap w (ofReal_mem_nbhd Φ.ε_pos x.2)).symm

/-- An analytic IFS with a non-singleton attractor that satisfies the ESC satisfies the
hypotheses of Rapaport's Theorem 1.2 and Corollary 1.3. -/
private theorem rapaportHyp (hN : 0 < N) (hnd : ¬ ∃ x, Φ.attractor = {x}) (hesc : Φ.ESC) :
    RapaportHyp Φ.realMap where
  mapsTo i x hx := (Φ.inClass i).re_mem_I x hx
  analytic i x hx :=
    ((Φ.differentiableOn_f i).analyticOnNhd (isOpen_nbhd _) _
      (nbhd_subset_two (ofReal_mem_nbhd Φ.ε_pos hx))).re_ofReal
  deriv_pos i x hx := by
    have hx' := ofReal_mem_nbhd Φ.ε_pos hx
    rw [Φ.abs_deriv_realMap i hx']
    exact norm_pos_iff.2 ((Φ.inClass i).deriv_ne_zero _ (subset_closure hx'))
  deriv_lt_one i x hx := by
    have hx' := ofReal_mem_nbhd Φ.ε_pos hx
    rw [Φ.abs_deriv_realMap i hx']
    exact (Φ.inClass i).norm_deriv_lt_one _ (subset_closure hx')
  no_common_fixed_point h := hnd ((Φ.exists_attractor_eq_singleton_iff hN).2 h)
  exp_separated := by
    obtain ⟨c, hc, hfreq⟩ := hesc
    refine ⟨c, hc, hfreq.mono fun n hn u v huv => ?_⟩
    rw [← Φ.supDist_eq_iSup_realComp]
    exact hn u v huv

/-- For a probability measure `μ` on `I`, `∫ log |f_i'| dμ ≤ log c_max`. -/
private theorem dim_integral_le (hN : 0 < N) (i : Fin N) {μ : Measure ℝ}
    [IsProbabilityMeasure μ] (hμ : μ Iᶜ = 0) :
    ∫ x, Real.log |deriv (Φ.realMap i) x| ∂μ ≤ Real.log Φ.cmax := by
  have hb : ∀ᵐ x ∂μ, Real.log Φ.cmin ≤ Real.log |deriv (Φ.realMap i) x| ∧
      Real.log |deriv (Φ.realMap i) x| ≤ Real.log Φ.cmax :=
    (ae_iff.2 hμ).mono fun x hx => by
      have hcl : (x : ℂ) ∈ closure (nbhd ε) := subset_closure (ofReal_mem_nbhd Φ.ε_pos hx)
      have h0 := Φ.cmin_pos hN
      have h1 := Φ.cmin_le_norm_deriv i hcl
      rw [Φ.abs_deriv_realMap i (ofReal_mem_nbhd Φ.ε_pos hx)]
      exact ⟨Real.log_le_log h0 h1, Real.log_le_log (h0.trans_le h1) (Φ.norm_deriv_le_cmax i hcl)⟩
  have hint : Integrable (fun x => Real.log |deriv (Φ.realMap i) x|) μ :=
    Integrable.of_bound (measurable_deriv (Φ.realMap i)).abs.log.aestronglyMeasurable
      (|Real.log Φ.cmin| + |Real.log Φ.cmax|) (hb.mono fun x hx => by
        rw [Real.norm_eq_abs, abs_le]
        constructor <;> linarith [neg_abs_le (Real.log Φ.cmin), le_abs_self (Real.log Φ.cmax),
          abs_nonneg (Real.log Φ.cmin), abs_nonneg (Real.log Φ.cmax)])
  exact (integral_mono_ae hint (integrable_const _) (hb.mono fun _ h => h.2)).trans_eq (by simp)

/-- The Lyapunov exponent of a self-conformal measure satisfies `χ ≥ -log c_max`. -/
theorem neg_log_cmax_le_lyapunov (hN : 0 < N) {p : Fin N → ℝ} (hp : IsProbVec p)
    {μ : Measure ℝ} (hμ : Φ.IsSelfConformal p μ) : -Real.log Φ.cmax ≤ Φ.lyapunov p μ := by
  obtain ⟨hμ1, hμ2, -⟩ := hμ
  rw [lyapunov, Challenge.lyapunov, neg_le_neg_iff]
  exact (Finset.sum_le_sum fun i _ =>
    mul_le_mul_of_nonneg_left (Φ.dim_integral_le hN i hμ2) (hp.1 i).le).trans_eq
    (by rw [← Finset.sum_mul, hp.2, one_mul])

/-- Theorem 1.6 (Rapaport). An analytic IFS whose attractor is not a singleton and which
satisfies the ESC has equality in (1.6). -/
theorem theorem_1_6 (hM : RapaportMeasureStatement) (hS : RapaportSetStatement) (hN : 0 < N)
    (hnd : ¬ ∃ x, Φ.attractor = {x}) (hesc : Φ.ESC) : Φ.DimEquality := by
  have hφ := Φ.rapaportHyp hN hnd hesc
  obtain ⟨s, -, hs⟩ := Φ.exists_pressure_zero hN
  refine ⟨⟨s, hs, ?_⟩, fun p hp μ hμ => ?_⟩
  · apply hS Φ.realMap hφ Φ.attractor ⟨_, mem_range_self fun _ => ⟨0, hN⟩⟩
      (isCompact_range Φ.continuous_natProj) Φ.attractor_subset_I Φ.attractor_eq_iUnion s
    apply (positive_length_tendsto_iff (fun n : ℕ => Real.log (∑ u : Fin n → Fin N,
      (⨆ x : I, |deriv (realComp Φ.realMap (List.ofFn u)) x|) ^ s))).mpr
    refine ((hs s).2 rfl).congr fun n => ?_
    simp only [pressureSum, supDeriv_eq_iSup_realComp]
  · have hpos : 0 < Φ.lyapunov p μ :=
      (neg_pos.mpr (Real.log_neg (Φ.cmax_pos hN) Φ.cmax_lt_one)).trans_le
        (Φ.neg_log_cmax_le_lyapunov hN hp hμ)
    exact (hM Φ.realMap hφ p hp.1 hp.2 μ hμ.1 hμ.2.1 hμ.2.2 hpos.ne').mono
      fun _ hx => (scale_tendsto_iff _ _).mp hx

end IFS

end AnalyticESC
