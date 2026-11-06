module

public import AnalyticESC.Dimension.Pressure

public section

set_option hygiene false
local notation "𝕹" => Φ.realMap i
local notation "𝕸" => ofReal_mem_nbhd Φ.ε_pos hx
local notation "𝕷" => realComp Φ.realMap w
/-!
# Theorem 1.6

Rapaport's theorem, as stated in Theorem 1.6 for the class `𝔖_N`: an analytic IFS with a
non-singleton attractor that satisfies the ESC has equality in (1.6). It follows from Rapaport's
Theorem 1.2 and Corollary 1.3 (`RapaportMeasureStatement`, `RapaportSetStatement`), stated for real
analytic maps of `I`, and from the remark after Theorem 1.6: the attractor is a singleton exactly
when the maps have a common fixed point.
-/

namespace AnalyticESC

variable {x : ℝ}

open Set Filter Topology MeasureTheory

namespace IFS

variable (Φ : IFS N ε) (w : 𝔚 N) (ω : 𝔖 N) {p : Fin N → ℝ}

/-! ### The natural projection and the attractor -/

/-- `π(ω) = f_{ω₀}(π(σω))`, where `σ` is the left shift. -/
theorem natProj_eq_realMap :
    Φ.natProj ω = Φ.realMap (ω 0) (Φ.natProj fun j => ω (j + 1)) := by
  rw [Φ.natProj_eq_comp_prefix ω 1]
  aesop

/-- `|π(ω) - f_{ω₁ ⋯ ωₙ}(0)| ≤ c_max^n`. -/
theorem abs_natProj_sub_le n :
    |Φ.natProj ω - (Φ.comp (List.ofFn fun k : Fin n => ω k) 0).re| ≤ Φ.cmax ^ n := by
  have hπ : Φ.natProj (fun j => ω (j + n)) ∈ I := Φ.attractor_subset_I ⟨_, rfl⟩
  have h := Φ.abs_re_comp_sub_le (List.ofFn fun k : Fin n => ω k) hπ
    zero_mem_I
  rwa [List.length_ofFn, Complex.ofReal_zero, ← Φ.natProj_eq_comp_prefix] at h

/-- The natural projection is continuous. -/
theorem continuous_natProj : Continuous Φ.natProj := by
  refine TendstoUniformly.continuous
    (F := fun n ω => (Φ.comp (List.ofFn fun k : Fin n => ω k) 0).re) (p := atTop) ?_
    (Frequently.of_forall fun n => ?_)
  · rw [Metric.tendstoUniformly_iff]
    intro δ hδ
    filter_upwards [(tendsto_pow_atTop_nhds_zero_of_lt_one Φ.cmax_nonneg
      Φ.cmax_lt_one).eventually (gt_mem_nhds hδ)] with n hn ω
    exact (Φ.abs_natProj_sub_le ω n).trans_lt hn
  · fun_prop

/-- The attractor is compact. -/
theorem isCompact_attractor : IsCompact Φ.attractor := isCompact_range Φ.continuous_natProj

/-- The attractor is nonempty. -/
theorem attractor_nonempty (hN : 0 < N) : Φ.attractor.Nonempty :=
  ⟨_, mem_range_self (fun _ => (⟨0, hN⟩ : Fin N))⟩

/-- The attractor is invariant: `Λ = ⋃_i f_i(Λ)`. -/
theorem attractor_eq_iUnion : Φ.attractor = ⋃ i, Φ.realMap i '' Φ.attractor := by
  ext x
  simp
  constructor
  · rintro ⟨ω, rfl⟩
    exact ⟨ω 0, _, ⟨_, rfl⟩, (Φ.natProj_eq_realMap ω).symm⟩
  · rintro ⟨i, _, ⟨ω, rfl⟩, rfl⟩
    let ω' : 𝔖 N := fun j => match j with
      | 0 => i
      | j + 1 => ω j
    exact ⟨ω', Φ.natProj_eq_realMap ω'⟩

/-- The remark after Theorem 1.6: the attractor is a singleton exactly when the maps have a
common fixed point in `I`. -/
theorem exists_attractor_eq_singleton_iff (hN : 0 < N) :
    (∃ x, Φ.attractor = {x}) ↔ ∃ x ∈ I, ∀ i, Φ.realMap i x = x := by
  constructor
  · rintro ⟨x, hx⟩
    refine ⟨x, Φ.attractor_subset_I (by simp_all), fun i => ?_⟩
    have h1 : Φ.natProj (fun _ => i) = x := by
      have h : Φ.natProj (fun _ => i) ∈ Φ.attractor := by tauto
      simp_all
    have h2 : Φ.natProj (fun _ => i) = Φ.realMap i (Φ.natProj fun _ => i) :=
      Φ.natProj_eq_realMap _
    grind
  · rintro ⟨p, hp, hfix⟩
    have hf : ∀ i, Φ.f i p = p := fun i =>
      Complex.ext (hfix i) (by simpa using Φ.im_f_ofReal i (nbhd_subset_two (ofReal_mem_nbhd Φ.ε_pos hp)))
    have hc : ∀ w, Φ.comp w p = p := by
      intro w
      induction w with
      | nil => rfl
      | cons i w ih => rw [comp_cons, Function.comp_apply, ih, hf]
    have hπ : ∀ ω, Φ.natProj ω = p := by
      intro ω
      have h0 : |Φ.natProj ω - p| ≤ 0 :=
        ge_of_tendsto' (tendsto_pow_atTop_nhds_zero_of_lt_one Φ.cmax_nonneg Φ.cmax_lt_one) (by intro n; have hπ : Φ.natProj (fun j => ω (j + n)) ∈ I := Φ.attractor_subset_I ⟨_, rfl⟩; have h := Φ.abs_re_comp_sub_le (List.ofFn fun k : Fin n => ω k) hπ hp; rwa [List.length_ofFn, hc, Complex.ofReal_re, ← Φ.natProj_eq_comp_prefix] at h)
      grind
    refine ⟨p, ?_⟩
    ext x
    constructor
    · rintro ⟨ω, rfl⟩
      simp_all
    · rintro rfl
      exact ⟨fun _ => ⟨0, hN⟩, hπ _⟩

/-! ### The real maps in Rapaport's setting -/

section
variable (hx : (x : ℂ) ∈ nbhd ε)
include hx

/-- The compositions of the real maps are the real restrictions of the compositions. -/
theorem realComp_realMap :
    realComp Φ.realMap w x = (Φ.comp w x).re := by
  induction w with
  | nil => rfl
  | cons i w ih =>
    have h : ((Φ.comp w x).re : ℂ) = Φ.comp w x :=
      Complex.ext (by simp) (by simp [Φ.im_comp_ofReal w hx])
    show Φ.realMap i (realComp Φ.realMap w x) = (Φ.f i (Φ.comp w x)).re
    rw [ih, realMap, h]

/-- `(φ_w)'(x) = f_w'(x)` at the real points of `B_ε`. -/
theorem deriv_realComp_realMap :
    deriv 𝕷 x = (𝔡ᶜ Φ w x).re := by
  have heq : realComp Φ.realMap w =ᶠ[𝓝 x] fun t => (Φ.comp w t).re := by
    filter_upwards [(isOpen_setOf_ofReal_mem isOpen_nbhd).mem_nhds hx] with t ht
    exact Φ.realComp_realMap w ht
  exact heq.deriv_eq ▸ (hasDerivAt_re_ofReal (Φ.differentiableAt_comp w (subset_closure hx))).deriv

/-- `|(φ_w)'(x)| = |f_w'(x)|` at the real points of `B_ε`. -/
theorem abs_deriv_realComp_realMap :
    |deriv 𝕷 x| = ‖𝔡ᶜ Φ w x‖ := by
  exact Φ.deriv_realComp_realMap w hx ▸ Complex.abs_re_eq_norm.2 (Φ.im_deriv_comp_ofReal w hx)

end

theorem abs_deriv_realMap i (hx : (x : ℂ) ∈ nbhd ε) :
    |deriv 𝕹 x| = ‖𝔡 Φ i x‖ :=
  Φ.abs_deriv_realComp_realMap [i] hx

/-- `sup_{x ∈ I} |f_u(x) - f_v(x)|` is the same for the real maps. -/
theorem supDist_eq_iSup_realComp u v :
    Φ.supDist u v = ⨆ x : I, |realComp Φ.realMap u x - realComp Φ.realMap v x| := by
  refine iSup_congr fun x => ?_
  have hx := ofReal_mem_nbhd Φ.ε_pos x.2
  rw [Φ.realComp_realMap u hx, Φ.realComp_realMap v hx]
  conv_lhs => rw [Φ.comp_ofReal u x.2, Φ.comp_ofReal v x.2]
  norm_cast

/-- `‖f_w'‖ = sup_{x ∈ I} |φ_w'(x)|`. -/
theorem supDeriv_eq_iSup_realComp :
    Φ.supDeriv w = ⨆ x : I, |deriv 𝕷 x| :=
  iSup_congr fun x => (Φ.abs_deriv_realComp_realMap w (ofReal_mem_nbhd Φ.ε_pos x.2)).symm

variable (hN : 0 < N)
include hN

/-- An analytic IFS with a non-singleton attractor that satisfies the ESC satisfies the
hypotheses of Rapaport's Theorem 1.2 and Corollary 1.3. -/
theorem rapaportHyp (hnd : ¬ ∃ x, Φ.attractor = {x}) (hesc : Φ.ESC) :
    RapaportHyp Φ.realMap where
  mapsTo i x hx := (Φ.inClass i).re_mem_I x hx
  analytic i x hx :=
    ((Φ.differentiableOn_f i).analyticOnNhd isOpen_nbhd _
      (Φ.ofReal_mem_nbhd2 hx)).re_ofReal
  deriv_pos i x hx := by
    exact Φ.abs_deriv_realMap i 𝕸 ▸ norm_pos_iff.2 ((Φ.inClass i).deriv_ne_zero _ (Φ.ofReal_mem_cl hx))
  deriv_lt_one i x hx := by
    exact Φ.abs_deriv_realMap i 𝕸 ▸ (Φ.inClass i).norm_deriv_lt_one _ (Φ.ofReal_mem_cl hx)
  no_common_fixed_point h := hnd ((Φ.exists_attractor_eq_singleton_iff hN).2 h)
  exp_separated := by
    obtain ⟨c, hc, hfreq⟩ := hesc
    refine ⟨c, hc, hfreq.mono fun n hn u v huv => ?_⟩
    rw [← Φ.supDist_eq_iSup_realComp]
    grind

local notation "𝔏" => Real.log |deriv 𝕹 x|
local notation "𝔐" => Real.log Φ.cmin ≤ 𝔏 ∧ 𝔏 ≤ Real.log Φ.cmax

/-- `log c_min ≤ log |f_i'(x)| ≤ log c_max` for `x ∈ I`. -/
theorem dim_log_abs_deriv_realMap_mem i (hx : x ∈ I) :
    𝔐 := by
  have hcl := Φ.ofReal_mem_cl hx
  have h1 := Φ.cmin_le_norm_deriv i hcl
  have h2 := Φ.norm_deriv_le_cmax i hcl
  have h0 := Φ.cmin_pos hN
  rw [Φ.abs_deriv_realMap i 𝕸]
  bound

/-- For a probability measure `μ` on `I`, `∫ log |f_i'| dμ ≤ log c_max`. -/
theorem dim_integral_le i {μ : Measure ℝ}
    [IsProbabilityMeasure μ] (hμ : μ Iᶜ = 0) :
    ∫ x, 𝔏 ∂μ ≤ Real.log Φ.cmax := by
  have hb : ∀ᵐ x ∂μ, 𝔐 :=
    (ae_iff.2 hμ).mono fun x hx => Φ.dim_log_abs_deriv_realMap_mem hN i hx
  have hm : AEStronglyMeasurable (fun x => 𝔏) μ :=
    (measurable_deriv 𝕹).abs.log.aestronglyMeasurable
  have hint : Integrable (fun x => 𝔏) μ := by
    refine Integrable.of_bound hm (|Real.log Φ.cmin| + |Real.log Φ.cmax|)
      (hb.mono fun x hx => ?_)
    rw [Real.norm_eq_abs, abs_le]
    grind
  calc ∫ x, 𝔏 ∂μ ≤ ∫ _x, Real.log Φ.cmax ∂μ :=
        integral_mono_ae hint (integrable_const _) (hb.mono fun x hx => hx.2)
    _ = Real.log Φ.cmax := by simp

/-- The Lyapunov exponent of a self-conformal measure satisfies `χ ≥ -log c_max`. -/
theorem neg_log_cmax_le_lyapunov (hp : IsProbVec p)
    (hμ : Φ.IsSelfConformal p μ) : -Real.log Φ.cmax ≤ Φ.lyapunov p μ := by
  obtain ⟨hμ1, hμ2, -⟩ := hμ
  rw [lyapunov, neg_le_neg_iff]
  calc ∑ i, p i * ∫ x, 𝔏 ∂μ ≤ ∑ i, p i * Real.log Φ.cmax :=
        Finset.sum_le_sum fun i _ =>
          mul_le_mul_of_nonneg_left (Φ.dim_integral_le hN i hμ2) (hp.1 i).le
    _ = Real.log Φ.cmax := by rw [← Finset.sum_mul, hp.2, one_mul]

/-- The Lyapunov exponent is positive, so its reciprocal is well defined. -/
theorem lyapunov_pos (hp : IsProbVec p)
    (hμ : Φ.IsSelfConformal p μ) : 0 < Φ.lyapunov p μ :=
  (neg_pos.mpr (Real.log_neg (Φ.cmax_pos hN)
    Φ.cmax_lt_one)).trans_le (Φ.neg_log_cmax_le_lyapunov hN hp hμ)

/-- Theorem 1.6 (Rapaport). An analytic IFS whose attractor is not a singleton and which
satisfies the ESC has equality in (1.6). -/
theorem theorem_1_6 (hM : RapaportMeasureStatement) (hS : RapaportSetStatement)
    (hnd : ¬ ∃ x, Φ.attractor = {x}) (hesc : Φ.ESC) : Φ.DimEquality := by
  have hφ := Φ.rapaportHyp hN hnd hesc
  obtain ⟨s, hs⟩ := Φ.exists_pressure_zero hN
  refine ⟨⟨s, hs, ?_⟩, ?_⟩
  · apply hS Φ.realMap hφ Φ.attractor (Φ.attractor_nonempty hN) Φ.isCompact_attractor
      Φ.attractor_subset_I Φ.attractor_eq_iUnion s
    apply (positive_length_tendsto_iff (fun n => Real.log (∑ u : Fin n → Fin N,
      (⨆ x : I, |deriv (realComp Φ.realMap (List.ofFn u)) x|) ^ s))).mpr
    refine ((hs s).2 rfl).congr fun n => ?_
    simp [pressureSum, supDeriv_eq_iSup_realComp]
  · intro p hp μ hμ
    filter_upwards [hM Φ.realMap hφ p hp.1 hp.2 μ hμ.1 hμ.2.1 hμ.2.2 (Φ.lyapunov_pos hN hp hμ).ne'] with x hx
    exact (scale_tendsto_iff _ _).mp hx

end IFS

end AnalyticESC
