module

public import RequestProject.Spectrum
public import RequestProject.Rellich

/-!
# Positivity of the first nonzero Neumann eigenvalue (Lemma 3.3)

We deduce `μ_j(Ω) > 0` for `j ≥ 1` from the Poincaré–Wirtinger inequality, which is part of
External theorem E2 ("Sobolev traces, compactness, and coordinates") of the paper:
for a bounded connected Lipschitz domain,
`‖u - |Ω|⁻¹ ∫_Ω u‖_{L²} ≤ C_Ω ‖∇u‖_{L²}`.
We use it in its (equivalent) mean-zero form.
-/

@[expose] public section

open MeasureTheory Filter Topology Set

noncomputable section

namespace PolyaNeumann

/-- Poincaré–Wirtinger with the mean fixed on a positive-measure subset of the domain. -/
theorem poincare_wirtinger {Ω B : Set ℂ} (hb : Bornology.IsBounded Ω)
    (hL : IsLipschitzDomain Ω) (hB : MeasurableSet B) (hBΩ : B ⊆ Ω) (hBpos : volume B ≠ 0) :
    ∃ C : ℝ, 0 < C ∧ ∀ (u : L2 Ω) (g : Fin 2 → L2 Ω), IsWeakGradient Ω u g →
      ∫ w in B, u w = 0 → ‖u‖ ^ 2 ≤ C * ∑ i, ‖g i‖ ^ 2 := by
  haveI : IsFiniteMeasure (volume.restrict Ω) := isFiniteMeasure_restrict.mpr hb.measure_lt_top.ne
  let L := lpIntegralPair ((memLp_const (μ := volume.restrict Ω) (p := 2) (1 : ℂ)).indicator hB)
  have hLapp (u : L2 Ω) : L u = ∫ w in B, u w := by
    dsimp only [L]
    simp_rw [lpIntegralPair_apply, ← indicator_mul_right B (fun z => u z) (fun _ => (1 : ℂ)), mul_one]
    rw [integral_indicator hB, Measure.restrict_restrict hB, inter_eq_left.mpr hBΩ]
  simp_rw [← hLapp]
  by_contra hcon
  push Not at hcon
  have hseq : ∀ n : ℕ, ∃ (u : L2 Ω) (g : Fin 2 → L2 Ω), IsWeakGradient Ω u g ∧
      L u = 0 ∧ ((n : ℝ) + 1) * ∑ i, ‖g i‖ ^ 2 < ‖u‖ ^ 2 :=
    fun n => hcon _ (by positivity)
  choose u g hg hmean hlt using hseq
  have hune : ∀ n, u n ≠ 0 := by
    intro n h
    have := hlt n
    rw [h, norm_zero] at this
    have : 0 ≤ ((n : ℝ) + 1) * ∑ i, ‖g n i‖ ^ 2 := by positivity
    linarith
  have hpos := fun n => norm_pos_iff.mpr (hune n)
  -- normalize
  set v : ℕ → L2 Ω := fun n => ((‖u n‖⁻¹ : ℝ) : ℂ) • u n with hv
  set h : ℕ → Fin 2 → L2 Ω := fun n => ((‖u n‖⁻¹ : ℝ) : ℂ) • g n with hh
  have hvg : ∀ n, IsWeakGradient Ω (v n) (h n) := fun n => (hg n).smul _
  have hvnorm : ∀ n, ‖v n‖ = 1 := by
    intro n
    simp  [hv, norm_smul, Real.norm_eq_abs, abs_inv, abs_norm]
    exact inv_mul_cancel₀ (hpos n).ne'
  have hhsum : ∀ n, ∑ i, ‖h n i‖ ^ 2 < 1 / ((n : ℝ) + 1) := by
    intro n
    have e : ∑ i, ‖h n i‖ ^ 2 = (∑ i, ‖g n i‖ ^ 2) / ‖u n‖ ^ 2 := by
      simp only [hh, Pi.smul_apply, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_inv,
        abs_norm, mul_pow, inv_pow, ← Finset.mul_sum]
      field_simp
    have hp := hpos n
    rw [e, div_lt_div_iff₀ (by positivity) (by positivity)]
    linarith [hlt n]
  have hhle : ∀ n i, ‖h n i‖ ^ 2 ≤ 1 / ((n : ℝ) + 1) := by
    intro n i
    have := Finset.single_le_sum (f := fun i => ‖h n i‖ ^ 2) (fun i _ => by positivity)
      (Finset.mem_univ i)
    linarith [hhsum n]
  have hhC : ∀ n i, ‖h n i‖ ≤ 1 := by
    intro n i
    have h1 := hhle n i
    have h2 : 1 / ((n : ℝ) + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]; simp
    nlinarith [norm_nonneg (h n i)]
  obtain ⟨φ, hφ, V, hV⟩ := rellich_compact hb hL v h hvg 1 (fun n => (hvnorm n).le) hhC
  -- the limit has norm one, zero mean and zero weak gradient
  have hVnorm : ‖V‖ = 1 := by
    have := (continuous_norm.tendsto V).comp hV
    exact tendsto_nhds_unique this (by simp [Function.comp_def, hvnorm])
  have hVmean : L V = 0 := tendsto_nhds_unique ((L.continuous.tendsto V).comp hV)
    (by simp [Function.comp_def, hv, hmean])
  have hhlim : ∀ i, Tendsto (fun n => h (φ n) i) atTop (𝓝 ((0 : Fin 2 → L2 Ω) i)) := by
    intro i
    rw [Pi.zero_apply, tendsto_zero_iff_norm_tendsto_zero]
    have hsq : Tendsto (fun n => ‖h (φ n) i‖ ^ 2) atTop (𝓝 0) := by
      have hlim : Tendsto (fun n : ℕ => 1 / ((φ n : ℝ) + 1)) atTop (𝓝 0) := by
        have := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).comp hφ.tendsto_atTop
        assumption
      exact squeeze_zero (fun n => by positivity) (fun n => hhle (φ n) i) hlim
    have := (Real.continuous_sqrt.tendsto 0).comp hsq
    simpa [Function.comp_def, Real.sqrt_sq (norm_nonneg _)] using this
  have hVg :=
    isWeakGradient_of_tendsto (fun n => hvg (φ n)) hV hhlim
  -- so the limit is constant, hence zero
  obtain ⟨c, hc⟩ := ae_const_of_weakGradient_zero hL.1 V hVg
  have hvol := ENNReal.toReal_pos hBpos ((measure_mono hBΩ).trans_lt hb.measure_lt_top).ne
  have hc0 : c = 0 := by
    rw [hLapp, integral_congr_ae (hc.filter_mono (ae_mono
      (Measure.restrict_mono_set volume hBΩ)))] at hVmean
    simpa [Measure.real, hvol.ne', smul_eq_mul] using hVmean
  have hV0 : V = 0 := by
    rw [Lp.eq_zero_iff_ae_eq_zero]
    filter_upwards [hc] with w hw
    simp [hw, hc0]
  rw [hV0, norm_zero] at hVnorm
  exact zero_ne_one hVnorm




end PolyaNeumann

end
