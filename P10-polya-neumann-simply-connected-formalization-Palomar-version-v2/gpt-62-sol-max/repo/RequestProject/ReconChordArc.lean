module

public import RequestProject.ReconBasic
public import RequestProject.BoundaryChart
public import RequestProject.ArcLength

/-!
# Lipschitz extension of boundary traces

For a bounded Lipschitz domain `Ω` with boundary parametrization `γ`, the parametrization is
bi-Lipschitz onto `∂Ω` (with respect to the distance on the circle, `chord_arc`), so every
closed Lipschitz function `h` on `[0, 2π]` is the trace `V ∘ γ` of a Lipschitz compactly
supported `V : ℂ → ℂ` (`exists_lipschitz_extension_of_trace`).

The chord-arc estimate is proved locally in a boundary chart: there the boundary is a Lipschitz
graph, the abscissa `x(s)` of `γ(s)` is strictly monotone, and the constant speed of `γ`
together with the cone condition `|γ'| ≤ (1 + K)|x'|` gives `|x'| ≥ c₀/(1 + K)`. A compactness
argument makes the estimate global.
-/

@[expose] public section

open MeasureTheory Set Filter Metric Topology
open scoped ComplexConjugate Real

noncomputable section

namespace PolyaNeumann

variable {Ω : Set ℂ} {γ : ℝ → ℂ}

section

variable (hγ : IsBoundaryParam Ω γ)
include hγ

lemma IsBoundaryParam.mem_frontier  (s : ℝ) : γ s ∈ frontier Ω := by
  have h2π : (0 : ℝ) < 2 * π := by positivity
  have hm := toIcoMod_mem_Ico h2π 0 s
  have he : γ (toIcoMod h2π 0 s) = γ s := by
    rw [toIcoMod, hγ.periodic.sub_zsmul_eq]
  rw [← he, ← hγ.image]
  grind

lemma IsBoundaryParam.eq_of_eq  {s s' : ℝ} (hss : |s - s'| < 2 * π)
    (he : γ s = γ s') : s = s' := by
  have h2π : (0 : ℝ) < 2 * π := by positivity
  have hm := toIcoMod_mem_Ico h2π 0 s
  have hm' := toIcoMod_mem_Ico h2π 0 s'
  have e1 : γ (toIcoMod h2π 0 s) = γ s := by rw [toIcoMod, hγ.periodic.sub_zsmul_eq]
  have e2 : γ (toIcoMod h2π 0 s') = γ s' := by rw [toIcoMod, hγ.periodic.sub_zsmul_eq]
  have heq : toIcoMod h2π 0 s = toIcoMod h2π 0 s' :=
    hγ.injOn (by simp_all) (by simp_all) (by simp_all)
  obtain ⟨n, hn⟩ := (toIcoMod_eq_toIcoMod h2π).mp heq
  rw [zsmul_eq_mul] at hn
  have hlt : |(n : ℝ)| < 1 := by
    have : |(n : ℝ) * (2 * π)| < 2 * π := by grind
    simp_all
  have hn0 : n = 0 := by
    have : |n| < 1 := by exact_mod_cast hlt
    simp_all
  rw [hn0] at hn
  grind

end

/-- **Lower bound in a cone.** If, on an interval, a constant-speed Lipschitz curve satisfies the
cone condition `‖γ s - γ s'‖ ≤ L |Re(c(γ s - γ s'))|` and `Re(c γ)` is strictly increasing, then
`Re(c γ)` grows at least at rate `c₀ / L`. -/
lemma lower_bound_of_cone {Kγ : NNReal} (hK : LipschitzWith Kγ γ) {a b : ℝ} {c : ℂ} {L c0 : ℝ}
    (hL : 0 < L) (hspeed : ∀ᵐ θ, ‖deriv γ θ‖ = c0)
    (hcone : ∀ s ∈ Ioo a b, ∀ s' ∈ Ioo a b, ‖γ s - γ s'‖ ≤ L * |(c * (γ s - γ s')).re|)
    (hmono : StrictMonoOn (fun s => (c * γ s).re) (Ioo a b)) {s s' : ℝ} (hs : s ∈ Ioo a b)
    (hs' : s' ∈ Ioo a b) (hss : s ≤ s') :
    c0 / L * (s' - s) ≤ (c * (γ s' - γ s)).re := by
  have hae : ∀ᵐ u, u ∈ Ioo a b → c0 / L ≤ (c * deriv γ u).re := by
    filter_upwards [hK.ae_differentiableAt, hspeed] with u hu hspeed hmem
    have hev : ∀ᶠ t in 𝓝[≠] (0 : ℝ), u + t ∈ Ioo a b := by
      have ht : Tendsto (fun t : ℝ => u + t) (𝓝 0) (𝓝 u) := by
        simpa using (continuous_const_add u).tendsto 0
      exact nhdsWithin_le_nhds (ht (isOpen_Ioo.mem_nhds hmem))
    have hcre : Continuous fun v : ℂ => (c * v).re := by fun_prop
    have hbnd : ‖deriv γ u‖ ≤ L * |(c * deriv γ u).re| := by
      refine (isClosed_le continuous_norm (continuous_const.mul hcre.abs)).mem_of_tendsto
        hu.hasDerivAt.tendsto_slope_zero ?_
      filter_upwards [hev] with t ht
      show ‖t⁻¹ • (γ (u + t) - γ u)‖ ≤ L * |(c * (t⁻¹ • (γ (u + t) - γ u))).re|
      rw [norm_smul, Complex.real_smul, mul_left_comm, Complex.re_ofReal_mul,
        abs_mul, Real.norm_eq_abs]
      linarith [mul_le_mul_of_nonneg_left (hcone _ ht u hmem) (abs_nonneg t⁻¹)]
    have hd : deriv (fun s => (c * γ s).re) u = (c * deriv γ u).re :=
      (Complex.reCLM.hasFDerivAt.comp_hasDerivAt u (hu.hasDerivAt.const_mul c)).deriv
    have hpos := hmono.monotoneOn.derivWithin_nonneg (x := u)
    rw [derivWithin_of_isOpen isOpen_Ioo hmem, hd] at hpos
    rw [hspeed, abs_of_nonneg hpos] at hbnd
    rw [div_le_iff₀ hL]
    linarith
  have hi := (intervalIntegrable_of_bounded (measurable_deriv γ).aestronglyMeasurable
    (norm_deriv_le_of_lipschitzWith hK) s s').const_mul c
  have hd := Complex.reCLM.intervalIntegral_comp_comm hi
  rw [intervalIntegral.integral_const_mul, integral_deriv_of_lipschitz hK] at hd
  change (∫ x in s..s', (c * deriv γ x).re) = (c * (γ s' - γ s)).re at hd
  rw [← hd, ← show (∫ _ in s..s', c0 / L) = c0 / L * (s' - s) by
    rw [intervalIntegral.integral_const, smul_eq_mul]; ring]
  refine intervalIntegral.integral_mono_ae_restrict hss intervalIntegrable_const
    ⟨Complex.reCLM.integrable_comp hi.1, Complex.reCLM.integrable_comp hi.2⟩ ?_
  rw [EventuallyLE, ae_restrict_iff' measurableSet_Icc]
  filter_upwards [hae] with _
  grind

/-- On a small parameter interval the curve has an increasing linear
coordinate, with its slope bounded below. -/
lemma local_boundary_coordinate (hL : IsLipschitzDomain Ω) (hγ : IsBoundaryParam Ω γ) (θ₀ : ℝ) :
    ∃ ε > 0, ε ≤ π / 2 ∧ ∃ c : ℂ, ‖c‖ = 1 ∧ ∃ k > 0,
      ∀ s ∈ Ioo (θ₀ - ε) (θ₀ + ε), ∀ t ∈ Ioo (θ₀ - ε) (θ₀ + ε), s ≤ t →
        k * (t - s) ≤ (c * (γ t - γ s)).re := by
  obtain ⟨Kγ, hKγ⟩ := hγ.lipschitz
  obtain ⟨c0, hc0, hspeed⟩ := hγ.const_speed
  have hΩo := hL.1.1
  obtain ⟨c, r, h, K, f, hch⟩ := hL.exists_chart (hγ.mem_frontier θ₀)
  have hc := hch.1
  have hbox : γ ⁻¹' chartBox (γ θ₀) c r h ∈ 𝓝 θ₀ :=
    hKγ.continuous.continuousAt.preimage_mem_nhds ((isOpen_chartBox _ _ _ _).mem_nhds
      ⟨by simp [hch.2.1], by simp [hch.2.2.1]⟩)
  obtain ⟨ε0, hε0, hball⟩ := Metric.mem_nhds_iff.mp hbox
  set ε := min ε0 (π / 2) with hε
  have hεpos : 0 < ε := lt_min hε0 (by positivity)
  have hε1 : ε ≤ ε0 := min_le_left _ _
  have hε2 : ε ≤ π / 2 := min_le_right _ _
  set U := Ioo (θ₀ - ε) (θ₀ + ε) with hUdef
  have hU : ∀ s ∈ U, γ s ∈ chartBox (γ θ₀) c r h := fun s hs => hball (by grind [mem_ball, Real.dist_eq, abs_lt])
  have hcone : ∀ s ∈ U, ∀ s' ∈ U, ‖γ s - γ s'‖ ≤ (1 + K) * |(c * (γ s - γ s')).re| := by
    intro s hs s' hs'
    have := norm_sub_le_of_frontier hΩo hch (hγ.mem_frontier s) (hγ.mem_frontier s')
      (hU s hs) (hU s' hs')
    have e : (c * (γ s - γ θ₀)).re - (c * (γ s' - γ θ₀)).re = (c * (γ s - γ s')).re := by
      simp only [mul_sub, Complex.sub_re]; ring
    rwa [e] at this
  have hdist : ∀ s ∈ U, ∀ s' ∈ U, |s - s'| < 2 * π := fun s hs s' hs' => by grind
  have hinj : InjOn (fun s => (c * γ s).re) U := by
    intro s hs s' hs' he
    have hre : (c * (γ s - γ θ₀)).re = (c * (γ s' - γ θ₀)).re := by
      simp only [mul_sub, Complex.sub_re]
      tauto
    exact hγ.eq_of_eq (hdist s hs s' hs') (eq_of_frontier_of_re_eq hΩo hch (hγ.mem_frontier s)
      (hγ.mem_frontier s') (hU s hs) (hU s' hs') hre)
  have hcont : ContinuousOn (fun s => (c * γ s).re) U :=
    (Complex.continuous_re.comp (continuous_const.mul hKγ.continuous)).continuousOn
  have hK1 : (0 : ℝ) < 1 + K := by positivity
  refine ⟨ε, hεpos, hε2, ?_⟩
  have key (c' : ℂ) (hc' : ‖c'‖ = 1) (hcone' : ∀ s ∈ U, ∀ t ∈ U,
      ‖γ s - γ t‖ ≤ (1 + K) * |(c' * (γ s - γ t)).re|)
      (hm : StrictMonoOn (fun s => (c' * γ s).re) U) :
      ∃ d : ℂ, ‖d‖ = 1 ∧ ∃ k > 0, ∀ s ∈ U, ∀ t ∈ U,
        s ≤ t → k * (t - s) ≤ (d * (γ t - γ s)).re := 
    ⟨c', hc', c0 / (1 + K), div_pos hc0 hK1,
      fun _ hs _ ht hst => lower_bound_of_cone hKγ hK1 hspeed hcone' hm hs ht hst⟩
  rcases hcont.strictMonoOn_of_injOn_Ioo (by linarith) hinj with hm | hm
  · exact key c hc hcone hm
  · refine key (-c) (by simpa) (fun s hs t ht => ?_) (fun s hs t ht hst => ?_)
    · simpa only [neg_mul, Complex.neg_re, abs_neg] using hcone s hs t ht
    · simpa only [neg_mul, Complex.neg_re, neg_lt_neg_iff] using hm hs ht hst

/-- **Local chord-arc estimate.** -/
lemma local_chord_arc (hL : IsLipschitzDomain Ω) (hγ : IsBoundaryParam Ω γ) (θ₀ : ℝ) :
    ∃ ε > 0, ∃ c1 > 0, ∀ s ∈ Ioo (θ₀ - ε) (θ₀ + ε), ∀ s' ∈ Ioo (θ₀ - ε) (θ₀ + ε),
      c1 * |s - s'| ≤ ‖γ s - γ s'‖ := by
  obtain ⟨ε, hε, -, c, hc, k, hk, h⟩ := local_boundary_coordinate hL hγ θ₀
  have hle (z : ℂ) : (c * z).re ≤ ‖z‖ := by simpa [norm_mul, hc] using Complex.re_le_norm (c * z)
  refine ⟨ε, hε, k, hk, fun s hs t ht => ?_⟩
  rcases le_total s t with hst | hts
  · rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr hst), norm_sub_rev]
    exact (h s hs t ht hst).trans (hle _)
  · rw [abs_of_nonneg (sub_nonneg.mpr hts)]
    exact (h t ht s hs hts).trans (hle _)

/-- The distance on the circle `ℝ / 2πℤ`, for parameters in `[0, 2π]`. -/
def circDist (θ θ' : ℝ) : ℝ := min |θ - θ'| (2 * π - |θ - θ'|)

/-- **Chord-arc estimate.** The boundary parametrization is bi-Lipschitz from the circle onto
`∂Ω`. -/
theorem chord_arc (hL : IsLipschitzDomain Ω) (hγ : IsBoundaryParam Ω γ) :
    ∃ c > 0, ∀ θ ∈ Icc 0 (2 * π), ∀ θ' ∈ Icc 0 (2 * π), c * circDist θ θ' ≤ ‖γ θ - γ θ'‖ := by
  obtain ⟨Kγ, hKγ⟩ := hγ.lipschitz
  have h2π : (0 : ℝ) < 2 * π := by positivity
  choose ε hε c1 hc1 hloc using local_chord_arc hL hγ
  set U : ℝ → Set ℝ := fun θ₀ => Ioo (θ₀ - ε θ₀) (θ₀ + ε θ₀) with hUdef
  obtain ⟨t, -, hcov⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 2 * π)).elim_nhds_subcover U
    (fun x _ => Ioo_mem_nhds (by simp_all) (by simp_all))
  have hcov' : Icc (0 : ℝ) (2 * π) ⊆ ⋃ i : t, U i := by
    intro x hx
    obtain ⟨i, hi, hx⟩ := mem_iUnion₂.mp (hcov hx)
    exact mem_iUnion.mpr ⟨⟨i, hi⟩, hx⟩
  obtain ⟨δ, hδ, hleb⟩ := lebesgue_number_lemma_of_metric isCompact_Icc
    (fun i : t => isOpen_Ioo) hcov'
  have htne : t.Nonempty := by
    obtain ⟨i, -⟩ := hleb 0 ⟨le_rfl, h2π.le⟩
    exact ⟨i, i.2⟩
  set cmin := t.inf' htne c1 with hcmin
  have hcmin0 : 0 < cmin := (Finset.lt_inf'_iff _).mpr fun i _ => hc1 i
  -- near pairs
  have hnear : ∀ θ ∈ Icc (0 : ℝ) (2 * π), ∀ θ'', |θ - θ''| < δ →
      cmin * |θ - θ''| ≤ ‖γ θ - γ θ''‖ := by
    intro θ hθ θ'' hθ''
    obtain ⟨i, hi⟩ := hleb θ hθ
    have h1 := hi (mem_ball_self hδ)
    have h2 := hi (by rw [mem_ball, Real.dist_eq, abs_sub_comm]; assumption)
    exact (mul_le_mul_of_nonneg_right (Finset.inf'_le _ i.2) (abs_nonneg _)).trans
      (hloc i θ h1 θ'' h2)
  -- far pairs
  have hcd : Continuous fun q : ℝ × ℝ => circDist q.1 q.2 := by
    unfold circDist; fun_prop
  set P := (Icc (0 : ℝ) (2 * π) ×ˢ Icc (0 : ℝ) (2 * π)) ∩ {q | δ ≤ circDist q.1 q.2} with hP
  have hPc : IsCompact P :=
    (isCompact_Icc.prod isCompact_Icc).inter_right (isClosed_le continuous_const hcd)
  have hcg : Continuous fun q : ℝ × ℝ => ‖γ q.1 - γ q.2‖ := by
    have := hKγ.continuous; fun_prop
  obtain ⟨m, hm0, hm⟩ : ∃ m > 0, ∀ q ∈ P, m ≤ ‖γ q.1 - γ q.2‖ := by
    rcases P.eq_empty_or_nonempty with he | hne
    grind
    obtain ⟨q, hq, hqmin⟩ := hPc.exists_isMinOn hne hcg.continuousOn
    refine ⟨‖γ q.1 - γ q.2‖, ?_, fun q' hq' => hqmin hq'⟩
    rcases (norm_nonneg (γ q.1 - γ q.2)).lt_or_eq with hpos | hzero
    assumption
    exfalso
    have he := sub_eq_zero.mp (norm_eq_zero.mp hzero.symm)
    obtain ⟨⟨hq1, hq2⟩, hqδ⟩ := hq
    simp only [mem_setOf_eq, circDist] at hqδ
    have habs : |q.1 - q.2| ≤ 2 * π := by
      grind
    rcases habs.lt_or_eq with hlt | heq
    · have := hγ.eq_of_eq hlt he
      rw [this, sub_self, abs_zero] at hqδ
      grind
    grind
  refine ⟨min cmin (m / (2 * π)), lt_min hcmin0 (by positivity), fun θ hθ θ' hθ' => ?_⟩
  have hd0 : 0 ≤ circDist θ θ' := by
    unfold circDist
    refine le_min (abs_nonneg _) ?_
    grind
  have hd2 : circDist θ θ' ≤ 2 * π := by
    unfold circDist
    simp
  by_cases hfar : δ ≤ circDist θ θ'
  · calc min cmin (m / (2 * π)) * circDist θ θ' ≤ m / (2 * π) * (2 * π) :=
          mul_le_mul (min_le_right _ _) hd2 hd0 (by positivity)
      _ = m := by field_simp
      _ ≤ ‖γ θ - γ θ'‖ := hm (θ, θ') ⟨⟨hθ, hθ'⟩, hfar⟩
  · push_neg at hfar
    unfold circDist at hfar ⊢
    rcases min_lt_iff.mp hfar with h1 | h1
    · calc min cmin (m / (2 * π)) * min |θ - θ'| (2 * π - |θ - θ'|) ≤ cmin * |θ - θ'| :=
            mul_le_mul (min_le_left _ _) (min_le_left _ _) (le_min (abs_nonneg _) (by grind))
              hcmin0.le
        _ ≤ ‖γ θ - γ θ'‖ := hnear θ hθ θ' h1
    · obtain ⟨θ'', hγeq, habs⟩ : ∃ θ'', γ θ'' = γ θ' ∧ |θ - θ''| = 2 * π - |θ - θ'| := by
        rcases le_total θ θ' with hle | hle
        · refine ⟨θ' - 2 * π, hγ.periodic.sub_eq θ', ?_⟩
          rw [abs_of_nonneg (by linarith [hθ.1, hθ'.2]), abs_of_nonpos (by linarith)]
          ring
        · refine ⟨θ' + 2 * π, hγ.periodic θ', ?_⟩
          rw [abs_of_nonpos (by linarith [hθ.2, hθ'.1]), abs_of_nonneg (by linarith)]
          ring
      have := hnear θ hθ θ'' (by rw [habs]; assumption)
      rw [hγeq, habs] at this
      calc min cmin (m / (2 * π)) * min |θ - θ'| (2 * π - |θ - θ'|)
          ≤ cmin * (2 * π - |θ - θ'|) :=
            mul_le_mul (min_le_left _ _) (min_le_right _ _) (le_min (abs_nonneg _) (by grind))
              hcmin0.le
        _ ≤ ‖γ θ - γ θ'‖ := this

/-- A closed Lipschitz function on `[0, 2π]` is Lipschitz for the circle distance. -/
lemma norm_sub_le_circDist {h : ℝ → ℂ} {K : NNReal} (hK : LipschitzOnWith K h (Icc 0 (2 * π)))
    (hper : h (2 * π) = h 0) {θ θ' : ℝ} (hθ : θ ∈ Icc 0 (2 * π)) (hθ' : θ' ∈ Icc 0 (2 * π)) :
    ‖h θ - h θ'‖ ≤ K * circDist θ θ' := by
  wlog hle : θ ≤ θ' generalizing θ θ'
  · simpa only [norm_sub_rev (h θ') (h θ), circDist, abs_sub_comm θ' θ] using
      this hθ' hθ (le_of_not_ge hle)
  have hp := Real.two_pi_pos.le
  have hd (x) (hx : x ∈ Icc (0 : ℝ) (2 * π)) (y) (hy : y ∈ Icc (0 : ℝ) (2 * π)) :
      ‖h x - h y‖ ≤ K * |x - y| := by
    simpa only [dist_eq_norm, Real.norm_eq_abs] using hK.dist_le_mul x hx y hy
  unfold circDist
  rw [mul_min_of_nonneg _ _ K.coe_nonneg]
  refine le_min (hd θ hθ θ' hθ') ?_
  have e : h θ - h θ' = (h θ - h 0) + (h (2 * π) - h θ') := by rw [hper]; abel
  rw [e]
  refine (norm_add_le _ _).trans ?_
  have a₁ := hd θ hθ 0 ⟨le_rfl, hp⟩
  have a₂ := hd (2 * π) ⟨hp, le_rfl⟩ θ' hθ'
  rw [abs_of_nonpos (sub_nonpos.mpr hle)]
  rw [sub_zero, abs_of_nonneg hθ.1] at a₁
  rw [abs_of_nonneg (sub_nonneg.mpr hθ'.2)] at a₂
  linarith

/-- Every closed Lipschitz function on `[0, 2π]` is the trace along `γ` of a Lipschitz compactly
supported function on `ℂ`. -/
theorem exists_lipschitz_extension_of_trace {Ω : Set ℂ} (hL : IsLipschitzDomain Ω) {γ : ℝ → ℂ} (hγ : IsBoundaryParam Ω γ) {h : ℝ → ℂ}
    {K : NNReal} (hK : LipschitzOnWith K h (Icc 0 (2 * π))) (hper : h (2 * π) = h 0) :
    ∃ V : ℂ → ℂ, (∃ K' : NNReal, LipschitzWith K' V) ∧ HasCompactSupport V ∧
      ∀ θ ∈ Icc 0 (2 * π), V (γ θ) = h θ := by
  classical
  obtain ⟨Kγ, hKγ⟩ := hγ.lipschitz
  obtain ⟨c, hc, hca⟩ := chord_arc hL hγ
  have h2π : (0 : ℝ) < 2 * π := by positivity
  set S : Set ℂ := γ '' Icc 0 (2 * π) with hS
  have hSc : IsCompact S := isCompact_Icc.image hKγ.continuous
  obtain ⟨R, hR⟩ := hSc.isBounded.subset_closedBall (0 : ℂ)
  obtain ⟨Mh, hMh⟩ := isCompact_Icc.exists_bound_of_continuousOn hK.continuousOn
  -- `h` is Lipschitz with respect to the chord
  set Lc : ℝ := K / c with hLc
  have hLc0 : 0 ≤ Lc := by positivity
  have hchord : ∀ θ ∈ Icc (0 : ℝ) (2 * π), ∀ θ' ∈ Icc (0 : ℝ) (2 * π),
      ‖h θ - h θ'‖ ≤ Lc * ‖γ θ - γ θ'‖ := by
    intro θ hθ θ' hθ'
    refine (norm_sub_le_circDist hK hper hθ hθ').trans ?_
    have := hca θ hθ θ' hθ'
    rw [div_mul_eq_mul_div, le_div_iff₀ hc]
    calc (K : ℝ) * circDist θ θ' * c = K * (c * circDist θ θ') := by ring
      _ ≤ K * ‖γ θ - γ θ'‖ := by gcongr
  choose! θof hθof using fun p (hp : p ∈ S) => hp
  have hval : ∀ θ ∈ Icc (0 : ℝ) (2 * π), h (θof (γ θ)) = h θ := by
    intro θ hθ
    have hm := mem_image_of_mem γ hθ
    have := hchord _ (hθof _ hm).1 θ hθ
    rw [(hθof _ hm).2, sub_self, norm_zero, mul_zero] at this
    exact sub_eq_zero.mp (norm_le_zero_iff.mp this)
  let T : Set ℂ := S ∪ {z | R + 1 ≤ ‖z‖}
  let V₀ : ℂ → ℂ := fun z => if z ∈ S then h (θof z) else 0
  let L : NNReal := ⟨max Lc Mh, hLc0.trans (le_max_left ..)⟩
  have hfar (z) (hz : z ∈ S) (w) (hw : R + 1 ≤ ‖w‖) : 1 ≤ ‖z - w‖ := by
    have h := norm_sub_norm_le w z
    rw [norm_sub_rev] at h
    have hzR : ‖z‖ ≤ R := by simpa using hR hz
    linarith
  have hzero (z) (hz : R + 1 ≤ ‖z‖) : V₀ z = 0 := by
    refine if_neg fun hm => ?_
    have := hfar z hm z hz
    norm_num at this
  have hcross (z) (hz : z ∈ S) (w) (hw : R + 1 ≤ ‖w‖) :
      ‖V₀ z - V₀ w‖ ≤ L * ‖z - w‖ := by
    rw [hzero w hw, sub_zero]
    simp only [V₀, if_pos hz]
    exact ((hMh _ (hθof z hz).1).trans (le_max_right ..)).trans
      (le_mul_of_one_le_right L.coe_nonneg (hfar z hz w hw))
  have hlip : LipschitzOnWith L V₀ T := LipschitzOnWith.of_dist_le_mul fun z hz w hw => by
    rw [dist_eq_norm, dist_eq_norm]
    rcases hz with hzs | hzf <;> rcases hw with hws | hwf
    · simp only [V₀, if_pos hzs, if_pos hws]
      have hz := hθof z hzs
      have hw := hθof w hws
      have hh := hchord _ hz.1 _ hw.1
      rw [hz.2, hw.2] at hh
      exact hh.trans (mul_le_mul_of_nonneg_right (le_max_left ..) (norm_nonneg _))
    · exact hcross z hzs w hwf
    · simpa only [norm_sub_rev (V₀ w) (V₀ z), norm_sub_rev w z] using hcross w hws z hzf
    · rw [hzero z hzf, hzero w hwf, sub_self, norm_zero]
      positivity
  obtain ⟨V, hV, hEq⟩ := hlip.extend_finite_dimension
  refine ⟨V, ⟨_, hV⟩, HasCompactSupport.intro (isCompact_closedBall (0 : ℂ) (R + 1)) ?_, ?_⟩
  · intro z hz
    have hz' : R + 1 ≤ ‖z‖ := le_of_lt (by simpa using hz)
    exact (hEq (Or.inr hz')).symm.trans (hzero z hz')
  · intro θ hθ
    have hmem : γ θ ∈ S := mem_image_of_mem γ hθ
    rw [← hEq (Or.inl hmem)]
    simpa only [V₀, if_pos hmem] using hval θ hθ

end PolyaNeumann
