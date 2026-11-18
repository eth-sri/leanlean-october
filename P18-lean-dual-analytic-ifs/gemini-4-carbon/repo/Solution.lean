module

public import AnalyticESC.Dimension

@[expose] public section

namespace Challenge

open Set Metric MeasureTheory Filter Topology AnalyticESC

variable {N : ℕ}

private theorem dualProjFin_eq_lib {ε : ℝ} (Φ : IFS N ε) (hd : NonzeroDerivatives Φ.f)
    (w : List (Fin N)) (x : I) : dualProjFin Φ.f hd w x = Φ.dualProj (.fin w) x := by
  rw [dualProjFin, Φ.dualProj_fin_eq_sum, ← Fin.sum_univ_eq_sum_range]
  refine Finset.sum_congr rfl fun n _ => ?_
  simp [IFS.dualTerm, Word.get?, Word.take, n.isLt, nonlin, IFS.nonlin]

theorem audit_sesc_open_dense (N : ℕ) :
    ∃ U : Set (Fin N → ℂ → ℂ), (∀ f ∈ U, InUnionClass f ∧ SESC f) ∧
      (∀ f ∈ U, ∃ r > 0, ∀ g, InUnionClass g → d2 f g < r → g ∈ U) ∧
      (∀ f, InUnionClass f → ∀ r > 0, ∃ g ∈ U, d2 f g < r) := by
  refine ⟨{f | ∃ ε : ℝ, ∃ Φ : IFS N ε, Φ.f = f ∧ Φ.DualSSC}, ?_, ?_, ?_⟩
  · rintro _ ⟨ε, Φ, rfl, hΦ⟩
    exact ⟨⟨ε, Φ.ε_pos, Φ.inClass⟩, Φ.theorem_2_2 hΦ⟩
  · rintro _ ⟨ε, Φ, rfl, hΦ⟩
    obtain ⟨δ, hδ, hΨ⟩ := Φ.lemma_2_7_union hΦ
    exact ⟨δ, hδ, fun g ⟨ε', hε', hg⟩ hfg => ⟨ε', ⟨g, hε', hg⟩, rfl, hΨ (⟨g, hε', hg⟩ : IFS N ε') hfg⟩⟩
  · rintro f ⟨ε, hε, hf⟩ r hr
    let Φ : IFS N ε := ⟨f, hε, hf⟩
    rcases Nat.eq_zero_or_pos N with rfl | hN
    · exact ⟨f, ⟨ε, Φ, rfl, fun i => (i 0).elim0⟩, by rwa [Challenge.d2, Real.iSup_of_isEmpty]⟩
    obtain ⟨Φ₁, hΦ₁, hI, hnc⟩ := Φ.exists_noCoincidence_near (half_pos hr)
    obtain ⟨ε', Ψ, hΨ, hssc⟩ := IFS.exists_dualSSC_near hN Φ₁ hI hnc (half_pos hr)
    exact ⟨Ψ.f, ⟨ε', Ψ, rfl, hssc⟩, by linarith [OpenDense.d2_le_add Φ Φ₁ Ψ]⟩

theorem audit_sesc_of_dualProj {ε : ℝ} (hε : 0 < ε) (f : Fin N → ℂ → ℂ)
    (hf : ∀ i, InClass ε (f i)) (hd : NonzeroDerivatives f)
    (hfin : ∀ n, ∀ i j : Fin n → Fin N, i ≠ j →
      0 < ⨆ x : I, ‖dualProjFin f hd (List.ofFn i) x - dualProjFin f hd (List.ofFn j) x‖)
    (hinf : ∀ i j : ℕ → Fin N, i ≠ j →
      0 < ⨆ x : I, ‖dualProjInf f hd i x - dualProjInf f hd j x‖) :
    SESC f := by
  let _ := hfin
  refine (⟨f, hε, hf⟩ : IFS N ε).theorem_2_2 fun i j hij => ?_
  by_contra! heq
  have hpos := hinf i j fun hw => hij (congrFun hw 0)
  have h0 : ∀ x : I, ‖dualProjInf f hd i x - dualProjInf f hd j x‖ = 0 :=
    fun x => by
      change ‖(⟨f, hε, hf⟩ : IFS N ε).dualProj (.inf i) x -
        (⟨f, hε, hf⟩ : IFS N ε).dualProj (.inf j) x‖ = 0
      rw [heq x x.2, sub_self, norm_zero]
  simp only [h0, Real.iSup_const_zero, lt_irrefl] at hpos

theorem audit_example_criterion {ε : ℝ} (hε : 0 < ε) (f : Fin N → ℂ → ℂ)
    (hf : ∀ i, InClass ε (f i)) (hd : NonzeroDerivatives f) (hN : 2 ≤ N) {α : ℝ} (hα : 0 < α)
    (hc : 1 - cmax ε f ≠ 0)
    (hsep : ∀ i j : Fin N, i ≠ j → ∃ x : I, α ≤ ‖nonlin (f i) x (hd i [] x) - nonlin (f j) x (hd j [] x)‖) :
    0 < beta f hd ∧ (divide (2 * beta f hd * cmax ε f) (1 - cmax ε f) hc < α →
      (∀ n, ∀ i j : Fin n → Fin N, i ≠ j →
        0 < ⨆ x : I, ‖dualProjFin f hd (List.ofFn i) x - dualProjFin f hd (List.ofFn j) x‖) ∧
      (∀ i j : ℕ → Fin N, i ≠ j →
        0 < ⨆ x : I, ‖dualProjInf f hd i x - dualProjInf f hd j x‖) ∧
      SESC f) := by
  let Φ : IFS N ε := ⟨f, hε, hf⟩
  obtain ⟨hβ, h⟩ := Φ.proposition_1_8 hN hα fun i j hij => by obtain ⟨x, hx⟩ := hsep i j hij; exact ⟨x, x.2, hx⟩
  refine ⟨hβ, fun hα' => ?_⟩
  obtain ⟨hne, hS⟩ := h hα'
  refine ⟨fun n i j hij => ?_, fun i j hij => hne (.inf i) (.inf j) (fun he => hij (by cases he; rfl)) (fun _ => by simp), hS⟩
  have hfin := hne (.fin (List.ofFn i)) (.fin (List.ofFn j))
    (fun he => hij (List.ofFn_injective (Word.fin.inj he))) (fun k => by simp [Option.isSome_iff_ne_none])
  simpa only [show f = Φ.f from rfl, ← dualProjFin_eq_lib Φ hd] using hfin

theorem audit_example_sesc : ∃ ε > 0, (∀ i, InClass ε (exampleMaps i)) ∧ SESC exampleMaps :=
  ⟨1 / 100, by norm_num, exampleMaps_inClass, exampleIFS_sesc⟩

theorem audit_conj_similarity {ε : ℝ} (hε : 0 < ε) (f : Fin N → ℂ → ℂ)
    (hf : ∀ i, InClass ε (f i)) (i : Fin N) :
    ∃ g, IsAnalyticCoord g ∧ (∀ x ∈ I, deriv g x ≠ 0) ∧
      ∃ lam t : ℝ, lam ≠ 0 ∧ |lam| < 1 ∧ ∀ x ∈ I, g (f i x).re = lam * g x + t := by
  obtain ⟨g, hco, hpos, hode⟩ := exists_koenigs_ode hε (hf i)
  exact ⟨g, hco, fun x hx => (hpos x hx).ne', conj_of_koenigs_ode hε (hf i) hco.1 hpos hode⟩

theorem audit_conj_iff {ε : ℝ} (hε : 0 < ε) (f : Fin N → ℂ → ℂ) (hf : ∀ i, InClass ε (f i))
    (hd : NonzeroDerivatives f) (hnd : ¬ ∃ x, attractor f = {x}) :
    ConjSelfSimilar (fun i (x : ℝ) => (f i x).re) ↔
      ∀ i j : ℕ → Fin N, ∀ x : I, dualProjInf f hd i x = dualProjInf f hd j x :=
  let Φ : IFS N ε := ⟨f, hε, hf⟩
  ⟨fun h i j x => Φ.dualProj_eq_of_conjSelfSimilar hnd h i j x x.2,
   fun h => Φ.conjSelfSimilar_of_dualProj_eq fun i j x hx => h i j ⟨x, hx⟩⟩

theorem audit_subconj_iff {ε : ℝ} (hε : 0 < ε) (f : Fin N → ℂ → ℂ) (hf : ∀ i, InClass ε (f i))
    (hd : NonzeroDerivatives f) (hnd : ¬ ∃ x, attractor f = {x}) :
    (∃ (m : ℕ) (i j : Fin m → Fin N), i ≠ j ∧
      ConjSelfSimilar ![fun x : ℝ => (comp f (List.ofFn i) x).re,
        fun x : ℝ => (comp f (List.ofFn j) x).re]) ↔
      ∃ (m : ℕ) (hm : 0 < m) (i j : Fin m → Fin N), i ≠ j ∧
        ∀ x : I, dualProjInf f hd (periodic hm i) x = dualProjInf f hd (periodic hm j) x := by
  have H := (⟨f, hε, hf⟩ : IFS N ε).subConjSelfSimilar_iff
  exact ⟨fun h => by obtain ⟨m, hm, i, j, hij, heq⟩ := H.mp h; exact ⟨m, hm, i, j, hij, fun x => heq x x.2⟩,
    fun ⟨m, hm, i, j, hij, heq⟩ => H.mpr ⟨m, hm, i, j, hij, fun x hx => heq ⟨x, hx⟩⟩⟩

theorem audit_dim_of_esc (hM : RapaportMeasureStatement) (hS : RapaportSetStatement) {ε : ℝ}
    (hε : 0 < ε) (f : Fin N → ℂ → ℂ) (hf : ∀ i, InClass ε (f i))
    (hN : 0 < N) (hnd : ¬ ∃ x, attractor f = {x}) (hesc : ESC f) : DimEquality f :=
  (⟨f, hε, hf⟩ : IFS N ε).theorem_1_6 hM hS hN hnd hesc

theorem audit_dim_open_dense (hM : RapaportMeasureStatement) (hS : RapaportSetStatement) (hN : 2 ≤ N) :
    ∃ U : Set (Fin N → ℂ → ℂ), (∀ f ∈ U, InUnionClass f ∧ DimEquality f) ∧
      (∀ f ∈ U, ∃ r > 0, ∀ g, InUnionClass g → d2 f g < r → g ∈ U) ∧
      (∀ f, InUnionClass f → ∀ r > 0, ∃ g ∈ U, d2 f g < r) := by
  have hN0 : 0 < N := by omega
  obtain ⟨U₁, hU₁, hU₁o, hU₁d⟩ := audit_sesc_open_dense N
  refine ⟨U₁ ∩ {f | ¬ ∃ x ∈ I, ∀ i, (f i x).re = x}, ?_, ?_, ?_⟩
  · rintro f ⟨hf₁, hfix⟩
    obtain ⟨⟨ε, hε, hfε⟩, hSESC⟩ := hU₁ f hf₁
    let Φ : IFS N ε := ⟨f, hε, hfε⟩
    exact ⟨⟨ε, hε, hfε⟩, Φ.theorem_1_6 hM hS hN0
      (fun h => hfix ((Φ.exists_attractor_eq_singleton_iff hN0).1 h)) (Φ.esc_of_sesc hSESC)⟩
  · rintro f ⟨hf₁, hfix⟩
    obtain ⟨r₁, hr₁, h₁⟩ := hU₁o f hf₁
    obtain ⟨r₂, hr₂, h₂⟩ := OpenDense.exists_forall_d2Sys_lt_not_fixed (hU₁ f hf₁).1 hfix
    exact ⟨min r₁ r₂, lt_min hr₁ hr₂, fun g hg hfg =>
      ⟨h₁ g hg (hfg.trans_le (min_le_left _ _)), h₂ g hg (hfg.trans_le (min_le_right _ _))⟩⟩
  · intro f hf r hr
    obtain ⟨g, hg, hgfix, hfg⟩ := OpenDense.exists_not_fixed_d2Sys_lt hN hf (half_pos hr)
    obtain ⟨ρ, hρ, hgρ⟩ := OpenDense.exists_forall_d2Sys_lt_not_fixed hg hgfix
    obtain ⟨h, hh₁, hgh⟩ := hU₁d g hg (min ρ (r / 2)) (lt_min hρ (half_pos hr))
    have hh := (hU₁ h hh₁).1
    exact ⟨h, ⟨hh₁, hgρ h hh (hgh.trans_le (min_le_left _ _))⟩,
      by linarith [OpenDense.d2Sys_le_add hf hg hh, hgh.trans_le (min_le_right _ _)]⟩

theorem audit_example_dim (hM : RapaportMeasureStatement) (hS : RapaportSetStatement) :
    ∃ s : ℝ, (∀ t, Tendsto (pressureRatio exampleMaps t) atTop (𝓝 0) ↔ t = s) ∧
      s < 1 ∧ dimH (attractor exampleMaps) = ENNReal.ofReal s ∧
      ∀ p : Fin 3 → ℝ, IsProbVec p → ∀ μ : Measure ℝ, IsSelfConformal exampleMaps p μ →
        ∀ hχ : lyapunov exampleMaps p μ ≠ 0,
        entropy p < lyapunov exampleMaps p μ ∧
        ∀ᵐ x ∂μ, Tendsto (fun r : Scale => logRatio (μ.real (closedBall x r)) r) scaleZero
          (𝓝 (divide (entropy p) (lyapunov exampleMaps p μ) hχ)) := by
  have hN : (0 : ℕ) < 3 := by norm_num
  have hc : ((3 : ℕ) : ℝ) * exampleIFS.cmax < 1 := by have := exampleIFS_cmax_lt; push_cast; linarith
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
  have hs1 : s < 1 := exampleIFS.exdim_lt_one hN hc ((positive_length_tendsto_iff _).1 ((hs s).2 rfl))
  refine ⟨s, hs, hs1, hdim.trans (by rw [min_eq_right hs1.le]), fun p hp μ hμ hχ => ?_⟩
  have hH : entropy p < exampleIFS.lyapunov p μ :=
    (exampleIFS.exdim_entropy_lt hN hc hp).trans_le (exampleIFS.neg_log_cmax_le_lyapunov hN hp hμ)
  have hχ_pos : 0 < exampleIFS.lyapunov p μ :=
    (neg_pos.2 (Real.log_neg ((exampleIFS.cmin_pos hN).trans_le (exampleIFS.cmin_le_cmax hN))
      exampleIFS.cmax_lt_one)).trans_le (exampleIFS.neg_log_cmax_le_lyapunov hN hp hμ)
  have hl := hloc p hp μ hμ hχ
  rw [min_eq_right (show divide (entropy p) (lyapunov exampleIFS.f p μ) hχ ≤ 1 from
    ((div_lt_one hχ_pos).2 hH).le)] at hl
  exact ⟨hH, hl⟩

theorem audit_example_localDim (hB : BowenGibbsStatement) :
    ∃ s : ℝ, (∀ t, Tendsto (pressureRatio exampleMaps t) atTop (𝓝 0) ↔ t = s) ∧
      (∃ ν : Measure (ℕ → Fin 3), IsProbabilityMeasure ν ∧ IsGibbsMeasure (potential exampleMaps s) ν) ∧
      ∀ ν : Measure (ℕ → Fin 3), IsProbabilityMeasure ν → IsGibbsMeasure (potential exampleMaps s) ν →
        Tendsto (fun r : Scale => logRatio ((ν.map (natProj exampleMaps)).real (closedBall 0 r)) r)
          scaleZero (𝓝 (s - 1 / 3)) := by
  obtain ⟨s, hs, hG, hm⟩ := example_bowen_core hB
  exact ⟨s, hs, hG, fun ν hν hGν => (hm ν hν hGν).1⟩

theorem audit_example_lq (hB : BowenGibbsStatement) :
    ∃ s : ℝ, (∀ t, Tendsto (pressureRatio exampleMaps t) atTop (𝓝 0) ↔ t = s) ∧
      ∀ ν : Measure (ℕ → Fin 3), IsProbabilityMeasure ν →
        IsGibbsMeasure (potential exampleMaps s) ν → ∀ q > 1, ∀ hq : q - 1 ≠ 0,
        lqDim (ν.map (natProj exampleMaps)) q hq ≤ divide q (q - 1) hq * (s - 1 / 3) ∧
        (3 * s < q → lqDim (ν.map (natProj exampleMaps)) q hq < s) := by
  obtain ⟨s, hs, -, hm⟩ := example_bowen_core hB
  refine ⟨s, hs, fun ν hν hG q hq1 hq0 => ?_⟩
  have hdim := (hm ν hν hG).2 q hq1 hq0
  exact ⟨hdim, fun h3 => hdim.trans_lt (by rw [divide, div_mul_eq_mul_div, div_lt_iff₀ (sub_pos.2 hq1)]; linarith)⟩

end Challenge
