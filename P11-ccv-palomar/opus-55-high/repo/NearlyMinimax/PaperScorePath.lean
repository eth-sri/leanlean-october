module

public import NearlyMinimax.MixtureRisk
public import RoughRegime.Macro
public import RoughRegime.Notation


𝗍

/-! The manuscript's score-to-risk comparison for actual mixtures of the
original statistical experiment. The exceptional-state contribution and the
restriction to clipped estimators are consequences, not hypotheses. -/
𝚴
𝚮
𝚨
𝚩

𝗇 𝔄 L t ∘ₘ σ t
𝗇 𝔅 Icc 0 δ
𝗇 𝔇 R t x
𝗇 𝔈 ∫ x, 𝔇 ^ 2 ∂𝔄
𝗇 𝔉 t ∈ 𝔅
𝗃 𝔊 ἀ t ht
𝗇 𝔍 𝙌
𝗇 𝔎 θ t a
𝗇 𝔏 risk.toReal + 𝘔 * ε
theorem paper_score_to_risk [MeasurableSpace Α]
    (C : ModelConstants d) (σ : ℝ → Measure Α)
    (L : ℝ → Kernel Α 𝔍)
    (θ : ℝ → Α → RegressionParameter d) (V : 𝘓)
    (R : ℝ → 𝔍 → ℝ) δ ε (hδ : 𝚈)
    (hσ : ∀ t ∈ 𝔅, IsProbabilityMeasure $ σ t )
    (hLprob : ∀ t ∈ 𝔅, IsMarkovKernel $ L t )
    (hL : ∀ t ∈ 𝔅, ∀ a, L t a = sampleLaw 𝔎 n)
    (hVθ : ∀ t ∈ 𝔅, ∀ a, (𝔎).variance = V t)
    (hV : ∀ t ∈ 𝔅, V t ∈ 𝙸₁)
    (bad : ℝ → Set Α) (hbad : ∀ t ∈ 𝔅, MeasurableSet $ bad t )
    (hlegal : ∀ t ∈ 𝔅, ∀ a ∉ bad t, Admissible C 𝔎)
    (hmass : ∀ t ∈ 𝔅, (σ t).real (bad t) ≤ ε)
    (hR : ∀ᵐ t ∂volume, 𝔉 → MemLp (R t) 2 𝔄)
    (hcenter : ∀ᵐ t ∂volume, 𝔉 →
       ∫ x, 𝔇 ∂𝔄 = 0)
    (hAC : ∀ T : 𝖧₂, AbsolutelyContinuousOnInterval
      (fun t => ∫ x, T.val.val x ∂𝔄) 0 δ)
    (hderiv : ∀ T : 𝖧₂, ∀ᵐ t ∂volume, 𝔉 →
      HasDerivAt (fun u => ∫ x, T.val.val x ∂ L u ∘ₘ σ u )
        (∫ x, T.val.val x * 𝔇 ∂𝔄) t)
    (hscoreInt : IntervalIntegrable
      (fun t => Real.sqrt 𝔈) volume 0 δ) :
    ENNReal.ofReal ((V δ - V 0) ^ 2 /
      (2 + ∫ t in (0)..δ, Real.sqrt 𝔈) ^ 2
      - 𝙰 ^ 2 * ε) ≤ minimaxRisk C n := by
  let P t := 𝔄
  have hprob t (ht : 𝔉) : IsProbabilityMeasure $ P t := by
    let _ := 𝔊 hσ
    let _ := 𝔊 hLprob
    infer_instance
  rw [minimaxRisk_eq_inf_bounded]
  apply le_iInf
  intro T
  let risk := 𝚡₂
  let D := 𝙰
  let r := Real.sqrt 𝔏
  have hrEq : 𝘴₁ = 𝔏 :=
    Real.sq_sqrt $ add_nonneg ENNReal.toReal_nonneg $ 𝖧₁ $ measureReal_nonneg.trans $ hmass 0 ⟨le_rfl, hδ⟩
  have hTrisk (t : ℝ) (ht : 𝔉) :
       ∫ x, (T.val.val x - V t) ^ 2 ∂P t ≤ 𝘴₁ := by
    let _ := 𝔊 hσ
    let _ := 𝔊 hLprob
    rw [hrEq]
    exact boundedEstimator_mixture_risk_le_of_exceptional_set C T (σ t) (L t) (θ t) (V t) ε
      𝔊 hL 𝔊 hVθ 𝔊 hV (bad t) 𝔊 hbad 𝔊 hlegal 𝔊 hmass
  have hT (t : ℝ) (ht : 𝔉) : MemLp T.val.val 2 $ P t := by
    let _ := 𝔊 hprob
    exact boundedEstimator_memLp C T (P t) 2
  have hlower := probability_absolutelyContinuous_score_path_risk_lower_bound
    P T.val.val R V δ r risk.toReal D ε hδ (Real.sqrt_nonneg _) hprob hT hR hcenter (hAC T)
    (hderiv T) hTrisk hscoreInt hrEq
  simpa only [P, D, risk, ENNReal.ofReal_toReal
    (boundedEstimator_worstCaseRisk_finite C T).ne] using ENNReal.ofReal_le_ofReal hlower
