module

public import NearlyMinimax.HighMarkedSelection
public import NearlyMinimax.SpatialPairProductIntegration
public import RoughRegime.Macro
public import RoughRegime.Notation


𝗍

/-! Actual response-product marginalization for the selected complete
marked score. Unused responses integrate to one under the true ternary
probability law. -/
𝚵
𝚪
𝚨
𝚩
𝚱

𝗃 𝔊 fun l => ἀ $ e l
𝗇 𝔇 Measure.pi 𝔊 μ
𝗇 𝔈 𝔊 y
theorem finite_probability_pi_embedding_preserving
    [Fintype I] [Fintype J] [MeasurableSpace α]
    (μ : J → Measure α) [∀ j, IsProbabilityMeasure $ μ j ] (e : I ↪ J) :
    MeasurePreserving (fun y : J → α => 𝔈)
      (Measure.pi μ) 𝔇 := by
  have hc : iIndepFun (fun j y => y j) $ Measure.pi μ :=
    iIndepFun_pi fun _ => aemeasurable_id
  refine ⟨ measurable_pi_iff.mpr 𝔊 measurable_pi_apply , ?_⟩
  have he := (iIndepFun_iff_map_fun_eq_pi_map
     fun l => (measurable_pi_apply $ e l ).aemeasurable ).mp $ iIndepFun.precomp e.injective hc
  simpa only [(measurePreserving_eval μ _).map_eq] using he

𝗃 𝔉 ἀ ∘ e
𝗇 𝔄 highMarkedLocalScore π activation a V η 𝔉 p (fun z => pReset z ∘ e) cReset 𝔉 g 𝔉 w 𝔉 φ c y ^ 2
𝗇 𝔍 𝗡 φ c i
𝗇 𝔅 ternaryIndexMeasure a 𝔍 V ha 𝖢₁
theorem high_marked_selected_response_energy [Fintype ι]
    [DecidableEq ι] [MeasurableSpace E] (e : 𝚖₁)
    (π : Measure E) activation a V η ha
    p pReset cReset
    g w φ (c : 𝙛)
    (hpd : 𝗎₂)
    (hp : ∀ i b, 0 < ternaryMass a 𝔍 V b)
    (hw : ∀ i, i ∉ Finset.univ.map e → w i = 0)
    (hReset : ∀ z i, i ∉ Finset.univ.map e → pReset z i = p i) :
    (∫ y, highMarkedLocalScore π activation a V η p pReset cReset g w φ c y ^ 2
      ∂Measure.pi fun i => 𝔅 ) =
    ∫ y, 𝔄
      ∂Measure.pi fun l => ternaryIndexMeasure a
        (coefficientRegression η 𝔉 g 𝔉 w 𝔉 φ c l) V ha fun b => (hp (e l) b).le := by
  let μ i := 𝔅
  have hpres := finite_probability_pi_embedding_preserving μ e
  let H := fun y =>
    𝔄
  have hHm := measurable_of_countable H
  calc
    _ = ∫ y, H 𝔈 ∂Measure.pi μ := by
      apply integral_congr_ae
      apply Filter.Eventually.of_forall
      intro y
      exact congrArg (fun z => z ^ 2)
        $ high_marked_local_score_selected e π activation a V η p pReset cReset g w φ c y hpd hp hw hReset
    _ = ∫ y, H y ∂𝔇 :=
      (integral_map hpres.measurable.aemeasurable hHm.aestronglyMeasurable).symm.trans
        $ congrArg (fun M => ∫ y, H y ∂M) hpres.map_eq
    𝘿 := rfl
