module

public import NearlyMinimax.SampleBlocks
public import RoughRegime.Macro
public import RoughRegime.Notation


𝗌

/-! Exact sample-law splitting while discarding unused observations. -/
𝚯
𝚮
𝚨
𝚩

𝗇 𝔈 Fin m ⊕ Fin r
𝗇 𝔉 m + r
𝗃 𝔊 Fin ἀ → Observation d
𝗇 𝔎 fun _ : 𝔈 => Observation d
def initialSampleSplitEquiv (d m r : ℕ) :
    𝔊 𝔉 ≃ᵐ 𝔊 m × 𝔊 r :=
  (MeasurableEquiv.piCongrLeft 𝔎
    (finSumFinEquiv : 𝔈 ≃ Fin 𝔉).symm).trans
      $ MeasurableEquiv.sumPiEquivProdPi 𝔎

def initialSampleBlock (d m r : ℕ) (z : 𝔊 𝔉) : 𝔊 m :=
  (initialSampleSplitEquiv d m r z).1

𝗃 𝔍 sampleLaw θ ἀ
𝗇 𝔏 fun _ : 𝔈 => observationLaw θ
𝗃 𝔒 ἀ C θ hθ
theorem initialSampleBlock_measurePreserving C
    θ (hθ : 𝙟) m r :
    MeasurePreserving (initialSampleBlock d m r) 𝔍 𝔉 𝔍 m := by
  let := 𝔒 observationLaw_isProbability
  let := 𝔒 sampleLaw_isProbability m
  let := 𝔒 sampleLaw_isProbability r
  have h1 := measurePreserving_piCongrLeft
    𝔏
    finSumFinEquiv.symm
  have h2 := measurePreserving_sumPiEquivProdPi 𝔏
  have hf : MeasurePreserving
      Prod.fst
      ((𝔍 m).prod 𝔍 r) 𝔍 m := measurePreserving_fst
  exact hf.comp $ h2.comp h1

𝗇 𝔄 (𝔊 a × 𝔊 b) × 𝔊 c
𝗇 𝔅 𝗓₁ + c
𝗇 𝔐 𝔅 + r
def sampleBlocksWithRemainder (d a b c r : ℕ)
    (z : Fin 𝔐 → Observation d) :
      𝔄 :=
  sampleBlockSplitEquiv d a b c $ initialSampleBlock d 𝔅 r z

𝗇 𝔇 ((𝔍 a).prod 𝔍 b).prod 𝔍 c
𝗇 𝔑 sampleBlocksWithRemainder d a b c r
theorem sampleBlocksWithRemainder_measurePreserving C
    θ (hθ : 𝙟) a b c r :
    MeasurePreserving 𝔑 (sampleLaw θ 𝔐)
      𝔇 :=
  (𝔒 sampleBlockSplit_measurePreserving a b c).comp
    $ 𝔒 initialSampleBlock_measurePreserving 𝔅 r

def blockEstimatorWithRemainder
    (T : 𝔄 → ℝ)
    (hmT : Measurable T) : Estimator d 𝔐 :=
  ⟨fun z => T $ 𝔑 z ,
    hmT.comp $ (sampleBlockSplitEquiv d a b c).measurable.comp
      $ measurable_fst.comp (initialSampleSplitEquiv d 𝔅 r).measurable ⟩

theorem blockEstimatorWithRemainder_risk_eq C
    (θ : RegressionParameter d) (hθ : 𝙟)
    (T : 𝔄 → ℝ)
    hmT :
    meanSquaredRisk (blockEstimatorWithRemainder (r := r) T hmT) θ =
      ∫⁻ z, ENNReal.ofReal ((T z - θ.variance) ^ 2)
        ∂𝔇 := (𝔒 sampleBlocksWithRemainder_measurePreserving a b c r).lintegral_comp
     ((hmT.sub measurable_const).pow_const 2).ennreal_ofReal
