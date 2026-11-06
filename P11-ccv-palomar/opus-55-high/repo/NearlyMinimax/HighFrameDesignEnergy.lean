module

public import NearlyMinimax.HighMarkedSpatialDesign
public import NearlyMinimax.HighConditionalScoreEnergy
public import RoughRegime.Macro
public import RoughRegime.Notation


𝗌

/-! The actual complete marked periodic-frame generator in the genuine
normalized iid design/response experiment. The source overlap factor
3^d multiplies a derived factorial series of true Q^r numerator envelopes. -/
𝚵
𝚮
𝚨
𝚩
𝛈

section
𝛙

𝗃 𝔜 ἀ d k
𝗇 𝔈 𝔜 HighWindowLabels
𝗇 𝔏 𝙇
𝗃 𝔬 ἀ j e
𝗇 𝔚 𝔬 pReset
𝗃 𝔫 𝔜 ἀ D n
𝗇 𝔛 𝔫 highFrameMarkedScore π activation a V η
𝗇 𝔡 𝙮 → ℝ
𝗇 𝔥 𝔈 → Measure E
𝗇 𝔦 𝙀
𝗃 𝔪 𝔈 → E → ἀ
def highFrameFullMarkedScore (d k D n : ℕ) [NeZero k]
    (π : 𝔥) (activation : 𝔪 ℝ)
    (a V η : ℝ) (p : 𝔦)
    (pReset : 𝔪 𝔦)
    (cReset : 𝔪 𝔡)
    (c : 𝔈 → 𝔡)
    (z : 𝔏 × 𝙈) : ℝ :=
  ∑ j, 𝔛 (p ∘ z.1)
    (fun j e => 𝔚 ∘ z.1) cReset c z.1 j z.2

𝗇 𝔄 𝔜 highLocalFieldWithout D η c j
𝗇 𝔅 𝔜 highPeriodicTensor j
𝗇 𝔇 𝔫 highFrameFullMarkedScore π activation a V η p pReset cReset c
𝗃 𝔭 ἀ k j
𝗇 𝔐 fun x => 𝔭 highLocalFrameFeature x
𝗇 𝔑 ∀ j γ, Measurable fun e => 𝔬 cReset γ
𝗇 𝔔 ∀ j, Measurable $ Function.uncurry $ pReset j
𝗃 𝔞 ἀ ∘ x
𝗇 𝔖 𝔞 p
𝗇 𝔗 (𝔜 highLocalFieldWithout_continuous D η c j).measurable
𝗃 𝔠 ἀ n (π j) $ activation j
𝗇 𝔣 ∀ j, SFinite $ π j
𝗇 𝔤 ∀ j, Measurable $ activation j
𝗇 𝔧 highMarkedResponseMass a V η
theorem highFrameFullMarkedScore_measurable (d k D n : ℕ) [NeZero k]
    (π : 𝔥) [𝔣]
    activation (hAct : 𝔤)
    a V η p (hp : Measurable p)
    pReset
    (hReset : 𝔔)
    cReset
    (hcReset : 𝔑)
    c :
    Measurable 𝔇 := by
  apply measurable_from_prod_countable_left
  intro y
  apply Finset.measurable_sum
  intro j hj
  let g := 𝔄
  let w := 𝔅
  let φ : Covariate d → 𝔡 := 𝔐
  have hg : Measurable g := 𝔗
  have hw : Measurable w := (𝔜 highPeriodicTensor_contDiff j).continuous.measurable
  have hφ : 𝘜₁ := 𝔭 highLocalFrameFeature_measurable
  have hR := 𝔠 highMarkedSampleNumerator_measurable (hAct j)
    a V η p hp (pReset j) (hReset j) (cReset j) (hcReset j) g w hg hw φ hφ (c j) y
  have hq : Measurable fun x : 𝔏 =>
      ∏ i, 𝔧 g w φ (c j) (x i) (y i) :=
    Finset.measurable_prod _ fun i _ =>
      (𝗉₂ (c j) $ y i ).comp $ measurable_pi_apply i
  change Measurable fun x =>
    highMarkedLocalScore (π j) (activation j) a V η 𝔖 (fun e => 𝔞 𝔚)
      (cReset j) 𝔞 g 𝔞 w 𝔞 φ (c j) y
  simp_rw [high_marked_sample_score_eq_ratio]
  exact hR.div $ (Finset.measurable_prod _ fun i _ => hp.comp $ measurable_pi_apply i ).mul hq

𝗇 𝔉 𝔭 highLocalFrameFeature
𝗇 𝔙 (𝚐 : ℕ)
𝗇 𝔊 𝔙 * ∑ j, Elocal j x
𝗇 𝔍 𝗏₁
𝗇 𝔎 (Measure.pi fun _ => highNormalizedDesignLaw p ).compProd $ responseSampleIndexKernel n a V F hF
𝗇 𝔒 fun j e => 𝔞 𝔚
𝗇 𝔓 fun j _ => (hlocal j).1
𝗃 𝔟 ἀ $ x i
𝗇 𝔘 𝔟 hq y
𝗇 𝔢 H j r
𝗇 𝔨 𝔜 highFrameField η 𝔍
𝗇 𝔩 (𝔜 highFrameField_contDiff η _).continuous.measurable
theorem high_frame_complete_design_spatial_series (d k D n : ℕ) [NeZero k] (hk : 𝗑)
    (π : 𝔥) [𝔣]
    (activation : 𝔪 ℝ)
    (hAct : 𝔤) (hActI : ∀ j, Integrable (activation j) $ π j )
    (a V η pMinus pPlus cMass : ℝ) (ha : 𝙞) (hpMinus : 0 < pMinus)
    (hpPlus : 𝗊₂) (hcMass : 0 < cMass)
    (p : 𝔦) (hp : Measurable p)
    (hraw : ∀ x, pMinus ≤ p x ∧ p x ≤ pPlus)
    pReset
    (hReset : 𝔔)
    (hBound : ∀ j e x, |𝔚 x| ≤ pPlus)
    (hOutside : ∀ j e x, x ∉ 𝔜 highTorusPatch j → 𝔚 x = p x)
    cReset
    (hcReset : 𝔑)
    c
    (hq : ∀ x y, cMass ≤ ternaryMass a (𝔨 x) V y)
    (hqReset : ∀ j e x y, 0 ≤ 𝔧
      𝔄 𝔅
      𝔐 𝔬 cReset x y)
    (hDensity : ∀ j (x : 𝔏),
       ∫ e, 𝔬 activation * ∏ i, 𝔟 𝔚 ∂π j = 0)
    (H : 𝔈 → 𝗖)
    (hH : ∀ j r, Integrable 𝔢 $ Measure.pi fun _ : Fin r => 𝖪 )
    (hH0 : ∀ j r u, 0 ≤ 𝔢 u)
    (hdom : ∀ j r x, (∀ i, x i ∈ 𝔜 highTorusPatch j) →
      selectedRawSquareEnergy (highMarkedSampleNumerator r (π j) (activation j) a V η p (pReset j)
        (cReset j) 𝔄 𝔅
          𝔐 $ c j ) x ≤ 𝔢 (𝔜 highPatchProductChart j x)) :
    let F := 𝔨
    let hF := 𝔩
    let S := 𝔇
    Integrable (fun z => 𝖩₂) 𝔎 ∧
     ∫ z, 𝖩₂ ∂ 𝔎 ≤
      𝔙 * ∑ j : 𝔈, ∑ r ∈ Finset.range 𝗉,
        (n * highFixedScoreDenominator pMinus cMass * 𝗄) ^ r /
          r.factorial * ∫ u, 𝔢 u
            ∂Measure.pi fun _ => 𝖪 := by
  let F := 𝔨
  have hF : Measurable F := 𝔩
  let S := 𝔇
  let μ := Measure.pi fun _ : Fin n => highNormalizedDesignLaw p
  let _ := high_normalized_design_probability p hp pMinus pPlus hpMinus $ Filter.Eventually.of_forall hraw
  let Eglobal := finiteResponseSquareEnergy n a V F S
  let Elocal (j : 𝔈) := 𝔠 highMarkedSampleConditionalEnergy
    a V η p (pReset j) (cReset j) 𝔄
      𝔅 𝔉 $ c j
  have hqLocal (j : 𝔈) (x : Covariate d) (y : Fin 3) :
      cMass ≤ 𝔧 𝔄
        𝔅 𝔉 (c j) x y := by
    unfold highMarkedResponseMass
    rw [← 𝔜 highFrameField_local_decomposition D hk η c j x]
    simp_all
  have hlocal (j : 𝔈) := high_marked_original_design_spatial_series hk j n
    (π j) (activation j) (hAct j) a V η ha pMinus pPlus cMass hpMinus hcMass p hp hraw
    (pReset j) (hReset j) (cReset j) (hcReset j)
    𝔄 𝔅
    𝔗
    (𝔜 highPeriodicTensor_contDiff j).continuous.measurable
    𝔉 𝔭 highLocalFrameFeature_measurable (c j)
    (hqLocal j) fun x hx => by
      by_contra h
      exact hx $ 𝔜 highPeriodicTensor_supported_patch j h
    (hOutside j) (H j) (hH j) (hH0 j) $ hdom j
  have hSm := 𝔫 highFrameFullMarkedScore_measurable π activation hAct
    a V η p hp pReset hReset cReset hcReset c
  have hEm : Measurable Eglobal := by
    apply Finset.measurable_sum
    intro y hy
    exact (Finset.measurable_prod _ fun i _ =>
      ternaryMass_measurable_comp a V _ (hF.comp $ measurable_pi_apply i ) $ y i ).mul
        $ (hSm.comp $ measurable_id.prodMk measurable_const ).pow_const 2
  have hEn (x : 𝔏) : 0 ≤ Eglobal x :=
    Finset.sum_nonneg fun y _ => mul_nonneg
      (Finset.prod_nonneg fun i _ => hcMass.le.trans $ 𝔟 hq $ y i ) $ sq_nonneg _
  have hpoint (x : 𝔏) : Eglobal x ≤ 𝔊 := by
    have he := 𝔫 highFrameMarkedScore_energy_bound hk π activation hActI a V η pPlus ha hpPlus
      𝔖 𝔒
      (fun j i => (hReset j).comp $ measurable_id.prodMk measurable_const )
      (fun j e i => 𝔬 hBound $ x i ) cReset hcReset c x
      (fun i => (hpMinus.trans_le (𝔟 hraw).1).ne')
      (fun i y => hcMass.trans_le 𝔘)
      (fun j e i y => 𝔬 hqReset (x i) y) fun j => hDensity j x
    rw [ternary_index_product_integral] at he
    have hloc (j : 𝔈) :
        (∫ y, 𝔛 𝔖
          𝔒 cReset c x j y ^ 2
          ∂Measure.pi fun i => ternaryIndexMeasure a 𝔟 F V ha
             fun y => (hcMass.trans_le 𝔘).le ) = Elocal j x := by
      have hreg := 𝔫 highFrameField_coefficientRegression hk η c j x
      change coefficientRegression η 𝔞 𝔄
        𝔞 𝔅 𝔞 𝔉 (c j) =
           fun i => 𝔟 F at hreg
      have hs := 𝔠 high_marked_sample_energy_integral a V η ha p (pReset j)
        (cReset j) 𝔄 𝔅
          𝔉 (c j) x
             fun x y => hcMass.trans_le $ hqLocal j x y
      rw [ternary_index_product_integral] at hs
      rw [hreg] at hs
      rw [ternary_index_product_integral]
      exact hs
    dsimp only [F] at hloc
    simp_rw [hloc] at he
    exact he
  have hu : Integrable (fun x => 𝔊) μ :=
    (integrable_finsetSum _ 𝔓).const_mul _
  have hEI : Integrable Eglobal μ := by
    apply hu.mono' hEm.aestronglyMeasurable
    exact Filter.Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg $ hEn x ]
      exact hpoint x
  have hs := response_sample_square_integrable_integral n μ a V ha F hF
    (fun x y => hcMass.le.trans $ hq x y ) S hSm hEI
  refine ⟨hs.1, ?_⟩
  rw [hs.2]
  calc
    _ ≤ ∫ x, 𝔊 ∂μ := integral_mono hEI hu hpoint
    _ = 𝔙 * ∑ j, ∫ x, Elocal j x ∂μ := by
      rw [integral_const_mul, integral_finsetSum _ 𝔓]
    𝖦 := mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun j _ => (hlocal j).2 ) $ Nat.cast_nonneg _
