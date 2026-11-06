module

public import NearlyMinimax.HighUnionScorePrimitives
public import NearlyMinimax.HighFrameDesignEnergy
public import RoughRegime.Macro
public import RoughRegime.Notation


𝗌

/-! Genuine canonical-source Fisher integrability and spatial factorial
energy from actual local numerator envelopes under the original sample law. -/
𝚴
𝚪
𝚨
𝛈
𝛀
𝚬
attribute [local irreducible] highUnionSourceDensity highUnionSourceState historyMarkedAppend
  highUnionSourceRegression highHistoryLikelihoodScore highSampleIndexKernel

𝗃 𝔟 ἀ d k
𝗇 𝔑 𝔟 HighWindowLabels
variable {d k D : ℕ} {I : Type*} [Fintype I] {E : 𝗀}
    [𝙪] [𝖭]
    [NeZero k] [LinearOrder 𝔑]
    (C : ModelConstants d) (R : 𝔟 HighUnionRowData D I E)
    {M Cfr : ℝ} (G : 𝗗)
    (hpos : 𝚣)

𝗇 𝔄 fun i j => j ∈ 𝔟 highNeighborLabels i
𝗃 𝔢 ἀ R $ highCenterMix C
𝗇 𝔇 𝔢 highUnionLaw
𝗇 𝔊 𝔢 highUnionActivation
𝗃 𝔡 ἀ C R
𝗇 𝔎 (𝔡 highUnionSourceState h).2
𝗇 𝔒 fun x => highLocalFrameFeature k j x
𝗇 𝔔 𝔡 highUnionSourceResetDensity j h
𝗇 𝔖 𝔡 highUnionSourceResetCoefficient j h
𝗇 𝔗 𝔡 highUnionSourceDensity
𝗇 𝔛 𝔟 highPeriodicTensor j
𝗇 𝔜 Fin r → Covariate d
𝗃 𝔣 𝔟 highLocalFieldWithout D η ἀ j
def highUnionSourceRawNumerator (r : ℕ) (a V η : ℝ)
    (h : HistoryMarked 𝔄 $ HighUnionMark E )
    (j : 𝔑) (x : 𝔜) (y : Fin r → Fin 3) : ℝ :=
  highMarkedSampleNumerator r 𝔇
    𝔊 a V η (𝔗 h)
    𝔔 𝔖
    𝔣 𝔎
    𝔛 𝔒
    (𝔎 j) x y

𝗇 𝔅 fun {_ _} h => 𝔟 highNeighborLabels_symmetric _ _ h
𝗇 𝔓 𝔡 highUnionSourceRegression η
𝗇 𝔈 highSampleIndexKernel n a V 𝔗 𝔓 hp hF h
𝗇 𝔉 Measure.pi fun _ : Fin r => 𝖪
𝗃 𝔙 𝔡 ἀ G
𝗇 𝔍 𝔙 highUnionSourceDensity_coarse_interval h
𝗇 𝔏 fun j => 𝔔
𝗇 𝔐 fun j => 𝔖
𝗃 𝔘 fun _ => ἀ
𝗇 𝔚 H j r
𝗃 𝔞 fun j => 𝔙 ἀ j h
𝗃 𝔠 ἀ (p h) hp.of_uncurry_left C.densityLower C.densityUpper C.densityLower_pos $ Filter.Eventually.of_forall 𝔍
include G hpos in
/-- The genuine sample-kernel score has square integrability and the
original factorial spatial budget, derived from local raw numerators. -/
theorem highUnionSource_sample_fisher_bound (n : ℕ) (hk : 𝗑)
    (a V η cMass : ℝ) (ha : 𝙞) (hcMass : 0 < cMass)
    (hq : ∀ h x y, cMass ≤ ternaryMass a (𝔓 h x) V y)
    (hDensity : ∀ j h (x : 𝙇),
       ∫ e, 𝔢 highUnionActivation e *
        ∏ i, 𝔔 e (x i) ∂𝔇 = 0)
    (h : HistoryMarked 𝔄 $ HighUnionMark E )
    (H : 𝔑 → (r : ℕ) → 𝔜 → ℝ)
    (hH : ∀ j r, Integrable 𝔚 𝔉)
    (hH0 : ∀ j r u, 0 ≤ 𝔚 u)
    (hdom : ∀ j r x, (∀ i, x i ∈ 𝔟 highTorusPatch j) →
      selectedRawSquareEnergy (𝔡 highUnionSourceRawNumerator r a V η h j) x ≤
        𝔚 (𝔟 highPatchProductChart j x)) :
    let hp := 𝔙 highUnionSourceDensity_joint_measurable
    let hF := 𝔙 highUnionSourceRegression_joint_measurable η
    let S := highHistoryLikelihoodScore 𝔄
      𝔅
      𝔇 𝔊
      n a V η 𝔗 𝔓 h
    Integrable (fun z => 𝖩₂)
      𝔈 ∧
     ∫ z, 𝖩₂ ∂𝔈 ≤
      (𝚐 : ℕ) * ∑ j : 𝔑, ∑ r ∈ Finset.range 𝗉,
        (𝙒 * highFixedScoreDenominator C.densityLower cMass * (2 / 𝙦) ^ d) ^ r /
          (r.factorial : ℝ) * ∫ u, 𝔚 u
            ∂𝔉 := by
  letI : 𝗄₁ := highUnionMark_standardBorel
  letI := 𝔙 highUnionSourceLaw_probability
  let π := 𝔇
  let act := 𝔊
  let p := 𝔗
  let F := 𝔓
  have hp : 𝘍 := 𝔙 highUnionSourceDensity_joint_measurable
  have hF : 𝗴 := 𝔙 highUnionSourceRegression_joint_measurable η
  have ham := highUnionActivation_measurable R G.activation_measurable $ highCenterMix C
  have hai : Integrable act π := Integrable.of_bound ham.aestronglyMeasurable
    𝗰₁
    $ Filter.Eventually.of_forall fun e => by simpa only [Real.norm_eq_abs] using 𝔙 highUnionSourceActivation_bound hpos e
  let c := 𝔎
  let Fh := 𝔟 highFrameField η 𝗏₁
  have hFh_eq : F h = Fh := by
    simp only [F,Fh,c]
    funext x
    unfold highUnionSourceRegression
    rfl
  have hFh : Measurable Fh := (𝔟 highFrameField_contDiff η _).continuous.measurable
  have hreg (j : 𝔑) (e : HighUnionMark E) (x : Covariate d) (y : Fin 3) :
      highMarkedResponseMass a V η 𝔣 c
        𝔛 𝔒
        (𝔖 e) x y =
      ternaryMass a (F (historyMarkedAppend
        𝔄
        𝔅 j 𝖷₁) x) V y := by
    unfold highMarkedResponseMass
    have hr := congrFun (𝔡 highUnionSourceRegression_append 1 hk η j h e 𝔘 x) 0
    exact congrArg (fun t : ℝ => ternaryMass a t V y) hr
  have hs := 𝔟 high_frame_complete_design_spatial_series D n hk
    𝔘 π 𝔘 act 𝔘 ham 𝔘 hai
    a V η C.densityLower C.densityUpper cMass ha C.densityLower_pos
    (by linarith [C.one_lt_densityUpper]) hcMass (p h) hp.of_uncurry_left
    𝔍
    𝔏
    𝔞 highUnionSourceResetDensity_measurable
    𝔞 highUnionSourceResetDensity_abs_le
    (fun j => 𝔡 highUnionSourceResetDensity_outside j h)
    𝔐
    𝔞 highUnionSourceResetCoefficient_measurable c
    (by
      change ∀ x y, cMass ≤ ternaryMass a (Fh x) V y
      intro x y
      rw [← hFh_eq]
      exact hq h x y) (by
      intro j e x y
      rw [hreg]
      exact hcMass.le.trans $ hq _ x y ) (fun j x => hDensity j h x) H hH hH0 hdom
  have he : highSampleIndexKernel n a V p F hp hF h =
      (Measure.pi fun _ : Fin n => highNormalizedDesignLaw $ p h ).compProd
        (responseSampleIndexKernel n a V Fh hFh) := by
    have hd := 𝔠 high_normalized_design_probability
    have hm : 0 < highRawDensityMass (p h) := C.densityLower_pos.trans_le
      (𝔠 highRawDensityMass_mem_Icc).1
    rw [highSampleIndexKernel_apply]
    have hed := (highSample_index_density n (p h) (F h) hp.of_uncurry_left hF.of_uncurry_left a V hd
      (fun x => C.densityLower_pos.le.trans (𝔙 highUnionSourceDensity_coarse_interval h x).1)
      hm fun x y => hcMass.le.trans $ hq h x y ).symm
    simpa only [hFh_eq,highSampleReference,highNormalizedDesignLaw] using hed
  have hS : highHistoryLikelihoodScore 𝔄
      𝔅 π act n a V η p F h =
      𝔟 highFrameFullMarkedScore D n 𝔘 π 𝔘 act a V η (p h)
        𝔏
        𝔐 c := by
    funext z
    obtain ⟨x,y⟩ := z
    exact 𝔡 highUnionSourceLikelihoodScore_eq_sum n hk a V η h x y
  dsimp only
  rw [hS,he]
  exact hs
