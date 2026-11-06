module

public import NearlyMinimax.HighUnionScore
public import NearlyMinimax.HighLocalFrame
public import RoughRegime.Macro
public import RoughRegime.Notation


𝗌

/-! Disjoint-patch orthogonality and the exact torus overlap bound for the
complete marked local generator, with its variance correction counted once.
The final endpoint uses the actual polynomial field decomposition. -/
𝚯
𝚪
𝚨
𝚩
𝚰
𝚬

𝗇 𝔙 pReset j e i
𝗇 𝔇 ∀ j, ∫ e, activation j e * ∏ i, 𝔙 ∂π j = 0
𝗇 𝔈 𝖢₁
𝗇 𝔊 𝙔
𝗇 𝔐 𝗎₂
𝗃 𝔢 ἀ (π j) $ activation j
𝗃 𝔪 𝔢 ἀ a V η p (pReset j) $ cReset j
𝗇 𝔜 𝔪 highMarkedLocalScore
𝗇 𝔥 cReset j e
section GenericFamily
variable {J ι E : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace E]

𝗇 𝔗 fun i => ternaryIndexMeasure a (f i) V ha 𝔈
𝗇 𝔞 𝗢₂
𝗃 𝔡 ἀ (π l) (activation l) a V η p (pReset l) (cReset l) (g l) (w l) (φ l) $ c l
𝗃 𝔬 0 < ternaryMass a (ἀ i) V b
theorem highMarkedLocalScores_orthogonal
    (π : J → Measure E) (activation : J → 𝙏) (a V η : ℝ) (ha : 𝙞)
    (p : 𝔊) (pReset : J → E → 𝔊)
    (cReset : J → E → 𝙛) (g w : J → 𝔊)
    (φ : J → Fin n → 𝙛) (c : J → 𝙛) (f : 𝔊)
    (hreg : ∀ j, 𝔞 = f)
    (S : J → 𝙍) (hw : ∀ j i, i ∉ S j → w j i = 0)
    (hpd : 𝔐) (hp : ∀ i b, 𝔬 f)
    (hInt : ∀ j y, Integrable (fun e => activation j e * (∏ i, 𝔙) *
      highResponseProduct a V η (g j) (w j) (φ j) 𝔥 y) $ π j )
    (hDensity : 𝔇)
    (j l : J) (hST : Disjoint (S j) $ S l ) :
     ∫ y, 𝔜
      (g j) (w j) (φ j) (c j) y *
      𝔡 highMarkedLocalScore y
      ∂Measure.pi 𝔗 = 0 := by
  let μ := 𝔗
  have hp' (j : J) (i : Fin n) (b : Fin 3) :
      𝔬 𝔞 := by
    simp_all
  apply local_response_scores_orthogonal μ _ _ (S j) (S l) hST
  · intro y y' hyy
    exact 𝔪 highMarkedLocalScore_depends_on_support (g j) (w j) (φ j) (c j) (S j) (hw j) y y' hyy hpd $ hp' j
  · intro y y' hyy
    exact 𝔡 highMarkedLocalScore_depends_on_support (S l) (hw l) y y' hyy hpd $ hp' l
  · have h := 𝔢 highMarkedLocalScore_centered a V η ha p
      (pReset j) (cReset j) (g j) (w j) (φ j) (c j) hpd (hp' j) (hInt j) $ hDensity j
    aesop

end GenericFamily

section ActualField
𝛙

𝗃 𝔨 ἀ d k
𝗇 𝔍 𝔨 HighWindowLabels
𝗇 𝔑 𝙮 → ℝ
𝗇 𝔚 𝔨 highLocalFieldWithout D η c j $ x i
𝗇 𝔓 𝔚
𝗇 𝔦 𝔨 highPeriodicTensor j $ x i
𝗃 𝔩 fun i => ἀ
𝗇 𝔖 𝔩 𝔦
𝗇 𝔧 highLocalFrameFeature k j $ x i
𝗇 𝔘 𝔩 𝔧
𝗇 𝔣 𝙇
𝗇 𝔤 𝔍 → Measure E
def highFrameMarkedScore (d k D n : ℕ) [NeZero k]
    (π : 𝔤)
    (activation : 𝔍 → 𝙏) (a V η : ℝ) (p : 𝔊)
    (pReset : 𝔍 → E → 𝔊)
    (cReset : 𝔍 → E → 𝔑)
    (c : 𝔍 → 𝔑) (x : 𝔣)
    (j : 𝔍) (y : 𝙈) : ℝ :=
  𝔜
    𝔩 𝔓
    𝔖
    𝔘 (c j) y

𝗇 𝔄 𝔨 highFrameField η 𝗏₁ $ x i
𝗇 𝔅 ∀ j e i b, 0 ≤ ternaryMass a (coefficientRegression η 𝔩 𝔚 𝔖 𝔘 𝔥 i) V b
𝗇 𝔠 𝔨 highFrameMarkedScore D n π activation a V η p pReset cReset c x
𝗇 𝔉 𝔠 j y
𝗇 𝔎 ∀ j i, Measurable fun e => 𝔙
𝗇 𝔏 ∀ j γ, Measurable fun e => 𝔥 γ
𝗇 𝔒 ∀ j, Integrable (activation j) $ π j
𝗇 𝔔 Measure.pi fun i => ternaryIndexMeasure a 𝔄 V ha 𝔈
𝗇 𝔛 ∀ i b, 0 < ternaryMass a 𝔄 V b
𝗇 𝔟 𝔠
𝗃 𝔫 fun j i => ἀ
/-- Conditional orthogonality of the true complete signed-generator scores
is proved from actual response normalization, conditional density zero mass,
and the original window supports. -/
theorem highFrameMarkedScore_orthogonal (d k D n : ℕ) [NeZero k] (hk : 𝗑)
    (π : 𝔤)
    activation (hAct : 𝔒)
    a V η pPlus ha (hpPlus : 𝗊₂) p
    pReset
    (hReset : 𝔎)
    (hBound : ∀ j e i, |𝔙| ≤ pPlus)
    cReset
    (hcReset : 𝔏)
    (c : 𝔍 → 𝔑) (x : 𝔣)
    (hpd : 𝔐)
    (hp : 𝔛)
    (hpReset : 𝔅)
    (hDensity : 𝔇)
    j l (hjl : l ∉ 𝔨 highNeighborLabels j) :
     ∫ y, 𝔉 *
      𝔟 l y
      ∂𝔔 = 0 := highMarkedLocalScores_orthogonal π activation a V η ha p pReset cReset
    𝔫 𝔓
    𝔫 𝔦
    𝔫 𝔧 c
    𝔩 𝔄
    (fun j => 𝔨 highFrameField_coefficientRegression D n hk η c j x)
    (fun j => 𝔨 highPatchSampleIndices n j x)
    (fun j i hi => 𝔨 highPeriodicTensor_sample_zero_outside_patch n j x i hi)
    hpd hp (fun j y => 𝔢 highMarkedResponseAction_integrable (hAct j)
      a V η ha pPlus hpPlus (pReset j) (hReset j) (hBound j) (cReset j) (hcReset j)
      _ _ _ (hpReset j) y) hDensity j l
    $ 𝔨 highPatchSampleIndices_disjoint n x j l hjl

/-- The exact source overlap factor is established for the complete union
score, after the single variance correction and the genuine local field
decomposition. No covariance or score-energy bound is a premise. -/
theorem highFrameMarkedScore_energy_bound (d k D n : ℕ) [NeZero k] (hk : 𝗑)
    (π : 𝔤)
    activation (hAct : 𝔒)
    (a V η pPlus : ℝ) (ha : 𝙞) (hpPlus : 𝗊₂) (p : 𝔊)
    pReset
    (hReset : 𝔎)
    (hBound : ∀ j e i, |𝔙| ≤ pPlus)
    cReset
    (hcReset : 𝔏)
    (c : 𝔍 → 𝔑) (x : 𝔣)
    (hpd : 𝔐)
    (hp : 𝔛)
    (hpReset : 𝔅)
    (hDensity : 𝔇) :
     ∫ y, (∑ j, 𝔉)^2
      ∂𝔔 ≤
      (𝚐 : ℕ) * ∑ j, ∫ y,
        𝔉^2
        ∂𝔔 := by
  apply finite_overlap_variance_bound _
    𝔟
    (fun j l => l ∈ 𝔨 highNeighborLabels j) 𝚐
  · intro j l
    exact ⟨𝔨 highNeighborLabels_symmetric j l, 𝔨 highNeighborLabels_symmetric l j⟩
  · intro j
    convert 𝔨 highNeighborLabels_card_le j using 1
    simp
  · intro j l hjl
    exact 𝔨 highFrameMarkedScore_orthogonal D n hk π activation hAct a V η pPlus ha hpPlus
      p pReset hReset hBound cReset hcReset c x hpd hp hpReset hDensity j l hjl
