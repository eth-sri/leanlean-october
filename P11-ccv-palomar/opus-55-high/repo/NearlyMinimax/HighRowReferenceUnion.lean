module

public import NearlyMinimax.HighPacketBalancing
public import RoughRegime.Macro
public import RoughRegime.Notation

𝗌

/-! A genuine finite tagged union of centered row references. Row selection
is weighted by its actual variation budget, preserving the source constant
and the signed generator action. Distinct zero-activation corrective tags are
allowed by the source and do not change the signed measure. -/
𝚫
𝚳
𝚨
𝚩
𝚰
𝚬

section
𝗃 𝔟 ἀ $ E j
variable {J : Type*} [Fintype J] {E : J → Type*} [∀ j, 𝔟 MeasurableSpace]

theorem rowSigmaMk_measurable j : Measurable $ @Sigma.mk J E j := by
  apply Measurable.of_le_map
  exact iInf_le _ j

𝗇 𝔄 (j : J) → E j → ℝ
𝗇 𝔙 ∀ j, Measurable $ F j
theorem rowSigmaFunction_measurable (F : 𝔄)
    (hF : 𝔙) : Measurable fun e : Sigma E => F e.1 e.2 := by
  intro s hs
  aesop

theorem highRowReferenceUnion_standardBorel [∀ j, 𝔟 StandardBorelSpace] :
    StandardBorelSpace $ Sigma E := by
  letI := fun j => 𝔟 upgradeStandardBorel
  letI : BorelSpace $ Sigma E := historySigma_borelSpace
  infer_instance

𝗇 𝔗 J → ℝ
def highRowTotalMass (B : 𝔗) : ℝ := ∑ j, B j

def highRowSelectionProbability (B : 𝔗) (j : J) : ℝ := B j / highRowTotalMass B

𝗇 𝔇 ∀ j, 0 ≤ B j
𝗇 𝔉 highRowSelectionProbability B j
theorem highRowSelectionProbability_nonneg B (hB : 𝔇) (j : J) :
    0 ≤ 𝔉 :=
  div_nonneg (hB j) $ Finset.sum_nonneg fun j _ => hB j

𝗇 𝔎 ∀ j, 0 < B j
𝗇 𝔏 0 < highRowTotalMass B
theorem highRowSelectionProbability_pos B (hB : 𝔎)
    (hTotal : 𝔏) (j : J) : 0 < 𝔉 :=
  div_pos (hB j) hTotal

theorem highRowSelectionProbability_sum (B : 𝔗) (hTotal : highRowTotalMass B ≠ 0) :
     ∑ j, 𝔉 = 1 := by
  unfold highRowSelectionProbability
  rw [← Finset.sum_div]
  exact div_self hTotal

𝗇 𝔑 (j : J) → 𝔟 Measure
/-- The actual positive reference law on the finite tagged mark union. -/
def highRowReferenceUnion (π : 𝔑) (B : 𝔗) : Measure $ Sigma E :=
  ∑ j, ENNReal.ofReal 𝔉 • (π j).map (Sigma.mk j)

𝗇 𝔊 highRowReferenceUnion π B
theorem highRowReferenceUnion_probability (π : 𝔑)
    [∀ j, IsProbabilityMeasure $ π j ] B (hB : 𝔇)
    (hTotal : 𝔏) : IsProbabilityMeasure 𝔊 := by
  constructor
  rw [highRowReferenceUnion, Measure.finsetSum_apply]
  simp
  rw [← ENNReal.ofReal_sum_of_nonneg fun j _ => highRowSelectionProbability_nonneg B hB j ,
    highRowSelectionProbability_sum B hTotal.ne']
  norm_num

𝗇 𝔅 F ⟨j, e⟩
𝗇 𝔍 (integrable_map_measure hF.aestronglyMeasurable (rowSigmaMk_measurable j).aemeasurable).mpr $ hInt j
𝗃 𝔛 ∀ j, Integrable (fun e => ἀ) $ π j
𝗇 𝔔 𝔛 𝔅
𝗇 𝔚 Sigma E → ℝ
theorem highRowReferenceUnion_integrable π B
    (F : 𝔚) (hF : Measurable F)
    (hInt : 𝔔) :
    Integrable F 𝔊 := by
  apply integrable_finsetSum_measure.mpr
  intro j _
  have h := 𝔍
  exact h.smul_measure ENNReal.ofReal_ne_top

theorem highRowReferenceUnion_integral π B
    (hB : 𝔇) (F : 𝔚) (hF : Measurable F)
    (hInt : 𝔔) :
     ∫ e, F e ∂𝔊 =
      ∑ j, 𝔉 * ∫ e, 𝔅 ∂π j := by
  unfold highRowReferenceUnion
  rw [integral_finsetSum_measure fun j _ =>
    (𝔍).smul_measure ENNReal.ofReal_ne_top ]
  apply Finset.sum_congr rfl
  intro j _
  rw [integral_smul_measure, integral_map (rowSigmaMk_measurable j).aemeasurable hF.aestronglyMeasurable,
    ENNReal.toReal_ofReal $ highRowSelectionProbability_nonneg B hB j , smul_eq_mul]

def highRowUnionActivation (B : 𝔗) (w : 𝔄) (e : Sigma E) : ℝ :=
  w e.1 e.2 / highRowSelectionProbability B e.1

𝗇 𝔈 ∀ j, Measurable $ w j
𝗇 𝔘 highRowUnionActivation B w
theorem highRowUnionActivation_measurable B (w : 𝔄)
    (hw : 𝔈) : Measurable 𝔘 :=
  rowSigmaFunction_measurable _ fun j => (hw j).div_const _

𝗃 𝔞 ∀ j, Integrable (ἀ j) $ π j
𝗇 𝔐 𝔞 w
𝗇 𝔒 highRowUnionActivation_measurable B w hw
theorem highRowUnionActivation_integrable π
    B (w : 𝔄) (hw : 𝔈)
    (hInt : 𝔐) :
    Integrable 𝔘 𝔊 :=
  highRowReferenceUnion_integrable π B _ 𝔒
     fun j => by simpa only [highRowUnionActivation] using
      (hInt j).div_const 𝔉

𝗇 𝔓 highRowUnionActivation B w e
𝗃 𝔜 ∫ e, ἀ j e ∂π j
/-- Every row is genuinely centered; hence so is the combined activation. -/
theorem highRowUnionActivation_centered π
    B (hB : 𝔇) (w : 𝔄)
    (hw : 𝔈) (hInt : 𝔐)
    (hCenter : ∀ j, 𝔜 w = 0) :
     ∫ e, 𝔓 ∂𝔊 = 0 := by
  rw [highRowReferenceUnion_integral π B hB _ 𝔒
     fun j => by simpa only [highRowUnionActivation] using
      (hInt j).div_const 𝔉 ]
  simp only [highRowUnionActivation, integral_div, hCenter, zero_div, mul_zero, Finset.sum_const_zero]

/-- The exact source activation budget is retained by the finite mixture. -/
theorem highRowUnionActivation_bound B (hB : 𝔎)
    (hTotal : 𝔏) δ (hδ : 𝙮₂)
    w (hw : ∀ j e, |w j e| ≤ B j / δ) (e : Sigma E) :
    |𝔓| ≤ highRowTotalMass B / δ := by
  have hα := highRowSelectionProbability_pos B hB hTotal e.1
  unfold highRowUnionActivation
  rw [abs_div, abs_of_pos hα]
  apply (div_le_iff₀ hα).mpr
  have he : highRowTotalMass B / δ * highRowSelectionProbability B e.1 = B e.1 / δ := by
    unfold highRowSelectionProbability
    field_simp
  simp_all

𝗇 𝔖 w j e * 𝔅
/-- The signed action of all row tags is exactly the sum of their genuine
row actions; the mixture weights cancel and no signed action premise is used. -/
theorem highRowUnionActivation_action π
    B (hB : 𝔎) (hTotal : 𝔏)
    w (hw : 𝔈)
    (F : 𝔚) (hF : Measurable F)
    (hInt : 𝔛 𝔖) :
     ∫ e, 𝔓 * F e ∂𝔊 =
      ∑ j, ∫ e, 𝔖 ∂π j := by
  have he j : (fun e => 𝔘 ⟨j,e⟩ * 𝔅) =
       fun e => 𝔖 / 𝔉 := by
    funext e
    unfold highRowUnionActivation
    ring
  rw [highRowReferenceUnion_integral π B (fun j => (hB j).le)
    (fun e => 𝔓 * F e)
    ((𝔒).mul hF)
     fun j => by rw [he j]; fun_prop ]
  apply Finset.sum_congr rfl
  intro j _
  rw [he j, integral_div]
  exact mul_div_cancel₀ _ (highRowSelectionProbability_pos B hB hTotal j).ne'

theorem highRowReferenceUnion_integral_common_mean π
    B (hB : 𝔇) (hTotal : 𝔏)
    (F : 𝔄) (hF : 𝔙)
    (hInt : 𝔞 F) m
    (hMean : ∀ j, 𝔜 F = m) :
     ∫ e : Sigma E, F e.1 e.2 ∂𝔊 = m := by
  rw [highRowReferenceUnion_integral π B hB _ (rowSigmaFunction_measurable F hF) hInt]
  simp only [hMean]
  rw [← Finset.sum_mul, highRowSelectionProbability_sum B hTotal.ne', one_mul]
