module

public import NearlyMinimax.HistoryLabelDerivative
public import RoughRegime.Macro
public import RoughRegime.Notation


𝗌

/-!
# Actual weak transport of the positive marked-history prior
-/

𝚩
𝛊
𝚮
𝚨

𝚲

𝗇 𝔄 𝘼
𝗇 𝔙 𝙯₁ p
𝗇 𝔈 F 𝔙 * a p.2
𝗇 𝔍 𝙁
𝗇 𝔏 𝙗
/-- The actual generator before folding the history into raw fields: append a fresh local mark. -/
def historyMarkedGeneratorExpectation (dependent : 𝔍)
    (hsymm : 𝔄) (ρ t : ℝ)
    [MeasurableSpace E] (μ : Measure 𝔏) (π : Measure E)
    (a : 𝙏) (F : 𝔏 → ℝ) : ℝ :=
  ∑ j, ∫ p : 𝔏 × E,
    𝔈 *
      𝘡₂ t a p.1 ∂μ.prod π

𝗃 𝔚 ἀ dependent $ historyReferenceRho Δ
𝗇 𝔖 𝔚 historyMarkedLabelTerm t a j h
𝗇 𝔅 F h * 𝔖
𝗇 𝔇 𝙤
𝗇 𝔎 𝙂
𝗇 𝔔 𝔈 * 𝔚 historyMarkedDensity t a p.1
𝗃 𝔗 ἀ dependent hrefl hsymm Δ
𝗇 𝔘 ∫ h, 𝔅 ∂𝔇
/-- Exact signed integral change of variables, proved for the actual normalized reference law. -/
theorem historyMarkedLabelTerm_integral (dependent : 𝔍)
    (hrefl : 𝔎) (hsymm : 𝔄)
    (Δ : ℕ) (t : ℝ) [MeasurableSpace E] [StandardBorelSpace E]
    (π : Measure E) [IsProbabilityMeasure π] a (ha : Measurable a)
    F (hF : Measurable F) j :
    𝔘 =
    historyReferenceRho Δ * ∫ p : 𝔏 × E,
      𝔔
        ∂(𝔇).prod π := by
  let μ := 𝔇
  let G := fun h =>
    𝔅
  have hG : Measurable G := hF.mul $ historyMarkedLabelTerm_measurable dependent _ t a ha j
  have he := congrArg (fun ν => ∫ h, G h ∂ν) $ 𝔗 historyMarkedReference_append_restrict j π
  rw [integral_smul_measure, integral_map (historyMarkedAppend_measurable dependent hsymm j).aemeasurable
    hG.aestronglyMeasurable] at he
  have hi : (historyMarkedTerminalSet dependent j).indicator G = G := by
    funext h
    by_cases ht : h ∈ historyMarkedTerminalSet dependent j
    · simp [ht]
    · simp [G, historyMarkedLabelTerm_eq_zero dependent hsymm _ t a j h ht]
  rw [← integral_indicator $ historyMarkedTerminalSet_measurable dependent j , hi] at he
  rw [ENNReal.toReal_ofReal 𝘤] at he
  have hp : ∀ p ,
      G 𝔙 =
        𝔔 := by
    intro p
    dsimp only [G]
    rw [historyMarkedLabelTerm_append dependent hrefl hsymm]
    ring
  simp_rw [hp] at he
  exact he.symm

𝗇 𝔉 𝘽
𝗇 𝔊 𝙥
𝗇 𝔒 F h * historyMarkedLabelTerm dependent ρ t a j h
/-- Bounded observables times true maximal-label terms are integrable over every finite law. -/
theorem historyMarkedLabelTerm_integrable (dependent : 𝔍)
    (hrefl : 𝔎) (hsymm : 𝔄)
    (Δ : ℕ) (hlabels : 𝔉)
    (ρ t B : ℝ) (hρ : 𝘢₁) (ht : 𝘈) (hB : 𝙐)
    [MeasurableSpace E] (μ : Measure 𝔏) [IsFiniteMeasure μ]
    a (ha : Measurable a) (habound : ∀ e, |a e| ≤ B)
    (hsmall : 𝘡₁ ≤ 𝔊)
    F (hF : Measurable F)
    M (hM : 𝙷) (hFbound : ∀ h, |F h| ≤ M) j :
    Integrable (fun h => 𝔒) μ := by
  apply Integrable.of_bound (hF.mul $ historyMarkedLabelTerm_measurable dependent ρ t a ha j ).aestronglyMeasurable
    $ M * (B * 𝗞 ^ Fintype.card J)
  apply Eventually.of_forall
  intro h
  change ‖𝔒‖ ≤ _
  rw [Real.norm_eq_abs, abs_mul]
  exact mul_le_mul (hFbound h)
    (𝔗 historyMarkedLabelTerm_bound hlabels ρ t B hρ ht hB a habound hsmall j h)
    (abs_nonneg _) hM

𝗇 𝔐 F h * 𝔚 historyMarkedDensityDerivative t a h
𝗇 𝔑 (historyReferenceRho Δ)⁻¹
𝗇 𝔓 historyMarkedGeneratorExpectation dependent hsymm (historyReferenceRho Δ) t 𝔇 π a F
/-- The integral of the actual density derivative is exactly the source signed append generator. -/
theorem historyMarkedDensityDerivative_integral_eq_generator (dependent : 𝔍)
    (hrefl : 𝔎) (hsymm : 𝔄)
    (Δ : ℕ) (hΔ : 𝙘) (hlabels : 𝔉)
    (t B : ℝ) (ht : 𝘈) (hB : 𝙐) [MeasurableSpace E] [StandardBorelSpace E]
    (π : Measure E) [IsProbabilityMeasure π] a (ha : Measurable a)
    (habound : ∀ e, |a e| ≤ B)
    (hsmall : t * B / historyReferenceRho Δ ≤ 𝔊)
    F (hF : Measurable F)
    M (hM : 𝙷) (hFbound : ∀ h, |F h| ≤ M) :
     ∫ h, 𝔐
      ∂𝔇 =
      𝔓 := by
  let μ := 𝔇
  let := 𝔗 historyMarkedReference_probability hΔ hlabels π
  have hi :=
     𝔗 historyMarkedLabelTerm_integrable hlabels _ t B
      (historyReferenceRho_pos Δ) ht hB μ a ha habound hsmall F hF M hM hFbound
  have hp : ∀ h ,
      𝔐 =
        𝔑 * ∑ j, 𝔅 := by
    intro h
    rw [historyMarkedDensityDerivative_eq_labelSum]
    calc
      _ = 𝔑 *
          (F h * ∑ j, 𝔖) := 𝖢₃
      𝘿 := by rw [Finset.mul_sum]
  simp_rw [hp]
  rw [integral_const_mul, integral_finsetSum Finset.univ fun j _ => hi j ]
  change 𝔑 *
     ∑ j, 𝔘 = _
  simp_rw [𝔗 historyMarkedLabelTerm_integral t π a ha F hF]
  unfold historyMarkedGeneratorExpectation
  rw [← Finset.mul_sum]
  rw [← mul_assoc, inv_mul_cancel₀ $ ne_of_gt $ historyReferenceRho_pos Δ , one_mul]

/-- Genuine interior weak evolution of the positive marked-history density law. -/
theorem historyMarkedExpectation_weak_transport (dependent : 𝔍)
    (hrefl : 𝔎) (hsymm : 𝔄)
    (Δ : ℕ) (hΔ : 𝙘) (hlabels : 𝔉)
    (T B t : ℝ) (ht : 𝘁₁) (htT : t < T) (hB : 𝙐)
    [MeasurableSpace E] [StandardBorelSpace E]
    (π : Measure E) [IsProbabilityMeasure π] a (ha : Measurable a)
    (habound : ∀ e, |a e| ≤ B)
    (hsmall : 𝚅₂ ≤ 𝔊)
    F (hF : Measurable F)
    M (hM : 𝙷) (hFbound : ∀ h, |F h| ≤ M) :
    HasDerivAt (𝔚 historyMarkedExpectation
      𝔇 a F)
      𝔓 t := by
  let := 𝔗 historyMarkedReference_probability hΔ hlabels π
  have hd := (𝔗 historyMarkedExpectation_hasDerivAt hlabels
    (historyReferenceRho Δ) T B t (historyReferenceRho_pos Δ) ht htT hB
    𝔇 a ha habound hsmall F hF M hM hFbound).2
  rw [𝔗 historyMarkedDensityDerivative_integral_eq_generator hΔ hlabels
    t B ht.le hB π a ha habound ((div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right htT.le hB) 𝘤).trans hsmall) F hF M hM hFbound] at hd
  exact hd
