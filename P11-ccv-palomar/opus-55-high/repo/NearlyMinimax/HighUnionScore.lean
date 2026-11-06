module

public import NearlyMinimax.HighCenteredRowUnion
public import NearlyMinimax.HighScoreOrthogonality
public import RoughRegime.Macro
public import RoughRegime.Notation

𝗌

/-! The actual full local signed-generator score. A genuine mark law acts
on the reset density and coefficient vector. The variance derivative occurs
exactly once, after the ordinary and fine-pair row actions are combined. -/
𝚫
𝚨
𝚩
𝚭
𝚬

section
𝛤

𝗃 𝔥 ἀ a V η g w φ
𝗇 𝔡 𝔥 highResponseProduct
𝗇 𝔙 𝔡 (cReset e) y
𝗇 𝔩 ∏ i, pReset e i
𝗇 𝔄 activation e * 𝔩 * 𝔙
𝗇 𝔉 𝙔
𝗇 𝔊 𝙛
𝗇 𝔓 𝙈
𝗇 𝔦 E → 𝔊
def highMarkedResponseAction (π : Measure E) (activation : 𝙏)
    (a V η : ℝ) (pReset : E → 𝔉) (cReset : 𝔦)
    (g w : 𝔉) (φ : Fin n → 𝔊) (y : 𝔓) : ℝ :=
  ∫ e, 𝔄 ∂π

𝗃 𝔬 ἀ π activation a V η
𝗇 𝔤 𝔬 highMarkedResponseAction pReset cReset g w φ
𝗇 𝔚 𝔤 y
𝗇 𝔢 𝔥 highResponseVarianceTerm c
𝗇 𝔞 𝔢 y i
𝗇 𝔪 𝗊
𝗇 𝔅 𝔚 - 𝙎 * 𝔪 * ∑ i, 𝖩 * 𝔞
𝗇 𝔇 𝔡 c y
𝗇 𝔍 𝔪
def highMarkedLocalScore (π : Measure E) (activation : 𝙏)
    (a V η : ℝ) (p : 𝔉) (pReset : E → 𝔉)
    (cReset : 𝔦) (g w : 𝔉) (φ : Fin n → 𝔊)
    (c : 𝔊) (y : 𝔓) : ℝ :=
  𝔅 /
    (𝔍 * 𝔇)

𝗇 𝔖 𝘝₁
theorem highMarkedResponseProduct_measurable a V η
    (cReset : 𝔦) (hc : 𝔖)
    (g w : 𝔉) φ y :
    Measurable fun e => 𝔙 := by
  apply Finset.measurable_fun_prod
  intro i _
  apply ternaryMass_measurable_comp
  unfold coefficientRegression
  fun_prop

𝗃 𝔭 hp i $ ἀ i
𝗇 𝔏 𝔭 y
𝗇 𝔨 𝗡 φ
theorem highMarkedResponseProduct_abs_le_one a V η (ha : 𝙞)
    (g w : 𝔉) φ (v : 𝔊)
    (hp : ∀ i b, 0 ≤ ternaryMass a (𝔨 v i) V b)
    y : |𝔡 v y| ≤ 1 := by
  unfold highResponseProduct
  rw [Finset.abs_prod]
  apply Finset.prod_le_one₀
  · simp
  · intro i _
    rw [abs_of_nonneg 𝔏]
    exact ternary_mass_le_one a _ V ha (hp i) $ y i

𝗇 𝔘 Integrable (fun e => 𝔄) π
𝗃 𝔮 fun i _ => ἀ i
/-- Integrability follows from the actual integrable activation, Borel
legal resets, and normalized nonnegative response masses. -/
theorem highMarkedResponseAction_integrable (π : Measure E)
    (activation : 𝙏) (hAct : Integrable activation π)
    (a V η : ℝ) (ha : 𝙞) (pPlus : ℝ) (hpPlus : 𝗊₂)
    (pReset : E → 𝔉) (hReset : ∀ i, Measurable fun e => pReset e i )
    (hBound : ∀ e i, |pReset e i| ≤ pPlus) (cReset : 𝔦)
    (hc : 𝔖)
    (g w : 𝔉) φ
    (hp : ∀ e i b, 0 ≤ ternaryMass a (𝔨 (cReset e) i) V b)
    (y : 𝔓) :
    𝔘 := by
  have hDensity := hAct.mul_bdd
    (Finset.measurable_fun_prod _ 𝔮 hReset).aestronglyMeasurable
    $ Filter.Eventually.of_forall fun e => by
      simpa only [Real.norm_eq_abs] using
        finite_density_product_abs_bound (pReset e) pPlus hpPlus $ hBound e
  exact hDensity.mul_bdd (highMarkedResponseProduct_measurable a V η cReset hc g w φ y).aestronglyMeasurable
    $ Filter.Eventually.of_forall fun e => by
      simpa only [Real.norm_eq_abs] using
        highMarkedResponseProduct_abs_le_one a V η ha g w φ (cReset e) (hp e) y

𝗇 𝔒 ∫ e, activation e * 𝔩 ∂π
𝗇 𝔔 𝔚
/-- Response normalization identifies the actual total action with the
conditional density action, rather than assuming score centering. -/
theorem highMarkedResponseAction_sum π activation
    a V η (ha : 𝙞) pReset (cReset : 𝔦)
    g w φ
    (hInt : ∀ y, 𝔘) :
     ∑ y : 𝔓, 𝔔 =
      𝔒 := by
  unfold highMarkedResponseAction
  rw [← integral_finsetSum Finset.univ fun y _ => hInt y ]
  simp_rw [← Finset.mul_sum, high_response_product_normalized a V η ha, mul_one]

𝗇 𝔣 𝔬 highMarkedLocalScore p pReset cReset g w φ c
𝗇 𝔈 𝔣 y
𝗇 𝔜 𝔨 c i
𝗇 𝔎 ∀ i b, 0 < ternaryMass a 𝔜 V b
𝗇 𝔛 Finset.prod_pos fun i _ => 𝔏
𝗇 𝔧 𝗎₂
/-- The full marked score is conditionally centered whenever the actual
signed density action vanishes. For the source row union this primitive
comes from each row's proved conditional zero-mass rule. -/
theorem highMarkedLocalScore_centered (π : Measure E) activation
    a V η ha p pReset
    cReset (g w : 𝔉) φ (c : 𝔊)
    (hpd : 𝔧)
    (hp : 𝔎)
    (hInt : ∀ y, 𝔘)
    (hDensity : 𝔒 = 0) :
    (∫ y, 𝔈
      ∂Measure.pi fun i => ternaryIndexMeasure a 𝔜 V
        ha 𝖢₁ ) = 0 := by
  rw [ternary_index_product_integral]
  change ∑ y, 𝔇 *
    𝔈 = 0
  have he y :
      𝔇 *
        𝔈 =
      𝔅 / 𝔍 := by
    have hL : 𝔇 ≠ 0 :=
      ne_of_gt 𝔛
    unfold highMarkedLocalScore
    field_simp
  simp_rw [he]
  rw [← Finset.sum_div, Finset.sum_sub_distrib,
    𝔬 highMarkedResponseAction_sum ha pReset cReset g w φ hInt,
    hDensity, ← Finset.mul_sum, Finset.sum_comm]
  simp only [← Finset.mul_sum, high_response_variance_term_sum_zero,
    mul_zero, Finset.sum_const_zero, sub_zero, zero_div]

𝗇 𝔐 𝔡 c y'
𝗇 𝔑 𝔡 c z
𝗇 𝔗 𝖩
𝗇 𝔟 𝔣
𝗇 𝔠 𝔤
𝗃 𝔫 ∑ i, 𝔗 * 𝔢 ἀ i
theorem highMarkedLocalScore_depends_on_support (π : Measure E)
    activation a V η p pReset
    cReset g w φ (c : 𝔊)
    (S : 𝙍) (hw : 𝖥₁)
    y y' (hyy : ∀ i ∈ S, y i = y' i)
    (hpd : 𝔧)
    (hp : 𝔎) :
    𝔈 =
      𝔟 y' := by
  have hB : 𝔍 ≠ 0 := Finset.prod_ne_zero_iff.mpr 𝔮 hpd
  have hLy : 𝔇 ≠ 0 :=
    ne_of_gt 𝔛
  have hLy' : 𝔐 ≠ 0 :=
    ne_of_gt $ Finset.prod_pos fun i _ => 𝔭 y'
  have hfirst : 𝔔 /
      𝔇 =
    𝔠 y' /
      𝔐 := by
    unfold highMarkedResponseAction
    rw [← integral_div, ← integral_div]
    apply integral_congr_ae
    apply Filter.Eventually.of_forall
    intro e
    simp only [mul_div_assoc]
    rw [𝔥 high_response_ratio_depends_on_support c (cReset e) S hw y y' hyy hp]
  have hvar :
      (∑ i, 𝔗 * 𝔞) /
        𝔇 =
      𝔫 y' /
        𝔐 := by
    simp_rw [Finset.sum_div, mul_div_assoc,
      𝔥 high_response_variance_ratio c y _ fun i => 𝔏 ,
      𝔥 high_response_variance_ratio c y' _ fun i => 𝔭 y' ]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : 𝚒₁
    all_goals simp_all
  have hrep z (hL : 𝔑 ≠ 0) :
      𝔟 z =
       𝔠 z /
        𝔑 / 𝔍 -
      𝙎 * (𝔫 z /
        𝔑) := by
    unfold highMarkedLocalScore
    field_simp
  simp_all

end

section RowUnion
variable {ι J : Type*} [Fintype ι] [DecidableEq ι] [Fintype J]
  {E : J → Type*} [∀ j, MeasurableSpace $ E j ]
