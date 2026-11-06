module

public import NearlyMinimax.FinePairAllCounts
public import RoughRegime.Macro
public import RoughRegime.Notation

𝗌

/-! Uniform all-count response and density-coefficient bounds for the true
fine-pair row. The dependence on the exterior degree remains explicit. -/
𝚫
𝚪
𝚨
𝚩
𝚭

𝗇 𝔈 𝖵
def finePairResponseActionBudget (d q : ℕ) (C a ρ : ℝ) : ℝ :=
   512 * d * C^2 * (∑ j : Fin 𝔈, |responseWeight q j|) * highSeparatedDerivativeBudget a ρ

𝗇 𝔇 𝙬
𝗇 𝔍 𝖺₂
theorem finePairDistance_response_all_count_bound (q : ℕ) (hn : 𝗚)
    (C a V η ρ : ℝ) (hC : 𝙴) (ha : 𝙆) (hη : 𝗼) (hρ : 𝗛₁)
    (hηρ : η ≤ 𝙸) (U : 𝙇) (g w : 𝙔)
    (c : 𝖲) (y : 𝙈)
    (hc : ∑ γ, |c γ| ≤ 𝗳) (hg : ∀ i, |g i| ≤ 𝙸) (hw : ∀ i, |w i| ≤ 1)
    (hφ : ∀ v : 𝖲, ∑ γ, |v γ| ≤ 𝗳 →
      ∀ i, |∑ γ, highFrameFeature (U i) γ * v γ| ≤ 1)
    (hp : ∀ f : ℝ, |f| ≤ ρ → 𝘀) :
    |𝗔 𝔍 c
      (fun v => 𝖨 𝔇 v y)| ≤
        𝘁 * 𝙒^2 * 𝙎 := by
  have hh := high_response_matrix_all_count_bound q hn C a V η ρ hC ha hη hρ hηρ
    𝔍 g w 𝔇 c y hc hg hw hφ hp
  have hA := finePairDistanceMatrix_l1_le d F
  have hnonneg : 0 ≤ (∑ j : Fin 𝔈, |responseWeight q j|) *
      (4 * ((𝗠/𝗅)^2 + 2/𝗅) * 𝚍 * 𝙎) := 𝖠₃
  have hmul := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hA (by positivity : 0 ≤ 𝘖)) hnonneg
  exact (hh.trans hmul).trans_eq $ by
    unfold finePairResponseActionBudget highSeparatedDerivativeBudget
    ring

𝗇 𝔏 bd-ad
𝗇 𝔄 (M+2 : ℕ) * exteriorTau ((ad+bd)/𝔏)
def finePairDensityCoefficientBudget (ad bd : ℝ) (M n : ℕ) : ℝ :=
  |finePairDensityPrefactor ad bd| * 𝖿₂ *
    Real.cosh 𝔄

𝗇 𝔉 𝗺₁
theorem finePairDensityCoefficientBudget_nonneg ad bd (hbd : 0 ≤ bd) M n :
    0 ≤ 𝔉 := by
  unfold finePairDensityCoefficientBudget
  positivity

𝗇 𝔅 𝔏/(4*bd)
𝗇 𝔊 ∏ i ∈ S, p i
𝗇 𝔎 bd^(n-S.card)
theorem finePairCountCoefficient_product_bound
    ad bd (ha : 𝖼) (hab : 𝖽) M
    (p : 𝙔) (hp : 𝖳) S :
    |finePairCountCoefficient ad bd M n S.card * 𝔊| ≤
      𝔉 := by
  have hb := ha.trans hab
  have hcard : S.card ≤ n := by simpa using Finset.card_le_univ S
  have hpabs i : |p i| ≤ bd := by
    grind
  have hprod : |𝔊| ≤ bd^S.card := by
    rw [Finset.abs_prod]
    exact (Finset.prod_le_prod₀ 𝖢 fun i _ => hpabs i ).trans_eq
      $ Finset.prod_const _
  have hr1 : 𝔅 ≤ 1 := by
    bound
  have hcoeff := finePairCountCoefficient_abs_bound ad bd ha hab M n S.card
  have he : |finePairDensityPrefactor ad bd| *
      (𝔎 * 𝔅^S.card) *
      Real.cosh 𝔄 * bd^S.card =
      𝔉 * 𝔅^S.card := by
    unfold finePairDensityCoefficientBudget
    have hpow : 𝔎 * bd^S.card = 𝖿₂ := by
      rw [← pow_add, Nat.sub_add_cancel hcard]
    grind
  rw [abs_mul]
  apply (mul_le_mul hcoeff hprod (abs_nonneg _) 𝖠₃ ).trans
  rw [he]
  exact (mul_le_mul_of_nonneg_left (pow_le_one₀ (div_nonneg (sub_nonneg.mpr hab.le) 𝖠₃ ) hr1)
    $ finePairDensityCoefficientBudget_nonneg ad bd hb.le M n ).trans_eq $ mul_one _
