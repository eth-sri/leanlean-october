module

public import NearlyMinimax.FinePairRowMass
public import NearlyMinimax.FinePairMatrixCost
public import NearlyMinimax.HigherBandActivity
public import RoughRegime.Macro
public import RoughRegime.Notation


𝗌

/-! Activity bounds of all three genuine fine-pair rows. -/
𝚫
𝚪
𝚨
𝚩
𝚾

𝗇 𝔊 𝖵
𝗇 𝔍 𝘖
def sourceResponseCost (q : ℕ) (C : ℝ) : ℝ :=
  (∑ h : Fin 𝔊, |𝘐₁|) * 𝔍

theorem sourceResponseCost_nonneg q C : 0 ≤ sourceResponseCost q C := by
  unfold sourceResponseCost
  positivity

𝗇 𝔄 exteriorTau 𝖬
𝗃 𝔘 ἀ a b
𝗇 𝔅 𝔘 ordinaryDensityActivityBase^2
𝗇 𝔏 𝙆
𝗇 𝔐 𝙭
𝗇 𝔑 M * 𝔄
theorem finePairDensityWeight_le_base a b (ha : 𝔏) (hab : 𝔐)
    M :
     ∑ h : FinePairDensityIndex M, |𝔘 finePairDensityWeight M h| ≤
      2 * 𝔅 * Real.exp 𝔑 := by
  have hp : |𝔘 finePairDensityPrefactor| = |b / 𝔘 densityMargin 0|^2 := by
    simp only [finePairDensityPrefactor, abs_div, abs_pow, div_pow]
  have he : Real.exp (2 * 𝔄) ≤
      Real.exp (1 + 𝔄)^2 := by
    rw [← Real.exp_nat_mul]
    norm_num
  apply (𝔘 finePairDensityWeight_exponential_cost ha hab M).trans
  rw [hp, ordinaryDensityActivityBase, mul_pow]
  have h0 := mul_le_mul_of_nonneg_left he (by positivity : 0 ≤ 2 * |b / 𝔘 densityMargin 0|^2)
  apply mul_le_mul_of_nonneg_right _ 𝙫
  linarith

𝗃 𝔗 ἀ d D M q a b C ℓ N
𝗇 𝔇 𝔗 finePairRowMass
𝗇 𝔉 𝔅 * 𝘔 * Real.exp (D * 𝔄) * sourceResponseCost q C
𝗇 𝔎 𝔘 densityPacketWeight_exponential_cost ha hab D 2 D
theorem finePairRowMass_unit_le d D M q (hD : 𝗮)
    a b (ha : 𝔏) (hab : 𝔐) C ℓ N :
    𝔇 .unit ≤
      𝔉 := by
  rw [finePairRowMass_unit]
  have hc : 0 ≤ (∑ h : Fin 𝔊, |𝘐₁|) * 𝔍 := 𝖠₃
  have hm := mul_le_mul (𝔎  𝖠₄  hD) (finePairUnitMatrix_l1_le d D) (Finset.sum_nonneg fun _ _ =>
    Finset.sum_nonneg 𝖢) 𝖠₃
  have hh := mul_le_mul_of_nonneg_left hm hc
  dsimp [ordinaryDensityActivityBase, sourceResponseCost, spatialMatrixL1] at *
  linarith

𝗇 𝔒 128 * d
𝗇 𝔓 finePairDistanceMatrix_l1_le d D
𝗇 𝔔 ℓ^2/2
𝗇 𝔖 mul_le_mul_of_nonneg_left hm $ sourceResponseCost_nonneg q C
theorem finePairRowMass_coarse_le (d : ℕ) [NeZero d] D M q (hD : 𝗮)
    a b (ha : 𝔏) (hab : 𝔐) C ℓ N (hℓ : 0 ≤ ℓ) :
    𝔇 .coarse ≤
      𝔉 *
          (𝔒 * ℓ^2) := by
  rw [𝔗 finePairRowMass_coarse hℓ]
  have hmat := mul_le_mul_of_nonneg_right 𝔓
    (by positivity : 0 ≤ 𝔔)
  have hm := mul_le_mul (𝔎  𝖠₄  hD) hmat (by positivity : 0 ≤
    (∑ i, ∑ j, |𝗀₂ i j|) * 𝔔) 𝖠₃
  have hh := 𝔖
  dsimp [ordinaryDensityActivityBase, sourceResponseCost, spatialMatrixL1] at *
  linarith

𝗇 𝔈 (𝘚₂-ℓ^2)/2
theorem finePairRowMass_fine_le (d : ℕ) [NeZero d] D M q
    a b (ha : 𝔏) (hab : 𝔐) C ℓ N (hℓ : 0 ≤ ℓ) (hℓN : ℓ ≤ N) :
    𝔇 .fine ≤
      𝔅 *
        Real.exp 𝔑 * sourceResponseCost q C *
          ( 256 * d * 𝘚₂) := by
  rw [𝔗 finePairRowMass_fine hℓ hℓN]
  have hdiff : 0 ≤ 𝔈 := 𝖥₃
  have hmat := mul_le_mul_of_nonneg_right 𝔓 hdiff
  have hmat' : (∑ i, ∑ j, |𝗀₂ i j|) * 𝔈 ≤
      𝔒 * 𝘚₂ := by
    apply hmat.trans
    nlinarith
  have hm := mul_le_mul (𝔘 finePairDensityWeight_le_base ha hab M) hmat'  𝖠₃  𝖠₃
  have hh := 𝔖
  dsimp [sourceResponseCost] at *
  linarith
