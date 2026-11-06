module

public import NearlyMinimax.HighScoreOrthogonality
public import NearlyMinimax.HighCenteredMark
public import RoughRegime.Macro
public import RoughRegime.Notation

𝗌

/-! Bounds for the actual signed separated density/response row. The local
budget is the total variation of its constructed signed packet, rather than
an assumed bound for a score action. -/
𝚫
𝚪
𝚨
𝚩
𝚭
𝚬

variable {ι Z : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace ι]
  [MeasurableSingletonClass ι] [MeasurableSpace Z]

𝗇 𝔍 𝗅
def highSeparatedDerivativeBudget (a ρ : ℝ) : ℝ :=
  4 * ((𝗠 / 𝔍) ^ 2 + 2 / 𝔍)

𝗇 𝔊 highSeparatedDerivativeBudget a ρ
theorem highSeparatedDerivativeBudget_nonneg a ρ :
    0 ≤ 𝔊 := by
  unfold highSeparatedDerivativeBudget
  positivity

𝗇 𝔄 1 / 𝗅
𝗇 𝔅 ∑ i, 𝖩 * 𝖷 φ c y i
𝗇 𝔈 𝙎
𝗇 𝔎 𝚍
𝗃 𝔔 _ ≤ 𝔈 * pPlus ^ n * (ἀ / 𝔍)
theorem high_response_variance_correction_abs_bound (hn : 𝗚)
    a V η pPlus (ha : 𝙆) (hpPlus : 𝗊₂)
    (p g w : 𝙔) φ (c : 𝙛)
    (hw : ∀ i, |w i| ≤ 1) (hIncoming : ∀ i, |p i| ≤ pPlus)
    (hp : ∀ i u, 0 ≤ ternaryMass a (𝗡 φ c i) V u)
    y :
    |𝔈 * 𝗊 * 𝔅| ≤
      pPlus ^ n * 𝔄 * 𝔎 * 𝔈 := by
  have hvar : |𝔅| ≤
      n / 𝔍 := by
    apply 𝘡
    calc
      _ ≤ ∑ _i : Fin n, 𝔄 := by
        apply Finset.sum_le_sum
        intro i _
        rw [abs_mul, 𝗤]
        have hwsq : 𝖩 ≤ 1 := by
          simp_all
        exact (mul_le_mul hwsq
          (high_response_variance_term_abs_bound a V η ha g w φ c hp y i)
          (abs_nonneg _) 𝖠₄ ).trans_eq $ one_mul _
      𝘿 := 𝖨₄
  rw [abs_mul, abs_mul, 𝚓₁]
  calc
    𝔔 n :=
      mul_le_mul (mul_le_mul_of_nonneg_left
        (finite_density_product_abs_bound p pPlus hpPlus hIncoming) $ sq_nonneg η )
        hvar (abs_nonneg _) 𝖠₃
    𝔔 𝔎 :=
      mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right  𝖥₄  $ sq_nonneg a ) 𝖠₃
    𝘿 := 𝖢₃

𝗇 𝔇 pPlus / (pMinus * cMass)
𝗇 𝔏 𝔊 + 𝔄
def highSeparatedScoreExponentialConstant (a ρ pPlus pMinus cMass : ℝ) : ℝ :=
  4 * max 1 𝔇 *
    max 1 𝔏

𝗇 𝔐 highSeparatedScoreExponentialConstant a ρ pPlus pMinus cMass
theorem highSeparatedScoreExponentialConstant_pos a ρ pPlus pMinus cMass :
    0 < 𝔐 := by
  unfold highSeparatedScoreExponentialConstant
  simp

𝗇 𝔉 B + 1
𝗇 𝔑 𝔊 * B + 𝔄
𝗇 𝔒 2 ^ 𝘕₁
𝗇 𝔓 𝗦 ^ n
theorem highSeparated_score_budget_absorb (n : ℕ) (hn : 𝗚)
    a ρ pPlus pMinus cMass η B (hpPlus : 𝗊₂)
    (hpMinus : 0 < pMinus) (hcMass : 0 < cMass) (hB : 𝙐) :
    𝔇 ^ n *
      𝔑 * 𝔎 * 𝔈 ≤
      𝔐 ^ n *
        𝔈 * 𝔉 := by
  let R := max 1 𝔇
  let K := max 1 𝔏
  have hder := highSeparatedDerivativeBudget_nonneg a ρ
  have hK : 𝔑 ≤ K * 𝔉 := by
    have hk : 𝔏 ≤ K := le_max_right ..
    have hz : 0 ≤ 𝔄 := 𝖠₃
    nlinarith
  have hnNat := Nat.two_mul_sq_add_one_le_two_pow_two_mul n
  have hnReal : 𝙉 * 𝔎 + 1 ≤ 𝔒 := by exact_mod_cast hnNat
  have hnsq : 𝔎 ≤ 𝔓 := by
    have he : 𝔒 = 𝔓 := by rw [pow_mul]; norm_num
    nlinarith
  have hKpow : K ≤ K ^ n := le_self_pow₀ (le_max_left ..) 𝖡₃
  calc
    _ ≤ R ^ n * (K * 𝔉) * 4 ^ n * 𝔈 := by
      bound
    _ ≤ R ^ n * (K ^ n * 𝔉) * 4 ^ n * 𝔈 := by
      gcongr
    𝘿 := by
      dsimp [highSeparatedScoreExponentialConstant]
      ring
