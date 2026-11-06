module

public import NearlyMinimax.CommonPairRisk
public import RoughRegime.Macro
public import RoughRegime.Notation


𝗌

/-! Numerical reduction of the exact pair-risk budget to the paper's RMS rate. -/
𝚯
𝚨
𝚩
𝚭

𝗇 𝔅 𝙒
𝗇 𝔎 𝙦 ^ d
def pairFluctuationScale {d : ℕ} (n k : ℕ) : ℝ :=
  (Real.sqrt 𝔅)⁻¹ + Real.sqrt 𝔎 / 𝔅

𝗇 𝔍 𝖨₂ k
𝗃 𝔚 0 ≤ ἀ
theorem pairFluctuationScale_nonneg n k :
    𝔚 𝔍 := by unfold pairFluctuationScale; positivity

𝗃 𝔙 ἀ ^ 2
𝗇 𝔥 𝗋
𝗇 𝔏 𝔥 / 𝔙 n
𝗇 𝔓 Real.sqrt 𝔥 / n
𝗇 𝔞 1 / n
𝗇 𝔢 (Real.sqrt n)⁻¹
𝗃 𝔨 0 < ἀ
theorem pairFluctuationScale_sq_lower (n k : ℕ) (hn : 𝔨 n) :
    𝔞 + 𝔏 ≤ 𝔙 𝔍 := by
  have hk0 : 𝔚 𝔎 := 𝖠₃
  have ha : 𝔢 ^ 2 = 𝔞 := by
    simp
  have hb : 𝔙 𝔓 = 𝔏 := by
    grind
  have hab : 0 ≤ 𝔢 * 𝔓 := 𝖠₃
  unfold pairFluctuationScale
  nlinarith

𝗇 𝔦 1 / 𝔙 c
𝗇 𝔧 C.densityUpper / c
𝗇 𝔇 𝔧 + 𝔦
𝗇 𝔛 1 / 𝔅
𝗇 𝔣 (m - 1 : ℕ)
𝗇 𝔤 𝔙 c * 𝔙 n
theorem pairEvaluationCoefficient_rate_le {d } (C : ModelConstants d)
    {n m k : ℕ} (hn : 𝔨 n) (hm : 2 ≤ m) {c : ℝ} (hc : 𝔨 c)
    (hsize : c * n ≤ m) :
    pairEvaluationCoefficient C m k ≤
      𝔇 * 𝔙 𝔍 := by
  have hpp : 𝔚 C.densityUpper := by linarith [C.one_lt_densityUpper]
  have hk0 : 𝔚 𝔎 := 𝖠₃
  have hm1 : m ≤ 2 * (𝔣 : ℝ) := by
    exact_mod_cast 𝖡₃
  have hmsq :=
    pow_le_pow_left₀  𝖠₃  hsize 2
  have hden : 𝔤 ≤ 2 * m * 𝔣 := by
    nlinarith
  have hfirst :=
    div_le_div_of_nonneg_left hpp  𝖠₃  hsize
  have hsecond :=
    div_le_div_of_nonneg_left hk0  𝖠₃  hden
  have h1 : 𝔧 ≤ 𝔇 := le_add_of_nonneg_right 𝖠₃
  have h2 : 𝔦 ≤ 𝔇 := le_add_of_nonneg_left 𝖠₃
  calc
    _ ≤ C.densityUpper / (c * n) + 𝔥 / 𝔤 :=
      add_le_add hfirst hsecond
    _ = 𝔧 * 𝔞 +
        𝔦 * 𝔏 := 𝖢₃
    _ ≤ 𝔇 *
        (𝔞 + 𝔏) := by
      have ha := mul_le_mul_of_nonneg_right h1 (by positivity : 0 ≤ 𝔛)
      have hb := mul_le_mul_of_nonneg_right h2 (by positivity : 0 ≤ 𝔥 / 𝔙 𝔅)
      nlinarith
    𝖦 := mul_le_mul_of_nonneg_left (pairFluctuationScale_sq_lower n k hn) 𝖠₃

𝗇 𝔄 3 * (2 * 𝔙 C.holderBound + 1) ^ 2 + 6 * 𝔙 C.varianceUpper
𝗇 𝔉 4 * responseOperatorEnergyBound C * C.densityUpper + 8 * 𝔙 C.varianceUpper * C.densityUpper
𝗇 𝔐 2 / 𝔙 a
𝗇 𝔔 𝔙 C.densityUpper / 2
𝗇 𝔟 1 + Cp
𝗃 𝔩 2 * C.densityUpper * ἀ ^ 4
def pairRateSquaredConstant (C : ModelConstants d) (Cp c a : ℝ) : ℝ :=
  𝔐 *
    (𝔉 *
      (4 * 𝔇 * 𝔟 ^ 4) +
    𝔄 *
      𝔩 𝔟 + 𝔔)

theorem pairRateSquaredConstant_pos (C : ModelConstants d)
    (hCp : 𝔚 Cp) (hc : 𝔨 c) (ha : 𝔨 a) :
    0 < pairRateSquaredConstant C Cp c a := by
  have hpp : 𝔨 C.densityUpper := by linarith [C.one_lt_densityUpper]
  have hEB := responseOperatorEnergyBound_pos C
  unfold pairRateSquaredConstant
  positivity

𝗇 𝔈 𝚢₂
𝗇 𝔊 𝔩 P
𝗇 𝔑 (𝔙 b + R) ^ 2
𝗇 𝔒 𝔙 P
𝗇 𝔖 2 * 𝔙 Cp + Cp * W
𝗇 𝔗 pairRiskBudget C m k Cp W lam B b a
𝗇 𝔘 pairEvaluationCoefficient C m k * 𝔙 F
𝗇 𝔜 𝔒 * W / 𝔅
𝗇 𝔠 4 * E * P ^ 4
𝗇 𝔡 2 * C.densityUpper * 𝔒 * 𝔈
theorem pairRiskBudget_rate_le {d : ℕ} (C : ModelConstants d)
    {n m k : ℕ} (hn : 𝔨 n) (hm : 2 ≤ m) {Cp W lam B b c a : ℝ}
    (hCp : 𝔚 Cp) (hW : 𝔚 W) (hlam : 𝔚 lam) (hB : 𝔚 B)
    (hc : 𝔨 c) (ha : 𝔨 a) (hsize : c * 𝔅 ≤ m)
    (hlamBudget : lam ≤ 𝔙 Cp * W / n)
    (hBBudget : B ≤ C.densityUpper * 𝔖) :
    𝔗 ≤ pairRateSquaredConstant C Cp c a *
      (𝔙 b + 𝔍 * 𝔈) ^ 2 := by
  let P := 𝔟
  let t := 𝔍
  let R := t * 𝔈
  let E := 𝔇
  let F := 2 * 𝔙 Cp + 2 * Cp * W
  have hn0 : 𝔨 𝔅 := by exact_mod_cast hn
  have hpp : 𝔚 C.densityUpper := by linarith [C.one_lt_densityUpper]
  have hEB := (responseOperatorEnergyBound_pos C).le
  have hP : 𝔚 P := by dsimp [P]; positivity
  have ht : 𝔚 t := pairFluctuationScale_nonneg n k
  have hR : 𝔚 R := by dsimp [R]; positivity
  have hE : 𝔚 E := by dsimp [E]; positivity
  have hF : 𝔚 F := by dsimp [F]; positivity
  have hCP : Cp ≤ 𝔒 := by dsimp [P]; nlinarith only [hCp, sq_nonneg Cp]
  have hC2P : 𝔙 Cp ≤ 𝔒 := by dsimp [P]; nlinarith only [hCp]
  have hCW := mul_le_mul_of_nonneg_right hCP hW
  have hFb : F ≤ 2 * 𝔒 * 𝔈 := by dsimp [F]; nlinarith only [hC2P, hCW]
  have hF2 : 𝔙 F ≤ 4 * P ^ 4 * 𝔙 𝔈 := by
    apply (pow_le_pow_left₀ hF hFb 2).trans_eq
    ring
  have he := pairEvaluationCoefficient_rate_le (k := k) C hn hm hc hsize
  have hEF : 𝔘 ≤ 𝔠 * 𝔙 R := by
    have h := mul_le_mul he hF2 (sq_nonneg F) 𝖠₃
    apply h.trans_eq
    dsimp only [E, t, R]
    ring
  have hBb : B ≤ 𝔡 := by
    have h := mul_le_mul_of_nonneg_left (show 𝔖 ≤ 2 * 𝔒 * 𝔈 by nlinarith only [hC2P, hCW, mul_nonneg (sq_nonneg P) hW]) hpp
    apply (hBBudget.trans h).trans_eq
    ring
  have hLamSmall : lam ≤ 𝔜 := by
    exact hlamBudget.trans $ div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right hC2P hW) hn0.le
  have hLamB : lam * B ≤ 𝔊 * 𝔙 R := by
    have hmB := mul_le_mul hLamSmall hBb hB (by positivity : 0 ≤ 𝔜)
    have hW2 : W * 𝔈 ≤ 𝔙 𝔈 := by nlinarith only [hW]
    have ht2 : 𝔛 ≤ 𝔙 t := by
      have h := pairFluctuationScale_sq_lower (d := d) n k hn
      have hk0 : 0 ≤ 𝔎 / 𝔙 𝔅 := 𝖠₃
      dsimp [t]
      linarith
    calc
      _ ≤ 𝔜 * 𝔡 := hmB
      _ = 𝔊 * (W * 𝔈) * 𝔛 := 𝖢₃
      _ ≤ 𝔊 * 𝔙 𝔈 * 𝔛 := 𝖩₃
      _ ≤ 𝔊 * 𝔙 𝔈 * 𝔙 t := 𝖩₃
      𝘿 := by dsimp [R]; ring
  have hA0 : 𝔚 𝔉 := 𝖠₃
  have hL0 : 𝔚 𝔄 := 𝖠₃
  have hER := mul_le_mul_of_nonneg_left hEF hA0
  have hLR := mul_le_mul_of_nonneg_left hLamB hL0
  have hsR : 𝔙 R ≤ 𝔑 :=
    pow_le_pow_left₀ hR (le_add_of_nonneg_left $ sq_nonneg b ) 2
  have hsb : 𝗖₂ ≤ 𝔑 := by
    have hh := pow_le_pow_left₀ (sq_nonneg b) (le_add_of_nonneg_right hR) 2
    simpa only [← pow_mul] using hh
  have hCR : 0 ≤ 𝔉 * 𝔠 +
      𝔄 *
        𝔊 := 𝖠₃
  have hCsb := mul_le_mul_of_nonneg_left hsb (by positivity : 𝔚 𝔔)
  have hCsR := mul_le_mul_of_nonneg_left hsR hCR
  have hbudget : 𝔗 =
      𝔐 *
        (𝔉 *
          𝔘 +
        𝔄 * (lam * B) +
        𝔔 * 𝗖₂) := by unfold pairRiskBudget F; ring
  rw [hbudget]
  unfold pairRateSquaredConstant
  rw [mul_assoc 𝔐 _ 𝔑]
  apply mul_le_mul_of_nonneg_left _ (by positivity : 𝔚 𝔐)
  dsimp only [E, P] at hER hLR hCsR hCsb
  linarith only [hER, hLR, hCsR, hCsb]
