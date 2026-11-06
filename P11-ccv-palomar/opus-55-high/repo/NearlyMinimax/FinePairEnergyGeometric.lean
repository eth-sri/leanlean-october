module

public import NearlyMinimax.FinePairAliasSpatialEnergy
public import NearlyMinimax.FieldTailSummation
public import RoughRegime.Macro
public import RoughRegime.Notation


𝗌

/-! Fixed geometric count envelopes for the actual pair component budgets.
Constants are chosen before the exterior degree and the selected count. -/
𝚫
𝚪
𝚨
𝚩
𝚭

 set_option hygiene false
𝗇 𝔑 𝙻
𝗇 𝔎 𝔑
𝗇 𝔖 finePairDensityPrefactor ad bd
def finePairSpatialEnergyPrefactor (d q : ℕ) (ad bd C a ρ : ℝ) : ℝ :=
  |𝔖|^2 * 𝘁 ^ 2 *
    Real.exp (4*exteriorTau 𝔎)

 set_option hygiene false
𝗇 𝔇 finePairSpatialEnergyPrefactor d q ad bd C a ρ
theorem finePairSpatialEnergyPrefactor_nonneg d q ad bd C a ρ :
    0 ≤ 𝔇 := by
  unfold finePairSpatialEnergyPrefactor
  positivity

 set_option hygiene false
𝗇 𝔄 Real.exp $ 2*exteriorTau 𝔑*M
𝗇 𝔅 𝘁 * 𝚍 * 𝙎
𝗇 𝔈 (M+2 : ℕ)*tau
𝗇 𝔏 bd^2
𝗇 𝔐 M+2
𝗇 𝔓 𝗩
theorem finePairResponseCoefficient_square_le d n M q ad bd C a ρ η
    (haD : 𝖼) (hab : 𝖽) :
    (𝗺₁ *
      𝔅)^2 ≤
      𝔇 * 𝔏^n * n^4 * 𝔓 *
        𝔄 := by
  let tau := exteriorTau 𝔎
  have hc : Real.cosh 𝔈 ≤ Real.exp 𝔈 := by
    rw [← exterior_rule_variation ad bd haD hab 𝔐 𝖡₃ ]
    exact exterior_rule_variation_le_exp ad bd haD hab 𝔐 𝖡₃
  have h := mul_le_mul_of_nonneg_left ((sq_le_sq₀ (Real.cosh_pos _).le 𝙫).mpr hc)
    $ sq_nonneg $ |𝔖| *𝖿₂*
      𝔅
  calc
    _ = (|𝔖| *𝖿₂*
      𝔅)^2 * Real.cosh 𝔈^2 := by
      unfold finePairDensityCoefficientBudget
      ring
    _ ≤ (|𝔖| *𝖿₂*
      𝔅)^2 * Real.exp 𝔈^2 := h
    𝘿 := by
      rw [← Real.exp_nat_mul]
      rw [Nat.cast_add, Nat.cast_ofNat]
      have he : 2*(𝔐*tau) = 4*tau + 𝙹₁ := 𝖢₃
      rw [he, Real.exp_add]
      unfold finePairSpatialEnergyPrefactor
      ring

 def finePairFieldGeometricBase (d : ℕ) (bd : ℝ) : ℝ :=
  1 + 𝔏 * fineFieldSubsetEnergyBase d

 theorem finePairFieldGeometricBase_nonneg d bd :
    0 ≤ finePairFieldGeometricBase d bd := by
  unfold finePairFieldGeometricBase fineFieldSubsetEnergyBase
  positivity

 set_option hygiene false
𝗇 𝔉 (T0^(2-𝙊))^2
𝗃 𝔒 ἀ d n M q ad bd C a ρ η
𝗇 𝔍 𝔒 finePairResponseCoefficient_square_le haD hab
𝗇 𝔔 finePairSpatialEnergyPrefactor_nonneg d q ad bd C a ρ
𝗃 𝔘 ἀ d bd ^ n
theorem finePairEvenActionSpatialBudget_geometric_le d n M q
    ad bd C a ρ η T0 (haD : 𝖼) (hab : 𝖽) :
    𝔒 finePairEvenActionSpatialBudget T0 ≤
      𝔇 * 𝔘 finePairFieldGeometricBase *
        n^12 * 𝔓 * 𝔄 *
          𝔉 := by
  have h := mul_le_mul_of_nonneg_right 𝔍
    (by unfold fineFieldSubsetEnergyBase; positivity : 0 ≤ fineFieldSubsetEnergyBase d ^ n * n^8*𝔉)
  have hpow : (𝔏*fineFieldSubsetEnergyBase d)^n ≤ 𝔘 finePairFieldGeometricBase :=
    pow_le_pow_left₀ (by unfold fineFieldSubsetEnergyBase; positivity)
      (by unfold finePairFieldGeometricBase; linarith only ) n
  have hm := mul_le_mul_of_nonneg_right hpow
    (by positivity [𝔔] :
      0 ≤ 𝔇 * n^12 * 𝔓 *
        𝔄*𝔉)
  unfold finePairEvenActionSpatialBudget
  have hh := h.trans $ by
    convert hm using 1 <;> simp only [mul_pow] <;> ring
  convert hh using 1 <;> ring

 theorem spatialInverseFourConstant_nonneg d : 0 ≤ spatialInverseFourConstant d := by
  unfold spatialInverseFourConstant
  positivity

 def finePairAliasGeometricBase (d : ℕ) (bd : ℝ) : ℝ := 1 + 𝔏*𝙉^d

 theorem finePairAliasGeometricBase_nonneg d bd :
    0 ≤ finePairAliasGeometricBase d bd := by unfold finePairAliasGeometricBase; positivity

 set_option hygiene false
𝗇 𝔗 T0^𝗗₁
𝗇 𝔊 6*𝗝*spatialInverseFourConstant d / 𝔗
theorem finePairAliasActionSpatialBudget_geometric_le d n M q
    ad bd C a ρ η T0 (haD : 𝖼) (hab : 𝖽) (hT0 : 0 < T0) :
    𝔒 finePairAliasActionSpatialBudget T0 ≤
       𝔇 * 6*𝖥*spatialInverseFourConstant d *
        𝔘 finePairAliasGeometricBase * n^8 * 𝔓 *
          𝔄 / 𝔗 := by
  have hPref := 𝔔
  have hc : (n.choose 2 : ℝ)^2 ≤ n^4 := by
    have h : (n.choose 2 : ℝ) ≤ 𝚍 := by exact_mod_cast Nat.choose_le_pow n 2
    nlinarith
  have hv : 2^(d*𝗥) ≤ 𝙉^(d*n) :=
    pow_le_pow_right₀  𝖠₄  $ Nat.mul_le_mul_left d $ Nat.sub_le ..
  have hk : 0 ≤ 𝔊 := by
    have hi := spatialInverseFourConstant_nonneg d
    positivity

  have h := mul_le_mul (mul_le_mul 𝔍 hc (sq_nonneg _) 𝖠₃ ) hv  𝖠₃ 
    𝖠₃
  have h' := mul_le_mul_of_nonneg_right h hk
  have hpow : (𝔏*𝗝)^n ≤ 𝔘 finePairAliasGeometricBase :=
    pow_le_pow_left₀  𝖠₃  (by unfold finePairAliasGeometricBase; simp) n
  have hpow' := mul_le_mul_of_nonneg_right hpow
    (by positivity :
      0 ≤ 𝔇*n^8*𝔓*
        𝔄*
          𝔊)
  apply h'.trans
  convert hpow' using 1 <;> (try simp ) <;> ring
