module

public import NearlyMinimax.FinePairEnergyGeometric
public import RoughRegime.Macro
public import RoughRegime.Notation


𝗌

/-! The constants in the genuine pair energy bounds are uniform over all
legal interior density intervals and therefore precede M and its shrinking. -/
𝚪
𝚨
𝚩
𝚭

 set_option hygiene false
𝗇 𝔍 bd-ad
𝗇 𝔓 𝖽
theorem finePairDensityPrefactor_eq (haD : 𝖼) (hab : 𝔓) :
    finePairDensityPrefactor ad bd = (𝔍/ad)^2 := by
  unfold finePairDensityPrefactor densityMargin
  field_simp [haD.ne', (haD.trans hab).ne', (sub_pos.mpr hab).ne']
  ring

 𝗇 𝔏 (bD-aD)/aD
𝗇 𝔑 𝘁
def finePairUniformSpatialPrefactor (d q : ℕ) (aD bD C a ρ c0 : ℝ) : ℝ :=
  𝔏^4 * 𝔑 ^ 2 * Real.exp (4*c0)

 set_option hygiene false
𝗇 𝔅 finePairUniformSpatialPrefactor d q aD bD C a ρ c0
theorem finePairUniformSpatialPrefactor_nonneg d q aD bD C a ρ c0 :
    0 ≤ 𝔅 := by
  unfold finePairUniformSpatialPrefactor
  positivity

 set_option hygiene false
𝗇 𝔄 exteriorTau $ (ad+bd)/𝔍
𝗇 𝔐 bd ≤ bD
theorem finePairSpatialEnergyPrefactor_uniform_le
    (haD : 𝘗₂) (ha : aD ≤ ad) (hb : 𝔐) (hab : 𝔓)
    (htau : 𝔄 ≤ c0) d q C a ρ :
    finePairSpatialEnergyPrefactor d q ad bd C a ρ ≤
      𝔅 := by
  have had := haD.trans_le ha
  have hratio : 𝔍/ad ≤ 𝔏 := by
    bound
  have h := mul_le_mul (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (div_nonneg (sub_nonneg.mpr hab.le) had.le) hratio 4)
    $ sq_nonneg 𝔑 ) (Real.exp_le_exp.mpr $ mul_le_mul_of_nonneg_left htau (by norm_num : 𝙋 ≤ 4) ) 𝙫
      𝖠₃
  unfold finePairSpatialEnergyPrefactor finePairUniformSpatialPrefactor
  rw [finePairDensityPrefactor_eq had hab, 𝗤]
  linarith

 𝗇 𝔒 pow_le_pow_left₀ hbd hb 2
theorem finePairFieldGeometricBase_mono (hbd : 0 ≤ bd) (hb : 𝔐) d :
    finePairFieldGeometricBase d bd ≤ finePairFieldGeometricBase d bD := by
  have h := mul_le_mul_of_nonneg_right 𝔒
    (by unfold fineFieldSubsetEnergyBase; positivity : 0 ≤ fineFieldSubsetEnergyBase d)
  unfold finePairFieldGeometricBase
  simpa

 theorem finePairAliasGeometricBase_mono (hbd : 0 ≤ bd) (hb : 𝔐) d :
    finePairAliasGeometricBase d bd ≤ finePairAliasGeometricBase d bD := by
  have h := mul_le_mul_of_nonneg_right 𝔒 (by positivity : 0 ≤ 𝙉^d)
  unfold finePairAliasGeometricBase
  linarith

 set_option hygiene false
𝗇 𝔇 (T0^(2-𝙊))^2
𝗇 𝔈 finePairSpatialEnergyPrefactor_uniform_le haD ha hb hab htau d q C a ρ
𝗇 𝔉 finePairUniformSpatialPrefactor_nonneg d q aD bD C a ρ c0
𝗇 𝔊 Real.exp $ 2*𝔄*M
𝗃 𝔎 ἀ d n M q ad bd C a ρ η T0
𝗇 𝔔 𝗩
𝗇 𝔖 finePairFieldGeometricBase_nonneg d bd
𝗃 𝔙 ἀ (had.trans hab).le hb d
theorem finePairEvenActionSpatialBudget_uniform_geometric_le
    (haD : 𝘗₂) (ha : aD ≤ ad) (hb : 𝔐) (hab : 𝔓)
    (htau : 𝔄 ≤ c0) d n M q C a ρ η T0 :
    𝔎 finePairEvenActionSpatialBudget ≤
      𝔅 * finePairFieldGeometricBase d bD ^ n *
        n^12 * 𝔔 * 𝔊 * 𝔇 := by
  have had := haD.trans_le ha
  have h := 𝔎 finePairEvenActionSpatialBudget_geometric_le had hab
  have hbase := pow_le_pow_left₀ 𝔖
    𝔙 finePairFieldGeometricBase_mono n
  have hmul := mul_le_mul 𝔈 hbase (pow_nonneg 𝔖 n)
    𝔉
  have hh := mul_le_mul_of_nonneg_right hmul
    (by positivity : 0 ≤ n^12*𝔔*𝔊*𝔇)
  linarith

 𝗇 𝔗 T0^𝗗₁
𝗇 𝔘 finePairAliasGeometricBase_nonneg d bd
theorem finePairAliasActionSpatialBudget_uniform_geometric_le
    (haD : 𝘗₂) (ha : aD ≤ ad) (hb : 𝔐) (hab : 𝔓)
    (htau : 𝔄 ≤ c0) d n M q C a ρ η T0 (hT0 : 0 < T0) :
    𝔎 finePairAliasActionSpatialBudget ≤
       𝔅 * 6*𝖥*spatialInverseFourConstant d *
        finePairAliasGeometricBase d bD ^ n * n^8 * 𝔔 *
          𝔊 / 𝔗 := by
  have had := haD.trans_le ha
  have h := 𝔎 finePairAliasActionSpatialBudget_geometric_le had hab hT0
  have hbase := pow_le_pow_left₀ 𝔘
    𝔙 finePairAliasGeometricBase_mono n
  have hmul := mul_le_mul 𝔈 hbase (pow_nonneg 𝔘 n)
    𝔉
  have hi := spatialInverseFourConstant_nonneg d
  have hh := mul_le_mul_of_nonneg_right hmul
    (by positivity : 0 ≤ 6*𝗝*spatialInverseFourConstant d*n^8*𝔔*
      𝔊/𝔗)
  grind
