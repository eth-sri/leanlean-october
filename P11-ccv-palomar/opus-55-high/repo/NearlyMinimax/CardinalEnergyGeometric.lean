module

public import NearlyMinimax.HighCardinalSpatialEnergy
public import NearlyMinimax.TargetDefectBudget
public import RoughRegime.Macro
public import RoughRegime.Notation


𝗌

/-! Geometric count envelopes for the actual matched cardinal component
budgets, with fixed density upper bound before the density shrinking. -/
𝚪
𝚨
𝚩
𝚱

 set_option hygiene false
𝗇 𝔄 𝙉^d
𝗇 𝔒 𝙒^2
def cardinalAliasSpatialComponent (d n : ℕ) (bd a η T : ℝ) : ℝ :=
  𝗶₂ * 𝔒*𝔄*cardinalDefectSquareBudget d n T

 set_option hygiene false
𝗇 𝔇 𝗈
def cardinalTaylorSpatialComponent (d n q : ℕ) (bd C a ρ η : ℝ) : ℝ :=
  𝘔₁ * 𝔒*𝔄*
    ((100*𝙊)^2*16*spatialScaleIntegralConstant d)^𝔇

 𝗇 𝔎 cardinalTaylorSpatialComponent d n q bd C a ρ η
𝗇 𝔓 cardinalAliasSpatialComponent d n bd a η T
theorem cardinalRawSpatialEnergyBudget_split d n q bd C a ρ η T :
    cardinalRawSpatialEnergyBudget d n q bd C a ρ η T =
      𝔓 + 𝔎 := by
  unfold cardinalRawSpatialEnergyBudget cardinalAliasSpatialComponent cardinalTaylorSpatialComponent
  ring

 𝗇 𝔏 B^2*max 1 κ
def cardinalSpatialGeometricBase (B κ : ℝ) : ℝ := 1+𝔏

 theorem cardinalSpatialGeometricBase_nonneg B κ : 0 ≤ cardinalSpatialGeometricBase B κ := by
  unfold cardinalSpatialGeometricBase
  positivity

 theorem cardinal_monomial_geometric_le (hb : 𝘸) (hbB : b ≤ B) (hκ : 0 ≤ κ) n :
    𝘺^n*κ^𝔇 ≤ cardinalSpatialGeometricBase B κ^n := by
  have hM : 1 ≤ max 1 κ := le_max_left ..
  have hκp := (pow_le_pow_left₀ hκ (le_max_right 1 κ) 𝔇).trans
    $ pow_le_pow_right₀ hM $ Nat.sub_le n 1
  have h := mul_le_mul (pow_le_pow_left₀ (sq_nonneg b) (pow_le_pow_left₀ hb hbB 2) n) hκp (pow_nonneg hκ 𝔇) $ pow_nonneg (sq_nonneg B) n
  have h2 : 𝔏^n ≤ cardinalSpatialGeometricBase B κ^n :=
    pow_le_pow_left₀ (mul_nonneg (sq_nonneg B) $ zero_le_one.trans hM )
      (by unfold cardinalSpatialGeometricBase; simp) n
  exact h.trans $ by simpa only [mul_pow] using h2

 def cardinalInterpolationEnergyPrefactor (d : ℕ) (a : ℝ) : ℝ := 2*𝔄/a^4
 def cardinalTaylorEnergyPrefactor (d q : ℕ) (C a ρ : ℝ) : ℝ :=
  2*𝔄*highResponseRemainderConstant q C a ρ^2

 set_option hygiene false
𝗇 𝔉 𝗶^𝗥
𝗇 𝔍 T^(-𝙊)
𝗇 𝔐 cardinal_monomial_geometric_le hbd hB hκ n
theorem cardinalAliasSpatialComponent_geometric_le (hbd : 0 ≤ bd) (hB : bd ≤ B)
    d n a η T (ha : 𝙆) (hT : 𝖹) :
    𝔓 ≤
      cardinalInterpolationEnergyPrefactor d a * cardinalSpatialGeometricBase B 𝖦₂^n *
        𝚍*𝗩*𝔍*𝔉 := by
  have hκ : 0 ≤ 𝖦₂ := by unfold spatialUnaryIntegralConstant; positivity
  have hA : 0 ≤ cardinalInterpolationEnergyPrefactor d a := by unfold cardinalInterpolationEnergyPrefactor; positivity
  have hlog : 0 ≤ 𝗶 := 𝖥₄
  have h := mul_le_mul_of_nonneg_right 𝔐
    (by positivity : 0 ≤ cardinalInterpolationEnergyPrefactor d a*𝚍*𝗩*𝔍*𝔉)
  convert h using 1 <;> dsimp only [cardinalAliasSpatialComponent, cardinalRawAliasCoefficient, cardinalDefectSquareBudget, cardinalInterpolationEnergyPrefactor]
  all_goals ring

 set_option hygiene false
𝗇 𝔅 4*q+4
𝗇 𝔈 𝗬₁
𝗇 𝔊 cardinalTaylorEnergyPrefactor d q C a ρ
𝗇 𝔑 n^(4*q+6)
theorem cardinalTaylorSpatialComponent_geometric_le (hbd : 0 ≤ bd) (hB : bd ≤ B)
    d n q C a ρ η :
    𝔎 ≤
      𝔊 *
        cardinalSpatialGeometricBase B 𝔈^n *
          𝔑*η^𝔅 := by
  have hκ : 0 ≤ 𝔈 := by
    unfold spatialScaleIntegralConstant
    positivity
  have hA : 0 ≤ 𝔊 := by unfold cardinalTaylorEnergyPrefactor; positivity
  have hη : 0 ≤ η^𝔅 := by rw [show 𝔅 = 2*𝖵 by omega, pow_mul]; positivity
  have h := mul_le_mul_of_nonneg_right 𝔐
    (by positivity : 0 ≤ 𝔊*𝔑*η^𝔅)
  convert h using 1 <;> dsimp only [cardinalTaylorSpatialComponent, cardinalRawTaylorCoefficient, cardinalTaylorEnergyPrefactor]
  all_goals ring
