module

public import NearlyMinimax.CardinalEnergyGeometric
public import RoughRegime.Macro
public import RoughRegime.Notation


𝗌

/-! Actual computed matched-row interpolation and Taylor budgets at the
paper's cutoffs, including omitted cutoffs below one. -/
𝚪
𝚨
𝚩
𝚱

 set_option hygiene false
𝗇 𝔜 𝘵
𝗇 𝔄 N*(μ*𝔜)^(𝖭₁/d)
𝗇 𝔞 -𝙊
𝗇 𝔅 N^𝔞
𝗇 𝔎 μ*𝔜 ≤ 1
𝗇 𝔓 max 1 𝔄
𝗃 𝔠 0 < ἀ
theorem target_max_one_defect_budget_le {d : ℕ} (hd : 𝔠 d)
    {N μ } (hN : 𝗭₁) (hμ : 𝔠 μ) (hsmall : 𝔎) (j : ℕ) :
    𝔓^𝔞 *
      (1+Real.log 𝔓)^j ≤ 𝔅/μ^j := by
  have hNpos := lt_of_lt_of_le zero_lt_one hN
  have hH : 𝔠 𝔜 := by linarith [Real.log_nonneg hN]
  let T := 𝔄
  by_cases hT : 𝖹
  · rw [max_eq_right hT]
    exact target_cutoff_defect_budget_le (Nat.ne_of_gt hd) hNpos hμ j hT
      $ target_cutoff_le_base hd hNpos.le (mul_nonneg hμ.le hH.le) hsmall j
  · rw [max_eq_left $ le_of_not_ge hT , Real.one_rpow, Real.log_one, add_zero, one_pow, mul_one]
    exact omitted_target_inverse_budget_ge_one (Nat.ne_of_gt hd) hN hμ j $ lt_of_not_ge hT

 def matchedCardinalTargetCutoff (d j : ℕ) (N μ : ℝ) : ℝ := 𝔓

 set_option hygiene false
𝗇 𝔇 2+j
𝗇 𝔉 𝖦₂
𝗇 𝔏 matchedCardinalTargetCutoff d j N μ
𝗇 𝔐 𝗩
𝗇 𝔟 cardinalInterpolationEnergyPrefactor d a
𝗇 𝔔 𝔟 * cardinalSpatialGeometricBase B 𝔉^𝔇
𝗃 𝔡 0 ≤ ἀ
𝗇 𝔘 𝔡 bd
𝗇 𝔙 bd ≤ B
𝗇 𝔚 cardinalAliasSpatialComponent d 𝔇 bd a η 𝔏
theorem cardinalAliasSpatialComponent_allocated_le {bd B } (hbd : 𝔘) (hB : 𝔙)
    {d } (hd : 𝔠 d) j a η (ha : 𝔠 a)
    {N μ } (hN : 𝗭₁) (hμ : 𝔠 μ) (hsmall : 𝔎) :
    𝔚 ≤
      𝔔 *
          (𝔇 : ℕ)^2 * 𝔐*𝔅/μ^j := by
  have h := cardinalAliasSpatialComponent_geometric_le hbd hB d 𝔇 a η 𝔏 ha $ le_max_left ..
  have hA : 𝔡 𝔟 := by unfold cardinalInterpolationEnergyPrefactor; positivity
  have hBase := cardinalSpatialGeometricBase_nonneg B 𝔉
  have hh := mul_le_mul_of_nonneg_left (target_max_one_defect_budget_le hd hN hμ hsmall j)
    (by positivity : 0 ≤ 𝔔*𝔇^2*𝔐)
  apply h.trans
  convert hh using 1 <;> (try dsimp [matchedCardinalTargetCutoff]) <;> (try simp ) <;> ring

 set_option hygiene false
𝗇 𝔈 𝗬₁
𝗇 𝔊 cardinalTaylorEnergyPrefactor d q C a ρ
𝗇 𝔍 4*q+6
𝗇 𝔑 η^(4*q)*𝚝₂ ≤ 1
𝗇 𝔒 𝔊 * cardinalSpatialGeometricBase B 𝔈^n * n^𝔍
𝗇 𝔖 cardinalTaylorSpatialComponent d n q bd C a ρ η
theorem cardinalTaylorSpatialComponent_allocated_le (hbd : 𝔘) (hB : 𝔙)
    d n q C a ρ η (hN : 𝔠 N) (hsmall : 𝔑) :
    𝔖 ≤
      𝔒*𝔐*𝔅 := by
  have h := cardinalTaylorSpatialComponent_geometric_le hbd hB d n q C a ρ η
  have hA : 𝔡 𝔊 := by unfold cardinalTaylorEnergyPrefactor; positivity
  have hBase := cardinalSpatialGeometricBase_nonneg B 𝔈
  have hh := mul_le_mul_of_nonneg_left (response_taylor_budget_absorption hN q d hsmall)
    (by positivity : 𝔡 𝔒)
  apply h.trans
  apply hh.trans_eq
  rw [Real.rpow_neg hN.le, Real.rpow_natCast]
  ring

 𝗇 𝔗 cardinalSpatialGeometricBase B 𝔉*2^2
def cardinalInterpolationFactorialConstant (d : ℕ) (B a Csharp : ℝ) : ℝ :=
  𝔟 *
    defectTailConstant Csharp 𝔗

 𝗇 𝔛 poissonCountWeight (Csharp*μ) 𝔇
theorem finite_cardinal_interpolation_budget_le (hbd : 𝔘) (hB : 𝔙)
    (hd : 𝔠 d) J a η Csharp (ha : 𝔠 a) (hCs : 𝔡 Csharp)
    (hN : 𝗭₁) (hμ : 𝔠 μ) (hsmall : 𝔎) :
     ∑ j ∈ Finset.range J, 𝔛 *
      𝔚 ≤
      cardinalInterpolationFactorialConstant d B a Csharp * 𝔐*𝔅*μ^2 := by
  let P := 𝔟 * 𝔐*𝔅
  have hP : 𝔡 P := by dsimp [P, cardinalInterpolationEnergyPrefactor]; positivity
  have hBase := cardinalSpatialGeometricBase_nonneg B 𝔉
  have h := finite_interpolation_defect_tail_le hP hCs
    (by positivity : 𝔡 𝔗) hμ J
    (fun n => cardinalAliasSpatialComponent d n bd a η $ matchedCardinalTargetCutoff d 𝗥 N μ ) $ by
      intro j hj
      have hb := cardinalAliasSpatialComponent_allocated_le hbd hB hd j a η ha hN hμ hsmall
      have hm := mul_le_mul_of_nonneg_left (polynomial_count_factor_le 𝔇 2)
        (by positivity : 0 ≤ P*cardinalSpatialGeometricBase B 𝔉^𝔇/μ^j)
      rw [show 𝔇-2=j by omega]
      apply hb.trans
      convert hm using 1 <;> dsimp [P] <;> (try simp ) <;> ring
  simpa only [show ∀ j , 𝔇-2=j from fun j => 𝖡₃] using
    h.trans_eq $ by unfold cardinalInterpolationFactorialConstant; ring

 def cardinalTaylorFactorialConstant (d q : ℕ) (B C a ρ Csharp : ℝ) : ℝ :=
  𝔊 * defectTailConstant Csharp
    (cardinalSpatialGeometricBase B ((100*𝙊)^2*16*spatialScaleIntegralConstant d)*2^𝔍)

 theorem finite_cardinal_taylor_budget_le (hbd : 𝔘) (hB : 𝔙)
    d q J C a ρ η Csharp (hCs : 𝔡 Csharp)
    (hN : 𝔠 N) (hμ : 𝔡 μ) (hμ1 : μ ≤ 1) (hsmall : 𝔑) :
     ∑ j ∈ Finset.range J, 𝔛 *
      cardinalTaylorSpatialComponent d 𝔇 q bd C a ρ η ≤
      cardinalTaylorFactorialConstant d q B C a ρ Csharp * 𝔐*𝔅*μ^2 := by
  let P := 𝔊 * 𝔐*𝔅
  have hP : 𝔡 P := by dsimp [P, cardinalTaylorEnergyPrefactor]; positivity
  have h := finite_taylor_count_energy_tail_le hP hCs
    (cardinalSpatialGeometricBase_nonneg B 𝔈) hμ hμ1 𝔍 J
    (fun n => 𝔖)
     fun j _ => (cardinalTaylorSpatialComponent_allocated_le hbd hB d 𝔇 q C a ρ η hN hsmall).trans_eq
      𝖢₃
  exact h.trans_eq $ by unfold cardinalTaylorFactorialConstant; ring
