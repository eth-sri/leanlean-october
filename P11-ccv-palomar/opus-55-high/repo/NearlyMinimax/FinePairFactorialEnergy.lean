module

public import NearlyMinimax.FinePairEnergyUniform
public import RoughRegime.Macro
public import RoughRegime.Notation

𝗌

/-! Genuine finite factorial sums of the computed pair spatial budgets.
Every constant is fixed before the degree, count cutoff and density shrinking. -/
𝚪
𝚨
𝚩
𝚱

 set_option hygiene false
𝗃 𝔈 ἀ d q aD bD C a ρ c0
def finePairFieldFactorialConstant (d q : ℕ) (aD bD C a ρ c0 Csharp : ℝ) : ℝ :=
  𝔈 finePairUniformSpatialPrefactor *
    fieldTailConstant Csharp (finePairFieldGeometricBase d bD * 2^12)

 set_option hygiene false
𝗇 𝔄 exteriorTau 𝙻
𝗇 𝔅 (T0^(2-𝙊))^2
𝗇 𝔇 4+j
𝗇 𝔉 2*𝔄*M
𝗃 𝔊 finePairEvenActionSpatialBudget d ἀ M q ad bd C a ρ η T0
theorem finite_fine_pair_field_budget_le
    (haD : 𝘗₂) (ha : aD ≤ ad) (hb : bd ≤ bD) (hab : 𝖽)
    (htau : 𝔄 ≤ c0) d M q J
    C a ρ η T0 Csharp μ (hCs : 0 ≤ Csharp) (hμ : 0 ≤ μ) (hμ1 : μ ≤ 1) :
     ∑ j ∈ Finset.range J, poissonCountWeight (Csharp*μ) 𝔇 *
      𝔊 𝔇 ≤
      𝔈 finePairFieldFactorialConstant Csharp * 𝗩 *
        Real.exp 𝔉 * 𝔅 * μ^4 := by
  let P := 𝔈 finePairUniformSpatialPrefactor * 𝗩 *
    Real.exp 𝔉 * 𝔅
  have hP : 𝚏 := by positivity [𝔈 finePairUniformSpatialPrefactor_nonneg]
  have h := finite_polynomial_field_count_tail_le hP hCs (finePairFieldGeometricBase_nonneg d bD)
    hμ hμ1 12 J (fun n => 𝔊 n)
     fun j _ => (finePairEvenActionSpatialBudget_uniform_geometric_le haD ha hb hab htau d 𝔇 M q C a ρ η T0).trans_eq
      𝖢₃
  exact h.trans_eq $ by unfold finePairFieldFactorialConstant; ring
