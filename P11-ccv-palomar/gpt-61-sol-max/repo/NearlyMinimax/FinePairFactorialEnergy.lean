module

public import NearlyMinimax.FinePairEnergyUniform

@[expose] public section

/-! Genuine finite factorial sums of the computed pair spatial budgets.
Every constant is fixed before the degree, count cutoff and density shrinking. -/
noncomputable section
open scoped BigOperators
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

 def finePairFieldFactorialConstant d q aD bD C a ρ c0 Csharp  :=
  finePairUniformSpatialPrefactor d q aD bD C a ρ c0 *
    fieldTailConstant Csharp (finePairFieldGeometricBase d bD * 2^12)

 theorem finite_fine_pair_field_budget_le {aD bD ad bd c0 }
    (haD : 0 < aD) (ha : aD ≤ ad) (hb : bd ≤ bD) (hab : ad < bd)
    (htau : exteriorTau ((ad+bd)/(bd-ad)) ≤ c0) d M q J
    C a ρ η T0 Csharp μ (hCs : 0 ≤ Csharp) (hμ : 0 ≤ μ) (hμ1 : μ ≤ 1) :
    (∑ j ∈ Finset.range J, poissonCountWeight (Csharp*μ) (4+j) *
      finePairEvenActionSpatialBudget d (4+j) M q ad bd C a ρ η T0) ≤
      finePairFieldFactorialConstant d q aD bD C a ρ c0 Csharp * η^4 *
        Real.exp (2*exteriorTau ((ad+bd)/(bd-ad))*M) * (T0^(2-(d : ℝ)))^2 * μ^4 := by
  let P := finePairUniformSpatialPrefactor d q aD bD C a ρ c0 * η^4 *
    Real.exp (2*exteriorTau ((ad+bd)/(bd-ad))*M) * (T0^(2-(d : ℝ)))^2
  have hP : 0 ≤ P := by skip; positivity [finePairUniformSpatialPrefactor_nonneg d q aD bD C a ρ c0]
  have h := finite_polynomial_field_count_tail_le hP hCs (finePairFieldGeometricBase_nonneg d bD)
    hμ hμ1 12 J (fun n => finePairEvenActionSpatialBudget d n M q ad bd C a ρ η T0)
    (fun j _ => (finePairEvenActionSpatialBudget_uniform_geometric_le haD ha hb hab htau d (4+j) M q C a ρ η T0).trans_eq
      (by skip; ring))
  exact h.trans_eq (by unfold finePairFieldFactorialConstant; skip; ring)

end NearlyMinimax
