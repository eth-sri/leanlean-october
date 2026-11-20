module

public import NearlyMinimax.FinePairEnergyGeometric


@[expose] public section

/-! The constants in the genuine pair energy bounds are uniform over all
legal interior density intervals and therefore precede M and its shrinking. -/
noncomputable section
open scoped BigOperators
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

 variable {aD bD ad bd c0 : ℝ} (haD : 0 < aD) (ha : aD ≤ ad) (hb : bd ≤ bD) (hab : ad < bd)
    (htau : intervalExteriorTau ad bd ≤ c0) (d n M q : ℕ) (C a ρ η T0 : ℝ)

 def finePairUniformSpatialPrefactor (aD bD C a ρ c0 : ℝ) : ℝ :=
  ((bD-aD)/aD)^4 * finePairResponseActionBudget d q C a ρ ^ 2 * Real.exp (4*c0)

 theorem finePairUniformSpatialPrefactor_nonneg (aD bD C a ρ c0 : ℝ) :
    0 ≤ finePairUniformSpatialPrefactor d q aD bD C a ρ c0 := by
  unfold finePairUniformSpatialPrefactor
  positivity

 include haD ha hb hab htau in
theorem finePairSpatialEnergyPrefactor_uniform_le :
    finePairSpatialEnergyPrefactor d q ad bd C a ρ ≤
      finePairUniformSpatialPrefactor d q aD bD C a ρ c0 := by
  have had  := haD.trans_le ha
  have hratio0  := div_nonneg (sub_nonneg.mpr hab.le) had.le
  have hratio : (bd-ad)/ad ≤ (bD-aD)/aD := by
    bound
  have hp := pow_le_pow_left₀ hratio0 hratio 4
  have hexp := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left htau (by norm_num : (0 : ℝ) ≤ 4))
  have h := mul_le_mul (mul_le_mul_of_nonneg_right hp
    (sq_nonneg (finePairResponseActionBudget d q C a ρ))) hexp (Real.exp_pos _).le
      (by positivity : 0 ≤ ((bD-aD)/aD)^4*finePairResponseActionBudget d q C a ρ^2)
  unfold finePairSpatialEnergyPrefactor finePairUniformSpatialPrefactor
  rw [(by unfold finePairDensityPrefactor densityMargin; field_simp [had.ne', (had.trans hab).ne', (sub_pos.mpr hab).ne']; ring : finePairDensityPrefactor ad bd = ((bd - ad) / ad) ^ 2), abs_of_nonneg (sq_nonneg _)]
  simpa only [← pow_mul] using h

 include haD ha hb hab htau in
theorem finePairEvenActionSpatialBudget_uniform_geometric_le :
    finePairEvenActionSpatialBudget d n M q ad bd C a ρ η T0 ≤
      finePairUniformSpatialPrefactor d q aD bD C a ρ c0 * finePairFieldGeometricBase d bD ^ n *
        (n : ℝ)^12 * η^4 * Real.exp (2*intervalExteriorTau ad bd*M) * (T0^(2-(d : ℝ)))^2 := by
  have had := haD.trans_le ha
  have h := finePairEvenActionSpatialBudget_geometric_le d n M q ad bd C a ρ η T0 had hab
  have hp := finePairSpatialEnergyPrefactor_uniform_le haD ha hb hab htau d q C a ρ
  have hbase := pow_le_pow_left₀ (finePairFieldGeometricBase_nonneg d bd)
    ((by have h := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ ((had.trans hab).le) hb 2) (by unfold fineFieldSubsetEnergyBase; positivity : 0 ≤ fineFieldSubsetEnergyBase d); unfold finePairFieldGeometricBase; linarith only [h] : finePairFieldGeometricBase d bd ≤ finePairFieldGeometricBase d bD)) n
  have hmul := mul_le_mul hp hbase (pow_nonneg (finePairFieldGeometricBase_nonneg d bd) n)
    (finePairUniformSpatialPrefactor_nonneg d q aD bD C a ρ c0)
  have hh := mul_le_mul_of_nonneg_right hmul
    (by positivity : 0 ≤ (n : ℝ)^12*η^4*Real.exp (2*intervalExteriorTau ad bd*M)*(T0^(2-(d : ℝ)))^2)
  linarith

 include haD ha hb hab htau in
theorem finePairAliasActionSpatialBudget_uniform_geometric_le (hT0 : 0 < T0) :
    finePairAliasActionSpatialBudget d n M q ad bd C a ρ η T0 ≤
      (finePairUniformSpatialPrefactor d q aD bD C a ρ c0 * 6*(2 : ℝ)^d*spatialInverseFourConstant d) *
        finePairAliasGeometricBase d bD ^ n * (n : ℝ)^8 * η^4 *
          Real.exp (2*intervalExteriorTau ad bd*M) / T0^(d-4) := by
  have had := haD.trans_le ha
  have h := finePairAliasActionSpatialBudget_geometric_le d n M q ad bd C a ρ η T0 had hab hT0
  have hp := finePairSpatialEnergyPrefactor_uniform_le haD ha hb hab htau d q C a ρ
  have hbase := pow_le_pow_left₀ (finePairAliasGeometricBase_nonneg d bd)
    ((by have h := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ ((had.trans hab).le) hb 2) (by positivity : 0 ≤ (2 : ℝ)^d); unfold finePairAliasGeometricBase; linarith only [h] : finePairAliasGeometricBase d bd ≤ finePairAliasGeometricBase d bD)) n
  have hmul := mul_le_mul hp hbase (pow_nonneg (finePairAliasGeometricBase_nonneg d bd) n)
    (finePairUniformSpatialPrefactor_nonneg d q aD bD C a ρ c0)
  have hi := spatialInverseFourConstant_nonneg d
  have hh := mul_le_mul_of_nonneg_right hmul
    (by positivity : 0 ≤ 6*(2 : ℝ)^d*spatialInverseFourConstant d*(n : ℝ)^8*η^4*
      Real.exp (2*intervalExteriorTau ad bd*M)/T0^(d-4))
  grind

end NearlyMinimax
