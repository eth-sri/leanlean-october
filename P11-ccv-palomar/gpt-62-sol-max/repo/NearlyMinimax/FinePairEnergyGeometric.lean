module

public import NearlyMinimax.FinePairAliasSpatialEnergy
public import NearlyMinimax.DefectTailSummation


@[expose] public section

/-! Fixed geometric count envelopes for the actual pair component budgets.
Constants are chosen before the exterior degree and the selected count. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

 theorem finePairDensityPrefactor_eq {ad bd : ℝ} (haD : 0 < ad) (hab : ad < bd) :
    finePairDensityPrefactor ad bd = ((bd-ad)/ad)^2 := by
  unfold finePairDensityPrefactor densityMargin
  field_simp [haD.ne', (haD.trans hab).ne', (sub_pos.mpr hab).ne']
  ring

 def finePairUniformSpatialPrefactor (d q : ℕ) (aD bD C a ρ c0 : ℝ) : ℝ :=
  ((bD-aD)/aD)^4 * finePairResponseActionBudget d q C a ρ ^ 2 * Real.exp (4*c0)

 theorem finePairUniformSpatialPrefactor_nonneg (d q : ℕ) (aD bD C a ρ c0 : ℝ) :
    0 ≤ finePairUniformSpatialPrefactor d q aD bD C a ρ c0 := by
  unfold finePairUniformSpatialPrefactor
  positivity

section
variable {aD bD ad bd c0 : ℝ}
    (haD : 0 < aD) (ha : aD ≤ ad) (hb : bd ≤ bD) (hab : ad < bd)
    (htau : exteriorTau ((ad+bd)/(bd-ad)) ≤ c0) (d q : ℕ) (C a ρ : ℝ)
include haD ha hb hab htau

private theorem finePairResponseCoefficient_square_le (n M : ℕ) (η : ℝ) :
    (finePairActionCap d n M q ad bd C a ρ η)^2 ≤
      finePairUniformSpatialPrefactor d q aD bD C a ρ c0 * (bD^2)^n * (n : ℝ)^4 *
        (η^4 * Real.exp (2*exteriorTau ((ad+bd)/(bd-ad))*M)) := by
  have had := haD.trans_le ha
  have hbd := had.trans hab
  have hratio : (bd-ad)/ad ≤ (bD-aD)/aD := by gcongr <;> linarith
  let tau := exteriorTau ((ad+bd)/(bd-ad))
  have hc : Real.cosh ((M+2 : ℕ)*tau) ≤ Real.exp ((M+2 : ℕ)*tau) :=
    cosh_le_exp_of_nonneg (mul_nonneg (Nat.cast_nonneg _) (exteriorTau_interval_nonneg had.le hab))
  calc
    _ = ((bd-ad)/ad)^4 * (bd^2)^n *
        finePairResponseActionBudget d q C a ρ ^ 2 * (n : ℝ)^4 * η^4 * Real.cosh ((M+2 : ℕ)*tau)^2 := by
      unfold finePairActionCap finePairDensityCoefficientBudget
      rw [finePairDensityPrefactor_eq had hab, abs_of_nonneg (sq_nonneg _), ← pow_mul]
      ring
    _ ≤ ((bD-aD)/aD)^4 * (bD^2)^n *
        finePairResponseActionBudget d q C a ρ ^ 2 * (n : ℝ)^4 * η^4 * Real.exp ((M+2 : ℕ)*tau)^2 := by
      gcongr <;> first | positivity | linarith | exact (Real.cosh_pos _).le
    _ = ((bD-aD)/aD)^4 * (bD^2)^n *
        finePairResponseActionBudget d q C a ρ ^ 2 * (n : ℝ)^4 * η^4 *
          (Real.exp (4*tau) * Real.exp (2*tau*M)) := by
      rw [← Real.exp_nat_mul, ← Real.exp_add]
      push_cast
      congr 2 <;> ring
    _ ≤ ((bD-aD)/aD)^4 * (bD^2)^n * finePairResponseActionBudget d q C a ρ ^ 2 *
          (n : ℝ)^4 * η^4 * (Real.exp (4*c0) * Real.exp (2*tau*M)) := by
      have h := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left htau (by norm_num : (0 : ℝ) ≤ 4))
      gcongr
    _ = _ := by unfold finePairUniformSpatialPrefactor; dsimp [tau]; ring

end

/-- The product of a response coefficient bound and a spatial moment
bound is geometric in the observed count. -/
private theorem spatial_budget_majorize {L A b B Q K : ℝ} {n r j : ℕ}
    (hL : L ≤ A * (b ^ 2) ^ n * (n : ℝ) ^ r * Q)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hQ : 0 ≤ Q) (hK : 0 ≤ K) :
    L * B ^ n * (n : ℝ) ^ j * K ≤
      A * (1 + b ^ 2 * B) ^ n * (n : ℝ) ^ (r + j) * Q * K := by
  calc
    _ ≤ (A * (b ^ 2) ^ n * (n : ℝ) ^ r * Q) * B ^ n * (n : ℝ) ^ j * K := by gcongr
    _ = A * (b ^ 2 * B) ^ n * (n : ℝ) ^ (r + j) * Q * K := by rw [mul_pow, pow_add]; ring
    _ ≤ _ := by gcongr <;> first | positivity | linarith

 def finePairFieldGeometricBase (d : ℕ) (bd : ℝ) : ℝ :=
  1 + bd^2 * fineFieldSubsetEnergyBase d

 theorem finePairFieldGeometricBase_nonneg (d : ℕ) (bd : ℝ) :
    0 ≤ finePairFieldGeometricBase d bd := by
  unfold finePairFieldGeometricBase fineFieldSubsetEnergyBase
  positivity

 theorem spatialInverseFourConstant_nonneg (d : ℕ) : 0 ≤ spatialInverseFourConstant d := by
  unfold spatialInverseFourConstant radialExponentialConstant
  positivity

 def finePairAliasGeometricBase (d : ℕ) (bd : ℝ) : ℝ := 1 + bd^2*(2 : ℝ)^d

 theorem finePairAliasGeometricBase_nonneg (d : ℕ) (bd : ℝ) :
    0 ≤ finePairAliasGeometricBase d bd := by unfold finePairAliasGeometricBase; positivity

section
variable {aD bD ad bd c0 : ℝ}
    (haD : 0 < aD) (ha : aD ≤ ad) (hb : bd ≤ bD) (hab : ad < bd)
    (htau : exteriorTau ((ad+bd)/(bd-ad)) ≤ c0) (d n M q : ℕ) (C a ρ η T0 : ℝ)
include haD ha hb hab htau

theorem finePairEvenActionSpatialBudget_uniform_geometric_le :
    finePairEvenActionSpatialBudget d n M q ad bd C a ρ η T0 ≤
      finePairUniformSpatialPrefactor d q aD bD C a ρ c0 * finePairFieldGeometricBase d bD ^ n *
        (n : ℝ)^12 * η^4 * Real.exp (2*exteriorTau ((ad+bd)/(bd-ad))*M) * (T0^(2-(d : ℝ)))^2 := by
  have h := spatial_budget_majorize (n := n) (r := 4) (j := 8)
    (B := fineFieldSubsetEnergyBase d) (K := (T0^(2-(d : ℝ)))^2)
    (Q := η^4 * Real.exp (2*exteriorTau ((ad+bd)/(bd-ad))*M))
    (finePairResponseCoefficient_square_le haD ha hb hab htau d q C a ρ n M η)
    (finePairUniformSpatialPrefactor_nonneg d q aD bD C a ρ c0)
    (by unfold fineFieldSubsetEnergyBase; positivity) (by positivity) (sq_nonneg _)
  simpa only [finePairEvenActionSpatialBudget, finePairFieldGeometricBase, mul_assoc, Nat.reduceAdd] using h

 theorem finePairAliasActionSpatialBudget_uniform_geometric_le (hT0 : 0 < T0) :
    finePairAliasActionSpatialBudget d n M q ad bd C a ρ η T0 ≤
      (finePairUniformSpatialPrefactor d q aD bD C a ρ c0 * 6*(2 : ℝ)^d*spatialInverseFourConstant d) *
        finePairAliasGeometricBase d bD ^ n * (n : ℝ)^8 * η^4 *
          Real.exp (2*exteriorTau ((ad+bd)/(bd-ad))*M) / T0^(d-4) := by
  have hchoose : (n.choose 2 : ℝ) ≤ (n : ℝ)^2 := by exact_mod_cast Nat.choose_le_pow n 2
  have hcount : (n.choose 2 : ℝ)^2 ≤ (n : ℝ)^4 := by
    rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul]
    exact pow_le_pow_left₀ (by positivity) hchoose 2
  have hvol : (2 : ℝ)^(d*(n-2)) ≤ ((2 : ℝ)^d)^n := by
    rw [← pow_mul]
    exact pow_le_pow_right₀ (by norm_num) (Nat.mul_le_mul_left d (Nat.sub_le _ _))
  let K := 6*(2 : ℝ)^d*spatialInverseFourConstant d / T0^(d-4)
  have hi := spatialInverseFourConstant_nonneg d
  have hK : 0 ≤ K := by unfold K; positivity
  calc
    _ ≤ (finePairActionCap d n M q ad bd C a ρ η)^2 * (n : ℝ)^4 * ((2 : ℝ)^d)^n * K := by
      unfold finePairAliasActionSpatialBudget
      change _ * _ * _ * K ≤ _
      gcongr
    _ = (finePairActionCap d n M q ad bd C a ρ η)^2 * ((2 : ℝ)^d)^n * (n : ℝ)^4 * K := by ring
    _ ≤ _ := by
      have h := spatial_budget_majorize (n := n) (r := 4) (j := 4) (B := (2 : ℝ)^d) (K := K)
        (Q := η^4 * Real.exp (2*exteriorTau ((ad+bd)/(bd-ad))*M))
        (finePairResponseCoefficient_square_le haD ha hb hab htau d q C a ρ n M η)
        (finePairUniformSpatialPrefactor_nonneg d q aD bD C a ρ c0) (by positivity) (by positivity) hK
      convert h using 1 <;> simp [K, finePairAliasGeometricBase, div_eq_mul_inv] <;> ring

end

end NearlyMinimax
