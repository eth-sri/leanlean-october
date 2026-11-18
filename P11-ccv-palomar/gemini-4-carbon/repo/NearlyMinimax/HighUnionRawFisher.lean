module

public import NearlyMinimax.AliasTailSummation
public import NearlyMinimax.LowSmoothnessPrior
public import NearlyMinimax.LowerActivityHierarchy
public import NearlyMinimax.LowerSaddle
public import NearlyMinimax.PaperGoals

@[expose] public section

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators Topology ENNReal
namespace NearlyMinimax

attribute [local instance] Classical.propDecidable

-- 1. Cutoff algebra, cardinal & fine-pair geometric count envelopes
--    (`LocalCutoffAlgebra`, `TargetDefectBudget`, `CardinalEnergyGeometric`,
--     `FinePairCountTwoSpatialEnergy`, `FinePairEnergyGeometric`, `FinePairEnergyUniform`, `FinePairFactorialEnergy`)

section GeometricEnvelopes
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

theorem target_cutoff_inverse_budget {d : ℕ} (hd : d ≠ 0)
    {N mu H : ℝ} (hN : 0 < N) (hmu : 0 < mu) (hH : 0 < H) (j : ℕ) :
    (N * (mu * H) ^ ((j : ℝ) / d)) ^ (-(d : ℝ)) * H ^ j = N ^ (-(d : ℝ)) / mu ^ j := by
  have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast hd
  have hprod : 0 < mu * H := mul_pos hmu hH
  rw [Real.mul_rpow hN.le (Real.rpow_pos_of_pos hprod _).le, ← Real.rpow_mul hprod.le,
    show ((j : ℝ) / d) * (-(d : ℝ)) = -(j : ℝ) by field_simp,
    Real.rpow_neg hprod.le, Real.rpow_natCast, mul_pow]
  field_simp

theorem response_taylor_budget_absorption {eta N : ℝ} (hN : 0 < N)
    (q d : ℕ) (hsmall : eta ^ (4 * q) * N ^ d ≤ 1) :
    eta ^ (4 * q + 4) ≤ eta ^ 4 / N ^ d := by
  refine (le_div_iff₀ (pow_pos hN d)).mpr ?_
  simpa only [pow_add, mul_assoc, mul_comm, mul_left_comm, mul_one] using
    mul_le_mul_of_nonneg_left hsmall (by positivity : 0 ≤ eta ^ 4)

theorem target_cutoff_le_base {d : ℕ} (hd : 0 < d)
    {N mu H : ℝ} (hN : 0 ≤ N) (hmuH : 0 ≤ mu * H) (hsmall : mu * H ≤ 1) (j : ℕ) :
    N * (mu * H) ^ ((j : ℝ) / d) ≤ N := by
  simpa only [mul_one] using mul_le_mul_of_nonneg_left
    (Real.rpow_le_one hmuH hsmall (by positivity : 0 ≤ (j : ℝ) / d)) hN

theorem target_cutoff_defect_budget_le {d : ℕ} (hd : d ≠ 0)
    {N mu : ℝ} (hN : 0 < N) (hmu : 0 < mu) (j : ℕ)
    (hT : 1 ≤ N * (mu * (1 + Real.log N)) ^ ((j : ℝ) / d))
    (hTN : N * (mu * (1 + Real.log N)) ^ ((j : ℝ) / d) ≤ N) :
    (N * (mu * (1 + Real.log N)) ^ ((j : ℝ) / d)) ^ (-(d : ℝ)) *
      (1 + Real.log (N * (mu * (1 + Real.log N)) ^ ((j : ℝ) / d))) ^ j ≤
        N ^ (-(d : ℝ)) / mu ^ j := by
  have hN1 : 1 ≤ N := hT.trans hTN
  have hH : 0 < 1 + Real.log N := by linarith [Real.log_nonneg hN1]
  have hlog : 1 + Real.log (N * (mu * (1 + Real.log N)) ^ ((j : ℝ) / d)) ≤ 1 + Real.log N := by
    linarith [Real.log_le_log (by linarith only [hT]) hTN]
  exact (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (add_nonneg zero_le_one (Real.log_nonneg hT)) hlog j)
    (Real.rpow_nonneg (by positivity) _)).trans_eq (target_cutoff_inverse_budget hd hN hmu hH j)

theorem omitted_target_inverse_budget_ge_one {d : ℕ} (hd : d ≠ 0)
    {N mu : ℝ} (hN1 : 1 ≤ N) (hmu : 0 < mu) (j : ℕ)
    (hT : N * (mu * (1 + Real.log N)) ^ ((j : ℝ) / d) < 1) :
    1 ≤ N ^ (-(d : ℝ)) / mu ^ j := by
  have hN : 0 < N := zero_lt_one.trans_le hN1
  have hH : 0 < 1 + Real.log N := by linarith [Real.log_nonneg hN1]
  have hTp : 0 < N * (mu * (1 + Real.log N)) ^ ((j : ℝ) / d) := by positivity
  rw [← target_cutoff_inverse_budget hd hN hmu hH j]
  simpa only [one_mul] using mul_le_mul
    (Real.one_le_rpow_of_pos_of_le_one_of_nonpos hTp hT.le (neg_nonpos.mpr (Nat.cast_nonneg d)))
    (one_le_pow₀ (by linarith [Real.log_nonneg hN1])) zero_le_one (Real.rpow_nonneg hTp.le _)

def cardinalAliasSpatialComponent (d n : ℕ) (bd a η T : ℝ) : ℝ :=
  2 * cardinalRawAliasCoefficient n bd a η ^ 2 * (n : ℝ) ^ 2 * (2 : ℝ) ^ d * cardinalDefectSquareBudget d n T

def cardinalTaylorSpatialComponent (d n q : ℕ) (bd C a ρ η : ℝ) : ℝ :=
  2 * cardinalRawTaylorCoefficient n q bd C a ρ η ^ 2 * (n : ℝ) ^ 2 * (2 : ℝ) ^ d *
    ((100 * (d : ℝ)) ^ 2 * 16 * spatialScaleIntegralConstant d) ^ (n - 1)

theorem cardinalRawSpatialEnergyBudget_split (d n q : ℕ) (bd C a ρ η T : ℝ) :
    cardinalRawSpatialEnergyBudget d n q bd C a ρ η T =
      cardinalAliasSpatialComponent d n bd a η T + cardinalTaylorSpatialComponent d n q bd C a ρ η := by
  unfold cardinalRawSpatialEnergyBudget cardinalAliasSpatialComponent cardinalTaylorSpatialComponent; ring

def cardinalSpatialGeometricBase (B κ : ℝ) : ℝ := 1 + B ^ 2 * max 1 κ

theorem cardinalSpatialGeometricBase_nonneg (B κ : ℝ) : 0 ≤ cardinalSpatialGeometricBase B κ := by
  unfold cardinalSpatialGeometricBase
  have : 0 ≤ max (1 : ℝ) κ := zero_le_one.trans (le_max_left _ _)
  positivity

lemma cardinal_monomial_geometric_le {b B κ : ℝ} (hb : 0 ≤ b) (hbB : b ≤ B) (hκ : 0 ≤ κ) (n : ℕ) :
    (b ^ 2) ^ n * κ ^ (n - 1) ≤ cardinalSpatialGeometricBase B κ ^ n := by
  have hM : 1 ≤ max (1 : ℝ) κ := le_max_left _ _
  have hκp := (pow_le_pow_left₀ hκ (le_max_right (1 : ℝ) κ) (n - 1)).trans (pow_le_pow_right₀ hM (Nat.sub_le n 1))
  have hbp := pow_le_pow_left₀ (sq_nonneg b) (pow_le_pow_left₀ hb hbB 2) n
  have h2 : (B ^ 2 * max 1 κ) ^ n ≤ cardinalSpatialGeometricBase B κ ^ n :=
    pow_le_pow_left₀ (mul_nonneg (sq_nonneg B) (zero_le_one.trans hM)) (by unfold cardinalSpatialGeometricBase; linarith) n
  exact (mul_le_mul hbp hκp (pow_nonneg hκ _) (pow_nonneg (sq_nonneg B) n)).trans (by simpa only [mul_pow] using h2)

def cardinalInterpolationEnergyPrefactor (d : ℕ) (a : ℝ) : ℝ := 2 * (2 : ℝ) ^ d / a ^ 4
def cardinalTaylorEnergyPrefactor (d q : ℕ) (C a ρ : ℝ) : ℝ :=
  2 * (2 : ℝ) ^ d * highResponseRemainderConstant q C a ρ ^ 2

theorem cardinalAliasSpatialComponent_geometric_le {bd B : ℝ} (hbd : 0 ≤ bd) (hB : bd ≤ B)
    (d n : ℕ) (a η T : ℝ) (ha : 0 < a) (hT : 1 ≤ T) :
    cardinalAliasSpatialComponent d n bd a η T ≤
      cardinalInterpolationEnergyPrefactor d a * cardinalSpatialGeometricBase B (16 * spatialUnaryIntegralConstant d) ^ n *
        (n : ℝ) ^ 2 * η ^ 4 * T ^ (-(d : ℝ)) * (1 + Real.log T) ^ (n - 2) := by
  have hκ : 0 ≤ 16 * spatialUnaryIntegralConstant d := by unfold spatialUnaryIntegralConstant; positivity
  have hA : 0 ≤ cardinalInterpolationEnergyPrefactor d a := by unfold cardinalInterpolationEnergyPrefactor; positivity
  have hlog : 0 ≤ 1 + Real.log T := by linarith [Real.log_nonneg hT]
  have h := mul_le_mul_of_nonneg_right (cardinal_monomial_geometric_le hbd hB hκ n)
    (by positivity : 0 ≤ cardinalInterpolationEnergyPrefactor d a * (n : ℝ) ^ 2 * η ^ 4 * T ^ (-(d : ℝ)) * (1 + Real.log T) ^ (n - 2))
  convert h using 1 <;> dsimp only [cardinalAliasSpatialComponent, cardinalRawAliasCoefficient,
    cardinalDefectSquareBudget, cardinalInterpolationEnergyPrefactor]
  · simp only [mul_pow, ← pow_mul]; field_simp; ring
  · ring

theorem cardinalTaylorSpatialComponent_geometric_le {bd B : ℝ} (hbd : 0 ≤ bd) (hB : bd ≤ B)
    (d n q : ℕ) (C a ρ η : ℝ) :
    cardinalTaylorSpatialComponent d n q bd C a ρ η ≤
      cardinalTaylorEnergyPrefactor d q C a ρ *
        cardinalSpatialGeometricBase B ((100 * (d : ℝ)) ^ 2 * 16 * spatialScaleIntegralConstant d) ^ n *
          (n : ℝ) ^ (4 * q + 6) * η ^ (4 * q + 4) := by
  have hκ : 0 ≤ (100 * (d : ℝ)) ^ 2 * 16 * spatialScaleIntegralConstant d := by unfold spatialScaleIntegralConstant; positivity
  have hA : 0 ≤ cardinalTaylorEnergyPrefactor d q C a ρ := by unfold cardinalTaylorEnergyPrefactor; positivity
  have hη : 0 ≤ η ^ (4 * q + 4) := by rw [show 4 * q + 4 = 2 * (2 * q + 2) by omega, pow_mul]; positivity
  have h := mul_le_mul_of_nonneg_right (cardinal_monomial_geometric_le hbd hB hκ n)
    (by positivity : 0 ≤ cardinalTaylorEnergyPrefactor d q C a ρ * (n : ℝ) ^ (4 * q + 6) * η ^ (4 * q + 4))
  convert h using 1 <;> dsimp only [cardinalTaylorSpatialComponent, cardinalRawTaylorCoefficient, cardinalTaylorEnergyPrefactor]
  · simp only [mul_pow, ← pow_mul]; ring_nf
  · ring

def finePairCountTwoSpatialBudget (d : ℕ) (bd a ρ η N : ℝ) : ℝ :=
  (η ^ 2 * bd ^ 2 * ((2 * ρ + a) / a ^ 2) ^ 2) ^ 2 * (6 * (2 : ℝ) ^ d * spatialExponentialConstant d / N ^ d)

def finePairSpatialEnergyPrefactor (d q : ℕ) (ad bd C a ρ : ℝ) : ℝ :=
  |finePairDensityPrefactor ad bd| ^ 2 * finePairResponseActionBudget d q C a ρ ^ 2 *
    Real.exp (4 * exteriorTau ((ad + bd) / (bd - ad)))

theorem finePairSpatialEnergyPrefactor_nonneg (d q : ℕ) (ad bd C a ρ : ℝ) :
    0 ≤ finePairSpatialEnergyPrefactor d q ad bd C a ρ := by
  unfold finePairSpatialEnergyPrefactor; positivity

lemma finePairResponseCoefficient_square_le (d n M q : ℕ) (ad bd C a ρ η : ℝ)
    (haD : 0 < ad) (hab : ad < bd) :
    (finePairDensityCoefficientBudget ad bd M n *
      (finePairResponseActionBudget d q C a ρ * (n : ℝ) ^ 2 * η ^ 2)) ^ 2 ≤
      finePairSpatialEnergyPrefactor d q ad bd C a ρ * (bd ^ 2) ^ n * (n : ℝ) ^ 4 * η ^ 4 *
        Real.exp (2 * exteriorTau ((ad + bd) / (bd - ad)) * M) := by
  let tau := exteriorTau ((ad + bd) / (bd - ad))
  have hc : Real.cosh ((M + 2 : ℕ) * tau) ≤ Real.exp ((M + 2 : ℕ) * tau) := by
    dsimp [tau]; rw [← exterior_rule_variation ad bd haD hab (M + 2) (by omega)]
    exact exterior_rule_variation_le_exp ad bd haD hab (M + 2) (by omega)
  have h := mul_le_mul_of_nonneg_left ((sq_le_sq₀ (Real.cosh_pos _).le (Real.exp_pos _).le).mpr hc)
    (sq_nonneg (|finePairDensityPrefactor ad bd| * bd ^ n * (finePairResponseActionBudget d q C a ρ * (n : ℝ) ^ 2 * η ^ 2)))
  calc _ = (|finePairDensityPrefactor ad bd| * bd ^ n * (finePairResponseActionBudget d q C a ρ * (n : ℝ) ^ 2 * η ^ 2)) ^ 2 *
          Real.cosh ((M + 2 : ℕ) * tau) ^ 2 := by unfold finePairDensityCoefficientBudget; dsimp [tau]; ring
    _ ≤ _ * Real.exp ((M + 2 : ℕ) * tau) ^ 2 := h
    _ = _ := by
        rw [← Real.exp_nat_mul]; norm_num only [Nat.cast_ofNat]; rw [Nat.cast_add, Nat.cast_ofNat]
        rw [show 2 * (((M : ℝ) + 2) * tau) = 4 * tau + 2 * tau * M by ring, Real.exp_add]
        unfold finePairSpatialEnergyPrefactor; dsimp [tau]; simp only [mul_pow, ← pow_mul]; ring

def finePairFieldGeometricBase (d : ℕ) (bd : ℝ) : ℝ := 1 + bd ^ 2 * fineFieldSubsetEnergyBase d

theorem finePairFieldGeometricBase_nonneg (d : ℕ) (bd : ℝ) :
    0 ≤ finePairFieldGeometricBase d bd := by unfold finePairFieldGeometricBase fineFieldSubsetEnergyBase; positivity

theorem spatialInverseFourConstant_nonneg (d : ℕ) : 0 ≤ spatialInverseFourConstant d := by
  unfold spatialInverseFourConstant; positivity

def finePairAliasGeometricBase (d : ℕ) (bd : ℝ) : ℝ := 1 + bd ^ 2 * (2 : ℝ) ^ d

theorem finePairAliasGeometricBase_nonneg (d : ℕ) (bd : ℝ) :
    0 ≤ finePairAliasGeometricBase d bd := by unfold finePairAliasGeometricBase; positivity

def finePairUniformSpatialPrefactor (d q : ℕ) (aD bD C a ρ c0 : ℝ) : ℝ :=
  ((bD - aD) / aD) ^ 4 * finePairResponseActionBudget d q C a ρ ^ 2 * Real.exp (4 * c0)

theorem finePairUniformSpatialPrefactor_nonneg (d q : ℕ) (aD bD C a ρ c0 : ℝ) :
    0 ≤ finePairUniformSpatialPrefactor d q aD bD C a ρ c0 := by
  unfold finePairUniformSpatialPrefactor; positivity

lemma finePairSpatialEnergyPrefactor_uniform_le {aD bD ad bd c0 : ℝ}
    (haD : 0 < aD) (ha : aD ≤ ad) (hb : bd ≤ bD) (hab : ad < bd)
    (htau : exteriorTau ((ad + bd) / (bd - ad)) ≤ c0) (d q : ℕ) (C a ρ : ℝ) :
    finePairSpatialEnergyPrefactor d q ad bd C a ρ ≤
      finePairUniformSpatialPrefactor d q aD bD C a ρ c0 := by
  have had : 0 < ad := haD.trans_le ha
  have hratio : (bd - ad) / ad ≤ (bD - aD) / aD := by
    refine (div_le_div_iff₀ had haD).mpr ?_
    have hbD : 0 < bD := (had.trans hab).trans_le hb
    nlinarith only [ha, hb, haD, had, hbD, mul_nonneg (sub_nonneg.mpr ha) hbD.le, mul_nonneg (sub_nonneg.mpr hb) haD.le]
  have hp := pow_le_pow_left₀ (div_nonneg (sub_nonneg.mpr hab.le) had.le) hratio 4
  have hexp := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left htau (by norm_num : (0 : ℝ) ≤ 4))
  have h := mul_le_mul (mul_le_mul_of_nonneg_right hp (sq_nonneg (finePairResponseActionBudget d q C a ρ)))
    hexp (Real.exp_pos _).le (by positivity)
  have hpref_eq : finePairDensityPrefactor ad bd = ((bd - ad) / ad) ^ 2 := by
    unfold finePairDensityPrefactor densityMargin
    field_simp [had.ne', (had.trans hab).ne', (sub_pos.mpr hab).ne']; ring
  unfold finePairSpatialEnergyPrefactor finePairUniformSpatialPrefactor
  rw [hpref_eq, abs_of_nonneg (sq_nonneg _)]; simpa only [← pow_mul] using h

theorem finePairEvenActionSpatialBudget_uniform_geometric_le {aD bD ad bd c0 : ℝ}
    (haD : 0 < aD) (ha : aD ≤ ad) (hb : bd ≤ bD) (hab : ad < bd)
    (htau : exteriorTau ((ad + bd) / (bd - ad)) ≤ c0) (d n M q : ℕ) (C a ρ η T0 : ℝ) :
    finePairEvenActionSpatialBudget d n M q ad bd C a ρ η T0 ≤
      finePairUniformSpatialPrefactor d q aD bD C a ρ c0 * finePairFieldGeometricBase d bD ^ n *
        (n : ℝ) ^ 12 * η ^ 4 * Real.exp (2 * exteriorTau ((ad + bd) / (bd - ad)) * M) * (T0 ^ (2 - (d : ℝ))) ^ 2 := by
  have had := haD.trans_le ha
  have hgeom : finePairEvenActionSpatialBudget d n M q ad bd C a ρ η T0 ≤
      finePairSpatialEnergyPrefactor d q ad bd C a ρ * finePairFieldGeometricBase d bd ^ n *
        (n : ℝ) ^ 12 * η ^ 4 * Real.exp (2 * exteriorTau ((ad + bd) / (bd - ad)) * M) * (T0 ^ (2 - (d : ℝ))) ^ 2 := by
    have h1 := mul_le_mul_of_nonneg_right (finePairResponseCoefficient_square_le d n M q ad bd C a ρ η had hab)
      (by unfold fineFieldSubsetEnergyBase; positivity : 0 ≤ fineFieldSubsetEnergyBase d ^ n * (n : ℝ) ^ 8 * (T0 ^ (2 - (d : ℝ))) ^ 2)
    have hpow : (bd ^ 2 * fineFieldSubsetEnergyBase d) ^ n ≤ finePairFieldGeometricBase d bd ^ n :=
      pow_le_pow_left₀ (by unfold fineFieldSubsetEnergyBase; positivity) (by unfold finePairFieldGeometricBase; linarith) n
    have hm := mul_le_mul_of_nonneg_right hpow
      (by positivity [finePairSpatialEnergyPrefactor_nonneg d q ad bd C a ρ] :
        0 ≤ finePairSpatialEnergyPrefactor d q ad bd C a ρ * (n : ℝ) ^ 12 * η ^ 4 *
          Real.exp (2 * exteriorTau ((ad + bd) / (bd - ad)) * M) * (T0 ^ (2 - (d : ℝ))) ^ 2)
    unfold finePairEvenActionSpatialBudget
    have hh := h1.trans (by convert hm using 1 <;> simp only [mul_pow] <;> ring)
    convert hh using 1 <;> ring
  have hmono : finePairFieldGeometricBase d bd ≤ finePairFieldGeometricBase d bD := by
    have := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (had.trans hab).le hb 2)
      (by unfold fineFieldSubsetEnergyBase; positivity : 0 ≤ fineFieldSubsetEnergyBase d)
    unfold finePairFieldGeometricBase; linarith
  have hmul := mul_le_mul (finePairSpatialEnergyPrefactor_uniform_le haD ha hb hab htau d q C a ρ)
    (pow_le_pow_left₀ (finePairFieldGeometricBase_nonneg d bd) hmono n)
    (pow_nonneg (finePairFieldGeometricBase_nonneg d bd) n)
    (finePairUniformSpatialPrefactor_nonneg d q aD bD C a ρ c0)
  have hh := mul_le_mul_of_nonneg_right hmul
    (by positivity : 0 ≤ (n : ℝ) ^ 12 * η ^ 4 * Real.exp (2 * exteriorTau ((ad + bd) / (bd - ad)) * M) * (T0 ^ (2 - (d : ℝ))) ^ 2)
  exact hgeom.trans (by convert hh using 1 <;> ring)

theorem finePairAliasActionSpatialBudget_uniform_geometric_le {aD bD ad bd c0 : ℝ}
    (haD : 0 < aD) (ha : aD ≤ ad) (hb : bd ≤ bD) (hab : ad < bd)
    (htau : exteriorTau ((ad + bd) / (bd - ad)) ≤ c0) (d n M q : ℕ) (C a ρ η T0 : ℝ) (hT0 : 0 < T0) :
    finePairAliasActionSpatialBudget d n M q ad bd C a ρ η T0 ≤
      (finePairUniformSpatialPrefactor d q aD bD C a ρ c0 * 6 * (2 : ℝ) ^ d * spatialInverseFourConstant d) *
        finePairAliasGeometricBase d bD ^ n * (n : ℝ) ^ 8 * η ^ 4 *
          Real.exp (2 * exteriorTau ((ad + bd) / (bd - ad)) * M) / T0 ^ (d - 4) := by
  have had := haD.trans_le ha
  have hi := spatialInverseFourConstant_nonneg d
  have hgeom : finePairAliasActionSpatialBudget d n M q ad bd C a ρ η T0 ≤
      (finePairSpatialEnergyPrefactor d q ad bd C a ρ * 6 * (2 : ℝ) ^ d * spatialInverseFourConstant d) *
        finePairAliasGeometricBase d bd ^ n * (n : ℝ) ^ 8 * η ^ 4 *
          Real.exp (2 * exteriorTau ((ad + bd) / (bd - ad)) * M) / T0 ^ (d - 4) := by
    have hc : (n.choose 2 : ℝ) ^ 2 ≤ (n : ℝ) ^ 4 := by
      have h : (n.choose 2 : ℝ) ≤ (n : ℝ) ^ 2 := by exact_mod_cast Nat.choose_le_pow n 2
      simpa only [← pow_mul] using pow_le_pow_left₀ (Nat.cast_nonneg _) h 2
    have hv : (2 : ℝ) ^ (d * (n - 2)) ≤ (2 : ℝ) ^ (d * n) :=
      pow_le_pow_right₀ (by norm_num) (Nat.mul_le_mul_left d (Nat.sub_le _ _))
    have hPref := finePairSpatialEnergyPrefactor_nonneg d q ad bd C a ρ
    have h1 := mul_le_mul_of_nonneg_right
      (mul_le_mul (mul_le_mul (finePairResponseCoefficient_square_le d n M q ad bd C a ρ η had hab) hc
        (sq_nonneg _) (by positivity)) hv (by positivity) (by positivity))
      (by positivity : 0 ≤ 6 * (2 : ℝ) ^ d * spatialInverseFourConstant d / T0 ^ (d - 4))
    have hpow : (bd ^ 2 * (2 : ℝ) ^ d) ^ n ≤ finePairAliasGeometricBase d bd ^ n :=
      pow_le_pow_left₀ (by positivity) (by unfold finePairAliasGeometricBase; linarith) n
    have hpow' := mul_le_mul_of_nonneg_right hpow
      (by positivity : 0 ≤ finePairSpatialEnergyPrefactor d q ad bd C a ρ * (n : ℝ) ^ 8 * η ^ 4 *
        Real.exp (2 * exteriorTau ((ad + bd) / (bd - ad)) * M) * (6 * (2 : ℝ) ^ d * spatialInverseFourConstant d / T0 ^ (d - 4)))
    refine h1.trans ?_
    convert hpow' using 1 <;> (try simp only [mul_pow, ← pow_mul]) <;> ring
  have hmono : finePairAliasGeometricBase d bd ≤ finePairAliasGeometricBase d bD := by
    have := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (had.trans hab).le hb 2) (by positivity : 0 ≤ (2 : ℝ) ^ d)
    unfold finePairAliasGeometricBase; linarith
  have hmul := mul_le_mul (finePairSpatialEnergyPrefactor_uniform_le haD ha hb hab htau d q C a ρ)
    (pow_le_pow_left₀ (finePairAliasGeometricBase_nonneg d bd) hmono n)
    (pow_nonneg (finePairAliasGeometricBase_nonneg d bd) n)
    (finePairUniformSpatialPrefactor_nonneg d q aD bD C a ρ c0)
  have hh := mul_le_mul_of_nonneg_right hmul
    (by positivity : 0 ≤ 6 * (2 : ℝ) ^ d * spatialInverseFourConstant d * (n : ℝ) ^ 8 * η ^ 4 *
      Real.exp (2 * exteriorTau ((ad + bd) / (bd - ad)) * M) / T0 ^ (d - 4))
  exact hgeom.trans (by convert hh using 1 <;> ring)

def finePairFieldFactorialConstant (d q : ℕ) (aD bD C a ρ c0 Csharp : ℝ) : ℝ :=
  finePairUniformSpatialPrefactor d q aD bD C a ρ c0 *
    fieldTailConstant Csharp (finePairFieldGeometricBase d bD * 2 ^ 12)

theorem finite_fine_pair_field_budget_le {aD bD ad bd c0 : ℝ}
    (haD : 0 < aD) (ha : aD ≤ ad) (hb : bd ≤ bD) (hab : ad < bd)
    (htau : exteriorTau ((ad + bd) / (bd - ad)) ≤ c0) (d M q J : ℕ)
    (C a ρ η T0 Csharp μ : ℝ) (hCs : 0 ≤ Csharp) (hμ : 0 ≤ μ) (hμ1 : μ ≤ 1) :
    (∑ j ∈ Finset.range J, poissonCountWeight (Csharp * μ) (4 + j) *
      finePairEvenActionSpatialBudget d (4 + j) M q ad bd C a ρ η T0) ≤
      finePairFieldFactorialConstant d q aD bD C a ρ c0 Csharp * η ^ 4 *
        Real.exp (2 * exteriorTau ((ad + bd) / (bd - ad)) * M) * (T0 ^ (2 - (d : ℝ))) ^ 2 * μ ^ 4 := by
  let P := finePairUniformSpatialPrefactor d q aD bD C a ρ c0 * η ^ 4 *
    Real.exp (2 * exteriorTau ((ad + bd) / (bd - ad)) * M) * (T0 ^ (2 - (d : ℝ))) ^ 2
  have hP : 0 ≤ P := by dsimp [P]; positivity [finePairUniformSpatialPrefactor_nonneg d q aD bD C a ρ c0]
  exact (finite_polynomial_field_count_tail_le hP hCs (finePairFieldGeometricBase_nonneg d bD)
    hμ hμ1 12 J (fun n => finePairEvenActionSpatialBudget d n M q ad bd C a ρ η T0)
    fun j _ => (finePairEvenActionSpatialBudget_uniform_geometric_le haD ha hb hab htau d (4 + j) M q C a ρ η T0).trans_eq
      (by dsimp [P]; ring)).trans_eq (by unfold finePairFieldFactorialConstant; dsimp [P]; ring)

end GeometricEnvelopes

-- 2. Spatial envelopes, higher-band collapse & higher-count numerator geometry
--    (`HighSpatialEnvelopes`, `OrdinaryFineAliasGeometryEnvelope`, `HighSourceHigherCounts`,
--     `HigherBandRawCollapse`, `HighSourceHigherGeometry`)

section HigherGeometry
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000

def cardinalGeometryEnvelope {d n F : ℕ} (q : ℕ) (bd C a ρ η T : ℝ) (U : Fin n → Covariate d) : ℝ :=
  (3 : ℝ) ^ n * (2 * cardinalRawAliasCoefficient n bd a η ^ 2 *
    (∑ i, cardinalWeightDefect i (spatialInterpolationLambda d) T U) ^ 2 +
    2 * cardinalRawTaylorCoefficient n q bd C a ρ η ^ 2 *
      spatialMatrixL1 (integratedCardinalMatrix (D := F) (spatialInterpolationLambda d) T U) ^ 2)

theorem cardinalGeometryEnvelope_nonneg {d n F : ℕ} (q : ℕ) (bd C a ρ η T : ℝ)
    (U : Fin n → Covariate d) : 0 ≤ cardinalGeometryEnvelope (F := F) q bd C a ρ η T U := by
  unfold cardinalGeometryEnvelope; positivity

theorem cardinalGeometryEnvelope_integrable_and_le {d n F : ℕ} (hd : 5 ≤ d) (hn : 2 ≤ n)
    (q : ℕ) (bd C a ρ η : ℝ) {T : ℝ} (hT : 1 ≤ T) :
    Integrable (cardinalGeometryEnvelope (d := d) (n := n) (F := F) q bd C a ρ η T)
      (fullSpatialPatchDesign d n) ∧
    (∫ U, cardinalGeometryEnvelope (F := F) q bd C a ρ η T U ∂fullSpatialPatchDesign d n) ≤
      (3 : ℝ) ^ n * cardinalRawSpatialEnergyBudget d n q bd C a ρ η T := by
  have hlam : 0 ≤ spatialInterpolationLambda d := by unfold spatialInterpolationLambda; positivity
  have hZ : Integrable (fun U => (∑ i : Fin n, cardinalWeightDefect i (spatialInterpolationLambda d) T U) ^ 2)
      (fullSpatialPatchDesign d n) := by
    simpa only [abs_of_nonneg (cardinalWeightDefect_mem_unit _ hlam T _).1] using
      finite_sum_abs_square_integrable (fullSpatialPatchDesign d n) Finset.univ
        (fun i U => cardinalWeightDefect i (spatialInterpolationLambda d) T U)
        (fun i _ => cardinalWeightDefect_measurable i _ hT)
        (fun i _ => cardinalWeightDefect_square_integrable i hlam hT)
  have hE := integratedCardinalMatrix_full_square_integrable (D := F) hd hn hT
  refine ⟨((hZ.const_mul _).add (hE.const_mul _)).const_mul _, ?_⟩
  unfold cardinalGeometryEnvelope
  rw [integral_const_mul, integral_add (hZ.const_mul _) (hE.const_mul _), integral_const_mul, integral_const_mul]
  exact (mul_le_mul_of_nonneg_left (add_le_add
    (mul_le_mul_of_nonneg_left (cardinalWeightDefect_sum_square_integral_le (d := d) (n := n) (by omega) hn hT) (by positivity))
    (mul_le_mul_of_nonneg_left (integratedCardinalMatrix_full_square_integral_le (D := F) hd hn hT) (by positivity)))
    (by positivity : 0 ≤ (3 : ℝ) ^ n)).trans_eq (by unfold cardinalRawSpatialEnergyBudget; ring)

def fineFieldGeometryEnvelope {d n : ℕ} (ad bd T0 N : ℝ) (M q : ℕ) (C a ρ η : ℝ) (U : Fin n → Covariate d) : ℝ :=
  (3 : ℝ) ^ n * (finePairDensityCoefficientBudget ad bd M n *
    (finePairResponseActionBudget d q C a ρ * (n : ℝ) ^ 2 * η ^ 2)) ^ 2 *
      (∑ S ∈ ((Finset.univ : Finset (Fin n)).powerset).filter (fun S => 4 ≤ S.card ∧ Even S.card),
        |finePairTimeSubsetMoment T0 N U S|) ^ 2

def finePairAliasGeometryEnvelope {d n : ℕ} (ad bd T0 N : ℝ) (M q : ℕ) (C a ρ η : ℝ) (U : Fin n → Covariate d) : ℝ :=
  (3 : ℝ) ^ n * (finePairDensityCoefficientBudget ad bd M n *
    (finePairResponseActionBudget d q C a ρ * (n : ℝ) ^ 2 * η ^ 2)) ^ 2 *
      (∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard 2, |finePairTimeSubsetMoment T0 N U S|) ^ 2

theorem fineFieldGeometryEnvelope_nonneg {d n : ℕ} (ad bd T0 N : ℝ) (M q : ℕ) (C a ρ η : ℝ)
    (U : Fin n → Covariate d) : 0 ≤ fineFieldGeometryEnvelope ad bd T0 N M q C a ρ η U := by
  unfold fineFieldGeometryEnvelope; positivity

theorem finePairAliasGeometryEnvelope_nonneg {d n : ℕ} (ad bd T0 N : ℝ) (M q : ℕ) (C a ρ η : ℝ)
    (U : Fin n → Covariate d) : 0 ≤ finePairAliasGeometryEnvelope ad bd T0 N M q C a ρ η U := by
  unfold finePairAliasGeometryEnvelope; positivity

theorem fineFieldGeometryEnvelope_integrable_and_le {d n : ℕ} [NeZero d] (hd : 3 ≤ d)
    (ad bd T0 N : ℝ) (hT0 : 0 < T0) (M q : ℕ) (C a ρ η : ℝ) :
    Integrable (fineFieldGeometryEnvelope (d := d) (n := n) ad bd T0 N M q C a ρ η) (fullSpatialPatchDesign d n) ∧
    (∫ U, fineFieldGeometryEnvelope ad bd T0 N M q C a ρ η U ∂fullSpatialPatchDesign d n) ≤
      (3 : ℝ) ^ n * finePairEvenActionSpatialBudget d n M q ad bd C a ρ η T0 := by
  let s := ((Finset.univ : Finset (Fin n)).powerset).filter fun S => 4 ≤ S.card ∧ Even S.card
  have hs (S) (hS : S ∈ s) : 4 ≤ S.card := (Finset.mem_filter.mp hS).2.1
  have hi := finite_sum_abs_square_integrable (fullSpatialPatchDesign d n) s
    (fun S U => finePairTimeSubsetMoment T0 N U S)
    (fun S _ => finePairTimeSubsetMoment_measurable T0 N S)
    (fun S hS => finePairTimeSubsetMoment_square_integrable hd hT0 S (hs S hS))
  refine ⟨hi.const_mul _, ?_⟩
  unfold fineFieldGeometryEnvelope; rw [integral_const_mul]
  exact (mul_le_mul_of_nonneg_left (finePairTimeSubsetMoment_sum_abs_square_integral_le hd (hi := N) hT0 s hs)
    (by positivity)).trans_eq (by unfold finePairEvenActionSpatialBudget; ring)

theorem finePairAliasGeometryEnvelope_integrable_and_le {d n : ℕ} [NeZero d] (hd : 4 < d)
    (ad bd T0 N : ℝ) (hT0 : 0 < T0) (hN : T0 ≤ N) (M q : ℕ) (C a ρ η : ℝ) :
    Integrable (finePairAliasGeometryEnvelope (d := d) (n := n) ad bd T0 N M q C a ρ η) (fullSpatialPatchDesign d n) ∧
    (∫ U, finePairAliasGeometryEnvelope ad bd T0 N M q C a ρ η U ∂fullSpatialPatchDesign d n) ≤
      (3 : ℝ) ^ n * finePairAliasActionSpatialBudget d n M q ad bd C a ρ η T0 := by
  let s := (Finset.univ : Finset (Fin n)).powersetCard 2
  have hs (S) (hS : S ∈ s) : S.card = 2 := (Finset.mem_powersetCard.mp hS).2
  have hi := finite_sum_abs_square_integrable (fullSpatialPatchDesign d n) s
    (fun S U => finePairTimeSubsetMoment T0 N U S)
    (fun S _ => finePairTimeSubsetMoment_measurable T0 N S)
    (fun S hS => (finePairTimeSubsetMoment_two_subset_square_integrable_and_le hd hT0 hN S (hs S hS)).1)
  refine ⟨hi.const_mul _, ?_⟩
  unfold finePairAliasGeometryEnvelope; rw [integral_const_mul]
  have h := finite_sum_square_integral_le (fullSpatialPatchDesign d n) s
    (fun S U => |finePairTimeSubsetMoment T0 N U S|)
    ((2 : ℝ) ^ (d * (n - 2)) * (6 * (2 : ℝ) ^ d * spatialInverseFourConstant d / T0 ^ (d - 4)))
    (fun S _ => (finePairTimeSubsetMoment_measurable T0 N S).abs)
    (fun S hS => by simpa only [sq_abs] using (finePairTimeSubsetMoment_two_subset_square_integrable_and_le hd hT0 hN S (hs S hS)).1)
    (fun S hS => by simpa only [sq_abs] using (finePairTimeSubsetMoment_two_subset_square_integrable_and_le hd hT0 hN S (hs S hS)).2)
  refine (mul_le_mul_of_nonneg_left h (by positivity)).trans_eq ?_
  dsimp [s]; rw [Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
  unfold finePairAliasActionSpatialBudget; ring

def finePairCountTwoGeometryEnvelope {d : ℕ} (bd a ρ η N : ℝ) (U : Fin 2 → Covariate d) : ℝ :=
  9 * (η ^ 2 * bd ^ 2 * ((2 * ρ + a) / a ^ 2) ^ 2) ^ 2 * finePairDistanceFactor N (U 0) (U 1) ^ 2

theorem finePairCountTwoGeometryEnvelope_nonneg {d : ℕ} (bd a ρ η N : ℝ)
    (U : Fin 2 → Covariate d) : 0 ≤ finePairCountTwoGeometryEnvelope bd a ρ η N U := by
  unfold finePairCountTwoGeometryEnvelope; positivity

theorem finePairCountTwoGeometryEnvelope_integrable_and_le {d : ℕ} (hd : 0 < d)
    (bd a ρ η : ℝ) {N : ℝ} (hN : 0 < N) :
    Integrable (finePairCountTwoGeometryEnvelope (d := d) bd a ρ η N) (fullSpatialPatchDesign d 2) ∧
    (∫ U, finePairCountTwoGeometryEnvelope bd a ρ η N U ∂fullSpatialPatchDesign d 2) ≤
      9 * finePairCountTwoSpatialBudget d bd a ρ η N := by
  have hp := measurePreserving_finTwoArrow (volume.restrict (spatialPatchBox d))
  have hi : Integrable (fun U : Fin 2 → Covariate d => finePairDistanceFactor N (U 0) (U 1) ^ 2)
      (fullSpatialPatchDesign d 2) := hp.integrable_comp_of_integrable (finePairDistanceFactor_square_integrable hN)
  refine ⟨hi.const_mul _, ?_⟩
  unfold finePairCountTwoGeometryEnvelope; rw [integral_const_mul]
  have hInt := (hp.integral_comp
    (MeasurableEquiv.finTwoArrow : (Fin 2 → Covariate d) ≃ᵐ (Covariate d × Covariate d)).measurableEmbedding _).trans_le
      (finePairDistanceFactor_square_integral_le hd hN)
  exact (mul_le_mul_of_nonneg_left hInt (by positivity)).trans_eq (by unfold finePairCountTwoSpatialBudget; ring)

abbrev finePairCountTwoRawNumerator_sum_square_le_geometry := @finePairCountTwoRawNumerator_sum_square_le

def ordinaryFineAliasAmplitudeFactor (n M R q : ℕ) (ad bd c0 C a rho eta : ℝ) : ℝ :=
  ((1 + bd) ^ n * (1 + uniformOrdinaryDensityActivityBase ad bd c0) ^ R *
    Real.exp ((M : ℝ) * shrunkDensityExponent ad bd M)) *
      (ordinaryAliasResponseConstant q C a rho * (n : ℝ) ^ 2 * eta ^ 2)

def ordinaryFineAliasGeometryKernel {d n F : ℕ} (r : ℕ) (L T : ℝ) (U : Fin n → Covariate d) : ℝ :=
  ∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard r,
    spatialMatrixL1 (globalCardinalBandMatrix (D := F) (spatialInterpolationLambda d) L T
      (spatialSubsetConfiguration S U))

def ordinaryFineAliasFamilyResponseSquareEnvelope {d n F : ℕ} (I : Finset ℕ)
    (M R q : ℕ) (ad bd c0 C a rho eta L : ℝ) (T : ℕ → ℝ) (U : Fin n → Covariate d) : ℝ :=
  (3 : ℝ) ^ n *
    (∑ r ∈ I, ordinaryFineAliasAmplitudeFactor n M R q ad bd c0 C a rho eta *
      ordinaryFineAliasGeometryKernel (F := F) r L (T r) U) ^ 2

theorem ordinaryFineAliasFamilyResponseSquareEnvelope_nonneg {d n F : ℕ} (I : Finset ℕ)
    (M R q : ℕ) (ad bd c0 C a rho eta L : ℝ) (T : ℕ → ℝ) (U : Fin n → Covariate d) :
    0 ≤ ordinaryFineAliasFamilyResponseSquareEnvelope (F := F) I M R q ad bd c0 C a rho eta L T U := by
  unfold ordinaryFineAliasFamilyResponseSquareEnvelope; positivity

lemma ordinaryFineAliasGeometryKernel_measurable {d n F : ℕ} (r : ℕ) {L T : ℝ}
    (hL : 1 ≤ L) (hT : 1 ≤ T) :
    Measurable (ordinaryFineAliasGeometryKernel (d := d) (n := n) (F := F) r L T) :=
  Finset.measurable_sum _ fun S _ => Finset.measurable_sum _ fun gamma _ => Finset.measurable_sum _ fun beta _ =>
    ((integrated_cardinal_band_continuous (spatialInterpolationLambda d) hL hT gamma beta).measurable.abs).comp
      (spatialSubsetConfiguration_measurable S)

theorem ordinaryFineAliasFamilyResponseSquareEnvelope_integrable {d n F : ℕ}
    (hd : 5 ≤ d) (I : Finset ℕ) (M R q : ℕ) (ad bd c0 C a ρ η L : ℝ)
    (T : ℕ → ℝ) (hL : 1 ≤ L) (hI : ∀ r ∈ I, 2 ≤ r ∧ L ≤ T r) :
    Integrable (ordinaryFineAliasFamilyResponseSquareEnvelope (d := d) (n := n) (F := F)
      I M R q ad bd c0 C a ρ η L T) (fullSpatialPatchDesign d n) := by
  let f (r : ℕ) (U : Fin n → Covariate d) := ordinaryFineAliasAmplitudeFactor n M R q ad bd c0 C a ρ η *
    ordinaryFineAliasGeometryKernel (F := F) r L (T r) U
  have hm (r) (hr : r ∈ I) : Measurable (f r) :=
    (ordinaryFineAliasGeometryKernel_measurable r hL (hL.trans (hI r hr).2)).const_mul _
  have hi (r) (hr : r ∈ I) : Integrable (fun U => f r U ^ 2) (fullSpatialPatchDesign d n) := by
    convert (ordinaryFineAliasKernel_sum_square_integrable_and_le (F := F) (n := n)
      hd (hI r hr).1 hL (hL.trans (hI r hr).2) (hI r hr).2).1.const_mul
        (ordinaryFineAliasAmplitudeFactor n M R q ad bd c0 C a ρ η ^ 2) using 1
    funext U; dsimp [f, ordinaryFineAliasGeometryKernel]; ring
  have hs : Integrable (fun U => (∑ r ∈ I, f r U) ^ 2) (fullSpatialPatchDesign d n) :=
    (finite_sum_abs_square_integrable (fullSpatialPatchDesign d n) I f hm hi).mono'
      ((Finset.measurable_sum I hm).pow_const 2).aestronglyMeasurable
      (Filter.Eventually.of_forall fun U => by
        simpa only [Real.norm_eq_abs, abs_sq, sq_abs] using
          (sq_le_sq₀ (abs_nonneg _) (Finset.sum_nonneg fun _ _ => abs_nonneg _)).mpr
            (Finset.abs_sum_le_sum_abs (fun r => f r U) I))
  exact hs.const_mul ((3 : ℝ) ^ n)

theorem ordinaryFineAliasFamilyResponseSquareEnvelope_integrable_and_scale_le {d n F M R : ℕ}
    (hd : 5 ≤ d) (I : Finset ℕ) (hI : ∀ r ∈ I, 2 ≤ r ∧ r ≤ R)
    (ad bd c0 C a rho eta D K N : ℝ) (hbd : 0 ≤ bd)
    (hD : 0 ≤ D) (hK : 0 ≤ K) (hc0 : 0 ≤ c0) (hDK : D ≤ K * M)
    (hN : 0 < N) (hell : 1 ≤ N * Real.exp (-c0 * D))
    (hH : Real.log (1 + Real.log N) ≤ M) (T : ℕ → ℝ)
    (hLT : ∀ r ∈ I, N * Real.exp (-c0 * D) ≤ T r) (q : ℕ) :
    Integrable (ordinaryFineAliasFamilyResponseSquareEnvelope (d := d) (n := n) (F := F)
      I M R q ad bd c0 C a rho eta (N * Real.exp (-c0 * D)) T) (fullSpatialPatchDesign d n) ∧
    (∫ U, ordinaryFineAliasFamilyResponseSquareEnvelope (F := F)
      I M R q ad bd c0 C a rho eta (N * Real.exp (-c0 * D)) T U ∂fullSpatialPatchDesign d n) ≤
      ordinaryAliasFamilySpatialPrefactor d q R ad bd c0 C a rho *
        eta ^ 4 * Real.exp (2 * shrunkDensityExponent ad bd M * M) * N ^ (4 - (d : ℝ)) *
          Real.exp (lowerAliasSpatialL d R c0 K * M) * (ordinaryAliasSpatialResponseBase d bd) ^ n := by
  let L := N * Real.exp (-c0 * D)
  let f (r : ℕ) (U : Fin n → Covariate d) :=
    ordinaryFineAliasAmplitudeFactor n M R q ad bd c0 C a rho eta *
      ordinaryFineAliasGeometryKernel (F := F) r L (T r) U
  let B := ordinaryAliasSpatialPrefactor d q R ad bd c0 C a rho *
    eta ^ 4 * Real.exp (2 * shrunkDensityExponent ad bd M * M) * N ^ (4 - (d : ℝ)) *
      Real.exp (lowerAliasSpatialL d R c0 K * M) * (ordinaryAliasSpatialCountBase d bd) ^ n
  have hB : 0 ≤ B := by
    dsimp [B]; have := ordinaryAliasSpatialPrefactor_nonneg d q R ad bd c0 C a rho
    unfold ordinaryAliasSpatialCountBase; positivity
  have hm (r) (hr : r ∈ I) : Measurable (f r) :=
    (ordinaryFineAliasGeometryKernel_measurable r hell (hell.trans (hLT r hr))).const_mul _
  have hk (r) (hr : r ∈ I) := ordinaryFineAliasKernel_sum_square_integrable_and_le (F := F) (n := n)
    hd (hI r hr).1 hell (hell.trans (hLT r hr)) (hLT r hr)
  have hi (r) (hr : r ∈ I) : Integrable (fun U => f r U ^ 2) (fullSpatialPatchDesign d n) := by
    convert (hk r hr).1.const_mul (ordinaryFineAliasAmplitudeFactor n M R q ad bd c0 C a rho eta ^ 2) using 1
    funext U; dsimp [f, ordinaryFineAliasGeometryKernel]; ring
  have hb (r) (hr : r ∈ I) : (∫ U, f r U ^ 2 ∂fullSpatialPatchDesign d n) ≤ B := by
    have hid : (∫ U, f r U ^ 2 ∂fullSpatialPatchDesign d n) =
        ordinaryFineAliasAmplitudeFactor n M R q ad bd c0 C a rho eta ^ 2 *
          ∫ U, ordinaryFineAliasGeometryKernel (F := F) r L (T r) U ^ 2 ∂fullSpatialPatchDesign d n := by
      rw [← integral_const_mul]; exact congrArg _ (funext fun _ => by dsimp [f]; ring)
    have h1 : (∫ U, f r U ^ 2 ∂fullSpatialPatchDesign d n) ≤
        ordinaryFineAliasSpatialBudget d n M r R q ad bd c0 C a rho eta L := by
      rw [hid]
      exact (mul_le_mul_of_nonneg_left (hk r hr).2 (sq_nonneg _)).trans_eq
        (by unfold ordinaryFineAliasSpatialBudget ordinaryFineAliasAmplitudeFactor; ring)
    exact h1.trans (ordinaryFineAliasSpatialBudget_source_scale_le hd (hI r hr).2 hbd hD hK hc0 hDK hN hell hH q)
  have hcard : (I.card : ℝ) ^ 2 ≤ ((R + 1 : ℕ) : ℝ) ^ 2 := by
    have h := Finset.card_le_card (s := I) (t := Finset.range (R + 1)) fun r hr =>
      Finset.mem_range.mpr (by have := (hI r hr).2; omega)
    rw [Finset.card_range] at h; exact_mod_cast Nat.pow_le_pow_left h 2
  have hsum := (finite_sum_square_integral_le (fullSpatialPatchDesign d n) I f B hm hi hb).trans
    (mul_le_mul_of_nonneg_right hcard hB)
  refine ⟨ordinaryFineAliasFamilyResponseSquareEnvelope_integrable hd I M R q ad bd c0 C a rho eta L T hell
    fun r hr => ⟨(hI r hr).1, hLT r hr⟩, ?_⟩
  rw [show (∫ U, ordinaryFineAliasFamilyResponseSquareEnvelope (F := F) I M R q ad bd c0 C a rho eta L T U
    ∂fullSpatialPatchDesign d n) = (3 : ℝ) ^ n * ∫ U, (∑ r ∈ I, f r U) ^ 2 ∂fullSpatialPatchDesign d n by
      rw [← integral_const_mul]; rfl]
  exact (mul_le_mul_of_nonneg_left hsum (by positivity)).trans_eq (by
    unfold B ordinaryAliasFamilySpatialPrefactor ordinaryAliasSpatialResponseBase; rw [mul_pow]; ring)

def completeSourceHigherGeometryEnvelope {d n D : ℕ} (aD bD c0 ℓ N μ : ℝ)
    (M R q : ℕ) (C a ρ η : ℝ) (U : Fin n → Covariate d) : ℝ :=
  4 * (cardinalGeometryEnvelope (F := D) q (bD - (M : ℝ)⁻¹) C a ρ η (max 1 (higherBandTargetScale d n N μ)) U +
    (if M < n then ordinaryFineAliasFamilyResponseSquareEnvelope (F := D) (ordinaryFineAliasTargetSet d D ℓ N μ)
      M R q aD bD c0 C a ρ η ℓ (fun r => higherBandTargetScale d r N μ) U else 0) +
    (if M < n then finePairAliasGeometryEnvelope (aD + (M : ℝ)⁻¹) (bD - (M : ℝ)⁻¹) ℓ N M q C a ρ η U else 0) +
    fineFieldGeometryEnvelope (aD + (M : ℝ)⁻¹) (bD - (M : ℝ)⁻¹) ℓ N M q C a ρ η U)

theorem completeSourceHigherGeometryEnvelope_nonneg {d n D : ℕ} (aD bD c0 ℓ N μ : ℝ)
    (M R q : ℕ) (C a ρ η : ℝ) (U : Fin n → Covariate d) :
    0 ≤ completeSourceHigherGeometryEnvelope (D := D) aD bD c0 ℓ N μ M R q C a ρ η U := by
  unfold completeSourceHigherGeometryEnvelope
  have := cardinalGeometryEnvelope_nonneg (F := D) q (bD - (M : ℝ)⁻¹) C a ρ η (max 1 (higherBandTargetScale d n N μ)) U
  have := ordinaryFineAliasFamilyResponseSquareEnvelope_nonneg (F := D) (ordinaryFineAliasTargetSet d D ℓ N μ)
    M R q aD bD c0 C a ρ η ℓ (fun r => higherBandTargetScale d r N μ) U
  have := finePairAliasGeometryEnvelope_nonneg (aD + (M : ℝ)⁻¹) (bD - (M : ℝ)⁻¹) ℓ N M q C a ρ η U
  have := fineFieldGeometryEnvelope_nonneg (aD + (M : ℝ)⁻¹) (bD - (M : ℝ)⁻¹) ℓ N M q C a ρ η U
  split_ifs <;> positivity

theorem completeSourceHigherGeometryEnvelope_integrable {d n D : ℕ} [NeZero d]
    (hd : 5 ≤ d) (hn : 2 ≤ n) (aD bD c0 ℓ N μ : ℝ) (M R q : ℕ) (C a ρ η : ℝ)
    (hℓ : 1 ≤ ℓ) (hN : ℓ ≤ N) :
    Integrable (completeSourceHigherGeometryEnvelope (d := d) (n := n) (D := D)
      aD bD c0 ℓ N μ M R q C a ρ η) (fullSpatialPatchDesign d n) := by
  have hA := (cardinalGeometryEnvelope_integrable_and_le (F := D) hd hn q (bD - (M : ℝ)⁻¹) C a ρ η
    (T := max 1 (higherBandTargetScale d n N μ)) (le_max_left _ _)).1
  have hB := ordinaryFineAliasFamilyResponseSquareEnvelope_integrable (n := n) (F := D) hd
    (ordinaryFineAliasTargetSet d D ℓ N μ) M R q aD bD c0 C a ρ η ℓ
    (fun r => higherBandTargetScale d r N μ) hℓ fun r hr =>
      ⟨by have := (Finset.mem_filter.mp hr).2; omega, (Finset.mem_filter.mp hr).2.2.le⟩
  have hP := (finePairAliasGeometryEnvelope_integrable_and_le (d := d) (n := n) (by omega)
    (aD + (M : ℝ)⁻¹) (bD - (M : ℝ)⁻¹) ℓ N (lt_of_lt_of_le zero_lt_one hℓ) hN M q C a ρ η).1
  have hF := (fineFieldGeometryEnvelope_integrable_and_le (d := d) (n := n) (by omega)
    (aD + (M : ℝ)⁻¹) (bD - (M : ℝ)⁻¹) ℓ N (lt_of_lt_of_le zero_lt_one hℓ) M q C a ρ η).1
  unfold completeSourceHigherGeometryEnvelope
  split_ifs
  · exact (((hA.add hB).add hP).add hF).const_mul 4
  · simpa only [Pi.add_apply, add_zero] using (hA.add hF).const_mul 4

lemma ordinaryPairPacket_zero_other_count {ι Z : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace ι]
    [MeasurableSingletonClass ι] [MeasurableSpace Z] {n : ℕ} (hn : 3 ≤ n)
    (σ : Measure Z) [IsFiniteMeasure σ] (a b : ℝ) (ha : 0 < a) (hab : a < b)
    (m D q : ℕ) (hnm : n ≤ m) (hnD : n ≤ D) (C : ℝ)
    (A : Z → ι → ι → ℝ) (hA : ∀ i j, Measurable fun ζ => A ζ i j)
    (hcost : Integrable (separatedMatrixCost A) σ) (c : ι → ℝ)
    (p : Fin n → ℝ) (hp : ∀ i, p i ∈ Icc a b) (ψ : Z → Fin n → ℝ)
    (hmψ : ∀ i, Measurable fun ζ => ψ ζ i) (hbψ : ∀ ζ i, |ψ ζ i| ≤ 1) (Φ : (ι → ℝ) → ℝ) :
    (∫ᵛ e, highPacketObservable a b m 2 D q C c
      (fun ζ z eps => ∏ i, localDensityReset a b 2 z eps p (fun i _ => ψ ζ i) i) Φ e
      ∂<•highPacketSignedMeasure σ a b m 2 D q C A) = 0 := by
  rw [highPacketSignedMeasure_factor_integral σ a b m 2 D q C A hA hcost c
    (fun ζ z eps => ∏ i, localDensityReset a b 2 z eps p (fun i _ => ψ ζ i) i)
    (fun z eps => Finset.measurable_fun_prod _ fun i _ => ordinaryPairReset_measurable a b p ψ hmψ z eps i)
    (b ^ n) (pow_nonneg (ha.trans hab).le n)
    (fun ζ e => finite_density_product_abs_bound _ b (ha.trans hab).le
      (ordinaryPairReset_atom_abs_le a b ha hab m D p hp (ψ ζ) (hbψ ζ) e))
    Φ (finePairResponseAtomBound q C c Φ) (finePairResponseAtomBound_le q C c Φ)]
  simpa only [Finset.card_univ, Fintype.card_fin, if_neg (show n ≠ 2 by omega)] using
    highSeparatedPacketAction_count_selector σ a b ha hab m 2 D q (by omega) (by omega)
      (Finset.univ : Finset (Fin n)) (by simpa using hnD) (by simpa using hnm)
      (by simpa using (show 2 ≤ n by omega)) p (fun ζ i _ => ψ ζ i) (fun i _ => hmψ i)
      (fun ζ i _ => hbψ ζ i) C A hA hcost c Φ

lemma completeSourceRawNumerator_higher_components {d n : ℕ} [NeZero d]
    (ad bd lam ℓ N μ : ℝ) (haD : 0 < ad) (hab : ad < bd) (hlam : 0 ≤ lam) (hℓ : 1 ≤ ℓ)
    (D M q : ℕ) (hn : 3 ≤ n) (hnD : n ≤ D)
    (hnu : ∀ j : Fin (D - 2), 0 < higherBandTargetScale d (j.val + 3) N μ)
    (hFine : ∀ j : Fin (D - 2), ℓ < higherBandTargetScale d (j.val + 3) N μ → j.val + 3 ≤ M)
    (C a V η : ℝ) (hC : C ≠ 0) (U : Fin n → Covariate d) (hU : ∀ i l, |U i l| ≤ 2)
    (p g w : Fin n → ℝ) (hp : ∀ i, p i ∈ Icc ad bd) (c : HighFrameIndex d D → ℝ) (y : Fin n → Fin 3) :
    completeSourceRawNumerator ad bd lam ℓ N μ D M q C a V η U p g w c y =
      highCardinalRawNumerator ad bd lam (max 1 (higherBandTargetScale d n N μ)) D D q C a V η U p g w c y +
      (if M < n then ordinaryFineAliasFamilyRawAction (ordinaryFineAliasTargetSet d D ℓ N μ)
        ad bd lam ℓ (fun r => higherBandTargetScale d r N μ) M q C a V η U p g w c y else 0) +
      (if M < n then finePairPairAliasAction ad bd ℓ N M q C U p c
        (fun v => highResponseProduct a V η g w (fun i => highFrameFeature (U i)) v y) else 0) +
      finePairEvenFieldAction ad bd ℓ N M q C U p c
        (fun v => highResponseProduct a V η g w (fun i => highFrameFeature (U i)) v y) := by
  let Φ (v : HighFrameIndex d D → ℝ) := highResponseProduct a V η g w (fun i => highFrameFeature (U i)) v y
  have hu : finePairUnitFirstAction ad bd D q C p c Φ = 0 :=
    ordinaryPairPacket_zero_other_count hn (Measure.dirac ()) ad bd haD hab D D q hnD hnD C
      (fun _ => finePairUnitMatrix d D) (fun _ _ => measurable_const) (integrable_const _) c p hp
      (fun _ _ => 1) (fun _ => measurable_const) (by intro _ _; norm_num) Φ
  have hcoarse : finePairCoarseFirstAction ad bd ℓ D q C U p c Φ = 0 :=
    ordinaryPairPacket_zero_other_count hn _ ad bd haD hab D D q hnD hnD C _
      (finePairTimeMatrix_measurable d _) (finePairTimeMatrix_cost_integrable d 0 ℓ _) c p hp
      (fun ζ i => finePairTimeFieldValue ζ (U i))
      (fun i => (boundedHyperplaneFieldValue_section_measurable d (U i)).comp measurable_snd)
      (fun ζ i => (finePairTimeFieldValue_abs ζ (U i)).le) Φ
  have hhigh_num : completeSourceRawNumerator ad bd lam ℓ N μ D M q C a V η U p g w c y =
      higherBandFamilyFirstAction ad bd lam ℓ N μ D M q C U p c Φ +
      finePairPairAliasAction ad bd ℓ N M q C U p c Φ +
      finePairEvenFieldAction ad bd ℓ N M q C U p c Φ -
      η ^ 2 * (∏ i, p i) * ∑ i, (w i) ^ 2 *
        highResponseVarianceTerm a V η g w (fun i => highFrameFeature (U i)) c y i := by
    unfold completeSourceRawNumerator
    rw [completeSourceSignedFirstAction_eq_family,
      singletonFirstAction_zero_other_count ad bd haD hab D q (by omega) hnD (by omega) C p hp c Φ,
      finePairThreeRowFirstAction, hu, hcoarse,
      finePairFineFirstAction_alias_even_field ad bd ℓ N haD hab M q C U p hp c Φ]
    ring
  have hfine_below : (∑ j : Fin (D - 2), if j.val + 3 < n then
      higherBandFineFirstAction ad bd lam ℓ N μ (j.val + 3) M D q C U p c Φ else 0) =
      ordinaryFineAliasFamilyRawAction ((ordinaryFineAliasTargetSet d D ℓ N μ).filter fun r => r < n)
        ad bd lam ℓ (fun r => higherBandTargetScale d r N μ) M q C a V η U p g w c y := by
    unfold higherBandFineFirstAction
    have he : (∑ j : Fin (D - 2), if j.val + 3 < n then
        (if ℓ < higherBandTargetScale d (j.val + 3) N μ then
          higherBandFirstAction ad bd lam ℓ (higherBandTargetScale d (j.val + 3) N μ) (j.val + 3) M D q C true U p c Φ
        else 0) else 0) =
        ∑ j : Fin (D - 2), if j.val + 3 < n ∧ ℓ < higherBandTargetScale d (j.val + 3) N μ then
          ordinaryFineAliasRawAction ad bd lam ℓ (higherBandTargetScale d (j.val + 3) N μ)
            M (j.val + 3) q C a V η U p g w c y else 0 :=
      Finset.sum_congr rfl fun j _ => by
        by_cases hjn : j.val + 3 < n <;> by_cases ha' : ℓ < higherBandTargetScale d (j.val + 3) N μ
        · simp only [hjn, ha', and_self, ↓reduceIte]
          exact higherBandFirstAction_fine_eq_aliasRawAction ad bd lam ℓ _ haD hab hlam (by linarith)
            (hℓ.trans ha'.le) (j.val + 3) M D q (by omega) (by omega) hnD C a V η U hU p g w hp c y
        · simp [hjn, ha']
        · simp [hjn, ha']
        · simp [hjn, ha']
    rw [he, ← Finset.sum_filter]
    refine Finset.sum_bij (fun j _ => j.val + 3)
      (fun j hj => by
        have hg := (Finset.mem_filter.mp hj).2
        exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by have := j.isLt; omega), by omega, hg.2⟩, hg.1⟩)
      (fun _ _ _ _ h => Fin.ext (by omega))
      (fun r hr => by
        have hr' := Finset.mem_filter.mp hr
        have hI := Finset.mem_filter.mp hr'.1
        have hrd := Finset.mem_range.mp hI.1
        refine ⟨⟨r - 3, by omega⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, by dsimp; omega⟩
        simpa only [show r - 3 + 3 = r by omega] using And.intro hr'.2 hI.2.2)
      fun _ _ => rfl
  have hnuN : 0 < higherBandTargetScale d n N μ := by
    simpa only [show n - 3 + 3 = n by omega] using hnu ⟨n - 3, by omega⟩
  have hmat : integratedCardinalMatrix (D := D) lam (max 1 (higherBandTargetScale d n N μ)) U =
      integratedCardinalMatrix lam (higherBandTargetScale d n N μ) U :=
    funext fun γ => funext fun δ => integrated_cardinal_matrix_max_one (by omega) lam hnuN U γ δ
  have hcard_heat : highCardinalRawNumerator ad bd lam (max 1 (higherBandTargetScale d n N μ)) D D q C a V η U p g w c y =
      (∏ i, p i) * responseMatrixAction q C (integratedCardinalMatrix lam (higherBandTargetScale d n N μ) U) c Φ -
      η ^ 2 * (∏ i, p i) * ∑ i, (w i) ^ 2 * highResponseVarianceTerm a V η g w (fun i => highFrameFeature (U i)) c y i := by
    dsimp only [Φ]; rw [← hmat]
    rw [highCardinalRawNumerator_eq_alias_defect ad bd lam haD hab hlam (le_max_left _ _) D D q (by omega) hnD hnD hnD
      C a V η hC U hU p g w hp c y,
      integrated_cardinal_response_heat hnD q C a V η lam (max 1 (higherBandTargetScale d n N μ)) hC (le_max_left _ _) U g w c y]
    simp only [mul_sub, sub_mul, mul_one, Finset.sum_sub_distrib]; ring
  rw [hhigh_num, higherBandFamilyFirstAction_matched_and_fine_below ad bd lam ℓ N μ haD hab hlam hℓ D M q hn hnD hnu hFine C U hU p hp c,
    hfine_below, hcard_heat]
  by_cases hnM : M < n
  · have hflt : (ordinaryFineAliasTargetSet d D ℓ N μ).filter (fun r => r < n) = ordinaryFineAliasTargetSet d D ℓ N μ :=
      Finset.filter_eq_self.mpr fun r hr => by
        have ht := Finset.mem_filter.mp hr
        have hrd := Finset.mem_range.mp ht.1
        have hm := hFine ⟨r - 3, by omega⟩ (by simpa only [show r - 3 + 3 = r by omega] using ht.2.2)
        dsimp at hm; omega
    simp only [if_pos hnM, hflt]; ring
  · have hzero : ordinaryFineAliasFamilyRawAction ((ordinaryFineAliasTargetSet d D ℓ N μ).filter fun r => r < n)
        ad bd lam ℓ (fun r => higherBandTargetScale d r N μ) M q C a V η U p g w c y = 0 :=
      Finset.sum_eq_zero fun r hr => by
        have hf := Finset.mem_filter.mp hr
        have ht := Finset.mem_filter.mp hf.1
        unfold ordinaryFineAliasRawAction
        rw [densityCountCoefficient_exact ad bd haD hab M r n (by have := ht.2.1; omega) hf.2.le (le_of_not_gt hnM),
          if_neg (by omega : n ≠ r), zero_mul]
    rw [if_neg hnM, if_neg hnM, hzero,
      finePairPairAliasAction_zero_selected_count ad bd ℓ N haD hab M q hn (le_of_not_gt hnM) C U p c]
    ring

theorem completeSourceRawNumerator_higher_square_le_geometry {d n : ℕ} [NeZero d]
    (aD bD c0 ℓ N μ : ℝ) (haD : 0 < aD) (hℓ : 1 ≤ ℓ) (D M R q : ℕ)
    (hshrink : aD + (M : ℝ)⁻¹ < bD - (M : ℝ)⁻¹) (htau : shrunkDensityExponent aD bD M ≤ c0)
    (hn : 3 ≤ n) (hnD : n ≤ D) (hq : 1 ≤ q)
    (hnu : ∀ j : Fin (D - 2), 0 < higherBandTargetScale d (j.val + 3) N μ)
    (hFine : ∀ j : Fin (D - 2), ℓ < higherBandTargetScale d (j.val + 3) N μ → j.val + 3 ≤ M)
    (hI : ∀ r ∈ ordinaryFineAliasTargetSet d D ℓ N μ, 1 ≤ r ∧ r ≤ R)
    (C a V η ρ : ℝ) (hC : 1 ≤ C) (ha : 0 < a) (hη : 0 ≤ η) (hρ : 0 ≤ ρ) (hηρ : η ≤ ρ / 2)
    (U : Fin n → Covariate d) (hU : ∀ i l, |U i l| ≤ 2)
    (p g w : Fin n → ℝ) (hpD : ∀ i, p i ∈ Icc (aD + (M : ℝ)⁻¹) (bD - (M : ℝ)⁻¹))
    (hg : ∀ i, |g i| ≤ ρ / 2) (hw : ∀ i, |w i| ≤ 1) (c : HighFrameIndex d D → ℝ)
    (hc : ∑ γ, |c γ| ≤ C⁻¹) (hp : ∀ f : ℝ, |f| ≤ ρ → ∀ u, 0 ≤ ternaryMass a f V u) :
    (∑ y : Fin n → Fin 3, completeSourceRawNumerator (aD + (M : ℝ)⁻¹) (bD - (M : ℝ)⁻¹)
      (spatialInterpolationLambda d) ℓ N μ D M q C a V η U p g w c y ^ 2) ≤
      completeSourceHigherGeometryEnvelope (D := D) aD bD c0 ℓ N μ M R q C a ρ η U := by
  let ad := aD + (M : ℝ)⁻¹; let bd := bD - (M : ℝ)⁻¹
  have had : 0 < ad := by dsimp [ad]; positivity
  have hlam : 0 ≤ spatialInterpolationLambda d := by unfold spatialInterpolationLambda; positivity
  let A (y : Fin n → Fin 3) := highCardinalRawNumerator ad bd (spatialInterpolationLambda d)
    (max 1 (higherBandTargetScale d n N μ)) D D q C a V η U p g w c y
  let B (y : Fin n → Fin 3) := if M < n then ordinaryFineAliasFamilyRawAction (ordinaryFineAliasTargetSet d D ℓ N μ)
    ad bd (spatialInterpolationLambda d) ℓ (fun r => higherBandTargetScale d r N μ) M q C a V η U p g w c y else 0
  let P (y : Fin n → Fin 3) := if M < n then finePairPairAliasAction ad bd ℓ N M q C U p c
    (fun v => highResponseProduct a V η g w (fun i => highFrameFeature (U i)) v y) else 0
  let F (y : Fin n → Fin 3) := finePairEvenFieldAction ad bd ℓ N M q C U p c
    (fun v => highResponseProduct a V η g w (fun i => highFrameFeature (U i)) v y)
  have hA : (∑ y, A y ^ 2) ≤ cardinalGeometryEnvelope (F := D) q bd C a ρ η (max 1 (higherBandTargetScale d n N μ)) U :=
    (Finset.sum_le_sum (s := Finset.univ) fun y _ =>
      highCardinalRawNumerator_square_bound_of_chart ad bd _ had hshrink hlam (le_max_left _ _) D D q
        (by omega) hnD hnD hnD hq C a V η ρ hC ha hη hρ hηρ U hU p g w hpD hg hw c hc hp y).trans_eq
      (by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
        nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat]; rfl)
  have hB : (∑ y, B y ^ 2) ≤ (if M < n then ordinaryFineAliasFamilyResponseSquareEnvelope (F := D)
      (ordinaryFineAliasTargetSet d D ℓ N μ) M R q aD bD c0 C a ρ η ℓ (fun r => higherBandTargetScale d r N μ) U else 0) := by
    by_cases hMn : M < n
    · simp only [B, if_pos hMn]
      let H := ∑ r ∈ ordinaryFineAliasTargetSet d D ℓ N μ,
        ordinaryFineAliasAmplitudeFactor n M R q aD bD c0 C a ρ η *
          ordinaryFineAliasGeometryKernel (F := D) r ℓ (higherBandTargetScale d r N μ) U
      have hsq (y : Fin n → Fin 3) :
          ordinaryFineAliasFamilyRawAction (ordinaryFineAliasTargetSet d D ℓ N μ) ad bd
            (spatialInterpolationLambda d) ℓ (fun r => higherBandTargetScale d r N μ) M q C a V η U p g w c y ^ 2 ≤ H ^ 2 := by
        have hb_y : |ordinaryFineAliasFamilyRawAction (ordinaryFineAliasTargetSet d D ℓ N μ) ad bd
            (spatialInterpolationLambda d) ℓ (fun r => higherBandTargetScale d r N μ) M q C a V η U p g w c y| ≤ H :=
          (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun r hr =>
            ordinaryFineAliasRawAction_abs_bound_of_chart aD bD c0 (spatialInterpolationLambda d) ℓ
              (higherBandTargetScale d r N μ) haD hshrink htau (hI r hr).1 (hI r hr).2 q (by omega)
              C a V η ρ hC ha hη hρ hηρ U hU p g w hpD hg hw c hc hp y)
        simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) ((abs_nonneg _).trans hb_y)).mpr hb_y
      simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
        nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat, ordinaryFineAliasFamilyResponseSquareEnvelope, H] using
        Finset.sum_le_sum fun y (_ : y ∈ (Finset.univ : Finset (Fin n → Fin 3))) => hsq y
    · simp [B, hMn]
  let Kpair := finePairDensityCoefficientBudget ad bd M n * (finePairResponseActionBudget d q C a ρ * (n : ℝ) ^ 2 * η ^ 2)
  have hP : (∑ y, P y ^ 2) ≤ (if M < n then finePairAliasGeometryEnvelope ad bd ℓ N M q C a ρ η U else 0) := by
    by_cases hMn : M < n
    · simp only [P, if_pos hMn]
      let Z := ∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard 2, |finePairTimeSubsetMoment ℓ N U S|
      have hy (y : Fin n → Fin 3) : finePairPairAliasAction ad bd ℓ N M q C U p c
          (fun v => highResponseProduct a V η g w (fun i => highFrameFeature (U i)) v y) ^ 2 ≤ Kpair ^ 2 * Z ^ 2 := by
        have h := finePairPairAliasAction_abs_bound_of_chart ad bd ℓ N had hshrink M q (by omega) C a V η ρ
          hC ha hη hρ hηρ U hU p g w hpD c y hc hg hw hp
        rw [show (∑ S ∈ (Finset.univ : Finset (Fin n)).powerset,
          if S.card = 2 then |finePairTimeSubsetMoment ℓ N U S| else 0) = Z by
            dsimp [Z]; rw [Finset.powersetCard_eq_filter, Finset.sum_filter]] at h
        change |_| ≤ Kpair * Z at h
        simpa only [sq_abs, mul_pow] using (sq_le_sq₀ (abs_nonneg _) ((abs_nonneg _).trans h)).mpr h
      refine (Finset.sum_le_sum (s := Finset.univ) fun y _ => hy y).trans_eq ?_
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
        nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat]
      unfold finePairAliasGeometryEnvelope; dsimp [Kpair, Z]; ring
    · simp [P, hMn]
  have hF : (∑ y, F y ^ 2) ≤ fineFieldGeometryEnvelope ad bd ℓ N M q C a ρ η U := by
    let Z := ∑ S ∈ ((Finset.univ : Finset (Fin n)).powerset).filter (fun S => 4 ≤ S.card ∧ Even S.card),
      |finePairTimeSubsetMoment ℓ N U S|
    have hy (y : Fin n → Fin 3) : F y ^ 2 ≤ Kpair ^ 2 * Z ^ 2 := by
      have h := finePairEvenFieldAction_abs_bound_of_chart ad bd ℓ N had hshrink M q (by omega) C a V η ρ
        hC ha hη hρ hηρ U hU p g w hpD c y hc hg hw hp
      rw [show (∑ S ∈ (Finset.univ : Finset (Fin n)).powerset,
        if 4 ≤ S.card ∧ Even S.card then |finePairTimeSubsetMoment ℓ N U S| else 0) = Z by
          dsimp [Z]; rw [Finset.sum_filter]] at h
      change |F y| ≤ Kpair * Z at h
      simpa only [sq_abs, mul_pow] using (sq_le_sq₀ (abs_nonneg _) ((abs_nonneg _).trans h)).mpr h
    refine (Finset.sum_le_sum (s := Finset.univ) fun y _ => hy y).trans_eq ?_
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
      nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat]
    unfold fineFieldGeometryEnvelope; dsimp [Kpair, Z]; ring
  have hb (y : Fin n → Fin 3) : completeSourceRawNumerator ad bd (spatialInterpolationLambda d) ℓ N μ
      D M q C a V η U p g w c y ^ 2 ≤ 4 * (A y ^ 2 + B y ^ 2 + P y ^ 2 + F y ^ 2) := by
    rw [completeSourceRawNumerator_higher_components ad bd _ ℓ N μ had hshrink hlam hℓ D M q hn hnD
      hnu hFine C a V η (lt_of_lt_of_le zero_lt_one hC).ne' U hU p g w hpD c y]
    change (A y + B y + P y + F y) ^ 2 ≤ _
    nlinarith only [sq_nonneg (A y - B y), sq_nonneg (P y - F y), sq_nonneg (A y + B y - P y - F y)]
  have h := Finset.sum_le_sum (s := Finset.univ) fun y _ => hb y
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at h
  refine h.trans ?_
  unfold completeSourceHigherGeometryEnvelope
  convert mul_le_mul_of_nonneg_left (add_le_add (add_le_add (add_le_add hA hB) hP) hF)
    (by norm_num : (0 : ℝ) ≤ 4) using 1

end HigherGeometry

-- 3. Source activity, mass concentration & invariant tilted tails
--    (`SourcePairActivityConversion`, `SourceTotalActivity`, `SourceShrunkActivity`,
--     `HighMassTailScale`, `HighUnionTiltedTail`, `CompleteSourceInvariantMass`, `CompleteSourceSaddleMassTail`)

section ActivityAndMass
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

def sourceActivityConstant (d q : ℕ) (C B lam : ℝ) : ℝ :=
  B ^ 2 * sourceResponseCost q C * (1 + 512 * (d : ℝ)) + B * sourceResponseCost q C +
    4 * higherBandGeometricPrefactor B (higherBandInterpolationBase d lam) (sourceResponseCost q C)

theorem sourceActivityConstant_nonneg (d q : ℕ) (C B lam : ℝ) (hB : 0 ≤ B) :
    0 ≤ sourceActivityConstant d q C B lam := by
  unfold sourceActivityConstant higherBandGeometricPrefactor higherBandInterpolationBase sourceResponseCost
  positivity

theorem sourceRows_shrunk_activity_bound {d k D M q : ℕ} [NeZero d] (hd : 0 < d) (hD : 1 ≤ D)
    (a b C lam N μ c0 q1 q2 : ℝ) (ha : 0 < a)
    (hshrink : a + (M : ℝ)⁻¹ < b - (M : ℝ)⁻¹) (htau : shrunkDensityExponent a b M ≤ c0)
    (hc0 : 1 ≤ c0) (hN : 1 ≤ N) (hμ : 0 ≤ μ) (hbase1 : μ * (1 + Real.log N) ≤ 1)
    (hDN : (D : ℝ) * Real.exp (c0 * (D : ℝ)) ≤ N)
    (hq1 : q1 = higherBandGeometricRatio d D (higherBandSourceCact d a b c0 lam)
      (1 + Real.log N) (μ * (1 + Real.log N)) 1)
    (hq2 : q2 = higherBandGeometricRatio d D (higherBandSourceCact d a b c0 lam)
      (1 + Real.log N) (μ * (1 + Real.log N)) 2)
    (hq1h : q1 ≤ 1 / 2) (hq21 : q2 ≤ q1) (hsmall : (D : ℝ) ^ 2 * q1 ≤ 1) :
    highRowTotalMass (sourceRowData d k D M q (a + (M : ℝ)⁻¹) (b - (M : ℝ)⁻¹) C lam
      (N * Real.exp (-c0 * (D : ℝ))) N μ).rowMass ≤
      sourceActivityConstant d q C (uniformOrdinaryDensityActivityBase a b c0) lam *
        N ^ 2 * Real.exp (shrunkDensityExponent a b M * (M : ℝ)) := by
  let ad := a + (M : ℝ)⁻¹; let bd := b - (M : ℝ)⁻¹
  let ℓ := N * Real.exp (-c0 * (D : ℝ))
  let B := uniformOrdinaryDensityActivityBase a b c0
  have ht : 0 ≤ (M : ℝ)⁻¹ := inv_nonneg.mpr (Nat.cast_nonneg M)
  have hap : 0 < ad := by dsimp [ad]; linarith
  have hab : a < b := by linarith
  have hd0 : (0 : ℝ) ≤ D := Nat.cast_nonneg D
  have hN0 : 0 ≤ N := by linarith
  have hB : 0 ≤ B := mul_nonneg (Real.exp_pos _).le (div_nonneg (sub_pos.mpr hab).le ha.le)
  have hbB := ordinaryDensityActivityBase_shrunk_le ha ht hshrink htau
  have he : exteriorTau ((ad + bd) / (bd - ad)) = shrunkDensityExponent a b M :=
    exteriorTau_sqrt_ratio ad bd hap hshrink
  have hℓ : 0 ≤ ℓ := by dsimp [ℓ]; positivity
  have hℓN : ℓ ≤ N := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left
      (Real.exp_le_one_iff.mpr (by nlinarith : -c0 * (D : ℝ) ≤ 0)) hN0
  have htau0 : 0 ≤ exteriorTau ((ad + bd) / (bd - ad)) := by
    apply exteriorTau_nonneg
    apply (le_div_iff₀ (sub_pos.mpr hshrink)).mpr
    linarith [hap]
  let EM := Real.exp ((M : ℝ) * exteriorTau ((ad + bd) / (bd - ad)))
  let ED := Real.exp ((D : ℝ) * exteriorTau ((ad + bd) / (bd - ad)))
  have hED : 1 ≤ ED := Real.one_le_exp (mul_nonneg hd0 htau0)
  have hEM : 1 ≤ EM := Real.one_le_exp (mul_nonneg (Nat.cast_nonneg _) htau0)
  have hsingle : (D : ℝ) * ED ≤ N := by
    dsimp [ED]; rw [he]
    exact (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by nlinarith)) hd0).trans hDN
  have hcoarse : ED * ℓ ≤ N := by
    dsimp [ED, ℓ]; rw [he]
    have hh : Real.exp ((shrunkDensityExponent a b M - c0) * (D : ℝ)) ≤ 1 :=
      Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr htau) hd0)
    calc Real.exp ((D : ℝ) * shrunkDensityExponent a b M) * (N * Real.exp (-c0 * (D : ℝ)))
      _ = N * Real.exp ((shrunkDensityExponent a b M - c0) * (D : ℝ)) := by
          rw [sub_mul, Real.exp_sub, show -c0 * (D : ℝ) = -(c0 * (D : ℝ)) by ring, Real.exp_neg,
            mul_comm (D : ℝ) (shrunkDensityExponent a b M)]; ring
      _ ≤ N := by simpa only [mul_one] using mul_le_mul_of_nonneg_left hh hN0
  have hpair : (D : ℝ) ^ 2 * ED * ℓ ^ 2 ≤ 2 * N ^ 2 := by
    dsimp [ED, ℓ]; rw [he]
    have hp_exp : (D : ℝ) ^ 2 * Real.exp (-(D : ℝ)) ≤ 2 := by
      have hp0 := Real.pow_div_factorial_le_exp (D : ℝ) hd0 2
      norm_num only [Nat.factorial, Nat.cast_ofNat, Nat.cast_one] at hp0
      have h1 := mul_le_mul_of_nonneg_right (by linarith : (D : ℝ) ^ 2 ≤ 2 * Real.exp D) (Real.exp_pos (-(D : ℝ))).le
      rwa [mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, mul_one] at h1
    have hbound : (D : ℝ) ^ 2 * Real.exp ((shrunkDensityExponent a b M - 2 * c0) * (D : ℝ)) ≤ 2 :=
      (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by nlinarith)) (sq_nonneg _)).trans hp_exp
    rw [show (D : ℝ) ^ 2 * Real.exp ((D : ℝ) * shrunkDensityExponent a b M) * (N * Real.exp (-c0 * (D : ℝ))) ^ 2 =
      N ^ 2 * ((D : ℝ) ^ 2 * Real.exp ((shrunkDensityExponent a b M - 2 * c0) * (D : ℝ))) by
        rw [mul_pow, ← Real.exp_nat_mul, show (shrunkDensityExponent a b M - 2 * c0) * (D : ℝ) =
          (D : ℝ) * shrunkDensityExponent a b M + ((2 : ℕ) : ℝ) * (-c0 * (D : ℝ)) by norm_num; ring, Real.exp_add]; ring]
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left hbound (sq_nonneg N)
  have hunit : (D : ℝ) ^ 2 * ED ≤ N ^ 2 := by
    have h1 := mul_le_mul_of_nonneg_left hED (by positivity : 0 ≤ (D : ℝ) ^ 2 * ED)
    have h2 := pow_le_pow_left₀ (by positivity : 0 ≤ (D : ℝ) * ED) hsingle 2
    nlinarith only [h1, h2]
  let K := ordinaryDensityActivityBase ad bd ^ 2 * sourceResponseCost q C
  have hK : 0 ≤ K := mul_nonneg (sq_nonneg _) (sourceResponseCost_nonneg q C)
  have hu' : finePairRowMass d D M q ad bd C ℓ N .unit ≤ K * N ^ 2 * EM := by
    have hu : finePairRowMass d D M q ad bd C ℓ N .unit ≤ K * N ^ 2 :=
      (finePairRowMass_unit_le d D M q hD ad bd hap hshrink C ℓ N).trans
        (by convert mul_le_mul_of_nonneg_left hunit hK using 1 <;> dsimp [K, ED] <;> ring)
    exact hu.trans (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hEM (by positivity))
  have hc' : finePairRowMass d D M q ad bd C ℓ N .coarse ≤ 256 * (d : ℝ) * K * N ^ 2 * EM := by
    have hc : finePairRowMass d D M q ad bd C ℓ N .coarse ≤ 256 * (d : ℝ) * K * N ^ 2 :=
      ((finePairRowMass_coarse_le d D M q hD ad bd hap hshrink C ℓ N hℓ).trans
        (by convert mul_le_mul_of_nonneg_left hpair (by positivity : 0 ≤ 128 * (d : ℝ) * K) using 1
            <;> dsimp [K, ED] <;> ring)).trans_eq (by ring)
    exact hc.trans (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hEM (by positivity))
  have hf := finePairRowMass_fine_le d D M q ad bd hap hshrink C ℓ N hℓ hℓN
  have hp : highRowTotalMass (finePairRowData d k D M q ad bd C ℓ N).rowMass ≤
      ordinaryDensityActivityBase ad bd ^ 2 * sourceResponseCost q C * (1 + 512 * (d : ℝ)) * N ^ 2 * EM := by
    change (∑ i, finePairRowMass d D M q ad bd C ℓ N i) ≤ _
    rw [show (Finset.univ : Finset FinePairRowTag) = {.unit, .coarse, .fine} by ext i; cases i <;> simp,
      Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
    dsimp [K, EM] at hu' hc' ⊢; nlinarith only [hu', hc', hf]
  have hp' : highRowTotalMass (finePairRowData d k D M q ad bd C ℓ N).rowMass ≤
      B ^ 2 * sourceResponseCost q C * (1 + 512 * (d : ℝ)) * N ^ 2 * EM :=
    hp.trans <| mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by unfold ordinaryDensityActivityBase; positivity) hbB 2)
        (sourceResponseCost_nonneg q C)) (by positivity)) (sq_nonneg N)) (Real.exp_pos _).le
  have hs := singletonRowMass_exponential_bound d D q hD ad bd hap hshrink C
  have hs' : singletonRowMass d D q ad bd C ≤ B * sourceResponseCost q C * N ^ 2 * EM := by
    have h2 := mul_le_mul_of_nonneg_right (mul_le_mul hbB hsingle (by positivity) hB) (sourceResponseCost_nonneg q C)
    have hN2 : N ≤ N ^ 2 * EM := (by nlinarith : N ≤ N ^ 2).trans
      (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hEM (sq_nonneg N))
    have h3 := mul_le_mul_of_nonneg_left hN2 (mul_nonneg hB (sourceResponseCost_nonneg q C))
    dsimp [ED, ordinaryDensityActivityBase, sourceResponseCost] at hs h2 h3 ⊢
    exact hs.trans (by nlinarith only [h2, h3])
  have hh := higherBandFamily_activity_bound (k := k) (M := M) (q := q) hd hD
    ad bd C lam ℓ N μ B q1 q2 hap hshrink hℓ hN hμ hbase1 hB hbB hq1 hq2 hq1h hq21 hsmall hcoarse
  have htot : highRowTotalMass (sourceRowData d k D M q ad bd C lam ℓ N μ).rowMass ≤
      sourceActivityConstant d q C B lam * N ^ 2 * EM := by
    rw [sourceRowTotalMass_eq]; dsimp [sourceActivityConstant]
    change _ ≤ _ * N ^ 2 * EM; nlinarith only [hp', hs', hh]
  simpa only [EM, he, mul_comm (M : ℝ) (shrunkDensityExponent a b M)] using htot

def highHistoryMassMomentConstant (d : ℕ) (a b : ℝ) : ℝ := (2 : ℝ) ^ (2 * d) * (b - a) ^ 2 / 8

theorem highHistoryMassMomentConstant_pos (d : ℕ) (a b : ℝ) (hab : a < b) :
    0 < highHistoryMassMomentConstant d a b := by
  unfold highHistoryMassMomentConstant; positivity

lemma highHistoryMassParameter_lowerSaddle (d : ℕ) (m θ C a b x : ℝ) :
    highHistoryMassParameter d (lowerSaddleGrid d m θ C x) a b =
      highHistoryMassMomentConstant d a b * (lowerSaddleH d m θ C x) ^ (d : ℝ) := by
  have hk : 0 < lowerSaddleGrid d m θ C x := by exact_mod_cast lowerSaddleGrid_positive (d : ℝ) m θ C x
  rw [highHistoryMassParameter_eq d _ a b hk, lowerSaddleH, Real.rpow_natCast]
  unfold highHistoryMassMomentConstant
  simp only [div_eq_mul_inv, mul_inv_rev, inv_pow]; ring

theorem eventually_highHistoryMass_saddle_guard {d : ℕ} (hd : 0 < d)
    {m θ cm : ℝ} (hm : 0 < m) (hθ : 0 < θ) (hcm : 0 < cm) (C a b : ℝ) (hab : a < b) :
    ∀ᶠ x : ℝ in atTop, 2 ≤ lowerSaddleGrid d m θ C x ∧
      8 * highHistoryMassParameter d (lowerSaddleGrid d m θ C x) a b * x ≤ cm / lowerSaddleM m x := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  filter_upwards [eventually_lowerSaddle_grid_and_mass hdR hm hθ hcm
    (highHistoryMassMomentConstant_pos d a b hab) C 2] with x hx
  refine ⟨hx.1, ?_⟩
  rw [highHistoryMassParameter_lowerSaddle]
  unfold lowerSaddleMu at hx; nlinarith only [hx.2]

theorem highHistoryMass_saddle_tail_eq (d : ℕ) (m θ C cm a b x : ℝ) :
    2 * Real.exp (-(cm / (lowerSaddleM m x : ℝ)) ^ 2 /
      (8 * highHistoryMassParameter d (lowerSaddleGrid d m θ C x) a b)) =
      lowerSaddleExceptionalTail d m θ C (cm ^ 2 / (8 * highHistoryMassMomentConstant d a b)) x := by
  rw [highHistoryMassParameter_lowerSaddle]; unfold lowerSaddleExceptionalTail
  congr 2; simp only [div_eq_mul_inv, mul_inv_rev]; ring

section CompleteSourceMass
variable {d k D M q : ℕ} [NeZero d] [NeZero k] [LinearOrder (HighWindowLabels d k)]
    (C : ModelConstants d) (hD : 3 ≤ D) (hq : 1 ≤ q)
    (hM : highCenterResolutionThreshold C ≤ (M : ℝ))
    (Cfr lam ℓ N μ : ℝ) (hCfr : 1 ≤ Cfr) (hℓ : 0 < ℓ) (hℓN : ℓ < N)
include hD hq hM hCfr hℓ hℓN

theorem completeSourceRows_mass_positive (i : SourceRowIndex d D M q
    (C.densityLower + 1 / (M : ℝ)) (C.densityUpper - 1 / (M : ℝ)) Cfr lam ℓ N μ) :
    0 < (completeSourceRows C k D M q Cfr lam ℓ N μ).rowMass i := by
  obtain ⟨ha, hab⟩ := high_source_interval_numeric C (M : ℝ) hM
  exact sourceRowMass_positive_actual d k D M q hD hq _ _ ha hab Cfr (by linarith) lam ℓ N μ hℓ hℓN i

theorem completeSourcePrior_probability (T : ℝ) (hT : 0 ≤ T)
    (hsmall : T * (highRowTotalMass (completeSourceRows C k D M q Cfr lam ℓ N μ).rowMass /
      highCenterMix C) / historyReferenceRho (3 ^ d) ≤ 1 / (2 + 8 * ((3 ^ d : ℕ) : ℝ) ^ 2))
    (t : ℝ) (ht : t ∈ Icc 0 T) :
    IsProbabilityMeasure (historyMarkedPrior (fun i j => j ∈ highNeighborLabels d k i) (3 ^ d) t
      (highUnionLaw (completeSourceRows C k D M q Cfr lam ℓ N μ) (highCenterMix C))
      (highUnionActivation (completeSourceRows C k D M q Cfr lam ℓ N μ) (highCenterMix C))) :=
  highUnionSourcePrior_probability C _
    (completeSourceRows_guards C k D M q hD hq hM Cfr lam ℓ N μ hCfr hℓ hℓN)
    (completeSourceRows_mass_positive C hD hq hM Cfr lam ℓ N μ hCfr hℓ hℓN) T hT hsmall t ht

theorem completeSourceMass_prior_law (T : ℝ) (hT : 0 ≤ T)
    (hsmall : T * (highRowTotalMass (completeSourceRows C k D M q Cfr lam ℓ N μ).rowMass /
      highCenterMix C) / historyReferenceRho (3 ^ d) ≤ 1 / (2 + 8 * ((3 ^ d : ℕ) : ℝ) ^ 2))
    (t : ℝ) (ht : t ∈ Icc 0 T) :
    Measure.map (highUnionSourceMass C (completeSourceRows C k D M q Cfr lam ℓ N μ))
      (historyMarkedPrior (fun i j => j ∈ highNeighborLabels d k i) (3 ^ d) t
        (highUnionLaw (completeSourceRows C k D M q Cfr lam ℓ N μ) (highCenterMix C))
        (highUnionActivation (completeSourceRows C k D M q Cfr lam ℓ N μ) (highCenterMix C))) =
    Measure.map (highUnionSourceMass C (completeSourceRows C k D M q Cfr lam ℓ N μ))
      (historyMarkedReference (fun i j => j ∈ highNeighborLabels d k i) (3 ^ d)
        (highUnionLaw (completeSourceRows C k D M q Cfr lam ℓ N μ) (highCenterMix C))) :=
  highUnionSourceMass_prior_law_of_append_annihilation C _
    (completeSourceRows_guards C k D M q hD hq hM Cfr lam ℓ N μ hCfr hℓ hℓN)
    (completeSourceRows_mass_positive C hD hq hM Cfr lam ℓ N μ hCfr hℓ hℓN)
    T hT hsmall (completeSourceMass_append_indicator_zero C hD hq hM Cfr lam ℓ N μ hCfr hℓ hℓN) t ht

theorem completeSourceMass_prior_tilted_tail (hk : 2 ≤ k) (T : ℝ) (hT : 0 ≤ T)
    (hsmall : T * (highRowTotalMass (completeSourceRows C k D M q Cfr lam ℓ N μ).rowMass /
      highCenterMix C) / historyReferenceRho (3 ^ d) ≤ 1 / (2 + 8 * ((3 ^ d : ℕ) : ℝ) ^ 2))
    (n : ℕ) (epsilon : ℝ)
    (hepsilon : 8 * highHistoryMassParameter d k C.densityLower C.densityUpper * (n : ℝ) ≤ epsilon)
    (t : ℝ) (ht : t ∈ Icc 0 T) :
    (massPowerTilt
      (historyMarkedPrior (fun i j => j ∈ highNeighborLabels d k i) (3 ^ d) t
        (highUnionLaw (completeSourceRows C k D M q Cfr lam ℓ N μ) (highCenterMix C))
        (highUnionActivation (completeSourceRows C k D M q Cfr lam ℓ N μ) (highCenterMix C)))
      (highUnionSourceMass C (completeSourceRows C k D M q Cfr lam ℓ N μ)) n).real
      {h | epsilon < |highUnionSourceMass C (completeSourceRows C k D M q Cfr lam ℓ N μ) h - 1|} ≤
      2 * Real.exp (-epsilon ^ 2 / (8 * highHistoryMassParameter d k C.densityLower C.densityUpper)) := by
  let R := completeSourceRows C k D M q Cfr lam ℓ N μ
  have G := completeSourceRows_guards C k D M q hD hq hM Cfr lam ℓ N μ hCfr hℓ hℓN
  rw [massPowerTilt_abs_event_eq_of_massLaw _ _ _ (highUnionSourceMass_measurable C R G) n
    (completeSourceMass_prior_law C hD hq hM Cfr lam ℓ N μ hCfr hℓ hℓN T hT hsmall t ht) epsilon]
  letI := highUnionSourceLaw_probability C R G
  letI := historyMarkedReference_probability _ (highNeighborLabels_self_mem d k)
    (fun {_ _} h => highNeighborLabels_symmetric d k _ _ h) (3 ^ d)
    (one_le_pow₀ (by norm_num : (1 : ℕ) ≤ 3)) (highNeighbor_dependency_card d k)
    (highUnionLaw R (highCenterMix C))
  have hM0 : 0 < (M : ℝ) := by linarith [(highCenterResolution_guards C (M : ℝ) G.resolution).1]
  exact massPowerTilt_abs_tail _ _ (highUnionSourceMass_measurable C R G) n
    C.densityLower C.densityUpper C.densityLower_pos
    (fun h => ⟨(le_add_of_nonneg_right (one_div_pos.mpr hM0).le).trans (highUnionSourceMass_interval C R G h).1,
      (highUnionSourceMass_interval C R G h).2.trans (sub_le_self _ (one_div_pos.mpr hM0).le)⟩)
    (highUnionSourceMass_reference_mean_one C R G) _ epsilon
    (highHistoryMassParameter_pos d k _ _ (by omega) (C.densityLower_lt_one.trans C.one_lt_densityUpper))
    (highUnionSourceMass_reference_mgf C R G hk) hepsilon

end CompleteSourceMass

def highCompleteSourceSaddleCoefficient {d : ℕ} (C : ModelConstants d) : ℝ :=
  lowerSaddleCoefficient C.smoothness d (densityIntervalExponent C.densityLower C.densityUpper)

def highCompleteSourceSaddleTheta {d : ℕ} (C : ModelConstants d) : ℝ :=
  lowerSaddleTheta C.smoothness d (densityIntervalExponent C.densityLower C.densityUpper)

def highCompleteSourceSaddleTail {d : ℕ} (C : ModelConstants d) (Cω cm : ℝ) (n : ℕ) : ℝ :=
  lowerSaddleExceptionalTail d (highCompleteSourceSaddleCoefficient C) (highCompleteSourceSaddleTheta C) Cω
    (cm ^ 2 / (8 * highHistoryMassMomentConstant d C.densityLower C.densityUpper)) n

-- 4. Model legality, ternary floors & local canonical response guards
--    (`TernaryEffectiveInterval`, `HighUnionObservationGuards`, `HighUnionSourceUniformModel`,
--     `HighCompleteSourceMarkedTail`, `HighSourceOriginalGuards`, `HighSourceCanonicalResponse`,
--     `HighSourceOriginalResponse`)

theorem LowSmoothnessTernaryConstants.effective_interval {d : ℕ}
    {C : ModelConstants d} (Q : LowSmoothnessTernaryConstants C)
    {V : ℝ} (hV : |V - Q.v| ≤ Q.ρ) : V ∈ Icc C.varianceLower (effectiveVarianceUpper C) := by
  have h := Q.legal 0 V (by simpa using Q.ρ_pos.le) hV
  have hp' : 0 < 1 - V / Q.a ^ 2 := by simpa [ternaryMass] using Q.c_pos.trans_le (h.2.2.1 1)
  have hVa : V < Q.a ^ 2 := (div_lt_one (sq_pos_of_pos Q.a_pos)).mp (by linarith)
  have hfourth : Q.a ^ 2 * V ≤ C.fourthBound := by
    have hf := h.2.2.2; rw [ternary_fourth_central_moment Q.a 0 V Q.a_pos.ne'] at hf; simpa using hf
  obtain ⟨θ, hθ, hθV⟩ := uniformZeroParameter_admissible C Q.a V Q.a_pos h.1.le h.2.1.le hVa hfourth
  simpa only [hθV, effectiveVarianceUpper] using admissible_variance_effective_interval C θ hθ

theorem HighUnionSourceGuards.mono_frame {d k F : ℕ} {I : Type*} [Fintype I]
    {E : I → Type*} [∀ i, MeasurableSpace (E i)]
    {C : ModelConstants d} {M Cfr Cfr' : ℝ} {R : HighUnionRowData d k F I E}
    (G : HighUnionSourceGuards C M Cfr R) (hfr : 1 ≤ Cfr') (hle : Cfr' ≤ Cfr) :
    HighUnionSourceGuards C M Cfr' R :=
  { G with
    frame := hfr
    vector_ball := fun i e => (G.vector_ball i e).trans
      ((inv_le_inv₀ (by linarith [G.frame]) (by linarith)).mpr hle) }

theorem highUnionSource_ternary_floor_uniform {d : ℕ} (C : ModelConstants d)
    (Q : LowSmoothnessTernaryConstants C) :
    ∃ Cfr η0 : ℝ, 1 ≤ Cfr ∧ 0 < η0 ∧
      ∀ k F : ℕ, ∀ (_ : NeZero k), ∀ (_ : LinearOrder (HighWindowLabels d k)), 4 ≤ k →
      ∀ (I : Type*) (_ : Fintype I) (E : I → Type*) (_ : (i : I) → MeasurableSpace (E i))
        (R : HighUnionRowData d k F I E) (M : ℝ),
      HighUnionSourceGuards C M Cfr R →
      ∀ cf : ℝ, 0 ≤ cf → cf * (k : ℝ) ^ (-C.smoothness) ≤ η0 →
      ∀ h : HistoryMarked (fun i j => j ∈ highNeighborLabels d k i) (HighUnionMark E),
      ∀ V : ℝ, |V - Q.v| ≤ Q.ρ →
      ∀ x y, Q.c ≤ ternaryMass Q.a
        (highUnionSourceRegression C R (cf * (k : ℝ) ^ (-C.smoothness)) h x) V y := by
  obtain ⟨Cfr, hCfr, hbound⟩ := highFrameField_original_model_bounds C
  obtain ⟨η0, hη0, hguard⟩ := highFrame_ternary_amplitude_guards Q
  refine ⟨Cfr, η0, hCfr, hη0, fun k F hk0 horder hk I hI E hE R M G cf hcf hη h V hV x y => ?_⟩
  letI := hk0; letI := horder; letI := hI; letI := hE
  let η := cf * (k : ℝ) ^ (-C.smoothness)
  let P (j) := highFramePolynomial ((highUnionSourceState C R h).2 j)
  have hP (j) : frameCoefficientL1 (P j) ≤ Cfr⁻¹ :=
    (highFramePolynomial_coefficientL1_le _).trans (highUnionSourceState_coefficient_ball C R G h j)
  obtain ⟨_, hηsup⟩ := hguard η (by dsimp [η]; positivity) hη
  have hf : |highUnionSourceRegression C R η h x| ≤ Q.ρ :=
    ((hbound k hk0 hk cf hcf P hP).1 x).trans (hηsup.trans (by linarith [Q.ρ_pos]))
  exact (Q.legal _ V hf hV).2.2.1 y

theorem highUnionSource_original_model_uniform {d : ℕ} (C : ModelConstants d)
    (Q : LowSmoothnessTernaryConstants C) :
    ∃ Cfr η0 : ℝ, 1 ≤ Cfr ∧ 0 < η0 ∧
      ∀ U : ExtensionDomain d,
      ∀ k F : ℕ, ∀ (_ : NeZero k), ∀ (_ : LinearOrder (HighWindowLabels d k)), 4 ≤ k →
      ∀ (I : Type*) (_ : Fintype I) (E : I → Type*) (_ : (i : I) → MeasurableSpace (E i))
        (_ : (i : I) → StandardBorelSpace (E i))
        (R : HighUnionRowData d k F I E) (M : ℝ),
      HighUnionSourceGuards C M Cfr R →
      ∀ cf : ℝ, 0 ≤ cf → highWindowHolderConstant C * cf ≤ C.holderBound →
        cf * (k : ℝ) ^ (-C.smoothness) ≤ η0 →
      ∀ cm : ℝ, 0 ≤ cm → cm ≤ 1 / C.densityUpper →
      ∀ h : HistoryMarked (fun i j => j ∈ highNeighborLabels d k i) (HighUnionMark E),
        |highUnionSourceMass C R h - 1| ≤ cm / M →
      ∀ V : ℝ, |V - Q.v| ≤ Q.ρ →
      let p := highUnionSourceDensity C R h
      let f := highUnionSourceRegression C R (cf * (k : ℝ) ^ (-C.smoothness)) h
      ∃ hq : ∀ x y, 0 ≤ ternaryMass Q.a (f x) V y,
        Admissible (C.withDomain U) (normalizedDensityTernaryParameter p f Q.a V
          (highFrameField_contDiff d k _ _).continuous.measurable Q.a_pos.ne' hq) := by
  obtain ⟨Cfr, hCfr, hbound⟩ := highFrameField_original_model_bounds C
  obtain ⟨η0, hη0, hguard⟩ := highFrame_ternary_amplitude_guards Q
  refine ⟨Cfr, η0, hCfr, hη0, fun U k F hk0 horder hk I hI E hE hEB R M G cf hcf hcfH hη cm hcm hcmU h hmass V hV => ?_⟩
  letI := hk0; letI := horder; letI := hI; letI := hE; letI := hEB
  let η := cf * (k : ℝ) ^ (-C.smoothness)
  let P (j) := highFramePolynomial ((highUnionSourceState C R h).2 j)
  let f := highFrameField d k η P
  let p := highUnionSourceDensity C R h
  have hP (j) : frameCoefficientL1 (P j) ≤ Cfr⁻¹ :=
    (highFramePolynomial_coefficientL1_le _).trans (highUnionSourceState_coefficient_ball C R G h j)
  obtain ⟨_, hsupη⟩ := hguard η (by dsimp [η]; positivity) hη
  obtain ⟨hvalue, _, _, hnorm⟩ := hbound k hk0 hk cf hcf P hP
  have hlegal (x : Covariate d) := Q.legal (f x) V ((hvalue x).trans (hsupη.trans (by linarith [Q.ρ_pos]))) hV
  have hq : ∀ x y, 0 ≤ ternaryMass Q.a (f x) V y := fun x y => Q.c_pos.le.trans ((hlegal x).2.2.1 y)
  refine ⟨hq, ?_⟩
  have hF := highFrameField_contDiff d k η P
  have hp : Measurable p := (highUnionSourceDensity_joint_measurable C R G).comp (measurable_const.prodMk measurable_id)
  have hraw : ∀ᵐ x ∂cubeVolume d, C.densityLower + 1 / M ≤ p x ∧ p x ≤ C.densityUpper - 1 / M :=
    Filter.Eventually.of_forall fun x => highUnionSourceDensity_interval C R G h x
  have hM := (highCenterResolution_guards C M G.resolution).1
  have hM0 : 0 < M := by linarith
  have hp0 : 0 ≤ᵐ[cubeVolume d] p := by
    filter_upwards [hraw] with x hx; change 0 ≤ p x; linarith [C.densityLower_pos, one_div_pos.mpr hM0]
  have hmass0 : 0 < highRawDensityMass p :=
    lt_of_lt_of_le (by norm_num) (high_raw_mass_lower C M cm (highRawDensityMass p) hM hcm hcmU hmass)
  refine ⟨highNormalizedDensity_measurable p hp, hF.continuous.measurable,
    highNormalizedDensity_bounds C M cm hM hcm hcmU p hraw hmass,
    highNormalizedDensity_normalized p (highRawDensity_integrable C M hM0 p hp hraw) hp0 hmass0,
    ⟨f, fun _ _ => rfl, (hF.of_le (by simp)).contDiffOn, (hnorm U.carrier).trans (ENNReal.ofReal_le_ofReal hcfH)⟩,
    (hlegal 0).1.le, (hlegal 0).2.1.le, Filter.Eventually.of_forall fun x => ?_⟩
  refine ⟨ternary_error_integrable Q.a V f hF.continuous.measurable x _,
    ternary_error_integrable Q.a V f hF.continuous.measurable x _,
    ternary_error_integrable Q.a V f hF.continuous.measurable x _,
    ternary_error_mean Q.a V f hF.continuous.measurable x Q.a_pos.ne' (hq x),
    ternary_error_variance Q.a V f hF.continuous.measurable x Q.a_pos.ne' (hq x),
    (ternary_error_fourth Q.a V f hF.continuous.measurable x Q.a_pos.ne' (hq x)).trans_le ?_⟩
  simpa only [ternary_fourth_central_moment _ _ _ Q.a_pos.ne', ModelConstants.withDomain] using (hlegal x).2.2.2

theorem crude_raw_square_energy_pointwise {d n : ℕ} (Chi η B : ℝ)
    (hChi : 0 ≤ Chi) (hB : 0 ≤ B)
    (R : (Fin n → Covariate d) → (Fin n → Fin 3) → ℝ)
    (hcap : ∀ x y, |R x y| ≤ Chi ^ n * η ^ 2 * (B + 1)) (x : Fin n → Covariate d) :
    selectedRawSquareEnergy R x ≤ (3 * Chi ^ 2) ^ n * η ^ 4 * (B + 1) ^ 2 := by
  have hp (y) : R x y ^ 2 ≤ Chi ^ (2 * n) * η ^ 4 * (B + 1) ^ 2 := by
    have hh := (sq_le_sq₀ (abs_nonneg _) (by positivity : 0 ≤ Chi ^ n * η ^ 2 * (B + 1))).mpr (hcap x y)
    simp only [sq_abs] at hh
    convert hh using 1 <;> (try rw [mul_pow, mul_pow, ← pow_mul]) <;> ring
  have he : selectedRawSquareEnergy R x = ∑ y : Fin n → Fin 3, R x y ^ 2 :=
    Finset.sum_congr (by ext; simp) fun _ _ => rfl
  refine (he.trans_le (Finset.sum_le_sum fun y _ => hp y)).trans_eq ?_
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
    Nat.cast_pow, Nat.cast_ofNat, nsmul_eq_mul, mul_pow, ← pow_mul]; ring

def highUnionSourceRawNumerator {d k D : ℕ} {I : Type*} [Fintype I] {E : I → Type*}
    [∀ i, MeasurableSpace (E i)] [∀ i, StandardBorelSpace (E i)]
    [NeZero k] [LinearOrder (HighWindowLabels d k)]
    (C : ModelConstants d) (R : HighUnionRowData d k D I E)
    (r : ℕ) (a V η : ℝ)
    (h : HistoryMarked (fun i j => j ∈ highNeighborLabels d k i) (HighUnionMark E))
    (j : HighWindowLabels d k) (x : Fin r → Covariate d) (y : Fin r → Fin 3) : ℝ :=
  highMarkedSampleNumerator r (highUnionLaw R (highCenterMix C))
    (highUnionActivation R (highCenterMix C)) a V η (highUnionSourceDensity C R h)
    (highUnionSourceResetDensity C R j h) (highUnionSourceResetCoefficient C R j h)
    (highLocalFieldWithout d k D η (highUnionSourceState C R h).2 j)
    (highPeriodicTensor d k j) (fun x => highLocalFrameFeature k j x)
    ((highUnionSourceState C R h).2 j) x y

abbrev highUnionSourceMarkedNumerator {d k D : ℕ} {I : Type*} [Fintype I] {E : I → Type*}
    [∀ i, MeasurableSpace (E i)] [∀ i, StandardBorelSpace (E i)]
    [NeZero k] [LinearOrder (HighWindowLabels d k)]
    (C : ModelConstants d) (R : HighUnionRowData d k D I E)
    (n : ℕ) (a V η : ℝ) (j : HighWindowLabels d k)
    (h : HistoryMarked (fun i j => j ∈ highNeighborLabels d k i) (HighUnionMark E)) :=
  highUnionSourceRawNumerator C R n a V η h j

end ActivityAndMass

section LocalResponseGuards
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
attribute [local irreducible] highUnionSourceDensity highUnionSourceState historyMarkedAppend

structure HighFrameOriginalLocalGuards (d k D : ℕ) [NeZero k] (Cfr eta rho : ℝ)
    (c : HighWindowLabels d k → HighFrameIndex d D → ℝ) : Prop where
  amplitude_nonneg : 0 ≤ eta
  amplitude_half : eta ≤ rho / 2
  coefficient_ball : ∀ j, (∑ γ, |c j γ|) ≤ Cfr⁻¹
  weight_abs : ∀ j x, |highPeriodicTensor d k j x| ≤ 1
  without_abs : ∀ j x, |highLocalFieldWithout d k D eta c j x| ≤ rho / 2
  profile_abs : ∀ j (v : HighFrameIndex d D → ℝ), (∑ γ, |v γ|) ≤ Cfr⁻¹ →
    ∀ x, |∑ γ, highLocalFrameFeature k j x γ * v γ| ≤ 1
  regression_abs : ∀ j (v : HighFrameIndex d D → ℝ), (∑ γ, |v γ|) ≤ Cfr⁻¹ →
    ∀ x, |highLocalFieldWithout d k D eta c j x + eta * highPeriodicTensor d k j x *
      (∑ γ, highLocalFrameFeature k j x γ * v γ)| ≤ rho

theorem completeSource_original_local_guards {d : ℕ} [NeZero d]
    (C : ModelConstants d) (Q : LowSmoothnessTernaryConstants C) :
    ∃ Cfr0 eta0 : ℝ, 1 ≤ Cfr0 ∧ 0 < eta0 ∧
      ∀ k D M q : ℕ, ∀ (_ : NeZero k), ∀ (_ : LinearOrder (HighWindowLabels d k)),
      4 ≤ k → 3 ≤ D → 1 ≤ q → highCenterResolutionThreshold C ≤ (M : ℝ) →
      ∀ Cfr lam ell N mu cf : ℝ, Cfr0 ≤ Cfr → 0 < ell → ell < N → 0 ≤ cf →
      cf * (k : ℝ) ^ (-C.smoothness) ≤ eta0 →
      ∀ h : HistoryMarked (fun i j => j ∈ highNeighborLabels d k i)
        (HighUnionMark (SourceRowMark d D M q (C.densityLower + 1 / (M : ℝ))
          (C.densityUpper - 1 / (M : ℝ)) Cfr lam ell N mu)),
      let R := completeSourceRows C k D M q Cfr lam ell N mu
      HighFrameOriginalLocalGuards d k D Cfr (cf * (k : ℝ) ^ (-C.smoothness)) Q.ρ
        (highUnionSourceState C R h).2 := by
  obtain ⟨Cfr0, hfr0, hfield⟩ := highFrameField_original_model_bounds C
  let eta0 := Q.ρ / (2 * ((2 : ℝ) ^ d + 1))
  refine ⟨Cfr0, eta0, hfr0, div_pos Q.ρ_pos (by positivity),
    fun k D M q hk0 horder hk hD hq hM Cfr lam ell N mu cf hfr hell hellN hcf heta h => ?_⟩
  letI := hk0; letI := horder
  let R := completeSourceRows C k D M q Cfr lam ell N mu
  let c := (highUnionSourceState C R h).2
  have hfr1 : 1 ≤ Cfr := hfr0.trans hfr
  have G := completeSourceRows_guards C k D M q hD hq hM Cfr lam ell N mu hfr1 hell hellN
  have hc := highUnionSourceState_coefficient_ball C R G h
  let eta := cf * (k : ℝ) ^ (-C.smoothness)
  have hen : 0 ≤ eta := by dsimp [eta]; positivity
  have hamp : ((2 : ℝ) ^ d + 1) * eta ≤ Q.ρ / 2 := by
    have ht := (le_div_iff₀ (by positivity : 0 < 2 * ((2 : ℝ) ^ d + 1))).mp heta
    change eta * (2 * ((2 : ℝ) ^ d + 1)) ≤ Q.ρ at ht; nlinarith
  have hehalf : eta ≤ Q.ρ / 2 := by nlinarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) d]
  have hP (j) : frameCoefficientL1 (highFramePolynomial (c j)) ≤ Cfr0⁻¹ :=
    (highFramePolynomial_coefficientL1_le _).trans
      ((hc j).trans ((inv_le_inv₀ (by linarith) (by linarith)).mpr hfr))
  have hF := (hfield k hk0 hk cf hcf (fun j => highFramePolynomial (c j)) hP).1
  have hw (j x) : |highPeriodicTensor d k j x| ≤ 1 := by
    rw [abs_of_nonneg (highPeriodicTensor_nonneg d k j x)]
    exact highPeriodicTensor_le_one d k (by omega) j x
  have hprof (j) (v : HighFrameIndex d D → ℝ) (hv : ∑ γ, |v γ| ≤ Cfr⁻¹) (x) :
      |∑ γ, highLocalFrameFeature k j x γ * v γ| ≤ 1 :=
    highLocalFrameFeature_ball_abs_le_one k j x Cfr hfr1 v hv
  have hterm (j) (v : HighFrameIndex d D → ℝ) (hv : ∑ γ, |v γ| ≤ Cfr⁻¹) (x) :
      |eta * highPeriodicTensor d k j x * (∑ γ, highLocalFrameFeature k j x γ * v γ)| ≤ eta := by
    rw [abs_mul, abs_mul, abs_of_nonneg hen]
    have ht := mul_le_mul (hw j x) (hprof j v hv x) (abs_nonneg _) zero_le_one
    nlinarith [mul_le_mul_of_nonneg_left ht hen]
  have hg (j x) : |highLocalFieldWithout d k D eta c j x| ≤ Q.ρ / 2 := by
    have hd := highFrameField_local_decomposition d k D hk eta c j x
    rw [show highLocalFieldWithout d k D eta c j x =
      highFrameField d k eta (fun l => highFramePolynomial (c l)) x -
        eta * highPeriodicTensor d k j x * (∑ γ, highLocalFrameFeature k j x γ * c j γ) by linarith [hd]]
    exact (abs_sub _ _).trans ((add_le_add (hF x) (hterm j (c j) (hc j) x)).trans (by nlinarith only [hamp]))
  exact ⟨hen, hehalf, hc, hw, hg, hprof, fun j v hv x =>
    (abs_add_le _ _).trans (by linarith only [hg j x, hterm j v hv x, hehalf])⟩

end LocalResponseGuards

section CanonicalResponse
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 1800000
attribute [local irreducible] highUnionSourceDensity highUnionSourceState historyMarkedAppend

lemma completeSourceRawNumerator_eq_canonical {d k D M q n : ℕ} [NeZero d] [NeZero k]
    [LinearOrder (HighWindowLabels d k)]
    (C : ModelConstants d) (hD : 3 ≤ D) (hq : 1 ≤ q)
    (hM : highCenterResolutionThreshold C ≤ (M : ℝ))
    (Cfr lam ℓ N μ : ℝ) (hCfr : 1 ≤ Cfr) (hℓ : 0 < ℓ) (hℓN : ℓ < N)
    (j : HighWindowLabels d k)
    (h : HistoryMarked (fun i j => j ∈ highNeighborLabels d k i)
      (HighUnionMark (SourceRowMark d D M q (C.densityLower + 1 / (M : ℝ))
        (C.densityUpper - 1 / (M : ℝ)) Cfr lam ℓ N μ)))
    (x : Fin n → Covariate d) (hx : ∀ u, x u ∈ highTorusPatch d k j)
    (a V η : ℝ) (ha : a ≠ 0) (g w : Fin n → ℝ)
    (hp : ∀ v : HighFrameIndex d D → ℝ, (∑ γ, |v γ|) ≤ Cfr⁻¹ → ∀ u b,
      0 ≤ ternaryMass a (coefficientRegression η g w (fun u : Fin n => highLocalFrameFeature (D := D) k j (x u)) v u) V b)
    (y : Fin n → Fin 3) :
    let R := completeSourceRows C k D M q Cfr lam ℓ N μ
    highMarkedLocalScoreNumerator (highUnionLaw R (highCenterMix C))
      (highUnionActivation R (highCenterMix C)) a V η
      (fun u => highUnionSourceDensity C R h (x u))
      (fun e u => highUnionSourceResetDensity C R j h e (x u))
      (highUnionSourceResetCoefficient C R j h) g w (fun u : Fin n => highLocalFrameFeature (D := D) k j (x u))
      ((highUnionSourceState C R h).2 j) y =
      completeSourceRawNumerator (C.densityLower + 1 / (M : ℝ))
        (C.densityUpper - 1 / (M : ℝ)) lam ℓ N μ D M q Cfr a V η
        (fun u : Fin n => highLocalCoordinates d k j (x u))
        (fun u => highUnionSourceDensity C R h (x u)) g w ((highUnionSourceState C R h).2 j) y := by
  let Φ (v : HighFrameIndex d D → ℝ) :=
    highResponseProduct a V η g w (fun u : Fin n => highLocalFrameFeature (D := D) k j (x u)) v y
  have hmΦ : Measurable Φ := highMarkedResponseProduct_measurable a V η (fun v => v)
    (fun γ => measurable_pi_apply γ) g w (fun u : Fin n => highLocalFrameFeature (D := D) k j (x u)) y
  have hbΦ (v : HighFrameIndex d D → ℝ) (hv : ∑ γ, |v γ| ≤ Cfr⁻¹) : |Φ v| ≤ 1 :=
    highMarkedResponseProduct_abs_le_one a V η ha g w
      (fun u : Fin n => highLocalFrameFeature (D := D) k j (x u)) v (hp v hv) y
  have he := completeSourceCanonicalAction_eq_signed_first_action C hD hq hM Cfr lam ℓ N μ
    hCfr hℓ hℓN j h x hx Φ hmΦ 1 (by norm_num) hbΦ
  unfold highMarkedLocalScoreNumerator completeSourceRawNumerator
  congr 1
  exact (integral_congr_ae <| Filter.Eventually.of_forall fun _ => by dsimp only [Φ]; ring).trans he

theorem completeSourceDensity_product_zero {d k D M q : ℕ}
    [NeZero d] [NeZero k] [LinearOrder (HighWindowLabels d k)]
    (C : ModelConstants d) (hD : 3 ≤ D) (hq : 1 ≤ q)
    (hM : highCenterResolutionThreshold C ≤ (M : ℝ))
    (Cfr lam ℓ N μ : ℝ) (hCfr : 1 ≤ Cfr) (hℓ : 0 < ℓ) (hℓN : ℓ < N)
    (j : HighWindowLabels d k)
    (h : HistoryMarked (fun i j => j ∈ highNeighborLabels d k i)
      (HighUnionMark (SourceRowMark d D M q (C.densityLower + 1 / (M : ℝ))
        (C.densityUpper - 1 / (M : ℝ)) Cfr lam ℓ N μ))) (n : ℕ) (x : Fin n → Covariate d) :
    (∫ e, highUnionActivation (completeSourceRows C k D M q Cfr lam ℓ N μ) (highCenterMix C) e *
      ∏ i, highUnionSourceResetDensity C (completeSourceRows C k D M q Cfr lam ℓ N μ)
        j h e (x i) ∂highUnionLaw (completeSourceRows C k D M q Cfr lam ℓ N μ) (highCenterMix C)) = 0 := by
  let a := C.densityLower + 1 / (M : ℝ); let b := C.densityUpper - 1 / (M : ℝ)
  let R := completeSourceRows C k D M q Cfr lam ℓ N μ
  have G := completeSourceRows_guards C k D M q hD hq hM Cfr lam ℓ N μ hCfr hℓ hℓN
  obtain ⟨ha, hab⟩ := high_source_interval_numeric C (M : ℝ) hM
  have hpos := sourceRowMass_positive_actual d k D M q hD hq a b ha hab Cfr (by linarith) lam ℓ N μ hℓ hℓN
  let β₀ : HighFrameIndex d D := ⟨fun _ => 0, by simp⟩
  let r₀ : HighResponseMarkIndex (HighFrameIndex d D) q := ((β₀, β₀), (false, false), 0)
  let proj := sourceRowDensityProj d D M q a b Cfr lam ℓ N μ
  let lift := sourceRowDensityLift d D M q a b Cfr lam ℓ N μ r₀
  let Fobs (e : HighUnionMark (SourceRowMark d D M q a b Cfr lam ℓ N μ)) : ℝ :=
    ∏ i, highUnionSourceResetDensity C R j h e (x i)
  have hF : Measurable Fobs := Finset.measurable_fun_prod _ fun _ _ =>
    (highUnionSourceResetDensity_measurable C R G j h).comp (measurable_id.prodMk measurable_const)
  have hFb (e) : ‖Fobs e‖ ≤ C.densityUpper ^ n := by
    simpa only [Real.norm_eq_abs, Fobs] using finite_density_product_abs_bound
      (fun i => highUnionSourceResetDensity C R j h e (x i)) C.densityUpper
      (by linarith [C.one_lt_densityUpper]) fun i => highUnionSourceResetDensity_abs_le C R G j h e (x i)
  change (∫ e, highUnionActivation R (highCenterMix C) e * Fobs e ∂highUnionLaw R (highCenterMix C)) = 0
  rw [highUnionSource_bounded_action C R G hpos Fobs hF (C.densityUpper ^ n) hFb]
  have hrow (i) : (∫ e, R.rowActivation i e * Fobs (Sum.inl ⟨i, e⟩) ∂(R.rowLaw i)) = 0 := by
    let Hi (z : SourceRowDensityMark d D M q a b Cfr lam ℓ N μ i) : ℝ := Fobs (Sum.inl ⟨i, lift i z⟩)
    have hHi : Measurable Hi := hF.comp (measurable_inl.comp ((rowSigmaMk_measurable i).comp
      (sourceRowDensityLift_measurable d D M q a b Cfr lam ℓ N μ r₀ i)))
    have he (e) : Fobs (Sum.inl ⟨i, e⟩) = Hi (proj i e) :=
      Finset.prod_congr rfl fun l _ => by
        unfold highUnionSourceResetDensity highUnionSourceDensity
        change (highUnionSourceState C R _).1 (x l) = (highUnionSourceState C R _).1 (x l)
        rw [highUnionSourceState_append, highUnionSourceState_append]
        change (if x l ∈ highTorusPatch d k j then R.rowSlope j i e (x l) * _ + R.rowIntercept i e else _) =
          (if x l ∈ highTorusPatch d k j then R.rowSlope j i (lift i (proj i e)) (x l) * _ +
            R.rowIntercept i (lift i (proj i e)) else _)
        dsimp only [R, completeSourceRows, a, b]
        rw [sourceRow_density_projection_slope d k D M q a b Cfr lam ℓ N μ r₀ j i e (x l),
          sourceRow_density_projection_intercept d k D M q a b Cfr lam ℓ N μ r₀ i e]
    refine (integral_congr_ae <| Filter.Eventually.of_forall fun e => congrArg _ (he e)).trans ?_
    exact sourceRow_density_observable_zero d k D M q a b Cfr lam ℓ N μ hpos i Hi hHi (C.densityUpper ^ n) fun _ => hFb _
  simp only [hrow, Finset.sum_const_zero]

end CanonicalResponse

section OriginalResponse
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
attribute [local irreducible] highUnionSourceDensity highUnionSourceState historyMarkedAppend

theorem completeSource_original_response_exact_and_low_counts {d : ℕ} [NeZero d]
    (C : ModelConstants d) (Q : LowSmoothnessTernaryConstants C) :
    ∃ Cfr0 eta0 : ℝ, 1 ≤ Cfr0 ∧ 0 < eta0 ∧
      ∀ k D M q : ℕ, ∀ (_ : NeZero k), ∀ (_ : LinearOrder (HighWindowLabels d k)),
      4 ≤ k → 3 ≤ D → 1 ≤ q → highCenterResolutionThreshold C ≤ (M : ℝ) →
      ∀ Cfr lam ell N mu cf : ℝ, Cfr0 ≤ Cfr → 0 < ell → ell < N → 0 ≤ cf →
      cf * (k : ℝ) ^ (-C.smoothness) ≤ eta0 →
      ∀ V : ℝ, |V - Q.v| ≤ Q.ρ → ∀ j : HighWindowLabels d k,
      ∀ h : HistoryMarked (fun i j => j ∈ highNeighborLabels d k i)
        (HighUnionMark (SourceRowMark d D M q (C.densityLower + 1 / (M : ℝ))
          (C.densityUpper - 1 / (M : ℝ)) Cfr lam ell N mu)),
      ∀ n : ℕ, ∀ x : Fin n → Covariate d, (∀ i, x i ∈ highTorusPatch d k j) →
      ∀ y : Fin n → Fin 3,
      let R := completeSourceRows C k D M q Cfr lam ell N mu
      let eta := cf * (k : ℝ) ^ (-C.smoothness)
      let c := (highUnionSourceState C R h).2
      highUnionSourceMarkedNumerator C R n Q.a V eta j h x y =
        completeSourceRawNumerator (C.densityLower + 1 / (M : ℝ)) (C.densityUpper - 1 / (M : ℝ))
          lam ell N mu D M q Cfr Q.a V eta (fun i => highLocalCoordinates d k j (x i))
          (fun i => highUnionSourceDensity C R h (x i))
          (fun i => highLocalFieldWithout d k D eta c j (x i))
          (fun i => highPeriodicTensor d k j (x i)) (c j) y ∧
        (n ≤ 1 → highUnionSourceMarkedNumerator C R n Q.a V eta j h x y = 0) := by
  obtain ⟨Cfr0, eta0, hfr0, heta0, hguards⟩ := completeSource_original_local_guards C Q
  refine ⟨Cfr0, eta0, hfr0, heta0,
    fun k D M q hk0 horder hk hD hq hM Cfr lam ell N mu cf hfr hell hellN hcf heta V hV j h n x hx y => ?_⟩
  letI := hk0; letI := horder
  let R := completeSourceRows C k D M q Cfr lam ell N mu
  let eta := cf * (k : ℝ) ^ (-C.smoothness)
  let c := (highUnionSourceState C R h).2
  let U := fun i : Fin n => highLocalCoordinates d k j (x i)
  let p := fun i : Fin n => highUnionSourceDensity C R h (x i)
  let g := fun i : Fin n => highLocalFieldWithout d k D eta c j (x i)
  let w := fun i : Fin n => highPeriodicTensor d k j (x i)
  have hfr1 := hfr0.trans hfr
  have G := completeSourceRows_guards C k D M q hD hq hM Cfr lam ell N mu hfr1 hell hellN
  have H := hguards k D M q hk0 horder hk hD hq hM Cfr lam ell N mu cf hfr hell hellN hcf heta h
  have hmass (v : HighFrameIndex d D → ℝ) (hv : ∑ γ, |v γ| ≤ Cfr⁻¹) (i : Fin n) (b : Fin 3) :
      0 ≤ ternaryMass Q.a
        (coefficientRegression eta g w (fun u : Fin n => highLocalFrameFeature k j (x u)) v i) V b :=
    Q.c_pos.le.trans ((Q.legal _ V (H.regression_abs j v hv (x i)) hV).2.2.1 b)
  have he := completeSourceRawNumerator_eq_canonical C hD hq hM Cfr lam ell N mu
    hfr1 hell hellN j h x hx Q.a V eta Q.a_pos.ne' g w hmass y
  change highUnionSourceMarkedNumerator C R n Q.a V eta j h x y =
    completeSourceRawNumerator _ _ lam ell N mu D M q Cfr Q.a V eta U p g w (c j) y at he
  refine ⟨he, fun hn => ?_⟩
  rw [he]
  obtain ⟨ha, hab⟩ := high_source_interval_numeric C (M : ℝ) hM
  have hp (i : Fin n) : p i ∈ Icc (C.densityLower + 1 / (M : ℝ)) (C.densityUpper - 1 / (M : ℝ)) :=
    highUnionSourceDensity_interval C R G h (x i)
  have hU (i : Fin n) (r : Fin d) : |U i r| ≤ 2 :=
    (highLocalCoordinates_abs_le_one d k j (x i) r).trans (by norm_num)
  rcases (show n = 0 ∨ n = 1 by omega) with rfl | rfl
  · exact completeSourceRawNumerator_count_zero _ _ lam ell N mu ha hab D M q (by omega)
      Cfr Q.a V eta U p g w (c j) y
  · exact completeSourceRawNumerator_count_one _ _ lam ell N mu ha hab D M q (by omega) hq
      Cfr Q.a V eta (by linarith) U hU p g w hp (c j) y

end OriginalResponse

-- 5. Frame design energy, window factorial & Fisher bounds
--    (`HighFrameDesignEnergy`, `HighWindowFactorialEnergy`, `HighUnionFisher`, `HighUnionRawFisher`)

section FrameDesignEnergy
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000

theorem highWindowLabels_card {d k : ℕ} [NeZero k] :
    Fintype.card (HighWindowLabels d k) = k ^ d := by
  simp only [HighWindowLabels, Fintype.card_fun, Fintype.card_fin, ZMod.card]

theorem high_design_factorial_parameter {d k n : ℕ} [NeZero k]
    (Csharp mu : ℝ) (hmu : mu = (n : ℝ) / (k : ℝ) ^ d) :
    (n : ℝ) * Csharp * (2 / (k : ℝ)) ^ d = (Csharp * (2 : ℝ) ^ d) * mu := by
  rw [hmu, div_pow]; ring

def highFrameFullMarkedScore {E : Type*} [MeasurableSpace E] (d k D n : ℕ) [NeZero k]
    (π : HighWindowLabels d k → Measure E) (activation : HighWindowLabels d k → E → ℝ)
    (a V η : ℝ) (p : Covariate d → ℝ)
    (pReset : HighWindowLabels d k → E → Covariate d → ℝ)
    (cReset : HighWindowLabels d k → E → HighFrameIndex d D → ℝ)
    (c : HighWindowLabels d k → HighFrameIndex d D → ℝ)
    (z : (Fin n → Covariate d) × (Fin n → Fin 3)) : ℝ :=
  ∑ j, highFrameMarkedScore d k D n π activation a V η (p ∘ z.1)
    (fun j e => pReset j e ∘ z.1) cReset c z.1 j z.2

theorem high_frame_complete_design_spatial_series {E : Type*} [MeasurableSpace E] (d k D n : ℕ) [NeZero k] (hk : 4 ≤ k)
    (π : HighWindowLabels d k → Measure E) [∀ j, SFinite (π j)]
    (activation : HighWindowLabels d k → E → ℝ)
    (hAct : ∀ j, Measurable (activation j)) (hActI : ∀ j, Integrable (activation j) (π j))
    (a V η pMinus pPlus cMass : ℝ) (ha : a ≠ 0) (hpMinus : 0 < pMinus)
    (hpPlus : 0 ≤ pPlus) (hcMass : 0 < cMass)
    (p : Covariate d → ℝ) (hp : Measurable p) (hraw : ∀ x, pMinus ≤ p x ∧ p x ≤ pPlus)
    (pReset : HighWindowLabels d k → E → Covariate d → ℝ)
    (hReset : ∀ j, Measurable (Function.uncurry (pReset j)))
    (hBound : ∀ j e x, |pReset j e x| ≤ pPlus)
    (hOutside : ∀ j e x, x ∉ highTorusPatch d k j → pReset j e x = p x)
    (cReset : HighWindowLabels d k → E → HighFrameIndex d D → ℝ)
    (hcReset : ∀ j γ, Measurable fun e => cReset j e γ)
    (c : HighWindowLabels d k → HighFrameIndex d D → ℝ)
    (hq : ∀ x y, cMass ≤ ternaryMass a (highFrameField d k η (fun l => highFramePolynomial (c l)) x) V y)
    (hqReset : ∀ j e x y, 0 ≤ highMarkedResponseMass a V η
      (highLocalFieldWithout d k D η c j) (highPeriodicTensor d k j)
      (fun x => highLocalFrameFeature k j x) (cReset j e) x y)
    (hDensity : ∀ j (x : Fin n → Covariate d), (∫ e, activation j e * ∏ i, pReset j e (x i) ∂π j) = 0)
    (H : HighWindowLabels d k → (r : ℕ) → (Fin r → Covariate d) → ℝ)
    (hH : ∀ j r, Integrable (H j r) (Measure.pi fun _ : Fin r => volume.restrict (spatialPatchBox d)))
    (hH0 : ∀ j r u, 0 ≤ H j r u)
    (hdom : ∀ j r x, (∀ i, x i ∈ highTorusPatch d k j) →
      selectedRawSquareEnergy (highMarkedSampleNumerator r (π j) (activation j) a V η p (pReset j)
        (cReset j) (highLocalFieldWithout d k D η c j) (highPeriodicTensor d k j)
          (fun x => highLocalFrameFeature k j x) (c j)) x ≤ H j r (highPatchProductChart d k j x)) :
    let F := highFrameField d k η fun l => highFramePolynomial (c l)
    let hF : Measurable F := (highFrameField_contDiff d k η _).continuous.measurable
    let S := highFrameFullMarkedScore d k D n π activation a V η p pReset cReset c
    Integrable (fun z => S z ^ 2) ((Measure.pi fun _ : Fin n => highNormalizedDesignLaw p).compProd
      (responseSampleIndexKernel n a V F hF)) ∧
    (∫ z, S z ^ 2 ∂(Measure.pi fun _ : Fin n => highNormalizedDesignLaw p).compProd
      (responseSampleIndexKernel n a V F hF)) ≤
      (3 ^ d : ℕ) * ∑ j : HighWindowLabels d k, ∑ r ∈ Finset.range (n + 1),
        ((n : ℝ) * highFixedScoreDenominator pMinus cMass * (2 / (k : ℝ)) ^ d) ^ r /
          (r.factorial : ℝ) * ∫ u, H j r u
            ∂Measure.pi fun _ : Fin r => volume.restrict (spatialPatchBox d) := by
  let F := highFrameField d k η fun l => highFramePolynomial (c l)
  have hF : Measurable F := (highFrameField_contDiff d k η _).continuous.measurable
  let S := highFrameFullMarkedScore d k D n π activation a V η p pReset cReset c
  let μ := Measure.pi fun _ : Fin n => highNormalizedDesignLaw p
  let _ := high_normalized_design_probability p hp pMinus pPlus hpMinus (Filter.Eventually.of_forall hraw)
  let Eglobal := finiteResponseSquareEnergy n a V F S
  let Elocal (j : HighWindowLabels d k) := highMarkedSampleConditionalEnergy n (π j) (activation j)
    a V η p (pReset j) (cReset j) (highLocalFieldWithout d k D η c j)
      (highPeriodicTensor d k j) (fun x => highLocalFrameFeature k j x) (c j)
  have hqLocal (j : HighWindowLabels d k) (x : Covariate d) (y : Fin 3) :
      cMass ≤ highMarkedResponseMass a V η (highLocalFieldWithout d k D η c j)
        (highPeriodicTensor d k j) (fun x => highLocalFrameFeature k j x) (c j) x y := by
    unfold highMarkedResponseMass; rw [← highFrameField_local_decomposition d k D hk η c j x]; exact hq x y
  have hlocal (j : HighWindowLabels d k) := high_marked_original_design_spatial_series hk j n
    (π j) (activation j) (hAct j) a V η ha pMinus pPlus cMass hpMinus hcMass p hp hraw
    (pReset j) (hReset j) (cReset j) (hcReset j)
    (highLocalFieldWithout d k D η c j) (highPeriodicTensor d k j)
    (highLocalFieldWithout_continuous d k D η c j).measurable
    (highPeriodicTensor_contDiff d k j).continuous.measurable
    (fun x => highLocalFrameFeature k j x) (highLocalFrameFeature_measurable k j) (c j)
    (hqLocal j) (fun x hx => by by_contra h; exact hx (highPeriodicTensor_supported_patch d k j h))
    (hOutside j) (H j) (hH j) (hH0 j) (hdom j)
  have hSm : Measurable S := by
    refine measurable_from_prod_countable_left fun y => Finset.measurable_sum _ fun j _ => ?_
    let g := highLocalFieldWithout d k D η c j
    let w := highPeriodicTensor d k j
    let φ (x : Covariate d) := highLocalFrameFeature (D := D) k j x
    have hg : Measurable g := (highLocalFieldWithout_continuous d k D η c j).measurable
    have hw : Measurable w := (highPeriodicTensor_contDiff d k j).continuous.measurable
    have hφ := highLocalFrameFeature_measurable (D := D) k j
    have hR := highMarkedSampleNumerator_measurable n (π j) (activation j) (hAct j)
      a V η p hp (pReset j) (hReset j) (cReset j) (hcReset j) g w hg hw φ hφ (c j) y
    have hL : Measurable fun x : Fin n → Covariate d => selectedRawLikelihood p
        (highMarkedResponseMass a V η g w φ (c j)) x y :=
      (Finset.measurable_prod _ fun i _ => hp.comp (measurable_pi_apply i)).mul
        (Finset.measurable_prod _ fun i _ =>
          (highMarkedResponseMass_measurable a V η g w hg hw φ hφ (c j) (y i)).comp (measurable_pi_apply i))
    change Measurable fun x : Fin n → Covariate d =>
      highMarkedLocalScore (π j) (activation j) a V η (p ∘ x) (fun e => pReset j e ∘ x)
        (cReset j) (g ∘ x) (w ∘ x) (φ ∘ x) (c j) y
    simp_rw [high_marked_sample_score_eq_ratio]; exact hR.div hL
  have hEm : Measurable Eglobal := Finset.measurable_sum _ fun y _ =>
    (Finset.measurable_prod _ fun i _ => ternaryMass_measurable_comp a V _ (hF.comp (measurable_pi_apply i)) (y i)).mul
      ((hSm.comp (measurable_id.prodMk measurable_const)).pow_const 2)
  have hEn (x : Fin n → Covariate d) : 0 ≤ Eglobal x :=
    Finset.sum_nonneg fun _ _ => mul_nonneg (Finset.prod_nonneg fun i _ => hcMass.le.trans (hq (x i) _)) (sq_nonneg _)
  have hpoint (x : Fin n → Covariate d) : Eglobal x ≤ (3 ^ d : ℕ) * ∑ j, Elocal j x := by
    have he := highFrameMarkedScore_energy_bound d k D n hk π activation hActI a V η pPlus ha hpPlus
      (p ∘ x) (fun j e => pReset j e ∘ x)
      (fun j _ => (hReset j).comp (measurable_id.prodMk measurable_const))
      (fun j e i => hBound j e (x i)) cReset hcReset c x
      (fun i => (hpMinus.trans_le (hraw (x i)).1).ne')
      (fun i y => hcMass.trans_le (hq (x i) y))
      (fun j e i y => hqReset j e (x i) y) fun j => hDensity j x
    rw [ternary_index_product_integral] at he
    have hloc (j : HighWindowLabels d k) :
        (∫ y, highFrameMarkedScore d k D n π activation a V η (p ∘ x)
          (fun j e => pReset j e ∘ x) cReset c x j y ^ 2
          ∂Measure.pi fun i => ternaryIndexMeasure a (F (x i)) V ha
            fun y => (hcMass.trans_le (hq (x i) y)).le) = Elocal j x := by
      have hreg := highFrameField_coefficientRegression d k D n hk η c j x
      change coefficientRegression η (highLocalFieldWithout d k D η c j ∘ x)
        (highPeriodicTensor d k j ∘ x) ((fun x => highLocalFrameFeature k j x) ∘ x) (c j) = fun i => F (x i) at hreg
      have hs := high_marked_sample_energy_integral n (π j) (activation j) a V η ha p (pReset j)
        (cReset j) (highLocalFieldWithout d k D η c j) (highPeriodicTensor d k j)
          (fun x => highLocalFrameFeature k j x) (c j) x fun _ y => hcMass.trans_le (hqLocal j _ y)
      rw [ternary_index_product_integral, hreg] at hs
      rwa [ternary_index_product_integral]
    dsimp only [F] at hloc; simp_rw [hloc] at he; exact he
  have hu : Integrable (fun x => (3 ^ d : ℕ) * ∑ j, Elocal j x) μ :=
    (integrable_finsetSum _ fun j _ => (hlocal j).1).const_mul _
  have hEI : Integrable Eglobal μ := hu.mono' hEm.aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => by rw [Real.norm_eq_abs, abs_of_nonneg (hEn x)]; exact hpoint x)
  have hs := response_sample_square_integrable_integral n μ a V ha F hF
    (fun x y => hcMass.le.trans (hq x y)) S hSm hEI
  refine ⟨hs.1, ?_⟩
  rw [hs.2]
  calc _ ≤ ∫ x, (3 ^ d : ℕ) * ∑ j, Elocal j x ∂μ := integral_mono hEI hu hpoint
    _ = (3 ^ d : ℕ) * ∑ j, ∫ x, Elocal j x ∂μ := by rw [integral_const_mul, integral_finsetSum _ fun j _ => (hlocal j).1]
    _ ≤ _ := mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun j _ => (hlocal j).2) (Nat.cast_nonneg _)

end FrameDesignEnergy

section RawFisherAndPath
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency true
attribute [local irreducible] highUnionSourceDensity highUnionSourceRegression highUnionSourceState
  historyMarkedAppend highHistoryLikelihoodScore highSampleIndexKernel highRawSampleLikelihood massPowerNormalizer

def highSourceSpatialSeries (d k n : ℕ) [NeZero k] (pMinus cMass : ℝ)
    (H : HighWindowLabels d k → (r : ℕ) → (Fin r → Covariate d) → ℝ) : ℝ :=
  (3 ^ d : ℕ) * ∑ j : HighWindowLabels d k, ∑ r ∈ Finset.range (n + 1),
    ((n : ℝ) * highFixedScoreDenominator pMinus cMass * (2 / (k : ℝ)) ^ d) ^ r /
      (r.factorial : ℝ) * ∫ u, H j r u
        ∂Measure.pi fun _ : Fin r => volume.restrict (spatialPatchBox d)

theorem highUnionSource_raw_fisher_bound {d k D : ℕ} {I : Type*} [Fintype I] {E : I → Type*}
    [∀ i, MeasurableSpace (E i)] [∀ i, StandardBorelSpace (E i)]
    [NeZero k] [LinearOrder (HighWindowLabels d k)]
    (C : ModelConstants d) (R : HighUnionRowData d k D I E)
    {M Cfr : ℝ} (G : HighUnionSourceGuards C M Cfr R) (hpos : ∀ i, 0 < R.rowMass i)
    (ν : Measure (HistoryMarked (fun i j => j ∈ highNeighborLabels d k i) (HighUnionMark E)))
    [IsProbabilityMeasure ν] (n : ℕ) (hk : 4 ≤ k)
    (a V η cMass : ℝ) (ha : a ≠ 0) (hcMass : 0 < cMass)
    (hq : ∀ h x y, cMass ≤ ternaryMass a (highUnionSourceRegression C R η h x) V y)
    (hDensity : ∀ j h (x : Fin n → Covariate d),
      (∫ e, highUnionActivation R (highCenterMix C) e *
        ∏ i, highUnionSourceResetDensity C R j h e (x i) ∂highUnionLaw R (highCenterMix C)) = 0)
    (H : HistoryMarked (fun i j => j ∈ highNeighborLabels d k i) (HighUnionMark E) →
      HighWindowLabels d k → (r : ℕ) → (Fin r → Covariate d) → ℝ)
    (hH : ∀ h j r, Integrable (H h j r) (Measure.pi fun _ : Fin r => volume.restrict (spatialPatchBox d)))
    (hH0 : ∀ h j r u, 0 ≤ H h j r u)
    (hdom : ∀ h j r x, (∀ i, x i ∈ highTorusPatch d k j) →
      selectedRawSquareEnergy (highUnionSourceRawNumerator C R r a V η h j) x ≤
        H h j r (highPatchProductChart d k j x))
    (B : ℝ) (hB : 0 ≤ B)
    (hbudget : ∀ h, highSourceSpatialSeries d k n C.densityLower cMass (H h) ≤ B) :
    let D_der := highHistoryLikelihoodDerivative (fun i j => j ∈ highNeighborLabels d k i)
      (fun {_ _} h => highNeighborLabels_symmetric d k _ _ h)
      (highUnionLaw R (highCenterMix C)) (highUnionActivation R (highCenterMix C))
      n a V η (highUnionSourceDensity C R) (highUnionSourceRegression C R η)
    let L := fun h => highRawSampleLikelihood n a V
      (highUnionSourceDensity C R h) (highUnionSourceRegression C R η h)
    let m := fun h => highRawDensityMass (highUnionSourceDensity C R h)
    Integrable (fun z => D_der z.1 z.2 ^ 2 / L z.1 z.2) (ν.prod (highSampleReference d n)) ∧
    (massPowerNormalizer ν m n)⁻¹ *
      (∫ z, D_der z.1 z.2 ^ 2 / L z.1 z.2 ∂ν.prod (highSampleReference d n)) ≤ B := by
  letI : StandardBorelSpace (HighUnionMark E) := highUnionMark_standardBorel
  letI := highUnionSourceLaw_probability C R G
  let π := highUnionLaw R (highCenterMix C)
  let act := highUnionActivation R (highCenterMix C)
  let p := highUnionSourceDensity C R
  let F := highUnionSourceRegression C R η
  have hp : Measurable (Function.uncurry p) := highUnionSourceDensity_joint_measurable C R G
  have hF : Measurable (Function.uncurry F) := highUnionSourceRegression_joint_measurable C R G η
  have ham := highUnionActivation_measurable R G.activation_measurable (highCenterMix C)
  have hai : Integrable act π := Integrable.of_bound ham.aestronglyMeasurable
    (highRowTotalMass R.rowMass / highCenterMix C)
    (Filter.Eventually.of_forall fun e => by simpa only [Real.norm_eq_abs] using highUnionSourceActivation_bound C R G hpos e)
  let D_der := highHistoryLikelihoodDerivative (fun i j => j ∈ highNeighborLabels d k i)
    (fun {_ _} h => highNeighborLabels_symmetric d k _ _ h) π act n a V η p F
  have hDm : Measurable (Function.uncurry D_der) := highHistoryLikelihoodDerivative_measurable
    (fun i j => j ∈ highNeighborLabels d k i)
    (fun {_ _} h => highNeighborLabels_symmetric d k _ _ h) π act ham n a V η p F hp hF
  have hs_sample (h) :
      let S := highHistoryLikelihoodScore (fun i j => j ∈ highNeighborLabels d k i)
        (fun {_ _} h => highNeighborLabels_symmetric d k _ _ h) π act n a V η p F h
      Integrable (fun z => S z ^ 2) (highSampleIndexKernel n a V p F hp hF h) ∧
      (∫ z, S z ^ 2 ∂highSampleIndexKernel n a V p F hp hF h) ≤
        highSourceSpatialSeries d k n C.densityLower cMass (H h) := by
    let c := (highUnionSourceState C R h).2
    let Fh := highFrameField d k η fun l => highFramePolynomial (c l)
    have hFh_eq : F h = Fh := funext fun _ => by simp only [F, Fh, c]; unfold highUnionSourceRegression; rfl
    have hFh : Measurable Fh := (highFrameField_contDiff d k η _).continuous.measurable
    have hreg (j : HighWindowLabels d k) (e : HighUnionMark E) (x : Covariate d) (y : Fin 3) :
        highMarkedResponseMass a V η (highLocalFieldWithout d k D η c j)
          (highPeriodicTensor d k j) (fun x => highLocalFrameFeature k j x)
          (highUnionSourceResetCoefficient C R j h e) x y =
        ternaryMass a (F (historyMarkedAppend
          (fun i j => j ∈ highNeighborLabels d k i)
          (fun {_ _} h => highNeighborLabels_symmetric d k _ _ h) j (h, e)) x) V y := by
      unfold highMarkedResponseMass
      exact congrArg (fun t : ℝ => ternaryMass a t V y)
        (congrFun (highUnionSourceRegression_append C R 1 hk η j h e fun _ => x) 0)
    have hs := high_frame_complete_design_spatial_series d k D n hk
      (fun _ => π) (fun _ => act) (fun _ => ham) (fun _ => hai)
      a V η C.densityLower C.densityUpper cMass ha C.densityLower_pos
      (by linarith [C.one_lt_densityUpper]) hcMass (p h) hp.of_uncurry_left
      (highUnionSourceDensity_coarse_interval C R G h)
      (fun j => highUnionSourceResetDensity C R j h)
      (fun j => highUnionSourceResetDensity_measurable C R G j h)
      (fun j => highUnionSourceResetDensity_abs_le C R G j h)
      (fun j => highUnionSourceResetDensity_outside C R j h)
      (fun j => highUnionSourceResetCoefficient C R j h)
      (fun j => highUnionSourceResetCoefficient_measurable C R G j h) c
      (fun x y => by change cMass ≤ ternaryMass a (Fh x) V y; rw [← hFh_eq]; exact hq h x y)
      (fun j e x y => by rw [hreg]; exact hcMass.le.trans (hq _ x y))
      (fun j x => hDensity j h x) (H h) (hH h) (hH0 h) (hdom h)
    have he : highSampleIndexKernel n a V p F hp hF h =
        (Measure.pi fun _ : Fin n => highNormalizedDesignLaw (p h)).compProd
          (responseSampleIndexKernel n a V Fh hFh) := by
      have hd := high_normalized_design_probability (p h) hp.of_uncurry_left
        C.densityLower C.densityUpper C.densityLower_pos
        (Filter.Eventually.of_forall (highUnionSourceDensity_coarse_interval C R G h))
      have hm_pos : 0 < highRawDensityMass (p h) := C.densityLower_pos.trans_le
        (highRawDensityMass_mem_Icc (p h) hp.of_uncurry_left
          C.densityLower C.densityUpper C.densityLower_pos
          (Filter.Eventually.of_forall (highUnionSourceDensity_coarse_interval C R G h))).1
      rw [highSampleIndexKernel_apply]
      simpa only [hFh_eq, highSampleReference, highNormalizedDesignLaw] using
        (highSample_index_density n (p h) (F h) hp.of_uncurry_left hF.of_uncurry_left a V hd
          (fun x => C.densityLower_pos.le.trans (highUnionSourceDensity_coarse_interval C R G h x).1)
          hm_pos fun x y => hcMass.le.trans (hq h x y)).symm
    have hS : highHistoryLikelihoodScore (fun i j => j ∈ highNeighborLabels d k i)
        (fun {_ _} h => highNeighborLabels_symmetric d k _ _ h) π act n a V η p F h =
        highFrameFullMarkedScore d k D n (fun _ => π) (fun _ => act) a V η (p h)
          (fun j => highUnionSourceResetDensity C R j h)
          (fun j => highUnionSourceResetCoefficient C R j h) c :=
      funext fun ⟨x, y⟩ => highUnionSourceLikelihoodScore_eq_sum C R n hk a V η h x y
    dsimp only; rw [hS, he]; exact hs
  have hj := high_raw_joint_fisher_integrable_bound ν n a V p F hp hF
    C.densityLower C.densityUpper C.densityLower_pos
    (highUnionSourceDensity_coarse_interval C R G) (fun h x y => hcMass.trans_le (hq h x y))
    D_der hDm B hB
    (fun h => by simpa only [highHistoryLikelihoodScore] using (hs_sample h).1)
    fun h => by simpa only [highHistoryLikelihoodScore] using (hs_sample h).2.trans (hbudget h)
  have hG : 0 < massPowerNormalizer ν (fun h => highRawDensityMass (p h)) n :=
    massPowerNormalizer_pos ν _ (highRawDensityMass_joint_measurable p hp) n
      C.densityLower C.densityUpper C.densityLower_pos
      fun h => highRawDensityMass_mem_Icc (p h) hp.of_uncurry_left
        C.densityLower C.densityUpper C.densityLower_pos
        (Filter.Eventually.of_forall (highUnionSourceDensity_coarse_interval C R G h))
  refine ⟨hj.1, ?_⟩
  calc _ ≤ (massPowerNormalizer ν (fun h => highRawDensityMass (p h)) n)⁻¹ *
          (massPowerNormalizer ν (fun h => highRawDensityMass (p h)) n * B) :=
        mul_le_mul_of_nonneg_left hj.2 (inv_nonneg.mpr hG.le)
    _ = B := by rw [← mul_assoc, inv_mul_cancel₀ hG.ne', one_mul]

def highNormalizedParameterPath {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    (T : ℝ) (hT : 0 ≤ T) (a v η : ℝ) (ha : a ≠ 0)
    (p F : Ω → Covariate d → ℝ) (hF : Measurable (Function.uncurry F))
    (hq : ∀ t ∈ Icc 0 T, ∀ ω x y, 0 ≤ ternaryMass a (F ω x) (v - η ^ 2 * t) y)
    (t : ℝ) (ω : Ω) : RegressionParameter d :=
  if ht : t ∈ Icc 0 T then
    normalizedDensityTernaryParameter (p ω) (F ω) a (v - η ^ 2 * t) hF.of_uncurry_left ha (hq t ht ω)
  else
    normalizedDensityTernaryParameter (p ω) (F ω) a v hF.of_uncurry_left ha
      fun x y => by simpa using hq 0 ⟨le_rfl, hT⟩ ω x y

theorem highNormalizedParameterPath_apply {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    (T : ℝ) (hT : 0 ≤ T) (a v η : ℝ) (ha : a ≠ 0)
    (p F : Ω → Covariate d → ℝ) (hF : Measurable (Function.uncurry F))
    (hq : ∀ t ∈ Icc 0 T, ∀ ω x y, 0 ≤ ternaryMass a (F ω x) (v - η ^ 2 * t) y)
    (t : ℝ) (ht : t ∈ Icc 0 T) (ω : Ω) :
    highNormalizedParameterPath T hT a v η ha p F hF hq t ω =
      normalizedDensityTernaryParameter (p ω) (F ω) a (v - η ^ 2 * t) hF.of_uncurry_left ha (hq t ht ω) := by
  unfold highNormalizedParameterPath; rw [dif_pos ht]

theorem intervalIntegral_sqrt_energy_le (f : ℝ → ℝ) (T M : ℝ) (hT : 0 ≤ T)
    (hi : IntervalIntegrable (fun t => Real.sqrt (f t)) volume 0 T)
    (hbound : ∀ t ∈ Icc 0 T, f t ≤ M) :
    (∫ t in (0 : ℝ)..T, Real.sqrt (f t)) ≤ T * Real.sqrt M := by
  simpa only [intervalIntegral.integral_const, sub_zero, smul_eq_mul] using
    intervalIntegral.integral_mono_on hT hi (intervalIntegrable_const (c := Real.sqrt M))
      fun t ht => Real.sqrt_le_sqrt (hbound t ht)

end RawFisherAndPath

-- 6. Time-marginal measurability, score kernel & prior path risk
--    (`HighTimeMarginal`, `HighScoreTimeKernel`, `ScoreEnergyIntegral`, `HighPriorRisk`)

section TimeMarginal
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
variable {J : Type*} [Fintype J] [LinearOrder J]

lemma historyMarkedPrior_integral_joint_measurable {E Z : Type*}
    [MeasurableSpace E] [MeasurableSpace Z]
    (dependent : J → J → Prop) (Δ : ℕ) (π : Measure E)
    [SFinite (historyMarkedReference dependent Δ π)]
    (activation : E → ℝ) (ham : Measurable activation)
    (G : ℝ × (HistoryMarked dependent E × Z) → ℝ) (hG : Measurable G) :
    Measurable fun z : ℝ × Z =>
      ∫ ω, G (z.1, (ω, z.2)) ∂historyMarkedPrior dependent Δ z.1 π activation := by
  let f : (ℝ × Z) × HistoryMarked dependent E → ℝ := fun z =>
    (ENNReal.ofReal (historyMarkedDensity dependent (historyReferenceRho Δ) z.1.1 activation z.2)).toReal *
      G (z.1.1, (z.2, z.1.2))
  have hm : Measurable f :=
    (((historyMarkedDensity_joint_measurable dependent (historyReferenceRho Δ) activation ham).comp
      ((measurable_fst.comp measurable_fst).prodMk measurable_snd)).ennreal_ofReal.ennreal_toReal).mul
      (hG.comp ((measurable_fst.comp measurable_fst).prodMk
        (measurable_snd.prodMk (measurable_snd.comp measurable_fst))))
  rw [show (fun z : ℝ × Z => ∫ ω, G (z.1, (ω, z.2)) ∂historyMarkedPrior dependent Δ z.1 π activation) =
    fun z => ∫ ω, f (z, ω) ∂historyMarkedReference dependent Δ π from funext fun z => by
      rw [historyMarkedPrior_eq_withDensity dependent Δ z.1 π activation ham,
        integral_withDensity_eq_integral_toReal_smul
          (historyMarkedDensity_measurable dependent _ z.1 activation ham).ennreal_ofReal
          (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]; rfl]
  exact hm.stronglyMeasurable.integral_prod_right'.measurable

lemma highMarginalRawLikelihood_time_measurable {E : Type*} [MeasurableSpace E] {d : ℕ}
    (dependent : J → J → Prop) (Δ : ℕ) (π : Measure E)
    [SFinite (historyMarkedReference dependent Δ π)]
    (activation : E → ℝ) (ham : Measurable activation) (n : ℕ) (a v η : ℝ)
    (p F : HistoryMarked dependent E → Covariate d → ℝ)
    (hp : Measurable (Function.uncurry p)) (hF : Measurable (Function.uncurry F)) :
    Measurable fun z : ℝ × ((Fin n → Covariate d) × (Fin n → Fin 3)) =>
      highMarginalRawLikelihood (historyMarkedPrior dependent Δ z.1 π activation) n a (v - η ^ 2 * z.1) p F z.2 :=
  historyMarkedPrior_integral_joint_measurable dependent Δ π activation ham _
    (highRawSampleLikelihood_time_measurable n a v η p F hp hF)

lemma highMarginalIndexScore_time_measurable {E : Type*} [MeasurableSpace E]
    [StandardBorelSpace E] {d : ℕ}
    (dependent : J → J → Prop) (hsymm : ∀ ⦃i j⦄, dependent i j → dependent j i)
    (Δ : ℕ) (π : Measure E) [SFinite π] [SFinite (historyMarkedReference dependent Δ π)]
    (activation : E → ℝ) (ham : Measurable activation) (n : ℕ) (a v η : ℝ)
    (p F : HistoryMarked dependent E → Covariate d → ℝ)
    (hp : Measurable (Function.uncurry p)) (hF : Measurable (Function.uncurry F)) :
    Measurable fun z : ℝ × ((Fin n → Covariate d) × (Fin n → Fin 3)) =>
      highMarginalIndexScore dependent hsymm (historyMarkedPrior dependent Δ z.1 π activation)
        π activation n a (v - η ^ 2 * z.1) η p F z.2 :=
  (historyMarkedPrior_integral_joint_measurable dependent Δ π activation ham _
    (highHistoryLikelihoodDerivative_time_measurable dependent hsymm π activation ham n a v η p F hp hF)).div
    (highMarginalRawLikelihood_time_measurable dependent Δ π activation ham n a v η p F hp hF)

end TimeMarginal

section TimeScoreKernel
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency true
variable {J : Type*} [Fintype J] [LinearOrder J]

section KernelMeasurable
attribute [local irreducible] highMarginalIndexScore highMarginalRawLikelihood
  historyMarkedPrior highRawDensityMass massPowerNormalizer

lemma highMarginalRealScore_time_measurable {E : Type*} [MeasurableSpace E]
    [StandardBorelSpace E] {d : ℕ}
    (dependent : J → J → Prop) (hsymm : ∀ ⦃i j⦄, dependent i j → dependent j i)
    (Δ : ℕ) (π : Measure E) [SFinite π] [SFinite (historyMarkedReference dependent Δ π)]
    (activation : E → ℝ) (ham : Measurable activation) (n : ℕ) (a v η : ℝ)
    (p F : HistoryMarked dependent E → Covariate d → ℝ)
    (hp : Measurable (Function.uncurry p)) (hF : Measurable (Function.uncurry F)) :
    Measurable fun z : ℝ × (Fin n → Observation d) =>
      highMarginalRealScore dependent hsymm (historyMarkedPrior dependent Δ z.1 π activation)
        π activation n a (v - η ^ 2 * z.1) η p F z.2 := by
  unfold highMarginalRealScore
  change Measurable ((fun z : ℝ × ((Fin n → Covariate d) × (Fin n → Fin 3)) =>
    highMarginalIndexScore dependent hsymm (historyMarkedPrior dependent Δ z.1 π activation)
      π activation n a (v - η ^ 2 * z.1) η p F z.2) ∘
    fun z : ℝ × (Fin n → Observation d) => (z.1, decodeDesignResponse a z.2))
  exact (highMarginalIndexScore_time_measurable dependent hsymm Δ π activation ham n a v η p F hp hF).comp
    (show Measurable fun z : ℝ × (Fin n → Observation d) => (z.1, decodeDesignResponse a z.2) from
      measurable_fst.prodMk ((decodeDesignResponse_measurable a).comp measurable_snd))

lemma highMassPowerNormalizer_time_measurable {E : Type*} [MeasurableSpace E] {d : ℕ}
    (dependent : J → J → Prop) (Δ : ℕ) (π : Measure E)
    [SFinite (historyMarkedReference dependent Δ π)]
    (activation : E → ℝ) (ham : Measurable activation) (n : ℕ)
    (p : HistoryMarked dependent E → Covariate d → ℝ) (hp : Measurable (Function.uncurry p)) :
    Measurable fun t => massPowerNormalizer (historyMarkedPrior dependent Δ t π activation)
      (fun ω => highRawDensityMass (p ω)) n := by
  unfold massPowerNormalizer
  have hG : Measurable fun z : ℝ × (HistoryMarked dependent E × Unit) => highRawDensityMass (p z.2.1) ^ n :=
    ((highRawDensityMass_joint_measurable p hp).pow_const n).comp (measurable_fst.comp measurable_snd)
  exact (historyMarkedPrior_integral_joint_measurable dependent Δ π activation ham _ hG).comp
    (show Measurable fun t : ℝ => (t, ()) from measurable_id.prodMk measurable_const)

end KernelMeasurable

def highHistoryIndexTimeKernel {E : Type*} [MeasurableSpace E] {d : ℕ}
    (dependent : J → J → Prop) (Δ : ℕ) (π : Measure E)
    [SFinite (historyMarkedReference dependent Δ π)]
    (activation : E → ℝ) (ham : Measurable activation) (n : ℕ) (a v η : ℝ)
    (p F : HistoryMarked dependent E → Covariate d → ℝ)
    (hp : Measurable (Function.uncurry p)) (hF : Measurable (Function.uncurry F)) :
    Kernel ℝ ((Fin n → Covariate d) × (Fin n → Fin 3)) :=
  (Kernel.const ℝ (highSampleReference d n)).withDensity fun t z => ENNReal.ofReal
    (highMarginalRawLikelihood (historyMarkedPrior dependent Δ t π activation) n a (v - η ^ 2 * t) p F z /
      massPowerNormalizer (historyMarkedPrior dependent Δ t π activation) (fun ω => highRawDensityMass (p ω)) n)

instance highHistoryIndexTimeKernel_isSFinite {E : Type*} [MeasurableSpace E] {d : ℕ}
    (dependent : J → J → Prop) (Δ : ℕ) (π : Measure E)
    [SFinite (historyMarkedReference dependent Δ π)]
    (activation : E → ℝ) (ham : Measurable activation) (n : ℕ) (a v η : ℝ)
    (p F : HistoryMarked dependent E → Covariate d → ℝ)
    (hp : Measurable (Function.uncurry p)) (hF : Measurable (Function.uncurry F)) :
    IsSFiniteKernel (highHistoryIndexTimeKernel dependent Δ π activation ham n a v η p F hp hF) :=
  Kernel.isSFiniteKernel_withDensity_of_isFiniteKernel _ fun _ _ => ENNReal.ofReal_ne_top

def highHistoryRealTimeKernel {E : Type*} [MeasurableSpace E] {d : ℕ}
    (dependent : J → J → Prop) (Δ : ℕ) (π : Measure E)
    [SFinite (historyMarkedReference dependent Δ π)]
    (activation : E → ℝ) (ham : Measurable activation) (n : ℕ) (a v η : ℝ)
    (p F : HistoryMarked dependent E → Covariate d → ℝ)
    (hp : Measurable (Function.uncurry p)) (hF : Measurable (Function.uncurry F)) :
    Kernel ℝ (Fin n → Observation d) :=
  (highHistoryIndexTimeKernel dependent Δ π activation ham n a v η p F hp hF).map (encodeDesignResponse a)

instance highHistoryRealTimeKernel_isSFinite {E : Type*} [MeasurableSpace E] {d : ℕ}
    (dependent : J → J → Prop) (Δ : ℕ) (π : Measure E)
    [SFinite (historyMarkedReference dependent Δ π)]
    (activation : E → ℝ) (ham : Measurable activation) (n : ℕ) (a v η : ℝ)
    (p F : HistoryMarked dependent E → Covariate d → ℝ)
    (hp : Measurable (Function.uncurry p)) (hF : Measurable (Function.uncurry F)) :
    IsSFiniteKernel (highHistoryRealTimeKernel dependent Δ π activation ham n a v η p F hp hF) := by
  unfold highHistoryRealTimeKernel; infer_instance

lemma highHistoryRealTimeKernel_eq_data {E : Type*} [MeasurableSpace E] {d : ℕ}
    (dependent : J → J → Prop) (Δ : ℕ) (π : Measure E)
    [SFinite (historyMarkedReference dependent Δ π)]
    (activation : E → ℝ) (ham : Measurable activation) (n : ℕ) (a v η : ℝ)
    (p F : HistoryMarked dependent E → Covariate d → ℝ)
    (hp : Measurable (Function.uncurry p)) (hF : Measurable (Function.uncurry F))
    (t : ℝ) [IsProbabilityMeasure (historyMarkedPrior dependent Δ t π activation)]
    (aRaw bRaw : ℝ) (haRaw : 0 < aRaw) (ha : a ≠ 0)
    (hraw : ∀ ω x, aRaw ≤ p ω x ∧ p ω x ≤ bRaw)
    (hq : ∀ ω x y, 0 ≤ ternaryMass a (F ω x) (v - η ^ 2 * t) y) :
    highHistoryRealTimeKernel dependent Δ π activation ham n a v η p F hp hF t =
      (highRealSampleKernel n a (v - η ^ 2 * t) p F hp hF) ∘ₘ
        massPowerTilt (historyMarkedPrior dependent Δ t π activation) (fun ω => highRawDensityMass (p ω)) n := by
  have hd : Measurable (Function.uncurry fun t z => ENNReal.ofReal
      (highMarginalRawLikelihood (historyMarkedPrior dependent Δ t π activation) n a (v - η ^ 2 * t) p F z /
        massPowerNormalizer (historyMarkedPrior dependent Δ t π activation) (fun ω => highRawDensityMass (p ω)) n)) :=
    ((highMarginalRawLikelihood_time_measurable dependent Δ π activation ham n a v η p F hp hF).div
      ((highMassPowerNormalizer_time_measurable dependent Δ π activation ham n p hp).comp measurable_fst)).ennreal_ofReal
  rw [highHistoryRealTimeKernel, Kernel.map_apply _ (encodeDesignResponse_measurable a),
    highHistoryIndexTimeKernel, Kernel.withDensity_apply _ hd t, Kernel.const_apply,
    ← highMassTilt_index_marginal_density (historyMarkedPrior dependent Δ t π activation)
      n a (v - η ^ 2 * t) p F hp hF aRaw bRaw haRaw ha hraw hq,
    Measure.map_comp _ _ (encodeDesignResponse_measurable a)]
  rfl

theorem highHistoryScore_sqrt_energy_intervalIntegrable {E : Type*} [MeasurableSpace E]
    [StandardBorelSpace E] {d : ℕ}
    (dependent : J → J → Prop) (hsymm : ∀ ⦃i j⦄, dependent i j → dependent j i)
    (Δ : ℕ) (π : Measure E) [IsProbabilityMeasure π]
    [SFinite (historyMarkedReference dependent Δ π)]
    (activation : E → ℝ) (ham : Measurable activation)
    (Ba : ℝ) (hBa : 0 ≤ Ba) (habound : ∀ e, |activation e| ≤ Ba)
    (n : ℕ) (a v η aRaw bRaw T M : ℝ) (ha : 0 < a) (haRaw : 0 < aRaw) (hT : 0 ≤ T)
    (p F : HistoryMarked dependent E → Covariate d → ℝ)
    (hp : Measurable (Function.uncurry p)) (hF : Measurable (Function.uncurry F))
    (hprob : ∀ t ∈ Icc 0 T, IsProbabilityMeasure (historyMarkedPrior dependent Δ t π activation))
    (hraw : ∀ ω x, aRaw ≤ p ω x ∧ p ω x ≤ bRaw)
    (hq : ∀ t ∈ Icc 0 T, ∀ ω x y, 0 < ternaryMass a (F ω x) (v - η ^ 2 * t) y)
    (hE : ∀ t ∈ Icc 0 T, Integrable
      (fun z : HistoryMarked dependent E × ((Fin n → Covariate d) × (Fin n → Fin 3)) =>
        (highHistoryLikelihoodDerivative dependent hsymm π activation n a (v - η ^ 2 * t) η p F z.1 z.2) ^ 2 /
          highRawSampleLikelihood n a (v - η ^ 2 * t) (p z.1) (F z.1) z.2)
      ((historyMarkedPrior dependent Δ t π activation).prod (highSampleReference d n)))
    (hbudget : ∀ t ∈ Icc 0 T,
      (massPowerNormalizer (historyMarkedPrior dependent Δ t π activation)
        (fun ω => highRawDensityMass (p ω)) n)⁻¹ *
        ∫ z : HistoryMarked dependent E × ((Fin n → Covariate d) × (Fin n → Fin 3)),
          (highHistoryLikelihoodDerivative dependent hsymm π activation n a (v - η ^ 2 * t) η p F z.1 z.2) ^ 2 /
            highRawSampleLikelihood n a (v - η ^ 2 * t) (p z.1) (F z.1) z.2
          ∂(historyMarkedPrior dependent Δ t π activation).prod (highSampleReference d n) ≤ M) :
    IntervalIntegrable (fun t => Real.sqrt (∫ z,
      (highMarginalRealScore dependent hsymm (historyMarkedPrior dependent Δ t π activation)
        π activation n a (v - η ^ 2 * t) η p F z) ^ 2
      ∂(highRealSampleKernel n a (v - η ^ 2 * t) p F hp hF) ∘ₘ
        massPowerTilt (historyMarkedPrior dependent Δ t π activation)
          (fun ω => highRawDensityMass (p ω)) n)) volume 0 T := by
  let κ := highHistoryRealTimeKernel dependent Δ π activation ham n a v η p F hp hF
  let proxy (t : ℝ) := ∫ z,
    (highMarginalRealScore dependent hsymm (historyMarkedPrior dependent Δ t π activation)
      π activation n a (v - η ^ 2 * t) η p F z) ^ 2 ∂κ t
  have hproxy_meas : Measurable proxy :=
    (((highMarginalRealScore_time_measurable dependent hsymm Δ π activation ham n a v η p F hp hF).pow_const 2).stronglyMeasurable.integral_kernel_prod_right'
      (κ := κ)).measurable
  have hb (t : ℝ) (ht : t ∈ Icc 0 T) : proxy t ≤ M := by
    letI := hprob t ht
    dsimp only [proxy, κ]
    rw [highHistoryRealTimeKernel_eq_data dependent Δ π activation ham n a v η p F hp hF
      t aRaw bRaw haRaw ha.ne' hraw fun ω x y => (hq t ht ω x y).le]
    exact (highMarginalRealScore_memLp_energy dependent hsymm
      (historyMarkedPrior dependent Δ t π activation) π activation ham Ba hBa habound
      n a (v - η ^ 2 * t) η aRaw bRaw ha haRaw p F hp hF hraw (hq t ht) (hE t ht)).2.trans (hbudget t ht)
  have hi : IntervalIntegrable (fun t => Real.sqrt (proxy t)) volume 0 T := by
    refine (intervalIntegrable_const (c := Real.sqrt M)).mono_fun'
      (Real.continuous_sqrt.measurable.comp hproxy_meas).aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_uIoc] with t ht
    rw [uIoc_of_le hT] at ht
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
    exact Real.sqrt_le_sqrt (hb t ⟨ht.1.le, ht.2⟩)
  refine hi.congr fun t ht => ?_
  rw [uIoc_of_le hT] at ht
  letI := hprob t ⟨ht.1.le, ht.2⟩
  try dsimp only [proxy, κ]
  rw [highHistoryRealTimeKernel_eq_data dependent Δ π activation ham n a v η p F hp hF
    t aRaw bRaw haRaw ha.ne' hraw fun ω x y => (hq t ⟨ht.1.le, ht.2⟩ ω x y).le]

attribute [local irreducible] highMarginalRealScore highRealSampleKernel historyMarkedPrior
  massPowerTilt massPowerNormalizer highRawDensityMass

theorem historyMarkedPrior_original_minimax_path_bound
    (dependent : J → J → Prop) (hrefl : ∀ j, dependent j j)
    (hsymm : ∀ ⦃i j⦄, dependent i j → dependent j i)
    (Δ : ℕ) (hΔ : 1 ≤ Δ) (hlabels : ∀ j, (dependentLabelFinset dependent j).card ≤ Δ)
    {E : Type*} [MeasurableSpace E] [StandardBorelSpace E]
    (π : Measure E) [IsProbabilityMeasure π] (activation : E → ℝ)
    (ham : Measurable activation) (hact : ∫ e, activation e ∂π = 0)
    (Ba T : ℝ) (hBa : 0 ≤ Ba) (hT : 0 ≤ T) (hab : ∀ e, |activation e| ≤ Ba)
    (hsmall : T * Ba / historyReferenceRho Δ ≤ 1 / (2 + 8 * (Δ : ℝ) ^ 2))
    {d : ℕ} (C : ModelConstants d) (n : ℕ) (a v η aRaw bRaw M ε : ℝ)
    (ha : 0 < a) (haRaw : 0 < aRaw)
    (p F : HistoryMarked dependent E → Covariate d → ℝ)
    (hp : Measurable (Function.uncurry p)) (hF : Measurable (Function.uncurry F))
    (hraw : ∀ ω x, aRaw ≤ p ω x ∧ p ω x ≤ bRaw)
    (hq : ∀ t ∈ Icc 0 T, ∀ ω x y, 0 < ternaryMass a (F ω x) (v - η ^ 2 * t) y)
    (hmass : ∀ t ∈ Icc 0 T,
      (historyMarkedPrior dependent Δ t π activation).map (fun ω => highRawDensityMass (p ω)) =
      (historyMarkedPrior dependent Δ 0 π activation).map (fun ω => highRawDensityMass (p ω)))
    (θ : ℝ → HistoryMarked dependent E → RegressionParameter d)
    (hθ : ∀ (t : ℝ) (ht : t ∈ Icc 0 T), ∀ ω, θ t ω =
      normalizedDensityTernaryParameter (p ω) (F ω) a (v - η ^ 2 * t) hF.of_uncurry_left
        ha.ne' fun x y => (hq t ht ω x y).le)
    (hV : ∀ t ∈ Icc 0 T, v - η ^ 2 * t ∈ Icc C.varianceLower (effectiveVarianceUpper C))
    (bad : ℝ → Set (HistoryMarked dependent E))
    (hbad : ∀ t ∈ Icc 0 T, MeasurableSet (bad t))
    (hlegal : ∀ t ∈ Icc 0 T, ∀ ω ∉ bad t, Admissible C (θ t ω))
    (hbadmass : ∀ t ∈ Icc 0 T,
      (massPowerTilt (historyMarkedPrior dependent Δ t π activation)
        (fun ω => highRawDensityMass (p ω)) n).real (bad t) ≤ ε)
    (hE : ∀ t ∈ Icc 0 T, Integrable
      (fun z : HistoryMarked dependent E × ((Fin n → Covariate d) × (Fin n → Fin 3)) =>
        (highHistoryLikelihoodDerivative dependent hsymm π activation n a (v - η ^ 2 * t) η p F z.1 z.2) ^ 2 /
          highRawSampleLikelihood n a (v - η ^ 2 * t) (p z.1) (F z.1) z.2)
      ((historyMarkedPrior dependent Δ t π activation).prod (highSampleReference d n)))
    (hbudget : ∀ t ∈ Icc 0 T,
      (massPowerNormalizer (historyMarkedPrior dependent Δ t π activation)
        (fun ω => highRawDensityMass (p ω)) n)⁻¹ *
        ∫ z : HistoryMarked dependent E × ((Fin n → Covariate d) × (Fin n → Fin 3)),
          (highHistoryLikelihoodDerivative dependent hsymm π activation n a (v - η ^ 2 * t) η p F z.1 z.2) ^ 2 /
            highRawSampleLikelihood n a (v - η ^ 2 * t) (p z.1) (F z.1) z.2
          ∂(historyMarkedPrior dependent Δ t π activation).prod (highSampleReference d n) ≤ M) :
    let P (t : ℝ) := (highRealSampleKernel n a (v - η ^ 2 * t) p F hp hF) ∘ₘ
      massPowerTilt (historyMarkedPrior dependent Δ t π activation) (fun ω => highRawDensityMass (p ω)) n
    let R (t : ℝ) := highMarginalRealScore dependent hsymm
      (historyMarkedPrior dependent Δ t π activation) π activation n a (v - η ^ 2 * t) η p F
    ENNReal.ofReal (η ^ 4 * T ^ 2 /
      (2 + ∫ t in (0 : ℝ)..T, Real.sqrt (∫ z, (R t z) ^ 2 ∂P t)) ^ 2 -
      (effectiveVarianceUpper C - C.varianceLower) ^ 2 * ε) ≤ minimaxRisk C n := by
  let ν (t : ℝ) := historyMarkedPrior dependent Δ t π activation
  let σ (t : ℝ) := massPowerTilt (ν t) (fun ω => highRawDensityMass (p ω)) n
  let L (t : ℝ) := highRealSampleKernel n a (v - η ^ 2 * t) p F hp hF
  let R (t : ℝ) := highMarginalRealScore dependent hsymm (ν t) π activation n a (v - η ^ 2 * t) η p F
  let _ := historyMarkedReference_probability dependent hrefl hsymm Δ hΔ hlabels π
  have hai : Integrable activation π := Integrable.of_bound ham.aestronglyMeasurable Ba
    (Eventually.of_forall fun e => by simpa only [Real.norm_eq_abs] using hab e)
  have hν (t : ℝ) (ht : t ∈ Icc 0 T) : IsProbabilityMeasure (ν t) :=
    historyMarkedPrior_probability dependent hrefl hsymm Δ hΔ hlabels t Ba ht.1 hBa π activation hai hact hab
      ((div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right ht.2 hBa) (historyReferenceRho_pos Δ).le).trans hsmall)
  have hσ (t : ℝ) (ht : t ∈ Icc 0 T) : IsProbabilityMeasure (σ t) := by
    let _ := hν t ht
    exact massPowerTilt_isProbability (ν t) _ (highRawDensityMass_joint_measurable p hp)
      n aRaw bRaw haRaw fun ω => highRawDensityMass_mem_Icc (p ω) hp.of_uncurry_left
        aRaw bRaw haRaw (Eventually.of_forall (hraw ω))
  have hL (t : ℝ) (ht : t ∈ Icc 0 T) : IsMarkovKernel (L t) :=
    highRealSampleKernel_markov n a (v - η ^ 2 * t) p F hp hF aRaw bRaw haRaw hraw ha.ne'
      fun ω x y => (hq t ht ω x y).le
  have hsample (t : ℝ) (ht : t ∈ Icc 0 T) (ω) : L t ω = sampleLaw (θ t ω) n := by
    rw [hθ t ht ω]
    exact highRealSampleKernel_eq_sampleLaw n a (v - η ^ 2 * t) p F hp hF aRaw bRaw haRaw hraw
      ha.ne' (fun ω x y => (hq t ht ω x y).le) ω
  have hvariance (t : ℝ) (ht : t ∈ Icc 0 T) (ω) : (θ t ω).variance = v - η ^ 2 * t := by rw [hθ t ht ω]; rfl
  have hR : ∀ᵐ t ∂volume, t ∈ Icc 0 T → MemLp (R t) 2 (L t ∘ₘ σ t) :=
    Eventually.of_forall fun t ht => by
      let _ := hν t ht
      exact (highMarginalRealScore_memLp_energy dependent hsymm (ν t) π activation ham
        Ba hBa hab n a (v - η ^ 2 * t) η aRaw bRaw ha haRaw p F hp hF hraw (hq t ht) (hE t ht)).1
  have hc := historyMarkedPrior_dataScore_centered_ae dependent hrefl hsymm Δ hΔ hlabels
    T Ba hBa π activation ham hact hab hsmall n a v η aRaw bRaw ha haRaw p F hp hF hraw hq hmass
  have hB : 0 ≤ effectiveVarianceUpper C :=
    C.varianceLower_pos.le.trans (effective_variance_interval_nondegenerate C).le
  have hAC (S : BoundedEstimator C n) : AbsolutelyContinuousOnInterval
      (fun t => ∫ z, S.val.val z ∂(L t ∘ₘ σ t)) 0 T :=
    historyMarkedPrior_dataMean_absolutelyContinuous dependent hrefl hsymm Δ hΔ hlabels
      T Ba hBa π activation ham hact hab hsmall n a v η aRaw bRaw ha haRaw p F hp hF hraw
      (fun t ht ω x y => (hq t ht ω x y).le) hmass S.val.val S.val.property
      (effectiveVarianceUpper C) hB
      (fun z => by rw [abs_of_nonneg (C.varianceLower_pos.le.trans (S.property z).1)]; exact (S.property z).2) hT
  have hd (S : BoundedEstimator C n) :=
    historyMarkedPrior_dataMean_score_hasDerivAt_ae dependent hrefl hsymm Δ hΔ hlabels
      T Ba hBa π activation ham hact hab hsmall n a v η aRaw bRaw ha haRaw p F hp hF hraw hq hmass
      S.val.val S.val.property (effectiveVarianceUpper C) hB
      fun z => by rw [abs_of_nonneg (C.varianceLower_pos.le.trans (S.property z).1)]; exact (S.property z).2
  have hi := highHistoryScore_sqrt_energy_intervalIntegrable dependent hsymm Δ π activation ham
    Ba hBa hab n a v η aRaw bRaw T M ha haRaw hT p F hp hF hν hraw hq hE hbudget
  have hh := paper_score_to_risk C σ L θ (fun t => v - η ^ 2 * t) R T ε hT hσ hL hsample hvariance
    hV bad hbad hlegal hbadmass hR hc hAC hd hi
  dsimp only at hh ⊢
  rwa [show ((v - η ^ 2 * T) - (v - η ^ 2 * 0)) ^ 2 = η ^ 4 * T ^ 2 by ring] at hh

end TimeScoreKernel
end NearlyMinimax
