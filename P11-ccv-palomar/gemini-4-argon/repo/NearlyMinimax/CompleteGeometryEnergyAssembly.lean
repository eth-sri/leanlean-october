module
public import NearlyMinimax.FieldTailSummation
public import NearlyMinimax.HighFrameDesignEnergy
public import NearlyMinimax.HighCompleteGeometry
@[expose] public section
noncomputable section
open MeasureTheory Set Filter
open scoped BigOperators Topology
namespace NearlyMinimax
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
section
variable {d : ℕ} {N mu H bd B μ aD bD ad c0 K : ℝ}
theorem target_cutoff_inverse_budget  (hd : d ≠ 0)
     (hN : 0 < N) (hmu : 0 < mu) (hH : 0 < H) (j : ℕ) :
    (N * (mu * H) ^ ((j : ℝ) / d)) ^ (-(d : ℝ)) * H ^ j =
      N ^ (-(d : ℝ)) / mu ^ j := by
  have hprod  := mul_pos hmu hH
  rw [Real.mul_rpow hN.le (Real.rpow_pos_of_pos hprod _).le, ← Real.rpow_mul hprod.le]
  have he : ((j : ℝ) / d) * (-(d : ℝ)) = -(j : ℝ) := by field_simp
  rw [he, Real.rpow_neg hprod.le, Real.rpow_natCast, mul_pow]
  field_simp
theorem target_cutoff_le_base  (hd : 0 < d)
     (hN : 0 ≤ N) (hmuH : 0 ≤ mu * H) (hsmall : mu * H ≤ 1) (j : ℕ) :
    N * (mu * H) ^ ((j : ℝ) / d) ≤ N := by
  simpa only [mul_one] using mul_le_mul_of_nonneg_left (Real.rpow_le_one hmuH hsmall (by positivity : 0 ≤ (j : ℝ) / d)) hN
theorem target_cutoff_defect_budget_le  (hd : d ≠ 0)
     (hN : 0 < N) (hmu : 0 < mu) (j : ℕ)
    (hT : 1 ≤ N * (mu * (1 + Real.log N)) ^ ((j : ℝ) / d))
    (hTN : N * (mu * (1 + Real.log N)) ^ ((j : ℝ) / d) ≤ N) :
    (N * (mu * (1 + Real.log N)) ^ ((j : ℝ) / d)) ^ (-(d : ℝ)) *
      (1 + Real.log (N * (mu * (1 + Real.log N)) ^ ((j : ℝ) / d))) ^ j ≤
        N ^ (-(d : ℝ)) / mu ^ j := by
  have hN1 : 1 ≤ N := hT.trans hTN
  have hH : 0 < 1 + Real.log N := by linarith [Real.log_nonneg hN1]
  have hlog : 1 + Real.log (N * (mu * (1 + Real.log N)) ^ ((j : ℝ) / d)) ≤ 1 + Real.log N := by
    have ht : 0 < N * (mu * (1 + Real.log N)) ^ ((j : ℝ) / d) := by linarith only [hT]
    have hh := Real.log_le_log ht hTN
    linarith only [hh]
  have hlog0 : 0 ≤ 1 + Real.log (N * (mu * (1 + Real.log N)) ^ ((j : ℝ) / d)) :=
    add_nonneg (by norm_num) (Real.log_nonneg hT)
  have hp : 0 ≤ (N * (mu * (1 + Real.log N)) ^ ((j : ℝ) / d)) ^ (-(d : ℝ)) :=
    Real.rpow_nonneg (by positivity) _
  have h := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hlog0 hlog j) hp
  exact h.trans_eq (target_cutoff_inverse_budget hd hN hmu hH j)
theorem omitted_target_inverse_budget_ge_one  (hd : d ≠ 0)
     (hN1 : 1 ≤ N) (hmu : 0 < mu) (j : ℕ)
    (hT : N * (mu * (1 + Real.log N)) ^ ((j : ℝ) / d) < 1) :
    1 ≤ N ^ (-(d : ℝ)) / mu ^ j := by
  have hN : 0 < N := lt_of_lt_of_le (by norm_num) hN1
  have hH : 0 < 1 + Real.log N := by linarith [Real.log_nonneg hN1]
  have hTp : 0 < N * (mu * (1 + Real.log N)) ^ ((j : ℝ) / d) := by positivity
  rw [← target_cutoff_inverse_budget hd hN hmu hH j]
  have hp := Real.one_le_rpow_of_pos_of_le_one_of_nonpos hTp hT.le
    (by exact neg_nonpos.mpr (Nat.cast_nonneg d))
  have hH1 : 1 ≤ (1 + Real.log N) ^ j :=
    one_le_pow₀ (by linarith [Real.log_nonneg hN1])
  have h := mul_le_mul hp hH1 (by norm_num : (0 : ℝ) ≤ 1) (Real.rpow_nonneg hTp.le _)
  simpa only [one_mul] using h
def cardinalAliasSpatialComponent (d n : ℕ) (bd a η T : ℝ) : ℝ :=
  2*cardinalRawAliasCoefficient n bd a η^2 * n^2*2^d*cardinalDefectSquareBudget d n T
 def cardinalTaylorSpatialComponent (d n q : ℕ) (bd C a ρ η : ℝ) : ℝ :=
  2*cardinalRawTaylorCoefficient n q bd C a ρ η^2 * n^2*2^d*
    ((100*d)^2*16*spatialScaleIntegralConstant d)^(n-1)
 theorem cardinalRawSpatialEnergyBudget_split (d n q bd C a ρ η T) :
    cardinalRawSpatialEnergyBudget d n q bd C a ρ η T =
      cardinalAliasSpatialComponent d n bd a η T + cardinalTaylorSpatialComponent d n q bd C a ρ η := by
  unfold cardinalRawSpatialEnergyBudget cardinalAliasSpatialComponent cardinalTaylorSpatialComponent
  ring
 def cardinalSpatialGeometricBase (B κ : ℝ) : ℝ := 1+B^2*max 1 κ
 theorem cardinalSpatialGeometricBase_nonneg (B κ ) : 0 ≤ cardinalSpatialGeometricBase B κ := by
  unfold cardinalSpatialGeometricBase
  positivity
 theorem cardinal_monomial_geometric_le  (hb : 0 ≤ b) (hbB : b ≤ B) (hκ : 0 ≤ κ) (n ) :
    (b^2)^n*κ^(n-1) ≤ cardinalSpatialGeometricBase B κ^n := by
  have hM : 1 ≤ max 1 κ := le_max_left _ _
  have hκp := (pow_le_pow_left₀ hκ (le_max_right 1 κ) (n-1)).trans
    (pow_le_pow_right₀ hM (Nat.sub_le n 1))
  have h2 : (B^2*max 1 κ)^n ≤ cardinalSpatialGeometricBase B κ^n :=
    pow_le_pow_left₀ (mul_nonneg (sq_nonneg B) (zero_le_one.trans hM))
      (by unfold cardinalSpatialGeometricBase; linarith only []) n
  exact (mul_le_mul (pow_le_pow_left₀ (sq_nonneg b) (pow_le_pow_left₀ hb hbB 2) n) hκp (pow_nonneg hκ (n-1)) (pow_nonneg (sq_nonneg B) n)).trans (by simpa only [mul_pow] using h2)
 def cardinalInterpolationEnergyPrefactor (d : ℕ) (a : ℝ) : ℝ := 2*2^d/a^4
 def cardinalTaylorEnergyPrefactor (d q : ℕ) (C a ρ : ℝ) : ℝ :=
  2*2^d*highResponseRemainderConstant q C a ρ^2
def matchedCardinalTargetCutoff (d j : ℕ) (N μ : ℝ) : ℝ := max 1 (N*(μ*(1+Real.log N))^((j : ℝ)/d))
 def cardinalInterpolationFactorialConstant (d : ℕ) (B a Csharp : ℝ) : ℝ :=
  cardinalInterpolationEnergyPrefactor d a *
    defectTailConstant Csharp (cardinalSpatialGeometricBase B (16*spatialUnaryIntegralConstant d)*2^2)
 theorem finite_cardinal_interpolation_budget_le  (hbd : 0 ≤ bd) (hB : bd ≤ B)
     (hd : 0 < d) (J : ℕ) (a η Csharp : ℝ) (ha : 0 < a) (hCs : 0 ≤ Csharp)
     (hN : 1 ≤ N) (hμ : 0 < μ) (hsmall : μ*(1+Real.log N) ≤ 1) :
    (∑ j ∈ Finset.range J, poissonCountWeight (Csharp*μ) (2+j) *
      cardinalAliasSpatialComponent d (2+j) bd a η (matchedCardinalTargetCutoff d j N μ)) ≤
      cardinalInterpolationFactorialConstant d B a Csharp * η^4*N^(-(d : ℝ))*μ^2 := by
  let P := cardinalInterpolationEnergyPrefactor d a * η^4*N^(-(d : ℝ))
  have hP : 0 ≤ P := by dsimp [P, cardinalInterpolationEnergyPrefactor]; positivity [lt_of_lt_of_le zero_lt_one hN]
  have hBase := cardinalSpatialGeometricBase_nonneg B (16*spatialUnaryIntegralConstant d)
  have h := finite_interpolation_defect_tail_le hP hCs
    (by positivity : 0 ≤ cardinalSpatialGeometricBase B (16*spatialUnaryIntegralConstant d)*2^2) hμ J
    (fun n => cardinalAliasSpatialComponent d n bd a η (matchedCardinalTargetCutoff d (n-2) N μ)) (by
      intro j hj
      have h_cardinalAliasSpatialComponent_allocated_le : cardinalAliasSpatialComponent d (2+j) bd a η (matchedCardinalTargetCutoff d j N μ) ≤
      cardinalInterpolationEnergyPrefactor d a *
        cardinalSpatialGeometricBase B (16*spatialUnaryIntegralConstant d)^(2+j) *
          (2+j : ℕ)^2 * η^4*N^(-(d : ℝ))/μ^j := by
        have h_cardinalAliasSpatialComponent_geometric_le (n) (T) (hT : 1 ≤ T) : cardinalAliasSpatialComponent d n bd a η T ≤
            cardinalInterpolationEnergyPrefactor d a * cardinalSpatialGeometricBase B (16*spatialUnaryIntegralConstant d)^n *
              (n : ℝ)^2*η^4*T^(-(d : ℝ))*(1+Real.log T)^(n-2) := by
          have hκ : 0 ≤ 16*spatialUnaryIntegralConstant d := by unfold spatialUnaryIntegralConstant; positivity
          have hp := cardinal_monomial_geometric_le hbd hB hκ n
          have : 0 ≤ cardinalInterpolationEnergyPrefactor d a := by unfold cardinalInterpolationEnergyPrefactor; positivity
          have : 0 ≤ 1+Real.log T := by linarith [Real.log_nonneg hT]
          have h := mul_le_mul_of_nonneg_right hp
            (by positivity : 0 ≤ cardinalInterpolationEnergyPrefactor d a*(n : ℝ)^2*η^4*T^(-(d : ℝ))*(1+Real.log T)^(n-2))
          convert h using 1 <;> dsimp only [cardinalAliasSpatialComponent, cardinalRawAliasCoefficient, cardinalDefectSquareBudget, cardinalInterpolationEnergyPrefactor]
          · simp only [mul_pow, ← pow_mul]
            field_simp
            ring
          · ring
        have h := h_cardinalAliasSpatialComponent_geometric_le (2+j) (matchedCardinalTargetCutoff d j N μ) (le_max_left _ _)
        have h_target_max_one_defect_budget_le : (max 1 (N*(μ*(1+Real.log N))^((j : ℝ)/d)))^(-(d : ℝ)) *
            (1+Real.log (max 1 (N*(μ*(1+Real.log N))^((j : ℝ)/d))))^j ≤ N^(-(d : ℝ))/μ^j := by
          have hNpos := lt_of_lt_of_le zero_lt_one hN
          have hH : 0 < 1+Real.log N := by linarith [Real.log_nonneg hN]
          let T := N*(μ*(1+Real.log N))^((j : ℝ)/d)
          by_cases hT : 1 ≤ T
          · rw [max_eq_right hT]
            exact target_cutoff_defect_budget_le (Nat.ne_of_gt hd) hNpos hμ j hT
              (target_cutoff_le_base hd hNpos.le (mul_nonneg hμ.le hH.le) hsmall j)
          · rw [max_eq_left (le_of_not_ge hT), Real.one_rpow, Real.log_one, add_zero, one_pow, mul_one]
            exact omitted_target_inverse_budget_ge_one (Nat.ne_of_gt hd) hN hμ j (lt_of_not_ge hT)
        have hi := h_target_max_one_defect_budget_le
        have : 0 ≤ cardinalInterpolationEnergyPrefactor d a := by unfold cardinalInterpolationEnergyPrefactor; positivity
        have := cardinalSpatialGeometricBase_nonneg B (16*spatialUnaryIntegralConstant d)
        have hh := mul_le_mul_of_nonneg_left hi
          (by positivity : 0 ≤ cardinalInterpolationEnergyPrefactor d a *
            cardinalSpatialGeometricBase B (16*spatialUnaryIntegralConstant d)^(2+j)*(2+j : ℕ)^2*η^4)
        apply h.trans
        convert hh using 1 <;> (try dsimp [matchedCardinalTargetCutoff]) <;> (try simp only [show 2+j-2=j by omega]) <;> ring
      have hb := h_cardinalAliasSpatialComponent_allocated_le
      have hp := polynomial_count_factor_le (2+j) 2
      have hm := mul_le_mul_of_nonneg_left hp
        (by positivity [lt_of_lt_of_le zero_lt_one hN] : 0 ≤ P*cardinalSpatialGeometricBase B (16*spatialUnaryIntegralConstant d)^(2+j)/μ^j)
      rw [show 2+j-2=j by omega]
      apply hb.trans
      convert hm using 1 <;> dsimp [P] <;> (try simp only [mul_pow]) <;> ring)
  simpa only [show ∀ j : ℕ, 2+j-2=j from fun j => by omega] using
    h.trans_eq (by unfold cardinalInterpolationFactorialConstant; dsimp [P]; ring)
 def cardinalTaylorFactorialConstant (d q : ℕ) (B C a ρ Csharp : ℝ) : ℝ :=
  cardinalTaylorEnergyPrefactor d q C a ρ * defectTailConstant Csharp
    (cardinalSpatialGeometricBase B ((100*(d : ℝ))^2*16*spatialScaleIntegralConstant d)*2^(4*q+6))
 theorem finite_cardinal_taylor_budget_le  (hbd : 0 ≤ bd) (hB : bd ≤ B)
    (d q J : ℕ) (C a ρ η Csharp : ℝ) (hCs : 0 ≤ Csharp)
     (hN : 0 < N) (hμ : 0 ≤ μ) (hμ1 : μ ≤ 1) (hsmall : η^(4*q)*N^d ≤ 1) :
    (∑ j ∈ Finset.range J, poissonCountWeight (Csharp*μ) (2+j) *
      cardinalTaylorSpatialComponent d (2+j) q bd C a ρ η) ≤
      cardinalTaylorFactorialConstant d q B C a ρ Csharp * η^4*N^(-(d : ℝ))*μ^2 := by
  let P := cardinalTaylorEnergyPrefactor d q C a ρ * η^4*N^(-(d : ℝ))
  have hP : 0 ≤ P := by dsimp [P, cardinalTaylorEnergyPrefactor]; positivity
  have h_cardinalTaylorSpatialComponent_allocated_le (n : ℕ) : cardinalTaylorSpatialComponent d n q bd C a ρ η ≤
      cardinalTaylorEnergyPrefactor d q C a ρ *
        cardinalSpatialGeometricBase B ((100*(d : ℝ))^2*16*spatialScaleIntegralConstant d)^n *
          (n : ℝ)^(4*q+6)*η^4*N^(-(d : ℝ)) := by
    have h_cardinalTaylorSpatialComponent_geometric_le : cardinalTaylorSpatialComponent d n q bd C a ρ η ≤
        cardinalTaylorEnergyPrefactor d q C a ρ *
          cardinalSpatialGeometricBase B ((100*d)^2*16*spatialScaleIntegralConstant d)^n *
            n^(4*q+6)*η^(4*q+4) := by
      have hκ : 0 ≤ (100*d)^2*16*spatialScaleIntegralConstant d := by
        unfold spatialScaleIntegralConstant
        positivity
      have hp := cardinal_monomial_geometric_le hbd hB hκ n
      have : 0 ≤ cardinalTaylorEnergyPrefactor d q C a ρ := by unfold cardinalTaylorEnergyPrefactor; positivity
      have : 0 ≤ η^(4*q+4) := by rw [show 4*q+4 = 2*(2*q+2) by omega, pow_mul]; positivity
      have h := mul_le_mul_of_nonneg_right hp
        (by positivity : 0 ≤ cardinalTaylorEnergyPrefactor d q C a ρ*n^(4*q+6)*η^(4*q+4))
      convert h using 1 <;> dsimp only [cardinalTaylorSpatialComponent, cardinalRawTaylorCoefficient, cardinalTaylorEnergyPrefactor]
      · simp only [mul_pow, ← pow_mul]
        ring_nf
      · ring
    have h := h_cardinalTaylorSpatialComponent_geometric_le
    have h_response_taylor_budget_absorption {eta : ℝ} (hsmall : eta ^ (4 * q) * N ^ d ≤ 1) : eta ^ (4 * q + 4) ≤ eta ^ 4 / N ^ d := by
      apply (le_div_iff₀ (pow_pos hN d)).mpr
      simpa only [pow_add, mul_assoc, mul_comm, mul_left_comm, mul_one] using (mul_le_mul_of_nonneg_left hsmall (by positivity : 0 ≤ eta ^ 4))
    have hi := h_response_taylor_budget_absorption hsmall
    have : 0 ≤ cardinalTaylorEnergyPrefactor d q C a ρ := by unfold cardinalTaylorEnergyPrefactor; positivity
    have := cardinalSpatialGeometricBase_nonneg B ((100*(d : ℝ))^2*16*spatialScaleIntegralConstant d)
    have hh := mul_le_mul_of_nonneg_left hi
      (by positivity : 0 ≤ cardinalTaylorEnergyPrefactor d q C a ρ *
        cardinalSpatialGeometricBase B ((100*(d : ℝ))^2*16*spatialScaleIntegralConstant d)^n*(n : ℝ)^(4*q+6))
    apply h.trans
    apply hh.trans_eq
    rw [Real.rpow_neg hN.le, Real.rpow_natCast]
    ring
  have h := finite_taylor_count_energy_tail_le hP hCs
    (cardinalSpatialGeometricBase_nonneg B ((100*(d : ℝ))^2*16*spatialScaleIntegralConstant d)) hμ hμ1 (4*q+6) J
    (fun n => cardinalTaylorSpatialComponent d n q bd C a ρ η)
    (fun j _ => (h_cardinalTaylorSpatialComponent_allocated_le (2+j)).trans_eq
      (by dsimp [P]; ring))
  exact h.trans_eq (by unfold cardinalTaylorFactorialConstant; dsimp [P]; ring)
def finePairSpatialEnergyPrefactor (d q : ℕ) (ad bd C a ρ : ℝ) : ℝ :=
  |finePairDensityPrefactor ad bd|^2 * finePairResponseActionBudget d q C a ρ ^ 2 *
    Real.exp (4*exteriorTau ((ad+bd)/(bd-ad)))
 theorem finePairSpatialEnergyPrefactor_nonneg (d q : ℕ) (ad bd C a ρ : ℝ) :
    0 ≤ finePairSpatialEnergyPrefactor d q ad bd C a ρ := by
  unfold finePairSpatialEnergyPrefactor
  positivity
 theorem finePairResponseCoefficient_square_le (d n M q : ℕ) (ad bd C a ρ η : ℝ)
    (haD : 0 < ad) (hab : ad < bd) :
    (finePairDensityCoefficientBudget ad bd M n *
      finePairResponseActionBudget d q C a ρ * ↑n^2 * η^2)^2 ≤
      finePairSpatialEnergyPrefactor d q ad bd C a ρ * (bd^2)^n * ↑n^4 * η^4 *
        Real.exp (2*exteriorTau ((ad+bd)/(bd-ad))*M) := by
  let tau := exteriorTau ((ad+bd)/(bd-ad))
  have := (haD.trans hab).le
  have h := mul_le_mul_of_nonneg_left ((sq_le_sq₀ (Real.cosh_pos _).le (Real.exp_pos _).le).mpr (by rw [← exterior_rule_variation ad bd haD hab (M+2) (by omega)]; exact exterior_rule_variation_le_exp ad bd haD hab (M+2) (by omega)))
    (sq_nonneg (|finePairDensityPrefactor ad bd| *bd^n*
      (finePairResponseActionBudget d q C a ρ*↑n^2*η^2)))
  calc
    _ = (|finePairDensityPrefactor ad bd| *bd^n*
      (finePairResponseActionBudget d q C a ρ*↑n^2*η^2))^2 * Real.cosh ((M+2 : ℕ)*tau)^2 := by
      unfold finePairDensityCoefficientBudget
      dsimp [tau]
      ring
    _ ≤ (|finePairDensityPrefactor ad bd| *bd^n*
      (finePairResponseActionBudget d q C a ρ*↑n^2*η^2))^2 * Real.exp ((M+2 : ℕ)*tau)^2 := h
    _ = _ := by
      rw [← Real.exp_nat_mul]
      norm_num only [Nat.cast_ofNat]
      rw [Nat.cast_add, Nat.cast_ofNat]
      have he : 2*((↑M+2)*tau) = 4*tau + 2*tau*M := by ring
      rw [he, Real.exp_add]
      unfold finePairSpatialEnergyPrefactor
      dsimp [tau]
      simp only [mul_pow, ← pow_mul]
      ring
 def finePairFieldGeometricBase (d : ℕ) (bd : ℝ) : ℝ :=
  1 + bd^2 * fineFieldSubsetEnergyBase d
 theorem finePairFieldGeometricBase_nonneg (d : ℕ) (bd : ℝ) :
    0 ≤ finePairFieldGeometricBase d bd := by
  unfold finePairFieldGeometricBase fineFieldSubsetEnergyBase
  positivity
 theorem spatialInverseFourConstant_nonneg (d : ℕ) : 0 ≤ spatialInverseFourConstant d := by
  unfold spatialInverseFourConstant
  positivity
 def finePairAliasGeometricBase (d : ℕ) (bd : ℝ) : ℝ := 1 + bd^2*↑2^d
 theorem finePairAliasGeometricBase_nonneg (d : ℕ) (bd : ℝ) :
    0 ≤ finePairAliasGeometricBase d bd := by unfold finePairAliasGeometricBase; positivity
def finePairUniformSpatialPrefactor (d q : ℕ) (aD bD C a ρ c0 : ℝ) : ℝ :=
  ((bD-aD)/aD)^4 * finePairResponseActionBudget d q C a ρ ^ 2 * Real.exp (4*c0)
 theorem finePairUniformSpatialPrefactor_nonneg (d q aD bD C a ρ c0) :
    0 ≤ finePairUniformSpatialPrefactor d q aD bD C a ρ c0 := by
  unfold finePairUniformSpatialPrefactor
  positivity
 theorem finePairSpatialEnergyPrefactor_uniform_le 
    (haD : 0 < aD) (ha : aD ≤ ad) (hb : bd ≤ bD) (hab : ad < bd)
    (htau : exteriorTau ((ad+bd)/(bd-ad)) ≤ c0) (d q C a ρ) :
    finePairSpatialEnergyPrefactor d q ad bd C a ρ ≤
      finePairUniformSpatialPrefactor d q aD bD C a ρ c0 := by
  have had  := haD.trans_le ha
  have hratio0  := div_nonneg (sub_nonneg.mpr hab.le) had.le
  have hratio : (bd-ad)/ad ≤ (bD-aD)/aD := by
    apply (div_le_div_iff₀ had haD).mpr
    have hbD  := (had.trans hab).trans_le hb
    nlinarith only [ha, hb, haD, had, hbD, mul_nonneg (sub_nonneg.mpr ha) hbD.le,
      mul_nonneg (sub_nonneg.mpr hb) haD.le]
  have hp := pow_le_pow_left₀ hratio0 hratio 4
  have hexp := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left htau (by norm_num : (0 : ℝ) ≤ 4))
  have h := mul_le_mul (mul_le_mul_of_nonneg_right hp
    (sq_nonneg (finePairResponseActionBudget d q C a ρ))) hexp (Real.exp_pos _).le
      (by positivity : 0 ≤ ((bD-aD)/aD)^4*finePairResponseActionBudget d q C a ρ^2)
  unfold finePairSpatialEnergyPrefactor finePairUniformSpatialPrefactor
  have h_finePairDensityPrefactor_eq : finePairDensityPrefactor ad bd = ((bd-ad)/ad)^2 := by
    unfold finePairDensityPrefactor densityMargin
    field_simp [had.ne', (had.trans hab).ne', (sub_pos.mpr hab).ne']
    ring
  rw [h_finePairDensityPrefactor_eq, abs_of_nonneg (sq_nonneg _)]
  simpa only [← pow_mul] using h
 theorem finePairFieldGeometricBase_mono  (hbd : 0 ≤ bd) (hb : bd ≤ bD) (d : ℕ) :
    finePairFieldGeometricBase d bd ≤ finePairFieldGeometricBase d bD := by
  have h := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hbd hb 2)
    (by unfold fineFieldSubsetEnergyBase; positivity : 0 ≤ fineFieldSubsetEnergyBase d)
  unfold finePairFieldGeometricBase
  linarith only [h]
 theorem finePairAliasGeometricBase_mono  (hbd : 0 ≤ bd) (hb : bd ≤ bD) (d ) :
    finePairAliasGeometricBase d bd ≤ finePairAliasGeometricBase d bD := by
  unfold finePairAliasGeometricBase
  linarith only [(mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hbd hb 2) (by positivity : 0 ≤ (2 : ℝ)^d))]
 theorem finePairEvenActionSpatialBudget_uniform_geometric_le 
    (haD : 0 < aD) (ha : aD ≤ ad) (hb : bd ≤ bD) (hab : ad < bd)
    (htau : exteriorTau ((ad+bd)/(bd-ad)) ≤ c0) (d n M q C a ρ η T0) :
    finePairEvenActionSpatialBudget d n M q ad bd C a ρ η T0 ≤
      finePairUniformSpatialPrefactor d q aD bD C a ρ c0 * finePairFieldGeometricBase d bD ^ n *
        n^12 * η^4 * Real.exp (2*exteriorTau ((ad+bd)/(bd-ad))*M) * (T0^(2-(d : ℝ)))^2 := by
  have had := haD.trans_le ha
  have h_finePairEvenActionSpatialBudget_geometric_le : finePairEvenActionSpatialBudget d n M q ad bd C a ρ η T0 ≤
      finePairSpatialEnergyPrefactor d q ad bd C a ρ * finePairFieldGeometricBase d bd ^ n *
        (n : ℝ)^12 * η^4 * Real.exp (2*exteriorTau ((ad+bd)/(bd-ad))*M) *
          (T0^(2-(d : ℝ)))^2 := by
    have h := mul_le_mul_of_nonneg_right (finePairResponseCoefficient_square_le d n M q ad bd C a ρ η had hab)
      (by unfold fineFieldSubsetEnergyBase; positivity : 0 ≤ fineFieldSubsetEnergyBase d ^ n * (n : ℝ)^8*(T0^(2-(d : ℝ)))^2)
    have hpow : (bd^2*fineFieldSubsetEnergyBase d)^n ≤ finePairFieldGeometricBase d bd ^ n :=
      pow_le_pow_left₀ (by unfold fineFieldSubsetEnergyBase; positivity)
        (by unfold finePairFieldGeometricBase; linarith only []) n
    have hm := mul_le_mul_of_nonneg_right hpow
      (by positivity [finePairSpatialEnergyPrefactor_nonneg d q ad bd C a ρ] :
        0 ≤ finePairSpatialEnergyPrefactor d q ad bd C a ρ * (n : ℝ)^12 * η^4 *
          Real.exp (2*exteriorTau ((ad+bd)/(bd-ad))*M)*(T0^(2-(d : ℝ)))^2)
    unfold finePairEvenActionSpatialBudget
    have hh := h.trans (by
      convert hm using 1 <;> simp only [mul_pow] <;> ring)
    convert hh using 1 <;> ring
  have hbase := pow_le_pow_left₀ (finePairFieldGeometricBase_nonneg d bd)
    (finePairFieldGeometricBase_mono (had.trans hab).le hb d) n
  have hmul := mul_le_mul (finePairSpatialEnergyPrefactor_uniform_le haD ha hb hab htau d q C a ρ) hbase (pow_nonneg (finePairFieldGeometricBase_nonneg d bd) n)
    (finePairUniformSpatialPrefactor_nonneg d q aD bD C a ρ c0)
  have hh := mul_le_mul_of_nonneg_right hmul
    (by positivity : 0 ≤ (n : ℝ)^12*η^4*Real.exp (2*exteriorTau ((ad+bd)/(bd-ad))*M)*(T0^(2-(d : ℝ)))^2)
  exact (h_finePairEvenActionSpatialBudget_geometric_le).trans (by convert hh using 1 <;> ring)
def finePairFieldFactorialConstant (d q : ℕ) (aD bD C a ρ c0 Csharp : ℝ) : ℝ :=
  finePairUniformSpatialPrefactor d q aD bD C a ρ c0 *
    fieldTailConstant Csharp (finePairFieldGeometricBase d bD * 2^12)
def finePairSaddleAliasExponent (d : ℕ) (c0 K : ℝ) : ℝ :=
  2*c0+c0*K*(d-4)
def finePairSaddleAliasFactorialConstant (d q : ℕ) (aD bD C a rho c0 K Cs : ℝ) : ℝ :=
  aliasTailConstant
    (finePairUniformSpatialPrefactor d q aD bD C a rho c0 * 6*2^d*spatialInverseFourConstant d)
    Cs (finePairAliasGeometricBase d bD*2^8) (finePairSaddleAliasExponent d c0 K)
theorem finite_fine_pair_saddle_alias_budget_le  (hd : 4 ≤ d)
     (haD : 0 < aD) (ha : aD ≤ ad) (hb : bd ≤ bD)
    (hab : ad < bd) (htau : exteriorTau ((ad+bd)/(bd-ad)) ≤ c0)
    (hc0 : 0 ≤ c0) (hK : 0 ≤ K) (M D q J : ℕ)
    (C a rho eta ell N Cs mu : ℝ) (hN : 0 < N)
    (hell : ell=N*Real.exp (-c0*D)) (hD : (D : ℝ) ≤ K*M)
    (hCs : 0 ≤ Cs) (hmu : 0 ≤ mu) (hmu1 : mu ≤ 1) :
    (∑ j ∈ Finset.range J, poissonCountWeight (Cs*mu) (M+1+j) *
      finePairAliasActionSpatialBudget d (M+1+j) M q ad bd C a rho eta ell) ≤
      finePairSaddleAliasFactorialConstant d q aD bD C a rho c0 K Cs *
        (eta^4*N^(4-(d : ℝ))) *
          poissonCountWeight (finePairSaddleAliasFactorialConstant d q aD bD C a rho c0 K Cs*mu) (M+1) := by
  let A := finePairUniformSpatialPrefactor d q aD bD C a rho c0 * 6*(2 : ℝ)^d*spatialInverseFourConstant d
  have hA : 0 ≤ A := by
    positivity [finePairUniformSpatialPrefactor_nonneg d q aD bD C a rho c0,
      spatialInverseFourConstant_nonneg d]
  have hBase  := finePairAliasGeometricBase_nonneg d bD
  have hL : 0 ≤ finePairSaddleAliasExponent d c0 K := by
    unfold finePairSaddleAliasExponent
    have hdR : (4 : ℝ) ≤ d := by exact_mod_cast hd
    positivity
  unfold finePairSaddleAliasFactorialConstant
  apply finite_alias_energy_tail_le hA (by positivity : 0 ≤ eta^4*N^(4-(d : ℝ))) hCs
    (by positivity) hL
    hmu hmu1 M J (fun n => finePairAliasActionSpatialBudget d n M q ad bd C a rho eta ell)
  intro j _
  let n := M+1+j
  have h_finePairAliasActionSpatialBudget_uniform_geometric_le : finePairAliasActionSpatialBudget d n M q ad bd C a rho eta ell ≤
      (finePairUniformSpatialPrefactor d q aD bD C a rho c0 * 6*(2 : ℝ)^d*spatialInverseFourConstant d) *
        finePairAliasGeometricBase d bD ^ n * (n : ℝ)^8 * eta^4 *
          Real.exp (2*exteriorTau ((ad+bd)/(bd-ad))*M) / ell^(d-4) := by
    have hT0 : 0 < ell := (by rw [hell]; positivity)
    have had := haD.trans_le ha
    have hbase := pow_le_pow_left₀ (finePairAliasGeometricBase_nonneg d bd)
      (finePairAliasGeometricBase_mono (had.trans hab).le hb d) n
    have hmul := mul_le_mul (finePairSpatialEnergyPrefactor_uniform_le haD ha hb hab htau d q C a rho) hbase (pow_nonneg (finePairAliasGeometricBase_nonneg d bd) n)
      (finePairUniformSpatialPrefactor_nonneg d q aD bD C a rho c0)
    have hi := spatialInverseFourConstant_nonneg d
    have hh := mul_le_mul_of_nonneg_right hmul
      (by positivity : 0 ≤ 6*(2 : ℝ)^d*spatialInverseFourConstant d*(n : ℝ)^8*eta^4*
        Real.exp (2*exteriorTau ((ad+bd)/(bd-ad))*M)/ell^(d-4))
    have h_finePairAliasActionSpatialBudget_geometric_le : finePairAliasActionSpatialBudget d n M q ad bd C a rho eta ell ≤
        (finePairSpatialEnergyPrefactor d q ad bd C a rho * 6*↑2^d*spatialInverseFourConstant d) *
          finePairAliasGeometricBase d bd ^ n * ↑n^8 * eta^4 *
            Real.exp (2*exteriorTau ((ad+bd)/(bd-ad))*M) / ell^(d-4) := by
      have := finePairSpatialEnergyPrefactor_nonneg d q ad bd C a rho
      have hCoeff := finePairResponseCoefficient_square_le d n M q ad bd C a rho eta had hab
      have hc : (n.choose 2 : ℝ)^2 ≤ ↑n^4 := by
        have h : (n.choose 2 : ℝ) ≤ ↑n^2 := by exact_mod_cast Nat.choose_le_pow n 2
        have h2 := pow_le_pow_left₀ (Nat.cast_nonneg (n.choose 2)) h 2
        simpa only [← pow_mul] using h2
      have hv : ↑2^(d*(n-2)) ≤ (2 : ℝ)^(d*n) :=
        pow_le_pow_right₀ (by norm_num) (Nat.mul_le_mul_left d (Nat.sub_le _ _))
      have hk : 0 ≤ 6*(2 : ℝ)^d*spatialInverseFourConstant d / ell^(d-4) := by
        have hi := spatialInverseFourConstant_nonneg d
        positivity
      have h := mul_le_mul (mul_le_mul hCoeff hc (sq_nonneg _) (by positivity)) hv (by positivity)
        (by positivity [finePairSpatialEnergyPrefactor_nonneg d q ad bd C a rho])
      have h' := mul_le_mul_of_nonneg_right h hk
      have hpow : (bd^2*↑2^d)^n ≤ finePairAliasGeometricBase d bd ^ n :=
        pow_le_pow_left₀ (by positivity) (by unfold finePairAliasGeometricBase; linarith only []) n
      have hpow' := mul_le_mul_of_nonneg_right hpow
        (by positivity [finePairSpatialEnergyPrefactor_nonneg d q ad bd C a rho, spatialInverseFourConstant_nonneg d] :
          0 ≤ finePairSpatialEnergyPrefactor d q ad bd C a rho*↑n^8*eta^4*
            Real.exp (2*exteriorTau ((ad+bd)/(bd-ad))*M)*
              (6*↑2^d*spatialInverseFourConstant d/ell^(d-4)))
      apply h'.trans
      convert hpow' using 1 <;> (try simp only [mul_pow, ← pow_mul]) <;> ring
    exact h_finePairAliasActionSpatialBudget_geometric_le.trans (by convert hh using 1 <;> ring)
  have h_fine_pair_alias_cutoff_scale_le {tau : ℝ} (htau : tau ≤ c0) : Real.exp (2*tau*M)/ell^(d-4) ≤
      N^(4-(d : ℝ))*Real.exp (finePairSaddleAliasExponent d c0 K*M) := by
    have h_fine_pair_alias_cutoff_inverse : 1/ell^(d-4) = N^(4-(d : ℝ))*Real.exp (c0*D*((d : ℝ)-4)) := by
      have hnat : ((d-4 : ℕ) : ℝ) = (d : ℝ)-4 := by
        exact_mod_cast (Nat.cast_sub hd : ((d-4 : ℕ) : ℤ) = (d : ℤ)-4)
      have hpow : N^(4-(d : ℝ)) = (N^(d-4))⁻¹ := by
        rw [show (4 : ℝ)-d = -((d : ℝ)-4) by ring, Real.rpow_neg hN.le,
          ← hnat, Real.rpow_natCast]
      rw [hell, mul_pow, ← Real.exp_nat_mul, hpow, one_div, mul_inv_rev, ← Real.exp_neg,
        mul_comm (Real.exp _)]
      congr 2
      rw [hnat]
      ring
    rw [div_eq_mul_inv, ← one_div, h_fine_pair_alias_cutoff_inverse, ← mul_assoc, mul_comm (Real.exp _) (N^_), mul_assoc, ← Real.exp_add]
    apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg hN.le _)
    apply Real.exp_le_exp.mpr
    have hdR : (4 : ℝ) ≤ d := by exact_mod_cast hd
    have hT := mul_le_mul_of_nonneg_right htau (by positivity : 0 ≤ (2 : ℝ)*M)
    have hDK := mul_le_mul_of_nonneg_left hD (by positivity : 0 ≤ c0*((d : ℝ)-4))
    unfold finePairSaddleAliasExponent
    nlinarith only [hT,hDK]
  have hm := mul_le_mul_of_nonneg_left (h_fine_pair_alias_cutoff_scale_le htau)
    (by positivity : 0 ≤ A*finePairAliasGeometricBase d bD^n*(n : ℝ)^8*eta^4)
  have hm' := mul_le_mul_of_nonneg_right (polynomial_count_factor_le n 8)
    (by positivity : 0 ≤ A*finePairAliasGeometricBase d bD^n*eta^4*N^(4-(d : ℝ))*
      Real.exp (finePairSaddleAliasExponent d c0 K*M))
  apply (h_finePairAliasActionSpatialBudget_uniform_geometric_le).trans
  calc
    _ ≤ A*finePairAliasGeometricBase d bD^n*(n : ℝ)^8*eta^4 *
        (N^(4-(d : ℝ))*Real.exp (finePairSaddleAliasExponent d c0 K*M)) := by
      convert hm using 1 <;> dsimp [A] <;> ring
    _ ≤ A*(eta^4*N^(4-(d : ℝ)))*Real.exp (finePairSaddleAliasExponent d c0 K*M)*
        (finePairAliasGeometricBase d bD*2^8)^n := by
      convert hm' using 1 <;> (try rw [mul_pow]) <;> ring
theorem finite_refined_gated_sum_le_tail (D M : ℕ) (f : ℕ → ℝ)
    (hf : ∀ r, 0 ≤ f r) :
    (∑ j ∈ Finset.range (D-2), if M<3+j then f (3+j) else 0) ≤
      ∑ j ∈ Finset.range (D-M), f (M+1+j) := by
  rw [← Finset.sum_filter]
  apply Finset.sum_le_sum_of_injOn (fun j => 3+j-(M+1))
  · intro i hi j hj hij
    change 3+i-(M+1)=3+j-(M+1) at hij
    have := (Finset.mem_filter.mp hi).2
    have := (Finset.mem_filter.mp hj).2
    omega
  · intro j hj
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hj
    rcases Finset.mem_filter.mp hi with ⟨hi,hiM⟩
    simp only [Finset.mem_range] at hi ⊢
    omega
  · intro j hj
    have := (Finset.mem_filter.mp hj).2
    exact le_of_eq (by congr 1; omega)
  · intro j _ _
    exact hf _
theorem finite_count_energy_from_blocks {x : ℝ} (hx : 0 ≤ x) (n D : ℕ) (hD : 2 ≤ D)
    (e : ℕ → ℝ) (he : ∀ r, 0 ≤ e r) (he0 : e 0 = 0) (he1 : e 1 = 0)
    (E2 Eref Etail : ℝ)
    (h2 : poissonCountWeight x 2 * e 2 ≤ E2)
    (href : (∑ r ∈ Finset.range (D-2), poissonCountWeight x (3+r) * e (3+r)) ≤ Eref)
    (htail : (∑ r ∈ Finset.range (n+1), poissonCountWeight x (D+1+r) * e (D+1+r)) ≤ Etail) :
    (∑ r ∈ Finset.range (n+1), poissonCountWeight x r * e r) ≤ E2+Eref+Etail := by
  have hf (r : ℕ) : 0 ≤ poissonCountWeight x r * e r :=
    mul_nonneg (poissonCountWeight_nonneg hx r) (he r)
  have hprefix : (∑ r ∈ Finset.range (D+1), poissonCountWeight x r * e r) ≤ E2+Eref := by
    have hlen : D+1 = 3+(D-2) := by omega
    rw [hlen, Finset.sum_range_add]
    have hthree : (∑ r ∈ Finset.range 3, poissonCountWeight x r * e r) =
        poissonCountWeight x 2 * e 2 := by
      simp [Finset.sum_range_succ, he0, he1]
    rw [hthree]
    exact add_le_add h2 href
  calc
    _ ≤ ∑ r ∈ Finset.range ((D+1)+(n+1)), poissonCountWeight x r * e r := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.range_mono (by omega))
      intro r _ _
      exact hf r
    _ = (∑ r ∈ Finset.range (D+1), poissonCountWeight x r * e r) +
        (∑ r ∈ Finset.range (n+1), poissonCountWeight x (D+1+r) * e (D+1+r)) := by
      rw [Finset.sum_range_add]
    _ ≤ _ := add_le_add hprefix htail
theorem poissonCountWeight_mul_pow (x a r) :
    poissonCountWeight x r * a^r = poissonCountWeight (a*x) r := by
  unfold poissonCountWeight
  rw [mul_pow]
  ring
theorem higherBandTargetScale_max_eq_matched {d r : ℕ} (hr : 2 ≤ r) (N mu : ℝ) :
    max 1 (higherBandTargetScale d r N mu) = matchedCardinalTargetCutoff d (r-2) N mu := by
  have hnat : ((r-2 : ℕ) : ℝ) = ↑r-2 := by
    rw [Nat.cast_sub hr]
    norm_num
  unfold higherBandTargetScale matchedCardinalTargetCutoff
  rw [hnat]
def cardinalGeometryFactorialConstant (d q : ℕ) (B C a rho Cs : ℝ) : ℝ :=
  cardinalInterpolationFactorialConstant d B a (3*Cs) +
    cardinalTaylorFactorialConstant d q B C a rho (3*Cs)
theorem finite_cardinal_geometry_budget_le  (hd : 5 ≤ d)
     (hbd : 0 ≤ bd) (hbdB : bd ≤ B) (q C a rho eta Cs)
    (ha : 0 < a) (hCs : 0 ≤ Cs)  (hN : 1 ≤ N) (hmu : 0 < mu)
    (hmu1 : mu ≤ 1) (hmuH : mu*(1+Real.log N) ≤ 1)
    (hTaylor : eta^(4*q)*N^d ≤ 1) :
    (∑ j ∈ Finset.range (D-2), poissonCountWeight (Cs*mu) (3+j) *
      ∫ U, cardinalGeometryEnvelope (d := d) (n := 3+j) (F := F) q bd C a rho eta
        (max 1 (higherBandTargetScale d (3+j) N mu)) U ∂fullSpatialPatchDesign d (3+j)) ≤
      cardinalGeometryFactorialConstant d q B C a rho Cs * eta^4*N^(-(d : ℝ))*mu^2 := by
  let f := fun r => poissonCountWeight ((3*Cs)*mu) r *
    (cardinalAliasSpatialComponent d r bd a eta (matchedCardinalTargetCutoff d (r-2) N mu) +
      cardinalTaylorSpatialComponent d r q bd C a rho eta)
  have hf r : 0 ≤ f r := by
    dsimp [f]
    have h := poissonCountWeight_nonneg (by positivity : 0 ≤ (3*Cs)*mu) r
    have : 0 ≤ cardinalDefectSquareBudget d r (matchedCardinalTargetCutoff d (r-2) N mu) := by
      have hT : 1 ≤ matchedCardinalTargetCutoff d (r-2) N mu := le_max_left _ _
      have : 0 ≤ 1+Real.log (matchedCardinalTargetCutoff d (r-2) N mu) := by
        linarith only [Real.log_nonneg hT]
      unfold cardinalDefectSquareBudget
      unfold spatialUnaryIntegralConstant
      positivity
    unfold cardinalAliasSpatialComponent cardinalTaylorSpatialComponent
      cardinalRawAliasCoefficient cardinalRawTaylorCoefficient spatialScaleIntegralConstant
    positivity
  have hmajor : (∑ j ∈ Finset.range (D-2), poissonCountWeight (Cs*mu) (3+j) *
      ∫ U, cardinalGeometryEnvelope (d := d) (n := 3+j) (F := F) q bd C a rho eta
        (max 1 (higherBandTargetScale d (3+j) N mu)) U ∂fullSpatialPatchDesign d (3+j)) ≤
        ∑ j ∈ Finset.range (D-2), f (3+j) := by
    apply Finset.sum_le_sum
    intro j _
    have hi := (cardinalGeometryEnvelope_integrable_and_le (d := d) (n := 3+j) (F := F)
      hd (by omega) q bd C a rho eta (T := max 1 (higherBandTargetScale d (3+j) N mu))
        (le_max_left _ _)).2
    have h := mul_le_mul_of_nonneg_left hi (poissonCountWeight_nonneg (by positivity : 0 ≤ Cs*mu) (3+j))
    rw [cardinalRawSpatialEnergyBudget_split, higherBandTargetScale_max_eq_matched (by omega)] at h
    rw [higherBandTargetScale_max_eq_matched (by omega)]
    convert h using 1
    try dsimp [f]
    rw [← mul_assoc, poissonCountWeight_mul_pow]
    congr 2
    ring
  have h_finite_refined_sum_le_start_two : (∑ j ∈ Finset.range (D-2), f (3+j)) ≤
      ∑ j ∈ Finset.range (D-1), f (2+j) := by
    apply Finset.sum_le_sum_of_injOn (fun j => j+1)
    · intro i _ j _ hij
      change i+1=j+1 at hij
      omega
    · intro j hj
      obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hj
      simp only [Finset.mem_range] at hi ⊢
      omega
    · intro j _
      exact le_of_eq (by congr 1; omega)
    · intro j _ _
      exact hf _
  apply (hmajor.trans h_finite_refined_sum_le_start_two).trans
  dsimp [f]
  simp_rw [show ∀ j, 2+j-2=j from fun j => by omega, mul_add]
  rw [Finset.sum_add_distrib]
  have hA := finite_cardinal_interpolation_budget_le hbd hbdB (by omega : 0 < d)
    (D-1) a eta (3*Cs) ha (by positivity) hN hmu hmuH
  have hT := finite_cardinal_taylor_budget_le hbd hbdB d q (D-1) C a rho eta (3*Cs)
    (by positivity) (lt_of_lt_of_le zero_lt_one hN) hmu.le hmu1 hTaylor
  exact (add_le_add hA hT).trans_eq (by unfold cardinalGeometryFactorialConstant; ring)
theorem finite_fine_field_geometry_budget_le  [NeZero d] (hd : 5 ≤ d) (hD : 3 ≤ D)
     (haD : 0 < aD) (had : aD ≤ ad) (hbd : bd ≤ bD)
    (hab : ad < bd) (htau : exteriorTau ((ad+bd)/(bd-ad)) ≤ c0)
    (M q C a rho eta ell N Cs mu) (hell : 0 < ell)
    (hCs : 0 ≤ Cs) (hmu : 0 ≤ mu) (hmu1 : mu ≤ 1) :
    (∑ j ∈ Finset.range (D-2), poissonCountWeight (Cs*mu) (3+j) *
      ∫ U, fineFieldGeometryEnvelope (d := d) (n := 3+j) ad bd ell N M q C a rho eta U
        ∂fullSpatialPatchDesign d (3+j)) ≤
      finePairFieldFactorialConstant d q aD bD C a rho c0 (3*Cs) * eta^4 *
        Real.exp (2*exteriorTau ((ad+bd)/(bd-ad))*M) * (ell^(2-(d : ℝ)))^2 * mu^4 := by
  let f := fun r => poissonCountWeight (Cs*mu) r *
    ∫ U, fineFieldGeometryEnvelope (d := d) (n := r) ad bd ell N M q C a rho eta U
      ∂fullSpatialPatchDesign d r
  have h_finite_refined_sum_eq_start_four : (∑ j ∈ Finset.range (D-2), f (3+j)) =
      ∑ j ∈ Finset.range (D-3), f (4+j) := by
    have hf3 : f 3 = 0 := (by simp [f, fineFieldGeometryEnvelope_count_three])
    rw [show D-2=(D-3)+1 by omega, Finset.sum_range_succ']
    simp only [add_zero, hf3, add_zero]
    apply Finset.sum_congr rfl
    intro j _
    congr 1
    omega
  rw [h_finite_refined_sum_eq_start_four]
  have hmajor : (∑ j ∈ Finset.range (D-3), f (4+j)) ≤
      ∑ j ∈ Finset.range (D-3), poissonCountWeight ((3*Cs)*mu) (4+j) *
        finePairEvenActionSpatialBudget d (4+j) M q ad bd C a rho eta ell := by
    apply Finset.sum_le_sum
    intro j _
    have h := mul_le_mul_of_nonneg_left
      (fineFieldGeometryEnvelope_integrable_and_le (d := d) (n := 4+j) (by omega)
        ad bd ell N hell M q C a rho eta).2
      (poissonCountWeight_nonneg (by positivity : 0 ≤ Cs*mu) (4+j))
    convert h using 1
    try dsimp [f]
    rw [← mul_assoc, poissonCountWeight_mul_pow]
    congr 2
    ring
  have hCs : 0 ≤ (3*Cs) := (by positivity)
  let P := finePairUniformSpatialPrefactor d q aD bD C a rho c0 * eta^4 *
    Real.exp (2*exteriorTau ((ad+bd)/(bd-ad))*M) * (ell^(2-(d : ℝ)))^2
  have hP : 0 ≤ P := by dsimp [P]; positivity [finePairUniformSpatialPrefactor_nonneg d q aD bD C a rho c0]
  have h := finite_polynomial_field_count_tail_le hP hCs (finePairFieldGeometricBase_nonneg d bD)
    hmu hmu1 12 (D-3) (fun n => finePairEvenActionSpatialBudget d n M q ad bd C a rho eta ell)
    (fun j _ => (finePairEvenActionSpatialBudget_uniform_geometric_le haD had hbd hab htau d (4+j) M q C a rho eta ell).trans_eq
      (by dsimp [P]; ring))
  exact hmajor.trans (by exact h.trans_eq (by unfold finePairFieldFactorialConstant; dsimp [P]; ring))
theorem finite_fine_pair_alias_geometry_budget_le {d D : ℕ} [NeZero d] (hd : 5 ≤ d)
     (haD : 0 < aD) (had : aD ≤ ad) (hbd : bd ≤ bD)
    (hab : ad < bd) (htau : exteriorTau ((ad+bd)/(bd-ad)) ≤ c0)
    (hc0 : 0 ≤ c0) (hK : 0 ≤ K) (M q : ℕ) (C a rho eta ell N Cs mu : ℝ)
    (hN : 0 < N) (hell : ell=N*Real.exp (-c0*D)) (hell1 : 1 ≤ ell)
    (hellN : ell ≤ N) (hDM : (D : ℝ) ≤ K*M)
    (hCs : 0 ≤ Cs) (hmu : 0 ≤ mu) (hmu1 : mu ≤ 1) :
    (∑ j ∈ Finset.range (D-2), poissonCountWeight (Cs*mu) (3+j) *
      (if M<3+j then ∫ U, finePairAliasGeometryEnvelope (d := d) (n := 3+j)
        ad bd ell N M q C a rho eta U ∂fullSpatialPatchDesign d (3+j) else 0)) ≤
      finePairSaddleAliasFactorialConstant d q aD bD C a rho c0 K (3*Cs) *
        (eta^4*N^(4-(d : ℝ))) *
          poissonCountWeight (finePairSaddleAliasFactorialConstant d q aD bD C a rho c0 K (3*Cs)*mu) (M+1) := by
  let f := fun r => poissonCountWeight ((3*Cs)*mu) r *
    finePairAliasActionSpatialBudget d r M q ad bd C a rho eta ell
  have hf (r : ℕ) : 0 ≤ f r := by
    dsimp [f, finePairAliasActionSpatialBudget]
    have h := poissonCountWeight_nonneg (by positivity : 0 ≤ (3*Cs)*mu) r
    have hK := spatialInverseFourConstant_nonneg d
    positivity
  have hmajor : (∑ j ∈ Finset.range (D-2), poissonCountWeight (Cs*mu) (3+j) *
      (if M<3+j then ∫ U, finePairAliasGeometryEnvelope (d := d) (n := 3+j)
        ad bd ell N M q C a rho eta U ∂fullSpatialPatchDesign d (3+j) else 0)) ≤
      ∑ j ∈ Finset.range (D-2), if M<3+j then f (3+j) else 0 := by
    apply Finset.sum_le_sum
    intro j _
    by_cases hMj : M<3+j
    · simp only [if_pos hMj]
      have h := mul_le_mul_of_nonneg_left
        (finePairAliasGeometryEnvelope_integrable_and_le (d := d) (n := 3+j) (by omega)
          ad bd ell N (lt_of_lt_of_le zero_lt_one hell1) hellN M q C a rho eta).2
        (poissonCountWeight_nonneg (by positivity : 0 ≤ Cs*mu) (3+j))
      convert h using 1
      dsimp [f]
      rw [← mul_assoc, poissonCountWeight_mul_pow]
      congr 2
      ring
    · simp only [if_neg hMj, mul_zero, le_refl]
  apply (hmajor.trans (finite_refined_gated_sum_le_tail D M f hf)).trans
  exact finite_fine_pair_saddle_alias_budget_le (by omega) haD had hbd hab htau hc0 hK M D q (D-M)
    C a rho eta ell N (3*Cs) mu hN hell hDM (by positivity) hmu hmu1
end
variable {d D : ℕ} {s ad bd : ℝ}
def ordinaryFineAliasSaddleCoefficient (s : ℝ) (d : ℕ) (ad bd : ℝ) : ℝ :=
  lowerSaddleCoefficient s d (densityIntervalExponent ad bd)
def ordinaryFineAliasSaddleTheta (s : ℝ) (d : ℕ) (ad bd : ℝ) : ℝ :=
  lowerSaddleTheta s d (densityIntervalExponent ad bd)
def ordinaryFineAliasSaddleTargetBound (s : ℝ) (d : ℕ) (ad bd : ℝ) : ℕ :=
  lowerAliasFineTargetBound d (ordinaryFineAliasSaddleTheta s d ad bd) (densityIntervalExponent ad bd+1)
def ordinaryFineAliasSaddleTailPrefactor (s : ℝ) (d q : ℕ) (ad bd C a rho : ℝ) : ℝ :=
  ordinaryAliasFamilySpatialPrefactor d q (ordinaryFineAliasSaddleTargetBound s d ad bd)
    ad bd (densityIntervalExponent ad bd+1) C a rho
def ordinaryFineAliasSaddleTailExponent (s : ℝ) (d : ℕ) (ad bd : ℝ) : ℝ :=
  lowerAliasSpatialFixedL d (ordinaryFineAliasSaddleTheta s d ad bd) (densityIntervalExponent ad bd+1)
def ordinaryFineAliasFactorialConstant (s : ℝ) (d q : ℕ) (ad bd C a rho Csharp : ℝ) : ℝ :=
  aliasTailConstant (ordinaryFineAliasSaddleTailPrefactor s d q ad bd C a rho)
    Csharp (ordinaryAliasSpatialResponseBase d bd) (ordinaryFineAliasSaddleTailExponent s d ad bd)
theorem ordinaryFineAliasFactorialConstant_ge_one {s ad bd C a rho Csharp : ℝ} 
    (hbd : 0 ≤ bd) (hCs : 0 ≤ Csharp) :
    1 ≤ ordinaryFineAliasFactorialConstant s d q ad bd C a rho Csharp := by
  exact aliasTailConstant_ge_one (ordinaryAliasFamilySpatialPrefactor_nonneg _ _ _ _ _ _ _ _ _)
    hCs (by unfold ordinaryAliasSpatialResponseBase ordinaryAliasSpatialCountBase; positivity)
def ordinaryFineAliasSaddleGeometryEnvelope (s : ℝ) (d q : ℕ)
    (ad bd Cw cf C a rho x : ℝ) (n F : ℕ) (U : Fin n → Covariate d) : ℝ :=
  let m := ordinaryFineAliasSaddleCoefficient s d ad bd
  let theta := ordinaryFineAliasSaddleTheta s d ad bd
  let c0 := densityIntervalExponent ad bd+1
  let M := lowerSaddleM m x
  let D := lowerSaddleD d m x
  let N := lowerSaddleN s d m theta Cw (shrunkDensityExponent ad bd) x
  let mu := lowerSaddleMu d m theta Cw x
  let L := lowerAliasCutoff s d m theta Cw c0 (shrunkDensityExponent ad bd) x
  let eta := lowerSaddleEta s d m theta Cw cf x
  ordinaryFineAliasFamilyResponseSquareEnvelope (F := F) (ordinaryFineAliasTargetSet d D L N mu)
    M (ordinaryFineAliasSaddleTargetBound s d ad bd) q ad bd c0 C a rho eta L (fun r => higherBandTargetScale d r N mu) U
theorem eventually_ordinaryFineAliasSaddleGeometryEnvelope_factorial_tail
      (hs : 1 < s) (hd : 4*s < (d : ℝ))
    (haD : 0 < ad) (hab : ad < bd) (Cw cf : ℝ) (q : ℕ)
    (C a rho Csharp : ℝ) (hCs : 0 ≤ Csharp) :
    ∀ᶠ x in atTop,
      let m := ordinaryFineAliasSaddleCoefficient s d ad bd
      let theta := ordinaryFineAliasSaddleTheta s d ad bd
      let M := lowerSaddleM m x
      let D := lowerSaddleD d m x
      let N := lowerSaddleN s d m theta Cw (shrunkDensityExponent ad bd) x
      let mu := lowerSaddleMu d m theta Cw x
      let eta := lowerSaddleEta s d m theta Cw cf x
      let C6 := ordinaryFineAliasFactorialConstant s d q ad bd C a rho Csharp
      ∀ F : ℕ → ℕ,
        (∑ j ∈ Finset.range (D-M), poissonCountWeight (Csharp*mu) (M+1+j) *
          (∫ U, ordinaryFineAliasSaddleGeometryEnvelope s d q ad bd Cw cf C a rho x
            (M+1+j) (F (M+1+j)) U ∂fullSpatialPatchDesign d (M+1+j))) ≤
        C6 * (eta^4 * Real.exp (2*shrunkDensityExponent ad bd M*M) * N^(4-(d : ℝ))) *
          poissonCountWeight (C6*mu) (M+1) := by
  let tau := densityIntervalExponent ad bd
  let m := ordinaryFineAliasSaddleCoefficient s d ad bd
  let theta := ordinaryFineAliasSaddleTheta s d ad bd
  have htau : 0 < tau := densityIntervalExponent_pos haD hab
  have hm : 0 < m := lowerSaddleCoefficient_pos hs hd htau
  have htheta : 0 < theta := lowerSaddleTheta_pos hs hd htau
  have hd0 : (0 : ℝ)<d := by linarith
  have h : (4 : ℝ)<d := by linarith
  have h' : 4<d := by exact_mod_cast h
  have h_eventually_ordinaryFineAliasSaddleGeometryEnvelope_integrable_and_scale_le : ∀ᶠ x in atTop, ∀ (n F : ℕ),
      Integrable (ordinaryFineAliasSaddleGeometryEnvelope s d q ad bd Cw cf C a rho x n F)
        (fullSpatialPatchDesign d n) ∧
      (∫ U, ordinaryFineAliasSaddleGeometryEnvelope s d q ad bd Cw cf C a rho x n F U
        ∂fullSpatialPatchDesign d n) ≤
        ordinaryFineAliasSaddleTailPrefactor s d q ad bd C a rho *
          (lowerSaddleEta s d (ordinaryFineAliasSaddleCoefficient s d ad bd)
            (ordinaryFineAliasSaddleTheta s d ad bd) Cw cf x)^4 *
          Real.exp (2*shrunkDensityExponent ad bd
            (lowerSaddleM (ordinaryFineAliasSaddleCoefficient s d ad bd) x)*
            (lowerSaddleM (ordinaryFineAliasSaddleCoefficient s d ad bd) x)) *
          (lowerSaddleN s d (ordinaryFineAliasSaddleCoefficient s d ad bd)
            (ordinaryFineAliasSaddleTheta s d ad bd) Cw (shrunkDensityExponent ad bd) x)^(4-(d : ℝ)) *
          Real.exp (ordinaryFineAliasSaddleTailExponent s d ad bd*
            (lowerSaddleM (ordinaryFineAliasSaddleCoefficient s d ad bd) x)) *
          (ordinaryAliasSpatialResponseBase d bd)^n := by
    filter_upwards [eventually_ordinaryFineAlias_saddle_guards hs hd haD hab Cw] with x G
    intro n F
    have hLT : ∀ r ∈ ordinaryFineAliasTargetSet d
        (lowerSaddleD d (ordinaryFineAliasSaddleCoefficient s d ad bd) x)
        (lowerAliasCutoff s d (ordinaryFineAliasSaddleCoefficient s d ad bd)
          (ordinaryFineAliasSaddleTheta s d ad bd) Cw (densityIntervalExponent ad bd+1) (shrunkDensityExponent ad bd) x)
        (lowerSaddleN s d (ordinaryFineAliasSaddleCoefficient s d ad bd)
          (ordinaryFineAliasSaddleTheta s d ad bd) Cw (shrunkDensityExponent ad bd) x)
        (lowerSaddleMu d (ordinaryFineAliasSaddleCoefficient s d ad bd)
          (ordinaryFineAliasSaddleTheta s d ad bd) Cw x),
        lowerAliasCutoff s d (ordinaryFineAliasSaddleCoefficient s d ad bd)
          (ordinaryFineAliasSaddleTheta s d ad bd) Cw (densityIntervalExponent ad bd+1) (shrunkDensityExponent ad bd) x ≤
        higherBandTargetScale d r
          (lowerSaddleN s d (ordinaryFineAliasSaddleCoefficient s d ad bd)
            (ordinaryFineAliasSaddleTheta s d ad bd) Cw (shrunkDensityExponent ad bd) x)
          (lowerSaddleMu d (ordinaryFineAliasSaddleCoefficient s d ad bd)
            (ordinaryFineAliasSaddleTheta s d ad bd) Cw x) := fun r hr => (Finset.mem_filter.mp hr).2.2.le
    exact ordinaryFineAliasFamilyResponseSquareEnvelope_integrable_and_scale_le G.dimension _ G.targets
      ad bd _ C a rho _ _ _ _ (haD.trans hab).le (Nat.cast_nonneg _) (by positivity)
      (by linarith [densityIntervalExponent_pos haD hab]) G.degree (lowerSaddleN_positive _ _ _ _ _ _ _)
      G.cutoff G.logarithm _ hLT q
  filter_upwards [h_eventually_ordinaryFineAliasSaddleGeometryEnvelope_integrable_and_scale_le,
    (lowerSaddleMu_tends_zero hd0 hm htheta Cw).eventually (gt_mem_nhds (by norm_num : (0 : ℝ)<1)),
    eventually_gt_atTop (0 : ℝ)] with x henergy hmu1 hx
  dsimp only
  intro F
  let M := lowerSaddleM m x
  let D := lowerSaddleD d m x
  let N := lowerSaddleN s d m theta Cw (shrunkDensityExponent ad bd) x
  let mu := lowerSaddleMu d m theta Cw x
  let eta := lowerSaddleEta s d m theta Cw cf x
  let A := ordinaryFineAliasSaddleTailPrefactor s d q ad bd C a rho
  let L := ordinaryFineAliasSaddleTailExponent s d ad bd
  let B := ordinaryAliasSpatialResponseBase d bd
  let P := eta^4 * Real.exp (2*shrunkDensityExponent ad bd M*M) * N^(4-(d : ℝ))
  have hmu0 : 0 ≤ mu := by dsimp [mu]; rw [lowerSaddleMu_eq_exp hx]; positivity
  have hA : 0 ≤ A := ordinaryAliasFamilySpatialPrefactor_nonneg _ _ _ _ _ _ _ _ _
  have hP : 0 ≤ P := by
    dsimp [P]
    exact mul_nonneg (mul_nonneg (by positivity) (Real.exp_pos _).le)
      (Real.rpow_nonneg (lowerSaddleN_positive _ _ _ _ _ _ _).le _)
  have hB : 0 ≤ B := by unfold B ordinaryAliasSpatialResponseBase ordinaryAliasSpatialCountBase; positivity
  have h_lowerAliasSpatialFixedL_nonneg {c0 : ℝ} (θ : ℝ) (hc0 : 0 ≤ c0) : 0 ≤ lowerAliasSpatialFixedL d θ c0 := lowerAliasSpatialL_nonneg (by omega) hc0 (by positivity)
  have hL : 0 ≤ L := (h_lowerAliasSpatialFixedL_nonneg _ (by linarith))
  apply finite_alias_energy_tail_le hA hP hCs hB hL hmu0 hmu1.le M (D-M)
    (fun n => ∫ U, ordinaryFineAliasSaddleGeometryEnvelope s d q ad bd Cw cf C a rho x
      n (F n) U ∂fullSpatialPatchDesign d n)
  intro j hj
  convert ((henergy (M+1+j) (F (M+1+j))).2) using 1 <;> simp only [A, P, L, B, m, theta, M, N, eta, ordinaryFineAliasSaddleTailPrefactor, ordinaryFineAliasSaddleTailExponent, ordinaryFineAliasSaddleTargetBound, ordinaryFineAliasSaddleCoefficient, ordinaryFineAliasSaddleTheta] <;> ring
theorem completeSourceHigherGeometryEnvelope_integral_eq {d r D : ℕ} [NeZero d]
    (hd : 5 ≤ d) (hr : 2 ≤ r) (aD bD c0 ell N mu : ℝ) (M R q : ℕ)
    (C a rho eta : ℝ) (hell : 1 ≤ ell) (hellN : ell ≤ N) :
    (∫ U, completeSourceHigherGeometryEnvelope (d := d) (n := r) (D := D)
      aD bD c0 ell N mu M R q C a rho eta U ∂fullSpatialPatchDesign d r) =
      4*((∫ U, cardinalGeometryEnvelope (d := d) (n := r) (F := D) q (bD-(M : ℝ)⁻¹) C a rho eta
          (max 1 (higherBandTargetScale d r N mu)) U ∂fullSpatialPatchDesign d r) +
        (if M<r then ∫ U, ordinaryFineAliasFamilyResponseSquareEnvelope (F := D)
          (ordinaryFineAliasTargetSet d D ell N mu) M R q aD bD c0 C a rho eta ell
          (fun t => higherBandTargetScale d t N mu) U ∂fullSpatialPatchDesign d r else 0) +
        (if M<r then ∫ U, finePairAliasGeometryEnvelope (d := d) (n := r)
          (aD+(M : ℝ)⁻¹) (bD-(M : ℝ)⁻¹) ell N M q C a rho eta U ∂fullSpatialPatchDesign d r else 0) +
        (∫ U, fineFieldGeometryEnvelope (d := d) (n := r)
          (aD+(M : ℝ)⁻¹) (bD-(M : ℝ)⁻¹) ell N M q C a rho eta U ∂fullSpatialPatchDesign d r)) := by
  have hA := (cardinalGeometryEnvelope_integrable_and_le (d := d) (n := r) (F := D) hd hr q
    (bD-(M : ℝ)⁻¹) C a rho eta (T := max 1 (higherBandTargetScale d r N mu)) (le_max_left _ _)).1
  have hB := ordinaryFineAliasFamilyResponseSquareEnvelope_integrable (d := d) (n := r) (F := D) hd
    (ordinaryFineAliasTargetSet d D ell N mu) M R q aD bD c0 C a rho eta ell
    (fun t => higherBandTargetScale d t N mu) hell (fun t ht => by
      have h := (Finset.mem_filter.mp ht).2
      exact ⟨by omega,h.2.le⟩)
  have hP := (finePairAliasGeometryEnvelope_integrable_and_le (d := d) (n := r) (by omega)
    (aD+(M : ℝ)⁻¹) (bD-(M : ℝ)⁻¹) ell N (lt_of_lt_of_le zero_lt_one hell) hellN M q C a rho eta).1
  have hF := (fineFieldGeometryEnvelope_integrable_and_le (d := d) (n := r) (by omega)
    (aD+(M : ℝ)⁻¹) (bD-(M : ℝ)⁻¹) ell N (lt_of_lt_of_le zero_lt_one hell) M q C a rho eta).1
  unfold completeSourceHigherGeometryEnvelope
  by_cases hMr : M<r
  · simp only [if_pos hMr]
    rw [integral_const_mul]
    have h1 := integral_add ((hA.add hB).add hP) hF
    have h2 := integral_add (hA.add hB) hP
    have h3 := integral_add hA hB
    simp only [Pi.add_apply] at h1 h2 h3
    rw [h1,h2,h3]
  · simp only [if_neg hMr,add_zero]
    rw [integral_const_mul,integral_add hA hF]
theorem finite_complete_higher_geometry_energy_le  [NeZero d]
    (hd : 5 ≤ d) (hD : 3 ≤ D) (aD bD c0 K ell N mu : ℝ) (M R q : ℕ)
    (C a rho eta Cs Eord : ℝ) (haD : 0 < aD) (ha : 0 < a)
    (hshrink : aD+(M : ℝ)⁻¹ < bD-(M : ℝ)⁻¹)
    (htau : exteriorTau (((aD+(M : ℝ)⁻¹)+(bD-(M : ℝ)⁻¹))/
      ((bD-(M : ℝ)⁻¹)-(aD+(M : ℝ)⁻¹))) ≤ c0)
    (hc0 : 0 ≤ c0) (hK : 0 ≤ K) (hCs : 0 ≤ Cs)
    (hell : 1 ≤ ell) (hellN : ell ≤ N) (hcut : ell=N*Real.exp (-c0*D))
    (hDM : (D : ℝ) ≤ K*M) (hmu : 0 < mu) (hmu1 : mu ≤ 1)
    (hmuH : mu*(1+Real.log N) ≤ 1) (hTaylor : eta^(4*q)*N^d ≤ 1)
    (hfield : Real.exp (2*exteriorTau (((aD+(M : ℝ)⁻¹)+(bD-(M : ℝ)⁻¹))/
        ((bD-(M : ℝ)⁻¹)-(aD+(M : ℝ)⁻¹)))*M) * (ell^(2-(d : ℝ)))^2 * mu^4 ≤
        mu^2*N^(-(d : ℝ)))
    (hord : (∑ j ∈ Finset.range (D-M), poissonCountWeight (Cs*mu) (M+1+j) *
      ∫ U, ordinaryFineAliasFamilyResponseSquareEnvelope (d := d) (n := M+1+j) (F := D)
        (ordinaryFineAliasTargetSet d D ell N mu) M R q aD bD c0 C a rho eta ell
        (fun t => higherBandTargetScale d t N mu) U ∂fullSpatialPatchDesign d (M+1+j)) ≤ Eord) :
    (∑ j ∈ Finset.range (D-2), poissonCountWeight (Cs*mu) (3+j) *
      ∫ U, completeSourceHigherGeometryEnvelope (d := d) (n := 3+j) (D := D)
        aD bD c0 ell N mu M R q C a rho eta U ∂fullSpatialPatchDesign d (3+j)) ≤
      4*(cardinalGeometryFactorialConstant d q bD C a rho Cs*eta^4*N^(-(d : ℝ))*mu^2 + Eord +
        finePairSaddleAliasFactorialConstant d q aD bD C a rho c0 K (3*Cs) *
          (eta^4*N^(4-(d : ℝ))) *
          poissonCountWeight (finePairSaddleAliasFactorialConstant d q aD bD C a rho c0 K (3*Cs)*mu) (M+1) +
        finePairFieldFactorialConstant d q aD bD C a rho c0 (3*Cs)*eta^4*mu^2*N^(-(d : ℝ))) := by
  have hN  := hell.trans hellN
  have had : aD ≤ aD+(M : ℝ)⁻¹ := le_add_of_nonneg_right
    (inv_nonneg.mpr (Nat.cast_nonneg M))
  have hbd : bD-(M : ℝ)⁻¹ ≤ bD := by linarith [inv_nonneg.mpr (Nat.cast_nonneg M : (0 : ℝ) ≤ M)]
  have hA := finite_cardinal_geometry_budget_le (D := D) (F := D) hd ((haD.trans_le had).le.trans hshrink.le) hbd q C a rho eta Cs ha hCs hN hmu hmu1 hmuH hTaylor
  have hP := finite_fine_pair_alias_geometry_budget_le (D := D) hd haD had hbd hshrink htau hc0 hK M q
    C a rho eta ell N Cs mu (lt_of_lt_of_le zero_lt_one hN) hcut hell hellN hDM hCs hmu.le hmu1
  have hF := finite_fine_field_geometry_budget_le (D := D) hd hD haD had hbd hshrink htau M q C a rho eta
    ell N Cs mu (lt_of_lt_of_le zero_lt_one hell) hCs hmu.le hmu1
  have hFconst : 0 ≤ finePairFieldFactorialConstant d q aD bD C a rho c0 (3*Cs) := by
    unfold finePairFieldFactorialConstant fieldTailConstant
    have hPre := finePairUniformSpatialPrefactor_nonneg d q aD bD C a rho c0
    have hP4 := poissonCountWeight_nonneg (by positivity [finePairFieldGeometricBase_nonneg d bD] :
      0 ≤ (3*Cs)*(finePairFieldGeometricBase d bD*2^12)) 4
    positivity
  have hFs := mul_le_mul_of_nonneg_left hfield
    (mul_nonneg hFconst (by positivity : 0 ≤ eta^4))
  have hFfinal : (∑ j ∈ Finset.range (D-2), poissonCountWeight (Cs*mu) (3+j) *
      ∫ U, fineFieldGeometryEnvelope (d := d) (n := 3+j)
        (aD+(M : ℝ)⁻¹) (bD-(M : ℝ)⁻¹) ell N M q C a rho eta U ∂fullSpatialPatchDesign d (3+j)) ≤
      finePairFieldFactorialConstant d q aD bD C a rho c0 (3*Cs)*eta^4*mu^2*N^(-(d : ℝ)) :=
    hF.trans (by convert hFs using 1 <;> ring)
  let f := fun r => poissonCountWeight (Cs*mu) r *
    ∫ U, ordinaryFineAliasFamilyResponseSquareEnvelope (d := d) (n := r) (F := D)
      (ordinaryFineAliasTargetSet d D ell N mu) M R q aD bD c0 C a rho eta ell
      (fun t => higherBandTargetScale d t N mu) U ∂fullSpatialPatchDesign d r
  have hf (r : ℕ) : 0 ≤ f r := mul_nonneg (poissonCountWeight_nonneg (mul_nonneg hCs hmu.le) r)
    (integral_nonneg (fun U => ordinaryFineAliasFamilyResponseSquareEnvelope_nonneg _ _ _ _ _ _ _ _ _ _ _ _ _ U))
  have heq : (∑ j ∈ Finset.range (D-2), poissonCountWeight (Cs*mu) (3+j) *
      ∫ U, completeSourceHigherGeometryEnvelope (d := d) (n := 3+j) (D := D)
        aD bD c0 ell N mu M R q C a rho eta U ∂fullSpatialPatchDesign d (3+j)) =
      4*((∑ j ∈ Finset.range (D-2), poissonCountWeight (Cs*mu) (3+j) *
        ∫ U, cardinalGeometryEnvelope (d := d) (n := 3+j) (F := D) q (bD-(M : ℝ)⁻¹) C a rho eta
          (max 1 (higherBandTargetScale d (3+j) N mu)) U ∂fullSpatialPatchDesign d (3+j)) +
        (∑ j ∈ Finset.range (D-2), if M<3+j then f (3+j) else 0) +
        (∑ j ∈ Finset.range (D-2), poissonCountWeight (Cs*mu) (3+j) *
          (if M<3+j then ∫ U, finePairAliasGeometryEnvelope (d := d) (n := 3+j)
            (aD+(M : ℝ)⁻¹) (bD-(M : ℝ)⁻¹) ell N M q C a rho eta U ∂fullSpatialPatchDesign d (3+j) else 0)) +
        (∑ j ∈ Finset.range (D-2), poissonCountWeight (Cs*mu) (3+j) *
          ∫ U, fineFieldGeometryEnvelope (d := d) (n := 3+j)
            (aD+(M : ℝ)⁻¹) (bD-(M : ℝ)⁻¹) ell N M q C a rho eta U ∂fullSpatialPatchDesign d (3+j))) := by
    have hInt (j : ℕ) := completeSourceHigherGeometryEnvelope_integral_eq (d := d) (r := 3+j) (D := D)
      hd (by omega) aD bD c0 ell N mu M R q C a rho eta hell hellN
    simp_rw [hInt]
    try dsimp [f]
    have halg (w A B P F : ℝ) : w*(4*(A+B+P+F))=4*(w*A+w*B+w*P+w*F) := by ring
    simp_rw [halg,mul_ite,mul_zero]
    rw [←Finset.mul_sum]
    simp only [Finset.sum_add_distrib]
  rw [heq]
  exact mul_le_mul_of_nonneg_left (add_le_add (add_le_add (add_le_add hA ((finite_refined_gated_sum_le_tail D M f hf).trans hord)) hP) hFfinal) (by norm_num)
def completeGeometryExteriorConstant (d : ℕ) (Cs Chi : ℝ) : ℝ :=
  max 1 (Cs * (3*2^d*Chi^2))
theorem completeGeometryExteriorConstant_pos (d Cs Chi) :
    0 < completeGeometryExteriorConstant d Cs Chi :=
  zero_lt_one.trans_le (le_max_left _ _)
theorem completeSourceGeometryEnvelope_exterior_integral_of_three_le 
    (D M R q n ) (h3 : 3 ≤ n) (hn : D < n)
    (aD bD c0 ell N mu C a rho eta Chi Bl ) :
    (∫ U, completeSourceGeometryEnvelope (d := d) D M R q aD bD c0 ell N mu C a rho eta Chi Bl n U
      ∂fullSpatialPatchDesign d n) = (3*2^d*Chi^2)^n*eta^4*(Bl+1)^2 := by
  rcases n with _|_|_|n
  · omega
  · omega
  · omega
  · simp only [completeSourceGeometryEnvelope, if_neg (not_le.mpr hn), integral_const,
      fullSpatialPatchDesign_real_univ, smul_eq_mul]
    rw [pow_mul, mul_pow]
    ring
def completeGeometryRadialConstant (d : ℕ) (B a rho Cs : ℝ) : ℝ :=
  27*Cs^2*B^4*((2*rho+a)/a^2)^4*2^d*spatialExponentialConstant d
def completeGeometryDefectConstant (d q : ℕ) (B C a rho Cs : ℝ) : ℝ :=
  1+|completeGeometryRadialConstant d B a rho Cs|+
    4*|cardinalGeometryFactorialConstant d q B C a rho Cs|
def completeGeometryFieldConstant (d q : ℕ) (aD bD C a rho c0 Cs : ℝ) : ℝ :=
  1+4*|finePairFieldFactorialConstant d q aD bD C a rho c0 (3*Cs)|
def completeGeometryAliasConstant (d q : ℕ) (aD bD C a rho c0 K Cs Cord : ℝ) : ℝ :=
  1+4*|Cord|+4*|finePairSaddleAliasFactorialConstant d q aD bD C a rho c0 K (3*Cs)|
theorem completeGeometryDefectConstant_pos (d q B C a rho Cs) :
    0 < completeGeometryDefectConstant d q B C a rho Cs := by
  unfold completeGeometryDefectConstant
  positivity
theorem completeGeometryFieldConstant_pos (d q aD bD C a rho c0 Cs) :
    0 < completeGeometryFieldConstant d q aD bD C a rho c0 Cs := by
  unfold completeGeometryFieldConstant
  positivity
theorem completeGeometryAliasConstant_pos (d q aD bD C a rho c0 K Cs Cord) :
    0 < completeGeometryAliasConstant d q aD bD C a rho c0 K Cs Cord := by
  unfold completeGeometryAliasConstant
  positivity
theorem four_component_raw_energy_algebra {mu Pdef Pal Plo A2 Ad Ao Ap Af : ℝ}
    (hmu : 0 ≤ mu) (hPd : 0 ≤ Pdef) (hPal : 0 ≤ Pal) (hPlo : 0 ≤ Plo)
    (hPloPal : Plo ≤ Pal) (hAo : 0 ≤ Ao) (hAp : 0 ≤ Ap) (M ) :
    A2*Pdef+4*(Ad*Pdef+Ao*Pal*poissonCountWeight (Ao*mu) (M+1)+
      Ap*Plo*poissonCountWeight (Ap*mu) (M+1)+Af*Pdef) ≤
      3*((1+|A2|+4*|Ad|)+(1+4*|Af|))*Pdef+
      3*(1+4*|Ao|+4*|Ap|)*Pal*poissonCountWeight ((1+4*|Ao|+4*|Ap|)*mu) (M+1) := by
  let C6 := 1+4*|Ao|+4*|Ap|
  have hC6 : 0 ≤ C6 := by dsimp [C6]; positivity
  have hAoC : Ao ≤ C6 := by
    linarith only [le_abs_self Ao,abs_nonneg Ao,abs_nonneg Ap]
  have hApC : Ap ≤ C6 := by
    linarith only [le_abs_self Ap,abs_nonneg Ao,abs_nonneg Ap]
  have hoW := poissonCountWeight_mono (mul_nonneg hAo hmu)
    (mul_le_mul_of_nonneg_right hAoC hmu) (M+1)
  have hpW := poissonCountWeight_mono (mul_nonneg hAp hmu)
    (mul_le_mul_of_nonneg_right hApC hmu) (M+1)
  have ho := mul_le_mul_of_nonneg_left hoW (mul_nonneg hAo hPal)
  have hpP := mul_le_mul_of_nonneg_left hPloPal hAp
  have hp := mul_le_mul hpP hpW (poissonCountWeight_nonneg (mul_nonneg hAp hmu) _)
    (mul_nonneg hAp hPal)
  have hcoef : 4*(Ao+Ap) ≤ 3*C6 := by
    linarith only [le_abs_self Ao,le_abs_self Ap,abs_nonneg Ao,abs_nonneg Ap]
  have hAli := mul_le_mul_of_nonneg_right hcoef
    (mul_nonneg hPal (poissonCountWeight_nonneg (mul_nonneg hC6 hmu) (M+1)))
  have hDef : A2+4*Ad+4*Af ≤ 3*((1+|A2|+4*|Ad|)+1+4*|Af|) := by
    linarith only [le_abs_self A2,le_abs_self Ad,le_abs_self Af,
      abs_nonneg A2,abs_nonneg Ad,abs_nonneg Af]
  have hd := mul_le_mul_of_nonneg_right hDef hPd
  nlinarith only [ho,hp,hAli,hd]
theorem completeSourceGeometryEnvelope_refined_integral 
    (D M R q j ) (hj : 3+j ≤ D) (aD bD c0 ell N mu C a rho eta Chi Bl ) :
    (∫ U, completeSourceGeometryEnvelope (d := d) D M R q aD bD c0 ell N mu C a rho eta Chi Bl (3+j) U
      ∂fullSpatialPatchDesign d (3+j)) =
      ∫ U, completeSourceHigherGeometryEnvelope (d := d) (n := 3+j) (D := D)
        aD bD c0 ell N mu M R q C a rho eta U ∂fullSpatialPatchDesign d (3+j) := by
  have hcast : 3+j=j+3 := by omega
  rw [hcast] at hj ⊢
  simp only [completeSourceGeometryEnvelope,if_pos hj]
end NearlyMinimax
