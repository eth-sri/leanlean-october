module

public import NearlyMinimax.AliasTailSummation
public import NearlyMinimax.HighUnionRawFisher
public import NearlyMinimax.LowerActivityHierarchy
public import NearlyMinimax.LowerSaddle
public import NearlyMinimax.Model

@[expose] public section

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators Topology ENNReal
namespace NearlyMinimax

attribute [local instance] Classical.propDecidable

-- 1. Finite count partition & factorial energy building blocks
--    (`FiniteCountEnergyAssembly`, `CardinalFactorialEnergy`, `FinePairSaddleFactorialEnergy`,
--     `OrdinaryFineAliasFactorialTail`, `OrdinaryFineAliasSaddleEnvelope`)

section FactorialGeometry
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

private theorem finite_refined_sum_le_start_two (D : ℕ) (f : ℕ → ℝ) (hf : ∀ r, 0 ≤ f r) :
    (∑ j ∈ Finset.range (D - 2), f (3 + j)) ≤ ∑ j ∈ Finset.range (D - 1), f (2 + j) := by
  refine Finset.sum_le_sum_of_injOn (fun j => j + 1) (fun i _ j _ hij => by change i + 1 = j + 1 at hij; omega)
    (fun j hj => ?_) (fun _ _ => le_of_eq (by congr 1; omega)) fun _ _ _ => hf _
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hj
  simp only [Finset.mem_range] at hi ⊢; omega

private theorem finite_refined_gated_sum_le_tail (D M : ℕ) (f : ℕ → ℝ) (hf : ∀ r, 0 ≤ f r) :
    (∑ j ∈ Finset.range (D - 2), if M < 3 + j then f (3 + j) else 0) ≤
      ∑ j ∈ Finset.range (D - M), f (M + 1 + j) := by
  rw [← Finset.sum_filter]
  refine Finset.sum_le_sum_of_injOn (fun j => 3 + j - (M + 1))
    (fun i hi j hj hij => by
      change 3 + i - (M + 1) = 3 + j - (M + 1) at hij
      have := (Finset.mem_filter.mp hi).2; have := (Finset.mem_filter.mp hj).2; omega)
    (fun j hj => ?_)
    (fun j hj => by have := (Finset.mem_filter.mp hj).2; exact le_of_eq (by congr 1; omega))
    fun _ _ _ => hf _
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hj
  rcases Finset.mem_filter.mp hi with ⟨hi, hiM⟩
  simp only [Finset.mem_range] at hi ⊢; omega

private theorem finite_refined_sum_eq_start_four (D : ℕ) (hD : 3 ≤ D) (f : ℕ → ℝ) (hf3 : f 3 = 0) :
    (∑ j ∈ Finset.range (D - 2), f (3 + j)) = ∑ j ∈ Finset.range (D - 3), f (4 + j) := by
  rw [show D - 2 = (D - 3) + 1 by omega, Finset.sum_range_succ']
  simp only [add_zero, hf3]
  exact Finset.sum_congr rfl fun _ _ => by congr 1; omega

private theorem finite_count_energy_from_blocks {x : ℝ} (hx : 0 ≤ x) (n D : ℕ) (hD : 2 ≤ D)
    (e : ℕ → ℝ) (he : ∀ r, 0 ≤ e r) (he0 : e 0 = 0) (he1 : e 1 = 0)
    {E2 Eref Etail : ℝ} (h2 : poissonCountWeight x 2 * e 2 ≤ E2)
    (href : (∑ r ∈ Finset.range (D - 2), poissonCountWeight x (3 + r) * e (3 + r)) ≤ Eref)
    (htail : (∑ r ∈ Finset.range (n + 1), poissonCountWeight x (D + 1 + r) * e (D + 1 + r)) ≤ Etail) :
    (∑ r ∈ Finset.range (n + 1), poissonCountWeight x r * e r) ≤ E2 + Eref + Etail := by
  have hprefix : (∑ r ∈ Finset.range (D + 1), poissonCountWeight x r * e r) ≤ E2 + Eref := by
    rw [show D + 1 = 3 + (D - 2) by omega, Finset.sum_range_add]
    have hthree : (∑ r ∈ Finset.range 3, poissonCountWeight x r * e r) = poissonCountWeight x 2 * e 2 := by
      simp [Finset.sum_range_succ, he0, he1]
    rw [hthree]; exact add_le_add h2 href
  refine (Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (show n + 1 ≤ (D + 1) + (n + 1) by omega))
    fun r _ _ => mul_nonneg (poissonCountWeight_nonneg hx r) (he r)).trans ?_
  rw [Finset.sum_range_add]; exact add_le_add hprefix htail

private def matchedCardinalTargetCutoff (d j : ℕ) (N μ : ℝ) : ℝ :=
  max 1 (N * (μ * (1 + Real.log N)) ^ ((j : ℝ) / d))

private def cardinalInterpolationFactorialConstant (d : ℕ) (B a Csharp : ℝ) : ℝ :=
  cardinalInterpolationEnergyPrefactor d a *
    defectTailConstant Csharp (cardinalSpatialGeometricBase B (16 * spatialUnaryIntegralConstant d) * 2 ^ 2)

private def cardinalTaylorFactorialConstant (d q : ℕ) (B C a ρ Csharp : ℝ) : ℝ :=
  cardinalTaylorEnergyPrefactor d q C a ρ * defectTailConstant Csharp
    (cardinalSpatialGeometricBase B ((100 * (d : ℝ)) ^ 2 * 16 * spatialScaleIntegralConstant d) * 2 ^ (4 * q + 6))

private def cardinalGeometryFactorialConstant (d q : ℕ) (B C a rho Cs : ℝ) : ℝ :=
  cardinalInterpolationFactorialConstant d B a (3 * Cs) +
    cardinalTaylorFactorialConstant d q B C a rho (3 * Cs)

private theorem finite_cardinal_interpolation_budget_le {bd B : ℝ} (hbd : 0 ≤ bd) (hB : bd ≤ B)
    {d : ℕ} (hd : 0 < d) (J : ℕ) (a η Csharp : ℝ) (ha : 0 < a) (hCs : 0 ≤ Csharp)
    {N μ : ℝ} (hN : 1 ≤ N) (hμ : 0 < μ) (hsmall : μ * (1 + Real.log N) ≤ 1) :
    (∑ j ∈ Finset.range J, poissonCountWeight (Csharp * μ) (2 + j) *
      cardinalAliasSpatialComponent d (2 + j) bd a η (matchedCardinalTargetCutoff d j N μ)) ≤
      cardinalInterpolationFactorialConstant d B a Csharp * η ^ 4 * N ^ (-(d : ℝ)) * μ ^ 2 := by
  have hNpos := lt_of_lt_of_le zero_lt_one hN
  let P := cardinalInterpolationEnergyPrefactor d a * η ^ 4 * N ^ (-(d : ℝ))
  have hP : 0 ≤ P := by dsimp [P, cardinalInterpolationEnergyPrefactor]; positivity
  have hBase := cardinalSpatialGeometricBase_nonneg B (16 * spatialUnaryIntegralConstant d)
  have h := finite_interpolation_defect_tail_le hP hCs
    (by positivity : 0 ≤ cardinalSpatialGeometricBase B (16 * spatialUnaryIntegralConstant d) * 2 ^ 2) hμ J
    (fun n => cardinalAliasSpatialComponent d n bd a η (matchedCardinalTargetCutoff d (n - 2) N μ)) fun j _ => by
      have hi : matchedCardinalTargetCutoff d j N μ ^ (-(d : ℝ)) *
          (1 + Real.log (matchedCardinalTargetCutoff d j N μ)) ^ j ≤ N ^ (-(d : ℝ)) / μ ^ j := by
        dsimp [matchedCardinalTargetCutoff]
        let T := N * (μ * (1 + Real.log N)) ^ ((j : ℝ) / d)
        have hH : 0 < 1 + Real.log N := by linarith [Real.log_nonneg hN]
        by_cases hT : 1 ≤ T
        · rw [max_eq_right hT]
          exact target_cutoff_defect_budget_le (Nat.ne_of_gt hd) hNpos hμ j hT
            (target_cutoff_le_base hd hNpos.le (mul_nonneg hμ.le hH.le) hsmall j)
        · rw [max_eq_left (le_of_not_ge hT), Real.one_rpow, Real.log_one, add_zero, one_pow, mul_one]
          exact omitted_target_inverse_budget_ge_one (Nat.ne_of_gt hd) hN hμ j (lt_of_not_ge hT)
      have hA : 0 ≤ cardinalInterpolationEnergyPrefactor d a := by unfold cardinalInterpolationEnergyPrefactor; positivity
      have hb : cardinalAliasSpatialComponent d (2 + j) bd a η (matchedCardinalTargetCutoff d j N μ) ≤
          cardinalInterpolationEnergyPrefactor d a *
            cardinalSpatialGeometricBase B (16 * spatialUnaryIntegralConstant d) ^ (2 + j) *
              (2 + j : ℕ) ^ 2 * η ^ 4 * N ^ (-(d : ℝ)) / μ ^ j := by
        refine (cardinalAliasSpatialComponent_geometric_le hbd hB d (2 + j) a η
          (matchedCardinalTargetCutoff d j N μ) ha (le_max_left _ _)).trans ?_
        have hh := mul_le_mul_of_nonneg_left hi
          (by positivity : 0 ≤ cardinalInterpolationEnergyPrefactor d a *
            cardinalSpatialGeometricBase B (16 * spatialUnaryIntegralConstant d) ^ (2 + j) * (2 + j : ℕ) ^ 2 * η ^ 4)
        convert hh using 1 <;> (try simp only [show 2 + j - 2 = j by omega]) <;> ring
      have hm := mul_le_mul_of_nonneg_left (polynomial_count_factor_le (2 + j) 2)
        (by positivity : 0 ≤ P * cardinalSpatialGeometricBase B (16 * spatialUnaryIntegralConstant d) ^ (2 + j) / μ ^ j)
      rw [show 2 + j - 2 = j by omega]
      refine hb.trans ?_
      convert hm using 1 <;> dsimp [P] <;> (try simp only [mul_pow, show 2 + j - 2 = j by omega]) <;> ring
  simpa only [show ∀ j : ℕ, 2 + j - 2 = j from fun _ => by omega] using
    h.trans_eq (by unfold cardinalInterpolationFactorialConstant; dsimp [P]; ring)

private theorem finite_cardinal_taylor_budget_le {bd B : ℝ} (hbd : 0 ≤ bd) (hB : bd ≤ B)
    (d q J : ℕ) (C a ρ η Csharp : ℝ) (hCs : 0 ≤ Csharp)
    {N μ : ℝ} (hN : 0 < N) (hμ : 0 ≤ μ) (hμ1 : μ ≤ 1) (hsmall : η ^ (4 * q) * N ^ d ≤ 1) :
    (∑ j ∈ Finset.range J, poissonCountWeight (Csharp * μ) (2 + j) *
      cardinalTaylorSpatialComponent d (2 + j) q bd C a ρ η) ≤
      cardinalTaylorFactorialConstant d q B C a ρ Csharp * η ^ 4 * N ^ (-(d : ℝ)) * μ ^ 2 := by
  let P := cardinalTaylorEnergyPrefactor d q C a ρ * η ^ 4 * N ^ (-(d : ℝ))
  have hP : 0 ≤ P := by dsimp [P, cardinalTaylorEnergyPrefactor]; positivity
  have hBase := cardinalSpatialGeometricBase_nonneg B ((100 * (d : ℝ)) ^ 2 * 16 * spatialScaleIntegralConstant d)
  have h := finite_taylor_count_energy_tail_le hP hCs hBase hμ hμ1 (4 * q + 6) J
    (fun n => cardinalTaylorSpatialComponent d n q bd C a ρ η) fun j _ => by
      have hA : 0 ≤ cardinalTaylorEnergyPrefactor d q C a ρ := by unfold cardinalTaylorEnergyPrefactor; positivity
      have hh := mul_le_mul_of_nonneg_left (response_taylor_budget_absorption hN q d hsmall)
        (by positivity : 0 ≤ cardinalTaylorEnergyPrefactor d q C a ρ *
          cardinalSpatialGeometricBase B ((100 * (d : ℝ)) ^ 2 * 16 * spatialScaleIntegralConstant d) ^ (2 + j) *
          ((2 + j : ℕ) : ℝ) ^ (4 * q + 6))
      refine ((cardinalTaylorSpatialComponent_geometric_le hbd hB d (2 + j) q C a ρ η).trans hh).trans_eq ?_
      dsimp [P]; rw [Real.rpow_neg hN.le, Real.rpow_natCast]; ring
  exact h.trans_eq (by unfold cardinalTaylorFactorialConstant; dsimp [P]; ring)

private def finePairSaddleAliasExponent (d : ℕ) (c0 K : ℝ) : ℝ := 2 * c0 + c0 * K * ((d : ℝ) - 4)

private def finePairSaddleAliasFactorialConstant (d q : ℕ) (aD bD C a rho c0 K Cs : ℝ) : ℝ :=
  aliasTailConstant
    (finePairUniformSpatialPrefactor d q aD bD C a rho c0 * 6 * (2 : ℝ) ^ d * spatialInverseFourConstant d)
    Cs (finePairAliasGeometricBase d bD * 2 ^ 8) (finePairSaddleAliasExponent d c0 K)

private theorem finite_fine_pair_saddle_alias_budget_le {d : ℕ} (hd : 4 ≤ d)
    {aD bD ad bd c0 K : ℝ} (haD : 0 < aD) (ha : aD ≤ ad) (hb : bd ≤ bD)
    (hab : ad < bd) (htau : exteriorTau ((ad + bd) / (bd - ad)) ≤ c0)
    (hc0 : 0 ≤ c0) (hK : 0 ≤ K) (M D q J : ℕ)
    (C a rho eta ell N Cs mu : ℝ) (hN : 0 < N)
    (hell : ell = N * Real.exp (-c0 * D)) (hD : (D : ℝ) ≤ K * M)
    (hCs : 0 ≤ Cs) (hmu : 0 ≤ mu) (hmu1 : mu ≤ 1) :
    (∑ j ∈ Finset.range J, poissonCountWeight (Cs * mu) (M + 1 + j) *
      finePairAliasActionSpatialBudget d (M + 1 + j) M q ad bd C a rho eta ell) ≤
      finePairSaddleAliasFactorialConstant d q aD bD C a rho c0 K Cs *
        (eta ^ 4 * N ^ (4 - (d : ℝ))) *
          poissonCountWeight (finePairSaddleAliasFactorialConstant d q aD bD C a rho c0 K Cs * mu) (M + 1) := by
  have hellpos : 0 < ell := by rw [hell]; positivity
  let A := finePairUniformSpatialPrefactor d q aD bD C a rho c0 * 6 * (2 : ℝ) ^ d * spatialInverseFourConstant d
  have hA : 0 ≤ A := by
    dsimp [A]; positivity [finePairUniformSpatialPrefactor_nonneg d q aD bD C a rho c0, spatialInverseFourConstant_nonneg d]
  have hBase : 0 ≤ finePairAliasGeometricBase d bD := finePairAliasGeometricBase_nonneg d bD
  have hdR : (4 : ℝ) ≤ d := by exact_mod_cast hd
  have hL : 0 ≤ finePairSaddleAliasExponent d c0 K := by unfold finePairSaddleAliasExponent; positivity
  have hs : Real.exp (2 * exteriorTau ((ad + bd) / (bd - ad)) * M) / ell ^ (d - 4) ≤
      N ^ (4 - (d : ℝ)) * Real.exp (finePairSaddleAliasExponent d c0 K * M) := by
    have hnat : ((d - 4 : ℕ) : ℝ) = (d : ℝ) - 4 := by exact_mod_cast (Nat.cast_sub hd : ((d - 4 : ℕ) : ℤ) = (d : ℤ) - 4)
    have hinv : 1 / ell ^ (d - 4) = N ^ (4 - (d : ℝ)) * Real.exp (c0 * D * ((d : ℝ) - 4)) := by
      have hpow : N ^ (4 - (d : ℝ)) = (N ^ (d - 4))⁻¹ := by
        rw [show (4 : ℝ) - d = -((d : ℝ) - 4) by ring, Real.rpow_neg hN.le, ← hnat, Real.rpow_natCast]
      rw [hell, mul_pow, ← Real.exp_nat_mul, hpow, one_div, mul_inv_rev, ← Real.exp_neg, mul_comm (Real.exp _)]
      congr 2; rw [hnat]; ring
    rw [div_eq_mul_inv, ← one_div, hinv, ← mul_assoc, mul_comm (Real.exp _) (N ^ _), mul_assoc, ← Real.exp_add]
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (Real.rpow_nonneg hN.le _)
    have hT := mul_le_mul_of_nonneg_right htau (by positivity : 0 ≤ (2 : ℝ) * M)
    have hDK := mul_le_mul_of_nonneg_left hD (by positivity : 0 ≤ c0 * ((d : ℝ) - 4))
    unfold finePairSaddleAliasExponent; nlinarith only [hT, hDK]
  unfold finePairSaddleAliasFactorialConstant
  refine finite_alias_energy_tail_le hA (by positivity : 0 ≤ eta ^ 4 * N ^ (4 - (d : ℝ))) hCs
    (by positivity) hL hmu hmu1 M J
    (fun n => finePairAliasActionSpatialBudget d n M q ad bd C a rho eta ell) fun j _ => ?_
  let n := M + 1 + j
  have h := finePairAliasActionSpatialBudget_uniform_geometric_le haD ha hb hab htau d n M q C a rho eta ell hellpos
  have hp := polynomial_count_factor_le n 8
  have hm := mul_le_mul_of_nonneg_left hs (by positivity : 0 ≤ A * finePairAliasGeometricBase d bD ^ n * (n : ℝ) ^ 8 * eta ^ 4)
  have hm' := mul_le_mul_of_nonneg_right hp
    (by positivity : 0 ≤ A * finePairAliasGeometricBase d bD ^ n * eta ^ 4 * N ^ (4 - (d : ℝ)) *
      Real.exp (finePairSaddleAliasExponent d c0 K * M))
  refine h.trans ?_
  calc _ ≤ A * finePairAliasGeometricBase d bD ^ n * (n : ℝ) ^ 8 * eta ^ 4 *
          (N ^ (4 - (d : ℝ)) * Real.exp (finePairSaddleAliasExponent d c0 K * M)) := by convert hm using 1 <;> dsimp [A] <;> ring
    _ ≤ A * (eta ^ 4 * N ^ (4 - (d : ℝ))) * Real.exp (finePairSaddleAliasExponent d c0 K * M) *
          (finePairAliasGeometricBase d bD * 2 ^ 8) ^ n := by convert hm' using 1 <;> (try rw [mul_pow]) <;> ring

private def ordinaryFineAliasSaddleTargetBound (s : ℝ) (d : ℕ) (ad bd : ℝ) : ℕ :=
  lowerAliasFineTargetBound d (lowerSaddleTheta s d (densityIntervalExponent ad bd)) (densityIntervalExponent ad bd + 1)

private def ordinaryFineAliasFactorialConstant (s : ℝ) (d q : ℕ) (ad bd C a rho Csharp : ℝ) : ℝ :=
  aliasTailConstant
    (ordinaryAliasFamilySpatialPrefactor d q (ordinaryFineAliasSaddleTargetBound s d ad bd)
      ad bd (densityIntervalExponent ad bd + 1) C a rho)
    Csharp (ordinaryAliasSpatialResponseBase d bd)
    (lowerAliasSpatialFixedL d (lowerSaddleTheta s d (densityIntervalExponent ad bd)) (densityIntervalExponent ad bd + 1))

private theorem ordinaryFineAliasFactorialConstant_ge_one {s ad bd C a rho Csharp : ℝ} {d q : ℕ}
    (hbd : 0 ≤ bd) (hCs : 0 ≤ Csharp) :
    1 ≤ ordinaryFineAliasFactorialConstant s d q ad bd C a rho Csharp :=
  aliasTailConstant_ge_one (ordinaryAliasFamilySpatialPrefactor_nonneg _ _ _ _ _ _ _ _ _)
    hCs (by unfold ordinaryAliasSpatialResponseBase ordinaryAliasSpatialCountBase; positivity)

private theorem eventually_ordinaryFineAlias_factorial_tail
    {s ad bd : ℝ} {d : ℕ} (hs : 1 < s) (hd : 4 * s < (d : ℝ))
    (haD : 0 < ad) (hab : ad < bd) (Cw cf : ℝ) (q : ℕ)
    (C a rho Csharp : ℝ) (hCs : 0 ≤ Csharp) :
    ∀ᶠ x in atTop,
      let m := lowerSaddleCoefficient s d (densityIntervalExponent ad bd)
      let theta := lowerSaddleTheta s d (densityIntervalExponent ad bd)
      let c0 := densityIntervalExponent ad bd + 1
      let M := lowerSaddleM m x
      let D := lowerSaddleD d m x
      let N := lowerSaddleN s d m theta Cw (shrunkDensityExponent ad bd) x
      let mu := lowerSaddleMu d m theta Cw x
      let L := lowerAliasCutoff s d m theta Cw c0 (shrunkDensityExponent ad bd) x
      let R := ordinaryFineAliasSaddleTargetBound s d ad bd
      let eta := lowerSaddleEta s d m theta Cw cf x
      let C6 := ordinaryFineAliasFactorialConstant s d q ad bd C a rho Csharp
      (∑ j ∈ Finset.range (D - M), poissonCountWeight (Csharp * mu) (M + 1 + j) *
        (∫ U, ordinaryFineAliasFamilyResponseSquareEnvelope (F := D) (ordinaryFineAliasTargetSet d D L N mu)
          M R q ad bd c0 C a rho eta L (fun r => higherBandTargetScale d r N mu) U
          ∂fullSpatialPatchDesign d (M + 1 + j))) ≤
      C6 * (eta ^ 4 * Real.exp (2 * shrunkDensityExponent ad bd M * M) * N ^ (4 - (d : ℝ))) *
        poissonCountWeight (C6 * mu) (M + 1) := by
  let tau := densityIntervalExponent ad bd
  let m := lowerSaddleCoefficient s d tau
  let theta := lowerSaddleTheta s d tau
  have htau : 0 < tau := densityIntervalExponent_pos haD hab
  have hm : 0 < m := lowerSaddleCoefficient_pos hs hd htau
  have htheta : 0 < theta := lowerSaddleTheta_pos hs hd htau
  have hd0 : (0 : ℝ) < d := by linarith
  have hd4 : 4 ≤ d := by
    have h : (4 : ℝ) < d := by linarith
    have h' : 4 < d := by exact_mod_cast h
    omega
  filter_upwards [eventually_ordinaryFineAlias_saddle_guards hs hd haD hab Cw,
    (lowerSaddleMu_tends_zero hd0 hm htheta Cw).eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1)),
    eventually_gt_atTop (0 : ℝ)] with x G hmu1 hx
  dsimp only
  let c0 := tau + 1
  let M := lowerSaddleM m x
  let D := lowerSaddleD d m x
  let N := lowerSaddleN s d m theta Cw (shrunkDensityExponent ad bd) x
  let mu := lowerSaddleMu d m theta Cw x
  let Lcut := lowerAliasCutoff s d m theta Cw c0 (shrunkDensityExponent ad bd) x
  let R := ordinaryFineAliasSaddleTargetBound s d ad bd
  let eta := lowerSaddleEta s d m theta Cw cf x
  let A := ordinaryAliasFamilySpatialPrefactor d q R ad bd c0 C a rho
  let Lexp := lowerAliasSpatialFixedL d theta c0
  let B := ordinaryAliasSpatialResponseBase d bd
  let P := eta ^ 4 * Real.exp (2 * shrunkDensityExponent ad bd M * M) * N ^ (4 - (d : ℝ))
  have hmu0 : 0 ≤ mu := by dsimp [mu]; rw [lowerSaddleMu_eq_exp hx]; positivity
  have hA : 0 ≤ A := ordinaryAliasFamilySpatialPrefactor_nonneg _ _ _ _ _ _ _ _ _
  have hP : 0 ≤ P := mul_nonneg (mul_nonneg (by positivity) (Real.exp_pos _).le)
    (Real.rpow_nonneg (lowerSaddleN_positive _ _ _ _ _ _ _).le _)
  have hbd : 0 ≤ bd := (haD.trans hab).le
  have hB : 0 ≤ B := by unfold B ordinaryAliasSpatialResponseBase ordinaryAliasSpatialCountBase; positivity
  have hL : 0 ≤ Lexp := lowerAliasSpatialFixedL_nonneg hd4 _ (by dsimp [c0]; linarith)
  refine finite_alias_energy_tail_le hA hP hCs hB hL hmu0 hmu1.le M (D - M)
    (fun n => ∫ U, ordinaryFineAliasFamilyResponseSquareEnvelope (F := D) (ordinaryFineAliasTargetSet d D Lcut N mu)
      M R q ad bd c0 C a rho eta Lcut (fun r => higherBandTargetScale d r N mu) U ∂fullSpatialPatchDesign d n) fun j _ => ?_
  have hLT : ∀ r ∈ ordinaryFineAliasTargetSet d D Lcut N mu, Lcut ≤ higherBandTargetScale d r N mu :=
    fun r hr => (Finset.mem_filter.mp hr).2.2.le
  have he := (ordinaryFineAliasFamilyResponseSquareEnvelope_integrable_and_scale_le G.dimension _ G.targets
    ad bd _ C a rho eta _ _ _ hbd (Nat.cast_nonneg _) (by positivity)
    (by linarith [densityIntervalExponent_pos haD hab]) G.degree (lowerSaddleN_positive _ _ _ _ _ _ _)
    G.cutoff G.logarithm _ hLT q (n := M + 1 + j) (F := D)).2
  exact he.trans_eq (by
    dsimp [A, P, Lexp, B, R, c0, tau, m, theta, M, D, N, mu, Lcut, eta,
      ordinaryFineAliasSaddleTargetBound, lowerAliasSpatialFixedL, lowerAliasCutoff]
    ring)

-- 2. Full-count spatial geometry envelope & higher/exterior assembly
--    (`HighCompleteGeometry`, `SpatialGeometryFactorialEnergy`, `HigherGeometryEnergyAssembly`,
--     `CompleteGeometryExteriorEnergy`, `CompleteGeometryEnergyAssembly`)

private def completeSourceGeometryEnvelope {d : ℕ} (D M R q : ℕ)
    (aD bD c0 ell N mu C a rho eta Chi Bl : ℝ) : (n : ℕ) → (Fin n → Covariate d) → ℝ
  | 0, _ => 0
  | 1, _ => 0
  | 2, U => finePairCountTwoGeometryEnvelope (bD - (M : ℝ)⁻¹) a rho eta N U
  | n + 3, U => if n + 3 ≤ D then
      completeSourceHigherGeometryEnvelope (D := D) aD bD c0 ell N mu M R q C a rho eta U
    else (3 * Chi ^ 2) ^ (n + 3) * eta ^ 4 * (Bl + 1) ^ 2

private theorem completeSourceGeometryEnvelope_nonneg {d : ℕ} (D M R q : ℕ)
    (aD bD c0 ell N mu C a rho eta Chi Bl : ℝ) (n : ℕ) (U : Fin n → Covariate d) :
    0 ≤ completeSourceGeometryEnvelope D M R q aD bD c0 ell N mu C a rho eta Chi Bl n U := by
  rcases n with _ | _ | _ | n
  · norm_num [completeSourceGeometryEnvelope]
  · norm_num [completeSourceGeometryEnvelope]
  · exact finePairCountTwoGeometryEnvelope_nonneg _ _ _ _ _ U
  · simp only [completeSourceGeometryEnvelope]
    split_ifs
    · exact completeSourceHigherGeometryEnvelope_nonneg _ _ _ _ _ _ _ _ _ _ _ _ _ _
    · positivity

private theorem completeSourceGeometryEnvelope_integrable {d : ℕ} [NeZero d] (hd : 5 ≤ d)
    (D M R q : ℕ) (aD bD c0 ell N mu C a rho eta Chi Bl : ℝ)
    (hell : 1 ≤ ell) (hN : ell ≤ N) (n : ℕ) :
    Integrable (completeSourceGeometryEnvelope (d := d) D M R q aD bD c0 ell N mu C a rho eta Chi Bl n)
      (fullSpatialPatchDesign d n) := by
  rcases n with _ | _ | _ | n
  · exact integrable_zero _ _ _
  · exact integrable_zero _ _ _
  · exact (finePairCountTwoGeometryEnvelope_integrable_and_le (by omega) _ _ _ _
      (lt_of_lt_of_le zero_lt_one (hell.trans hN))).1
  · change Integrable (fun U : Fin (n + 3) → Covariate d => if n + 3 ≤ D then
      completeSourceHigherGeometryEnvelope (D := D) aD bD c0 ell N mu M R q C a rho eta U
      else (3 * Chi ^ 2) ^ (n + 3) * eta ^ 4 * (Bl + 1) ^ 2) (fullSpatialPatchDesign d (n + 3))
    split_ifs
    · exact completeSourceHigherGeometryEnvelope_integrable hd (by omega) _ _ _ _ _ _ _ _ _ _ _ _ _ hell hN
    · exact integrable_const _

private theorem completeSourceGeometryEnvelope_mono_total {d : ℕ} (D M R q : ℕ)
    (aD bD c0 ell N mu C a rho eta Chi : ℝ) {B1 B2 : ℝ}
    (hB1 : 0 ≤ B1) (hB : B1 ≤ B2) (n : ℕ) (U : Fin n → Covariate d) :
    completeSourceGeometryEnvelope D M R q aD bD c0 ell N mu C a rho eta Chi B1 n U ≤
      completeSourceGeometryEnvelope D M R q aD bD c0 ell N mu C a rho eta Chi B2 n U := by
  rcases n with _ | _ | _ | n
  · exact le_rfl
  · exact le_rfl
  · exact le_rfl
  · change (if n + 3 ≤ D then _ else (3 * Chi ^ 2) ^ (n + 3) * eta ^ 4 * (B1 + 1) ^ 2) ≤
      (if n + 3 ≤ D then _ else (3 * Chi ^ 2) ^ (n + 3) * eta ^ 4 * (B2 + 1) ^ 2)
    split_ifs
    · exact le_rfl
    · exact mul_le_mul_of_nonneg_left ((sq_le_sq₀ (by linarith) (by linarith)).mpr (by linarith)) (by positivity)

private theorem poissonCountWeight_mul_pow (x a : ℝ) (r : ℕ) :
    poissonCountWeight x r * a ^ r = poissonCountWeight (a * x) r := by
  unfold poissonCountWeight; rw [mul_pow]; ring

private theorem finite_cardinal_geometry_budget_le {d D F : ℕ} (hd : 5 ≤ d)
    {bd B : ℝ} (hbd : 0 ≤ bd) (hbdB : bd ≤ B) (q : ℕ) (C a rho eta Cs : ℝ)
    (ha : 0 < a) (hCs : 0 ≤ Cs) {N mu : ℝ} (hN : 1 ≤ N) (hmu : 0 < mu)
    (hmu1 : mu ≤ 1) (hmuH : mu * (1 + Real.log N) ≤ 1) (hTaylor : eta ^ (4 * q) * N ^ d ≤ 1) :
    (∑ j ∈ Finset.range (D - 2), poissonCountWeight (Cs * mu) (3 + j) *
      ∫ U, cardinalGeometryEnvelope (d := d) (n := 3 + j) (F := F) q bd C a rho eta
        (max 1 (higherBandTargetScale d (3 + j) N mu)) U ∂fullSpatialPatchDesign d (3 + j)) ≤
      cardinalGeometryFactorialConstant d q B C a rho Cs * eta ^ 4 * N ^ (-(d : ℝ)) * mu ^ 2 := by
  have hmatch {r : ℕ} (hr : 2 ≤ r) : max 1 (higherBandTargetScale d r N mu) = matchedCardinalTargetCutoff d (r - 2) N mu := by
    unfold higherBandTargetScale matchedCardinalTargetCutoff
    rw [show ((r - 2 : ℕ) : ℝ) = (r : ℝ) - 2 by rw [Nat.cast_sub hr]; norm_num]
  let f (r : ℕ) := poissonCountWeight ((3 * Cs) * mu) r *
    (cardinalAliasSpatialComponent d r bd a eta (matchedCardinalTargetCutoff d (r - 2) N mu) +
      cardinalTaylorSpatialComponent d r q bd C a rho eta)
  have hf (r : ℕ) : 0 ≤ f r := by
    dsimp [f]
    have h := poissonCountWeight_nonneg (by positivity : 0 ≤ (3 * Cs) * mu) r
    have hb : 0 ≤ cardinalDefectSquareBudget d r (matchedCardinalTargetCutoff d (r - 2) N mu) := by
      have hT : 1 ≤ matchedCardinalTargetCutoff d (r - 2) N mu := le_max_left _ _
      have hlog : 0 ≤ 1 + Real.log (matchedCardinalTargetCutoff d (r - 2) N mu) := by
        linarith only [Real.log_nonneg hT]
      unfold cardinalDefectSquareBudget spatialUnaryIntegralConstant; positivity
    unfold cardinalAliasSpatialComponent cardinalTaylorSpatialComponent
      cardinalRawAliasCoefficient cardinalRawTaylorCoefficient spatialScaleIntegralConstant
    positivity
  have hmajor : (∑ j ∈ Finset.range (D - 2), poissonCountWeight (Cs * mu) (3 + j) *
      ∫ U, cardinalGeometryEnvelope (d := d) (n := 3 + j) (F := F) q bd C a rho eta
        (max 1 (higherBandTargetScale d (3 + j) N mu)) U ∂fullSpatialPatchDesign d (3 + j)) ≤
      ∑ j ∈ Finset.range (D - 2), f (3 + j) := by
    refine Finset.sum_le_sum fun j _ => ?_
    have hi := (cardinalGeometryEnvelope_integrable_and_le (d := d) (n := 3 + j) (F := F)
      hd (by omega) q bd C a rho eta (T := max 1 (higherBandTargetScale d (3 + j) N mu)) (le_max_left _ _)).2
    have h := mul_le_mul_of_nonneg_left hi (poissonCountWeight_nonneg (by positivity : 0 ≤ Cs * mu) (3 + j))
    rw [cardinalRawSpatialEnergyBudget_split, hmatch (by omega)] at h
    rw [hmatch (by omega)]; convert h using 1; dsimp [f]
    rw [← mul_assoc, poissonCountWeight_mul_pow]; congr 2; ring
  refine (hmajor.trans (finite_refined_sum_le_start_two D f hf)).trans ?_
  dsimp [f]; simp_rw [show ∀ j : ℕ, 2 + j - 2 = j from fun _ => by omega, mul_add]
  rw [Finset.sum_add_distrib]
  exact (add_le_add (finite_cardinal_interpolation_budget_le hbd hbdB (by omega) (D - 1) a eta (3 * Cs) ha (by positivity) hN hmu hmuH)
    (finite_cardinal_taylor_budget_le hbd hbdB d q (D - 1) C a rho eta (3 * Cs) (by positivity)
      (lt_of_lt_of_le zero_lt_one hN) hmu.le hmu1 hTaylor)).trans_eq (by unfold cardinalGeometryFactorialConstant; ring)

private theorem finite_fine_field_geometry_budget_le {d D : ℕ} [NeZero d] (hd : 5 ≤ d) (hD : 3 ≤ D)
    {aD bD ad bd c0 : ℝ} (haD : 0 < aD) (had : aD ≤ ad) (hbd : bd ≤ bD)
    (hab : ad < bd) (htau : exteriorTau ((ad + bd) / (bd - ad)) ≤ c0)
    (M q : ℕ) (C a rho eta ell N Cs mu : ℝ) (hell : 0 < ell)
    (hCs : 0 ≤ Cs) (hmu : 0 ≤ mu) (hmu1 : mu ≤ 1) :
    (∑ j ∈ Finset.range (D - 2), poissonCountWeight (Cs * mu) (3 + j) *
      ∫ U, fineFieldGeometryEnvelope (d := d) (n := 3 + j) ad bd ell N M q C a rho eta U
        ∂fullSpatialPatchDesign d (3 + j)) ≤
      finePairFieldFactorialConstant d q aD bD C a rho c0 (3 * Cs) * eta ^ 4 *
        Real.exp (2 * exteriorTau ((ad + bd) / (bd - ad)) * M) * (ell ^ (2 - (d : ℝ))) ^ 2 * mu ^ 4 := by
  let f (r : ℕ) := poissonCountWeight (Cs * mu) r *
    ∫ U, fineFieldGeometryEnvelope (d := d) (n := r) ad bd ell N M q C a rho eta U ∂fullSpatialPatchDesign d r
  have hf3 : f 3 = 0 := by
    have h0 (U : Fin 3 → Covariate d) : fineFieldGeometryEnvelope ad bd ell N M q C a rho eta U = 0 := by
      have hs : ((Finset.univ : Finset (Fin 3)).powerset).filter (fun S => 4 ≤ S.card ∧ Even S.card) = ∅ := by
        refine Finset.eq_empty_iff_forall_notMem.mpr fun S hS => ?_
        have hc := Finset.card_le_card (Finset.mem_powerset.mp (Finset.mem_filter.mp hS).1)
        have h4 := (Finset.mem_filter.mp hS).2.1
        simp only [Finset.card_univ, Fintype.card_fin] at hc; omega
      unfold fineFieldGeometryEnvelope; rw [hs]; simp
    simp [f, h0]
  change (∑ j ∈ Finset.range (D - 2), f (3 + j)) ≤ _
  rw [finite_refined_sum_eq_start_four D hD f hf3]
  refine (Finset.sum_le_sum fun j _ => ?_).trans
    (finite_fine_pair_field_budget_le haD had hbd hab htau d M q (D - 3) C a rho eta ell (3 * Cs) mu (by positivity) hmu hmu1)
  have h := mul_le_mul_of_nonneg_left
    (fineFieldGeometryEnvelope_integrable_and_le (d := d) (n := 4 + j) (by omega) ad bd ell N hell M q C a rho eta).2
    (poissonCountWeight_nonneg (by positivity : 0 ≤ Cs * mu) (4 + j))
  convert h using 1; try dsimp [f]
  rw [← mul_assoc, poissonCountWeight_mul_pow]; congr 2; ring

private theorem finite_fine_pair_alias_geometry_budget_le {d D : ℕ} [NeZero d] (hd : 5 ≤ d)
    {aD bD ad bd c0 K : ℝ} (haD : 0 < aD) (had : aD ≤ ad) (hbd : bd ≤ bD)
    (hab : ad < bd) (htau : exteriorTau ((ad + bd) / (bd - ad)) ≤ c0)
    (hc0 : 0 ≤ c0) (hK : 0 ≤ K) (M q : ℕ) (C a rho eta ell N Cs mu : ℝ)
    (hN : 0 < N) (hell : ell = N * Real.exp (-c0 * D)) (hell1 : 1 ≤ ell)
    (hellN : ell ≤ N) (hDM : (D : ℝ) ≤ K * M) (hCs : 0 ≤ Cs) (hmu : 0 ≤ mu) (hmu1 : mu ≤ 1) :
    (∑ j ∈ Finset.range (D - 2), poissonCountWeight (Cs * mu) (3 + j) *
      (if M < 3 + j then ∫ U, finePairAliasGeometryEnvelope (d := d) (n := 3 + j)
        ad bd ell N M q C a rho eta U ∂fullSpatialPatchDesign d (3 + j) else 0)) ≤
      finePairSaddleAliasFactorialConstant d q aD bD C a rho c0 K (3 * Cs) *
        (eta ^ 4 * N ^ (4 - (d : ℝ))) *
          poissonCountWeight (finePairSaddleAliasFactorialConstant d q aD bD C a rho c0 K (3 * Cs) * mu) (M + 1) := by
  let f (r : ℕ) := poissonCountWeight ((3 * Cs) * mu) r *
    finePairAliasActionSpatialBudget d r M q ad bd C a rho eta ell
  have hf (r : ℕ) : 0 ≤ f r := by
    dsimp [f, finePairAliasActionSpatialBudget]
    positivity [poissonCountWeight_nonneg (by positivity : 0 ≤ (3 * Cs) * mu) r, spatialInverseFourConstant_nonneg d]
  have hmajor : (∑ j ∈ Finset.range (D - 2), poissonCountWeight (Cs * mu) (3 + j) *
      (if M < 3 + j then ∫ U, finePairAliasGeometryEnvelope (d := d) (n := 3 + j)
        ad bd ell N M q C a rho eta U ∂fullSpatialPatchDesign d (3 + j) else 0)) ≤
      ∑ j ∈ Finset.range (D - 2), if M < 3 + j then f (3 + j) else 0 := by
    refine Finset.sum_le_sum fun j _ => ?_
    by_cases hMj : M < 3 + j
    · simp only [if_pos hMj]
      have h := mul_le_mul_of_nonneg_left
        (finePairAliasGeometryEnvelope_integrable_and_le (d := d) (n := 3 + j) (by omega)
          ad bd ell N (lt_of_lt_of_le zero_lt_one hell1) hellN M q C a rho eta).2
        (poissonCountWeight_nonneg (by positivity : 0 ≤ Cs * mu) (3 + j))
      convert h using 1; dsimp [f]
      rw [← mul_assoc, poissonCountWeight_mul_pow]; congr 2; ring
    · simp only [if_neg hMj, mul_zero, le_refl]
  exact (hmajor.trans (finite_refined_gated_sum_le_tail D M f hf)).trans
    (finite_fine_pair_saddle_alias_budget_le (by omega) haD had hbd hab htau hc0 hK M D q (D - M)
      C a rho eta ell N (3 * Cs) mu hN hell hDM (by positivity) hmu hmu1)

private theorem finite_complete_higher_geometry_energy_le {d D : ℕ} [NeZero d]
    (hd : 5 ≤ d) (hD : 3 ≤ D) (aD bD c0 K ell N mu : ℝ) (M R q : ℕ)
    (C a rho eta Cs Eord : ℝ) (haD : 0 < aD) (ha : 0 < a)
    (hshrink : aD + (M : ℝ)⁻¹ < bD - (M : ℝ)⁻¹)
    (htau : exteriorTau (((aD + (M : ℝ)⁻¹) + (bD - (M : ℝ)⁻¹)) / ((bD - (M : ℝ)⁻¹) - (aD + (M : ℝ)⁻¹))) ≤ c0)
    (hc0 : 0 ≤ c0) (hK : 0 ≤ K) (hCs : 0 ≤ Cs)
    (hell : 1 ≤ ell) (hellN : ell ≤ N) (hcut : ell = N * Real.exp (-c0 * D))
    (hDM : (D : ℝ) ≤ K * M) (hmu : 0 < mu) (hmu1 : mu ≤ 1)
    (hmuH : mu * (1 + Real.log N) ≤ 1) (hTaylor : eta ^ (4 * q) * N ^ d ≤ 1)
    (hfield : Real.exp (2 * exteriorTau (((aD + (M : ℝ)⁻¹) + (bD - (M : ℝ)⁻¹)) /
        ((bD - (M : ℝ)⁻¹) - (aD + (M : ℝ)⁻¹))) * M) * (ell ^ (2 - (d : ℝ))) ^ 2 * mu ^ 4 ≤
        mu ^ 2 * N ^ (-(d : ℝ)))
    (hord : (∑ j ∈ Finset.range (D - M), poissonCountWeight (Cs * mu) (M + 1 + j) *
      ∫ U, ordinaryFineAliasFamilyResponseSquareEnvelope (d := d) (n := M + 1 + j) (F := D)
        (ordinaryFineAliasTargetSet d D ell N mu) M R q aD bD c0 C a rho eta ell
        (fun t => higherBandTargetScale d t N mu) U ∂fullSpatialPatchDesign d (M + 1 + j)) ≤ Eord) :
    (∑ j ∈ Finset.range (D - 2), poissonCountWeight (Cs * mu) (3 + j) *
      ∫ U, completeSourceHigherGeometryEnvelope (d := d) (n := 3 + j) (D := D)
        aD bD c0 ell N mu M R q C a rho eta U ∂fullSpatialPatchDesign d (3 + j)) ≤
      4 * (cardinalGeometryFactorialConstant d q bD C a rho Cs * eta ^ 4 * N ^ (-(d : ℝ)) * mu ^ 2 + Eord +
        finePairSaddleAliasFactorialConstant d q aD bD C a rho c0 K (3 * Cs) *
          (eta ^ 4 * N ^ (4 - (d : ℝ))) *
          poissonCountWeight (finePairSaddleAliasFactorialConstant d q aD bD C a rho c0 K (3 * Cs) * mu) (M + 1) +
        finePairFieldFactorialConstant d q aD bD C a rho c0 (3 * Cs) * eta ^ 4 * mu ^ 2 * N ^ (-(d : ℝ))) := by
  have hN : 1 ≤ N := hell.trans hellN
  have hNpos : 0 < N := lt_of_lt_of_le zero_lt_one hN
  have had : aD ≤ aD + (M : ℝ)⁻¹ := le_add_of_nonneg_right (inv_nonneg.mpr (Nat.cast_nonneg M))
  have hbd : bD - (M : ℝ)⁻¹ ≤ bD := by linarith [inv_nonneg.mpr (Nat.cast_nonneg M : (0 : ℝ) ≤ M)]
  have hbd0 : 0 ≤ bD - (M : ℝ)⁻¹ := (haD.trans_le had).le.trans hshrink.le
  have hA := finite_cardinal_geometry_budget_le (D := D) (F := D) hd hbd0 hbd q C a rho eta Cs ha hCs hN hmu hmu1 hmuH hTaylor
  have hP := finite_fine_pair_alias_geometry_budget_le (D := D) hd haD had hbd hshrink htau hc0 hK M q
    C a rho eta ell N Cs mu hNpos hcut hell hellN hDM hCs hmu.le hmu1
  have hF := finite_fine_field_geometry_budget_le (D := D) hd hD haD had hbd hshrink htau M q C a rho eta
    ell N Cs mu (lt_of_lt_of_le zero_lt_one hell) hCs hmu.le hmu1
  have hFconst : 0 ≤ finePairFieldFactorialConstant d q aD bD C a rho c0 (3 * Cs) := by
    unfold finePairFieldFactorialConstant fieldTailConstant
    have hPre := finePairUniformSpatialPrefactor_nonneg d q aD bD C a rho c0
    have hP4 := poissonCountWeight_nonneg (by positivity [finePairFieldGeometricBase_nonneg d bD] :
      0 ≤ (3 * Cs) * (finePairFieldGeometricBase d bD * 2 ^ 12)) 4
    positivity
  have hFs := mul_le_mul_of_nonneg_left hfield (mul_nonneg hFconst (by positivity : 0 ≤ eta ^ 4))
  have hFfinal : (∑ j ∈ Finset.range (D - 2), poissonCountWeight (Cs * mu) (3 + j) *
      ∫ U, fineFieldGeometryEnvelope (d := d) (n := 3 + j)
        (aD + (M : ℝ)⁻¹) (bD - (M : ℝ)⁻¹) ell N M q C a rho eta U ∂fullSpatialPatchDesign d (3 + j)) ≤
      finePairFieldFactorialConstant d q aD bD C a rho c0 (3 * Cs) * eta ^ 4 * mu ^ 2 * N ^ (-(d : ℝ)) :=
    hF.trans (by convert hFs using 1 <;> ring)
  let f (r : ℕ) := poissonCountWeight (Cs * mu) r *
    ∫ U, ordinaryFineAliasFamilyResponseSquareEnvelope (d := d) (n := r) (F := D)
      (ordinaryFineAliasTargetSet d D ell N mu) M R q aD bD c0 C a rho eta ell
      (fun t => higherBandTargetScale d t N mu) U ∂fullSpatialPatchDesign d r
  have hf (r : ℕ) : 0 ≤ f r := mul_nonneg (poissonCountWeight_nonneg (mul_nonneg hCs hmu.le) r)
    (integral_nonneg fun U => ordinaryFineAliasFamilyResponseSquareEnvelope_nonneg _ _ _ _ _ _ _ _ _ _ _ _ _ U)
  have hO := (finite_refined_gated_sum_le_tail D M f hf).trans hord
  have hInt (j : ℕ) :
      (∫ U, completeSourceHigherGeometryEnvelope (d := d) (n := 3 + j) (D := D)
        aD bD c0 ell N mu M R q C a rho eta U ∂fullSpatialPatchDesign d (3 + j)) =
      4 * ((∫ U, cardinalGeometryEnvelope (d := d) (n := 3 + j) (F := D) q (bD - (M : ℝ)⁻¹) C a rho eta
            (max 1 (higherBandTargetScale d (3 + j) N mu)) U ∂fullSpatialPatchDesign d (3 + j)) +
          (if M < 3 + j then ∫ U, ordinaryFineAliasFamilyResponseSquareEnvelope (F := D)
            (ordinaryFineAliasTargetSet d D ell N mu) M R q aD bD c0 C a rho eta ell
            (fun t => higherBandTargetScale d t N mu) U ∂fullSpatialPatchDesign d (3 + j) else 0) +
          (if M < 3 + j then ∫ U, finePairAliasGeometryEnvelope (d := d) (n := 3 + j)
            (aD + (M : ℝ)⁻¹) (bD - (M : ℝ)⁻¹) ell N M q C a rho eta U ∂fullSpatialPatchDesign d (3 + j) else 0) +
          (∫ U, fineFieldGeometryEnvelope (d := d) (n := 3 + j)
            (aD + (M : ℝ)⁻¹) (bD - (M : ℝ)⁻¹) ell N M q C a rho eta U ∂fullSpatialPatchDesign d (3 + j))) := by
    have hAi := (cardinalGeometryEnvelope_integrable_and_le (d := d) (n := 3 + j) (F := D) hd (by omega) q
      (bD - (M : ℝ)⁻¹) C a rho eta (T := max 1 (higherBandTargetScale d (3 + j) N mu)) (le_max_left _ _)).1
    have hBi := ordinaryFineAliasFamilyResponseSquareEnvelope_integrable (d := d) (n := 3 + j) (F := D) hd
      (ordinaryFineAliasTargetSet d D ell N mu) M R q aD bD c0 C a rho eta ell
      (fun t => higherBandTargetScale d t N mu) hell fun t ht =>
        ⟨by have := (Finset.mem_filter.mp ht).2; omega, (Finset.mem_filter.mp ht).2.2.le⟩
    have hPi := (finePairAliasGeometryEnvelope_integrable_and_le (d := d) (n := 3 + j) (by omega)
      (aD + (M : ℝ)⁻¹) (bD - (M : ℝ)⁻¹) ell N (lt_of_lt_of_le zero_lt_one hell) hellN M q C a rho eta).1
    have hFi := (fineFieldGeometryEnvelope_integrable_and_le (d := d) (n := 3 + j) (by omega)
      (aD + (M : ℝ)⁻¹) (bD - (M : ℝ)⁻¹) ell N (lt_of_lt_of_le zero_lt_one hell) M q C a rho eta).1
    unfold completeSourceHigherGeometryEnvelope
    by_cases hMr : M < 3 + j
    · simp only [if_pos hMr]; rw [integral_const_mul]
      have h1 := integral_add ((hAi.add hBi).add hPi) hFi
      have h2 := integral_add (hAi.add hBi) hPi
      have h3 := integral_add hAi hBi
      simp only [Pi.add_apply] at h1 h2 h3; rw [h1, h2, h3]
    · simp only [if_neg hMr, add_zero]; rw [integral_const_mul, integral_add hAi hFi]
  simp_rw [hInt]
  have halg (w A B P F : ℝ) : w * (4 * (A + B + P + F)) = 4 * (w * A + w * B + w * P + w * F) := by ring
  simp_rw [halg, mul_ite, mul_zero]
  simp only [mul_ite, mul_zero] at hP
  rw [← Finset.mul_sum]; simp only [Finset.sum_add_distrib]
  exact mul_le_mul_of_nonneg_left (add_le_add (add_le_add (add_le_add hA hO) hP) hFfinal) (by norm_num)

private def completeGeometryExteriorConstant (d : ℕ) (Cs Chi : ℝ) : ℝ :=
  max 1 (Cs * (3 * (2 : ℝ) ^ d * Chi ^ 2))

private def completeGeometryRadialConstant (d : ℕ) (B a rho Cs : ℝ) : ℝ :=
  27 * Cs ^ 2 * B ^ 4 * ((2 * rho + a) / a ^ 2) ^ 4 * (2 : ℝ) ^ d * spatialExponentialConstant d

private def completeGeometryDefectConstant (d q : ℕ) (B C a rho Cs : ℝ) : ℝ :=
  1 + |completeGeometryRadialConstant d B a rho Cs| +
    4 * |cardinalGeometryFactorialConstant d q B C a rho Cs|

private def completeGeometryFieldConstant (d q : ℕ) (aD bD C a rho c0 Cs : ℝ) : ℝ :=
  1 + 4 * |finePairFieldFactorialConstant d q aD bD C a rho c0 (3 * Cs)|

private def completeGeometryAliasConstant (d q : ℕ) (aD bD C a rho c0 K Cs Cord : ℝ) : ℝ :=
  1 + 4 * |Cord| + 4 * |finePairSaddleAliasFactorialConstant d q aD bD C a rho c0 K (3 * Cs)|

private theorem completeSourceGeometryEnvelope_factorial_from_higher {d : ℕ} (hd : 0 < d)
    (D M R q n : ℕ) (hD : 3 ≤ D)
    (aD bD c0 K ell N mu C a rho eta Chi Bl Cs Cord tau : ℝ)
    (hN : 0 < N) (hCs : 0 ≤ Cs) (hmu : 0 ≤ mu) (hmu1 : mu ≤ 1)
    (hbd : 0 ≤ bD - (M : ℝ)⁻¹) (hbdB : bD - (M : ℝ)⁻¹ ≤ bD)
    (hCord : 0 ≤ Cord)
    (hCal : 0 ≤ finePairSaddleAliasFactorialConstant d q aD bD C a rho c0 K (3 * Cs))
    (htau : 0 ≤ tau)
    (hhigher : (∑ j ∈ Finset.range (D - 2), poissonCountWeight (Cs * mu) (3 + j) *
      ∫ U, completeSourceHigherGeometryEnvelope (d := d) (n := 3 + j) (D := D)
        aD bD c0 ell N mu M R q C a rho eta U ∂fullSpatialPatchDesign d (3 + j)) ≤
      4 * (cardinalGeometryFactorialConstant d q bD C a rho Cs * eta ^ 4 * N ^ (-(d : ℝ)) * mu ^ 2 +
        Cord * (eta ^ 4 * Real.exp (2 * tau * M) * N ^ (4 - (d : ℝ))) * poissonCountWeight (Cord * mu) (M + 1) +
        finePairSaddleAliasFactorialConstant d q aD bD C a rho c0 K (3 * Cs) *
          (eta ^ 4 * N ^ (4 - (d : ℝ))) *
          poissonCountWeight (finePairSaddleAliasFactorialConstant d q aD bD C a rho c0 K (3 * Cs) * mu) (M + 1) +
        finePairFieldFactorialConstant d q aD bD C a rho c0 (3 * Cs) * eta ^ 4 * mu ^ 2 * N ^ (-(d : ℝ)))) :
    (∑ r ∈ Finset.range (n + 1), poissonCountWeight (Cs * mu) r *
      ∫ U, completeSourceGeometryEnvelope (d := d) D M R q aD bD c0 ell N mu C a rho eta Chi Bl r U
        ∂fullSpatialPatchDesign d r) ≤
      3 * (completeGeometryDefectConstant d q bD C a rho Cs +
        completeGeometryFieldConstant d q aD bD C a rho c0 Cs) * eta ^ 4 * mu ^ 2 * N ^ (-(d : ℝ)) +
      3 * completeGeometryAliasConstant d q aD bD C a rho c0 K Cs Cord * eta ^ 4 *
        (Real.exp (2 * tau * M) * N ^ (4 - (d : ℝ))) *
          poissonCountWeight (completeGeometryAliasConstant d q aD bD C a rho c0 K Cs Cord * mu) (M + 1) +
      Real.exp (completeGeometryExteriorConstant d Cs Chi) * eta ^ 4 * (Bl + 1) ^ 2 *
        poissonCountWeight (completeGeometryExteriorConstant d Cs Chi * mu) (D + 1) := by
  let e (r : ℕ) := ∫ U, completeSourceGeometryEnvelope (d := d) D M R q aD bD c0 ell N mu C a rho eta Chi Bl r U
    ∂fullSpatialPatchDesign d r
  have he (r : ℕ) : 0 ≤ e r := integral_nonneg fun U =>
    completeSourceGeometryEnvelope_nonneg D M R q aD bD c0 ell N mu C a rho eta Chi Bl r U
  have hp : poissonCountWeight (Cs * mu) 2 * e 2 ≤
      completeGeometryRadialConstant d bD a rho Cs * eta ^ 4 * mu ^ 2 * N ^ (-(d : ℝ)) := by
    have hi : e 2 ≤ 9 * finePairCountTwoSpatialBudget d (bD - (M : ℝ)⁻¹) a rho eta N :=
      (finePairCountTwoGeometryEnvelope_integrable_and_le hd _ _ _ _ hN).2
    refine (mul_le_mul_of_nonneg_left hi (poissonCountWeight_nonneg (mul_nonneg hCs hmu) 2)).trans ?_
    let Kr := 27 * Cs ^ 2 * ((2 * rho + a) / a ^ 2) ^ 4 * (2 : ℝ) ^ d * spatialExponentialConstant d *
      eta ^ 4 * mu ^ 2 / N ^ d
    have hKr : 0 ≤ Kr := by have := spatialExponentialConstant_nonneg d; dsimp [Kr]; positivity
    have hm := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hbd hbdB 4) hKr
    rw [Real.rpow_neg hN.le, Real.rpow_natCast]
    convert hm using 1 <;> simp only [poissonCountWeight, finePairCountTwoSpatialBudget, completeGeometryRadialConstant]
      <;> dsimp [Kr] <;> norm_num only [Nat.factorial, Nat.cast_ofNat] <;> ring
  have ht : (∑ j ∈ Finset.range (n + 1), poissonCountWeight (Cs * mu) (D + 1 + j) * e (D + 1 + j)) ≤
      Real.exp (completeGeometryExteriorConstant d Cs Chi) * eta ^ 4 * (Bl + 1) ^ 2 *
        poissonCountWeight (completeGeometryExteriorConstant d Cs Chi * mu) (D + 1) := by
    let B := 3 * (2 : ℝ) ^ d * Chi ^ 2
    let P := eta ^ 4 * (Bl + 1) ^ 2
    let ch := completeGeometryExteriorConstant d Cs Chi
    have hB : 0 ≤ B := by dsimp [B]; positivity
    have hP : 0 ≤ P := by dsimp [P]; positivity
    have hbase : Cs * B ≤ ch := le_max_right _ _
    have heq (j : ℕ) : poissonCountWeight (Cs * mu) (D + 1 + j) * e (D + 1 + j) =
        P * poissonCountWeight (Cs * B * mu) (D + 1 + j) := by
      have hi : e (D + 1 + j) = B ^ (D + 1 + j) * P := by
        dsimp [e, B, P]
        rw [show D + 1 + j = (D - 2 + j) + 3 by omega]
        simp only [completeSourceGeometryEnvelope, if_neg (show ¬ (D - 2 + j) + 3 ≤ D by omega),
          integral_const, fullSpatialPatchDesign_real_univ, smul_eq_mul]
        rw [pow_mul, mul_pow, show (D - 2 + j) + 3 = D + 1 + j by omega]; ring
      rw [hi]; unfold poissonCountWeight; rw [mul_pow, mul_pow, mul_pow]; ring
    simp_rw [heq]; rw [← Finset.mul_sum]
    refine (mul_le_mul_of_nonneg_left (finite_poissonCountWeight_tail_le (by positivity) (D + 1) (n + 1)) hP).trans ?_
    have hexp : Real.exp (Cs * B * mu) ≤ Real.exp ch :=
      Real.exp_le_exp.mpr ((mul_le_of_le_one_right (mul_nonneg hCs hB) hmu1).trans hbase)
    have hweight := poissonCountWeight_mono (by positivity) (mul_le_mul_of_nonneg_right hbase hmu) (D + 1)
    exact (mul_le_mul_of_nonneg_left (mul_le_mul hexp hweight (poissonCountWeight_nonneg (by positivity) _)
      (Real.exp_pos ch).le) hP).trans_eq (by dsimp [P, ch]; ring)
  have heq_sum : (∑ j ∈ Finset.range (D - 2), poissonCountWeight (Cs * mu) (3 + j) * e (3 + j)) =
      ∑ j ∈ Finset.range (D - 2), poissonCountWeight (Cs * mu) (3 + j) *
        ∫ U, completeSourceHigherGeometryEnvelope (d := d) (n := 3 + j) (D := D)
          aD bD c0 ell N mu M R q C a rho eta U ∂fullSpatialPatchDesign d (3 + j) :=
    Finset.sum_congr rfl fun j hj => by
      dsimp [e]
      have hcast : 3 + j = j + 3 := by omega
      rw [hcast]
      simp only [completeSourceGeometryEnvelope, if_pos (show j + 3 ≤ D by have := Finset.mem_range.mp hj; omega)]
  have hh := heq_sum.trans_le hhigher
  have hblocks := finite_count_energy_from_blocks (mul_nonneg hCs hmu) n D (by omega) e he
    (by simp [e, completeSourceGeometryEnvelope]) (by simp [e, completeSourceGeometryEnvelope]) hp hh ht
  let Pdef := eta ^ 4 * mu ^ 2 * N ^ (-(d : ℝ))
  let Pal := eta ^ 4 * Real.exp (2 * tau * M) * N ^ (4 - (d : ℝ))
  let Plo := eta ^ 4 * N ^ (4 - (d : ℝ))
  let Ap := finePairSaddleAliasFactorialConstant d q aD bD C a rho c0 K (3 * Cs)
  let C6 := 1 + 4 * |Cord| + 4 * |Ap|
  have hPd : 0 ≤ Pdef := by dsimp [Pdef]; positivity
  have hPal : 0 ≤ Pal := by dsimp [Pal]; positivity
  have hPloPal : Plo ≤ Pal := by
    have h := mul_le_mul_of_nonneg_left (Real.one_le_exp (by positivity : 0 ≤ 2 * tau * M)) (by dsimp [Plo]; positivity : 0 ≤ Plo)
    dsimp [Plo, Pal] at h ⊢; linarith
  have hC6 : 0 ≤ C6 := by dsimp [C6]; positivity
  have hoW := poissonCountWeight_mono (mul_nonneg hCord hmu)
    (mul_le_mul_of_nonneg_right (by dsimp [C6]; linarith [le_abs_self Cord, abs_nonneg Ap] : Cord ≤ C6) hmu) (M + 1)
  have hpW := poissonCountWeight_mono (mul_nonneg hCal hmu)
    (mul_le_mul_of_nonneg_right (by dsimp [C6]; linarith [abs_nonneg Cord, le_abs_self Ap] : Ap ≤ C6) hmu) (M + 1)
  have ho := mul_le_mul_of_nonneg_left hoW (mul_nonneg hCord hPal)
  have hp_al := mul_le_mul (mul_le_mul_of_nonneg_left hPloPal hCal) hpW
    (poissonCountWeight_nonneg (mul_nonneg hCal hmu) _) (mul_nonneg hCal hPal)
  have hAli := mul_le_mul_of_nonneg_right
    (by dsimp [C6]; linarith [le_abs_self Cord, le_abs_self Ap, abs_nonneg Cord, abs_nonneg Ap] : 4 * (Cord + Ap) ≤ 3 * C6)
    (mul_nonneg hPal (poissonCountWeight_nonneg (mul_nonneg hC6 hmu) (M + 1)))
  let A2 := completeGeometryRadialConstant d bD a rho Cs
  let Ad := cardinalGeometryFactorialConstant d q bD C a rho Cs
  let Af := finePairFieldFactorialConstant d q aD bD C a rho c0 (3 * Cs)
  have hd_al := mul_le_mul_of_nonneg_right
    (by linarith [le_abs_self A2, le_abs_self Ad, le_abs_self Af, abs_nonneg A2, abs_nonneg Ad, abs_nonneg Af] :
      A2 + 4 * Ad + 4 * Af ≤ 3 * ((1 + |A2| + 4 * |Ad|) + (1 + 4 * |Af|))) hPd
  refine hblocks.trans ?_
  dsimp only [completeGeometryDefectConstant, completeGeometryFieldConstant, completeGeometryAliasConstant]
  change _ ≤ 3 * ((1 + |A2| + 4 * |Ad|) + (1 + 4 * |Af|)) * eta ^ 4 * mu ^ 2 * N ^ (-(d : ℝ)) +
    3 * C6 * eta ^ 4 * (Real.exp (2 * tau * M) * N ^ (4 - (d : ℝ))) * poissonCountWeight (C6 * mu) (M + 1) + _
  dsimp only [Pdef, Pal, Plo, Ap, A2, Ad, Af] at ho hp_al hAli hd_al
  nlinarith only [ho, hp_al, hAli, hd_al]

end FactorialGeometry

-- 3. Canonical complete-source pointwise domination (`HighSourceOriginalPair`, `HighSourceOriginalGeometry`, `HighSourceAllGeometry`)

section PointwiseDomination
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
attribute [local irreducible] highUnionSourceDensity highUnionSourceState historyMarkedAppend

private theorem completeSource_original_all_geometry {d : ℕ} [NeZero d]
    (C : ModelConstants d) (Q : LowSmoothnessTernaryConstants C) :
    ∃ Cfr0 eta0 : ℝ, 1 ≤ Cfr0 ∧ 0 < eta0 ∧
      ∀ k D M q : ℕ, ∀ (_ : NeZero k), ∀ (_ : LinearOrder (HighWindowLabels d k)),
      4 ≤ k → 3 ≤ D → 2 ≤ q → highCenterResolutionThreshold C ≤ (M : ℝ) →
      ∀ Cfr c0 ell N mu cf : ℝ, Cfr0 ≤ Cfr → 1 ≤ ell → ell < N → 0 ≤ cf →
      cf * (k : ℝ) ^ (-C.smoothness) ≤ eta0 →
      shrunkDensityExponent C.densityLower C.densityUpper M ≤ c0 →
      (∀ j : Fin (D - 2), 0 < higherBandTargetScale d (j.val + 3) N mu) →
      (∀ j : Fin (D - 2), ell < higherBandTargetScale d (j.val + 3) N mu → j.val + 3 ≤ M) →
      ∀ Rbound : ℕ, (∀ r ∈ ordinaryFineAliasTargetSet d D ell N mu, 1 ≤ r ∧ r ≤ Rbound) →
      ∀ V : ℝ, |V - Q.v| ≤ Q.ρ → ∀ j : HighWindowLabels d k,
      ∀ h : HistoryMarked (fun i j => j ∈ highNeighborLabels d k i)
        (HighUnionMark (SourceRowMark d D M q (C.densityLower + 1 / (M : ℝ))
          (C.densityUpper - 1 / (M : ℝ)) Cfr (spatialInterpolationLambda d) ell N mu)),
      ∀ n : ℕ, ∀ x : Fin n → Covariate d, (∀ i, x i ∈ highTorusPatch d k j) →
      let R := completeSourceRows C k D M q Cfr (spatialInterpolationLambda d) ell N mu
      let eta := cf * (k : ℝ) ^ (-C.smoothness)
      let Chi := highSeparatedScoreExponentialConstant Q.a Q.ρ C.densityUpper 1 1
      selectedRawSquareEnergy (highUnionSourceRawNumerator C R n Q.a V eta h j) x ≤
        completeSourceGeometryEnvelope D M Rbound q C.densityLower C.densityUpper c0 ell N mu Cfr Q.a Q.ρ eta
          Chi (highRowTotalMass R.rowMass) n (highPatchProductChart d k j x) := by
  obtain ⟨CG, eG, hCG, heG, hguards⟩ := completeSource_original_local_guards C Q
  obtain ⟨CR, eR, hCR, heR, hresponse⟩ := completeSource_original_response_exact_and_low_counts C Q
  obtain ⟨CB, eB, hCB, heB, hcrude⟩ := completeSourceNumerator_original_field_bound C Q
  let C0 := max CG (max CR CB)
  let e0 := min eG (min eR eB)
  have hG0 : CG ≤ C0 := le_max_left _ _
  have hR0 : CR ≤ C0 := (le_max_left _ _).trans (le_max_right _ _)
  have hB0 : CB ≤ C0 := (le_max_right _ _).trans (le_max_right _ _)
  have heG0 : e0 ≤ eG := min_le_left _ _
  have heR0 : e0 ≤ eR := (min_le_right _ _).trans (min_le_left _ _)
  have heB0 : e0 ≤ eB := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨C0, e0, hCG.trans hG0, lt_min heG (lt_min heR heB), ?_⟩
  intro k D M q hk0 horder hk hD hq hM Cfr c0 ell N mu cf hfr hell hellN hcf heta htau hnu hFine
    Rbound hI V hV j h n x hx
  letI := hk0; letI := horder
  let lam := spatialInterpolationLambda d
  let R := completeSourceRows C k D M q Cfr lam ell N mu
  let eta := cf * (k : ℝ) ^ (-C.smoothness)
  let c := (highUnionSourceState C R h).2
  let U := highPatchProductChart d k j x
  let p := fun i : Fin n => highUnionSourceDensity C R h (x i)
  let g := fun i : Fin n => highLocalFieldWithout d k D eta c j (x i)
  let w := fun i : Fin n => highPeriodicTensor d k j (x i)
  let Chi := highSeparatedScoreExponentialConstant Q.a Q.ρ C.densityUpper 1 1
  have hellp : 0 < ell := lt_of_lt_of_le zero_lt_one hell
  have hfr1 := hCG.trans (hG0.trans hfr)
  have H := hguards k D M q hk0 horder hk hD (by omega) hM Cfr lam ell N mu cf
    (hG0.trans hfr) hellp hellN hcf (heta.trans heG0) h
  have G := completeSourceRows_guards C k D M q hD (by omega) hM Cfr lam ell N mu hfr1 hellp hellN
  change selectedRawSquareEnergy (highUnionSourceRawNumerator C R n Q.a V eta h j) x ≤
    completeSourceGeometryEnvelope D M Rbound q C.densityLower C.densityUpper c0 ell N mu Cfr Q.a Q.ρ eta
      Chi (highRowTotalMass R.rowMass) n U
  rcases n with _ | _ | _ | n
  · have hz (y : Fin 0 → Fin 3) := (hresponse k D M q hk0 horder hk hD (by omega) hM Cfr lam ell N mu cf
      (hR0.trans hfr) hellp hellN hcf (heta.trans heR0) V hV j h 0 x hx y).2 (by omega)
    change selectedRawSquareEnergy (highUnionSourceRawNumerator C R 0 Q.a V eta h j) x ≤ 0
    simp only [selectedRawSquareEnergy]
    refine le_of_eq (Finset.sum_eq_zero fun y _ => ?_)
    change highUnionSourceMarkedNumerator C R 0 Q.a V eta j h x y ^ 2 = 0
    rw [hz, zero_pow (by decide : 2 ≠ 0)]
  · have hz (y : Fin 1 → Fin 3) := (hresponse k D M q hk0 horder hk hD (by omega) hM Cfr lam ell N mu cf
      (hR0.trans hfr) hellp hellN hcf (heta.trans heR0) V hV j h 1 x hx y).2 (by omega)
    change selectedRawSquareEnergy (highUnionSourceRawNumerator C R 1 Q.a V eta h j) x ≤ 0
    simp only [selectedRawSquareEnergy]
    refine le_of_eq (Finset.sum_eq_zero fun y _ => ?_)
    change highUnionSourceMarkedNumerator C R 1 Q.a V eta j h x y ^ 2 = 0
    rw [hz, zero_pow (by decide : 2 ≠ 0)]
  · obtain ⟨had, hab⟩ := high_source_interval_numeric C (M : ℝ) hM
    have hM2 : 2 ≤ M := by exact_mod_cast (highCenterResolution_guards C (M : ℝ) hM).1
    have hpi (i : Fin 2) : p i ∈ Icc (C.densityLower + 1 / (M : ℝ)) (C.densityUpper - 1 / (M : ℝ)) :=
      highUnionSourceDensity_interval C R G h (x i)
    have hUi (i : Fin 2) : U i ∈ hyperplaneCube d := highLocalCoordinates_abs_le_one d k j (x i)
    have hU2 (i : Fin 2) (r : Fin d) : |U i r| ≤ 2 := (hUi i r).trans (by norm_num)
    have hf (i : Fin 2) : |coefficientRegression eta g w (fun i => highFrameFeature (U i)) (c j) i| ≤ Q.ρ :=
      H.regression_abs j (c j) (H.coefficient_ball j) (x i)
    have he (y : Fin 2 → Fin 3) : highUnionSourceRawNumerator C R 2 Q.a V eta h j x y =
        finePairCountTwoRawNumerator (C.densityLower + 1 / (M : ℝ)) (C.densityUpper - 1 / (M : ℝ)) ell N D M q
          Cfr Q.a V eta U p g w (c j) y := by
      have hp1 := (hresponse k D M q hk0 horder hk hD (by omega) hM Cfr lam ell N mu cf
        (hR0.trans hfr) hellp hellN hcf (heta.trans heR0) V hV j h 2 x hx y).1
      have hp2 := completeSourceRawNumerator_count_two _ _ lam ell N mu had hab hellp.le hellN.le
        D M q hD hM2 hq Cfr Q.a V eta (by linarith) U hU2 hUi p g w hpi (c j) y
      have hfine := finePairThreeRow_count_two_numerator hD _ _ ell N had hab hellp.le hellN.le
        D M q (by omega) hM2 hq Cfr Q.a V eta (by linarith) U hUi p hpi g w (c j) y
      exact (hp1.trans hp2).trans hfine.symm
    have hcap := finePairCountTwoRawNumerator_sum_square_le_geometry hD _ _ ell N had hab hellp.le hellN.le
      D M q (by omega) hM2 hq Cfr Q.a V eta Q.ρ (by linarith) Q.a_pos Q.ρ_pos.le U hUi
      p g w hpi (fun i => H.weight_abs j (x i)) (c j) hf
    change selectedRawSquareEnergy (highUnionSourceRawNumerator C R 2 Q.a V eta h j) x ≤
      finePairCountTwoGeometryEnvelope (C.densityUpper - (M : ℝ)⁻¹) Q.a Q.ρ eta N U
    have hs : selectedRawSquareEnergy (highUnionSourceRawNumerator C R 2 Q.a V eta h j) x =
        ∑ y : Fin 2 → Fin 3, finePairCountTwoRawNumerator (C.densityLower + 1 / (M : ℝ))
          (C.densityUpper - 1 / (M : ℝ)) ell N D M q Cfr Q.a V eta U p g w (c j) y ^ 2 := by
      unfold selectedRawSquareEnergy
      exact Finset.sum_congr (by ext; simp) fun y _ => by rw [he]
    exact hs.trans_le (by unfold finePairCountTwoGeometryEnvelope; simpa only [one_div] using hcap)
  · by_cases hnD : n + 3 ≤ D
    · change selectedRawSquareEnergy (highUnionSourceRawNumerator C R (n + 3) Q.a V eta h j) x ≤
        if n + 3 ≤ D then completeSourceHigherGeometryEnvelope (D := D) C.densityLower C.densityUpper c0 ell N mu
          M Rbound q Cfr Q.a Q.ρ eta U else (3 * Chi ^ 2) ^ (n + 3) * eta ^ 4 * (highRowTotalMass R.rowMass + 1) ^ 2
      rw [if_pos hnD]
      obtain ⟨_, hab⟩ := high_source_interval_numeric C (M : ℝ) hM
      have hUi (i : Fin (n + 3)) (l : Fin d) : |U i l| ≤ 2 :=
        (highLocalCoordinates_abs_le_one d k j (x i) l).trans (by norm_num)
      have hpi (i : Fin (n + 3)) : p i ∈ Icc (C.densityLower + 1 / (M : ℝ)) (C.densityUpper - 1 / (M : ℝ)) :=
        highUnionSourceDensity_interval C R G h (x i)
      have hp_mass (f : ℝ) (hf : |f| ≤ Q.ρ) (u : Fin 3) : 0 ≤ ternaryMass Q.a f V u :=
        Q.c_pos.le.trans ((Q.legal f V hf hV).2.2.1 u)
      have hcap := completeSourceRawNumerator_higher_square_le_geometry C.densityLower C.densityUpper c0 ell N mu
        C.densityLower_pos hell D M Rbound q (by simpa only [one_div] using hab) htau (by omega) hnD (by omega)
        hnu hFine hI Cfr Q.a V eta Q.ρ hfr1 Q.a_pos H.amplitude_nonneg Q.ρ_pos.le H.amplitude_half U hUi p g w
        (by simpa only [one_div] using hpi) (fun i => H.without_abs j (x i)) (fun i => H.weight_abs j (x i))
        (c j) (H.coefficient_ball j) hp_mass
      have he (y : Fin (n + 3) → Fin 3) : highUnionSourceRawNumerator C R (n + 3) Q.a V eta h j x y =
          completeSourceRawNumerator (C.densityLower + 1 / (M : ℝ)) (C.densityUpper - 1 / (M : ℝ)) lam ell N mu
            D M q Cfr Q.a V eta U p g w (c j) y :=
        (hresponse k D M q hk0 horder hk hD (by omega) hM Cfr lam ell N mu cf (hR0.trans hfr) hellp hellN hcf
          (heta.trans heR0) V hV j h (n + 3) x hx y).1
      have hs : selectedRawSquareEnergy (highUnionSourceRawNumerator C R (n + 3) Q.a V eta h j) x =
          ∑ y : Fin (n + 3) → Fin 3, completeSourceRawNumerator (C.densityLower + 1 / (M : ℝ))
            (C.densityUpper - 1 / (M : ℝ)) lam ell N mu D M q Cfr Q.a V eta U p g w (c j) y ^ 2 := by
        unfold selectedRawSquareEnergy
        exact Finset.sum_congr (by ext; simp) fun y _ => by rw [he]
      exact hs.trans_le (by simpa only [one_div] using hcap)
    · change selectedRawSquareEnergy (highUnionSourceRawNumerator C R (n + 3) Q.a V eta h j) x ≤
        if n + 3 ≤ D then completeSourceHigherGeometryEnvelope (D := D) C.densityLower C.densityUpper c0 ell N mu
          M Rbound q Cfr Q.a Q.ρ eta U else (3 * Chi ^ 2) ^ (n + 3) * eta ^ 4 * (highRowTotalMass R.rowMass + 1) ^ 2
      rw [if_neg hnD]
      apply crude_raw_square_energy_pointwise Chi eta (highRowTotalMass R.rowMass)
      · exact (highSeparatedScoreExponentialConstant_pos Q.a Q.ρ C.densityUpper 1 1).le
      · exact G.total_positive.le
      · intro z y
        exact hcrude k D M q (n + 3) hk0 horder hk hD (by omega) (by omega) hM Cfr lam ell N mu cf
          (hB0.trans hfr) hellp hellN hcf (heta.trans heB0) V hV j h z y

end PointwiseDomination

-- 4. Path budget & flexible complete-source minimax cost bound (`HighPathBudget`, `HighCompletePathRisk`, `HighCompleteCostFlexible`)

section PathRisk
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency true
attribute [local irreducible] highUnionSourceDensity highUnionSourceRegression highUnionSourceState
  historyMarkedPrior massPowerNormalizer highRawDensityMass highMarginalRealScore highRealSampleKernel

private abbrev HighCompleteSourceHistory {d : ℕ} (C : ModelConstants d) (k D M q : ℕ)
    [NeZero k] [LinearOrder (HighWindowLabels d k)] (Cfr lam ell N mu : ℝ) :=
  HistoryMarked (fun i j => j ∈ highNeighborLabels d k i)
    (HighUnionMark (SourceRowMark d D M q (C.densityLower + 1 / (M : ℝ))
      (C.densityUpper - 1 / (M : ℝ)) Cfr lam ell N mu))

private def highPathConstant (Δ : ℕ) (rho eta0 : ℝ) : ℝ :=
  min 1 (min (historyReferenceRho Δ / (2 + 8 * (Δ : ℝ) ^ 2)) (rho / eta0 ^ 2))

private theorem highPathConstant_pos (Δ : ℕ) {rho eta0 : ℝ} (hrho : 0 < rho) (heta0 : 0 < eta0) :
    0 < highPathConstant Δ rho eta0 :=
  lt_min (by norm_num) (lt_min (div_pos (historyReferenceRho_pos Δ) (by positivity)) (div_pos hrho (by positivity)))

private theorem highPath_variance_budget (Δ : ℕ) {rho eta0 B I eta : ℝ}
    (hrho : 0 < rho) (heta0 : 0 < eta0) (hB : 0 ≤ B) (hI : 0 ≤ I)
    (heta : 0 ≤ eta) (hetaU : eta ≤ eta0) :
    eta ^ 2 * localScorePathLength (highPathConstant Δ rho eta0) B I ≤ rho := by
  have hc := highPathConstant_pos Δ hrho heta0
  have hlen : localScorePathLength (highPathConstant Δ rho eta0) B I ≤ highPathConstant Δ rho eta0 := by
    unfold localScorePathLength
    refine (div_le_iff₀ (by linarith only [hB, hI] : 0 < 1 + B + I)).mpr ?_
    simpa only [mul_one] using mul_le_mul_of_nonneg_left (by linarith only [hB, hI] : 1 ≤ 1 + B + I) hc.le
  have hlen0 := (localScorePathLength_pos hc hB hI).le
  have he2 : eta ^ 2 ≤ eta0 ^ 2 := (sq_le_sq₀ heta heta0.le).mpr hetaU
  have hcb : highPathConstant Δ rho eta0 ≤ rho / eta0 ^ 2 := (min_le_right _ _).trans (min_le_right _ _)
  have hbudget := (le_div_iff₀ (by positivity : 0 < eta0 ^ 2)).mp hcb
  exact (mul_le_mul he2 hlen hlen0 (sq_nonneg _)).trans (by nlinarith only [hbudget])

private theorem highCompleteSource_cost_risk_uniform_above {d : ℕ} [NeZero d]
    (C : ModelConstants d) (Q : LowSmoothnessTernaryConstants C) (CfrMin : ℝ) :
    ∃ Cfr eta0 ctr : ℝ, 1 ≤ Cfr ∧ CfrMin ≤ Cfr ∧ 0 < eta0 ∧ 0 < ctr ∧
      ∀ U : ExtensionDomain d, ∀ k D M q : ℕ,
      ∀ (_ : NeZero k) (_ : LinearOrder (HighWindowLabels d k)),
      ∀ hk : 4 ≤ k, ∀ hD : 3 ≤ D, ∀ hq : 1 ≤ q,
      ∀ hM : highCenterResolutionThreshold C ≤ (M : ℝ),
      ∀ lam ell N mu : ℝ, ∀ hell : 0 < ell, ∀ hellN : ell < N,
      let R := completeSourceRows C k D M q Cfr lam ell N mu
      let Ω := HighCompleteSourceHistory C k D M q Cfr lam ell N mu
      ∀ cf : ℝ, 0 ≤ cf → highWindowHolderConstant C * cf ≤ C.holderBound →
      let eta := cf * (k : ℝ) ^ (-C.smoothness)
      eta ≤ eta0 →
      ∀ cm : ℝ, 0 ≤ cm → cm ≤ 1 / C.densityUpper →
      ∀ n : ℕ, ∀ E : ℝ, 0 ≤ E →
      8 * highHistoryMassParameter d k C.densityLower C.densityUpper * (n : ℝ) ≤ cm / (M : ℝ) →
      let Bl := highRowTotalMass R.rowMass / highCenterMix C
      let c := highPathConstant (3 ^ d) Q.ρ eta0
      let I := Real.sqrt ((3 ^ d : ℕ) * (k : ℝ) ^ d * E)
      let delta := localScorePathLength c Bl I
      ∀ H : (r : ℕ) → (Fin r → Covariate d) → ℝ,
      (∀ r, Integrable (H r) (Measure.pi fun _ : Fin r => volume.restrict (spatialPatchBox d))) →
      (∀ r u, 0 ≤ H r u) →
      (∀ t ∈ Icc 0 delta, ∀ h : Ω, ∀ j r x, (∀ i, x i ∈ highTorusPatch d k j) →
        selectedRawSquareEnergy (highUnionSourceRawNumerator C R r Q.a (Q.v - eta ^ 2 * t) eta h j) x ≤
          H r (highPatchProductChart d k j x)) →
      highSourceSpatialSeries d k n C.densityLower Q.c (fun _j => H) ≤ (3 ^ d : ℕ) * (k : ℝ) ^ d * E →
      ENNReal.ofReal (ctr * eta ^ 4 / (1 + Bl ^ 2 + (k : ℝ) ^ d * E) -
        (effectiveVarianceUpper C - C.varianceLower) ^ 2 *
          (2 * Real.exp (-(cm / (M : ℝ)) ^ 2 / (8 * highHistoryMassParameter d k C.densityLower C.densityUpper)))) ≤
        minimaxRisk (C.withDomain U) n := by
  obtain ⟨Cfm, etam, hCfm, hetam, hmodel⟩ := highUnionSource_original_model_uniform C Q
  obtain ⟨Cfq, etaq, hCfq, hetaq, hfloor⟩ := highUnionSource_ternary_floor_uniform C Q
  let Cfr := max (max Cfm Cfq) CfrMin
  let eta0 := min etam etaq
  have hCfr : 1 ≤ Cfr := (hCfm.trans (le_max_left _ _)).trans (le_max_left _ _)
  have hCfmfr : Cfm ≤ Cfr := (le_max_left _ _).trans (le_max_left _ _)
  have hCfqfr : Cfq ≤ Cfr := (le_max_right _ _).trans (le_max_left _ _)
  have heta0 : 0 < eta0 := lt_min hetam hetaq
  let c := highPathConstant (3 ^ d) Q.ρ eta0
  have hc : 0 < c := highPathConstant_pos (3 ^ d) Q.ρ_pos heta0
  let ctr := c ^ 2 / (3 * (3 ^ d : ℕ) * (2 + c) ^ 2)
  have hctr : 0 < ctr := div_pos (sq_pos_of_pos hc) (by positivity)
  refine ⟨Cfr, eta0, ctr, hCfr, le_max_right _ _, heta0, hctr, ?_⟩
  intro U k D M q hk0 horder hk hD hq hM lam ell N mu hell hellN
  letI := hk0; letI := horder
  let R := completeSourceRows C k D M q Cfr lam ell N mu
  let Ω := HighCompleteSourceHistory C k D M q Cfr lam ell N mu
  let Emark := SourceRowMark d D M q (C.densityLower + 1 / (M : ℝ)) (C.densityUpper - 1 / (M : ℝ)) Cfr lam ell N mu
  have G := completeSourceRows_guards C k D M q hD hq hM Cfr lam ell N mu hCfr hell hellN
  have hpos := completeSourceRows_mass_positive (k := k) C hD hq hM Cfr lam ell N mu hCfr hell hellN
  letI : StandardBorelSpace (HighUnionMark Emark) := highUnionMark_standardBorel
  letI := highUnionSourceLaw_probability C R G
  dsimp only
  intro cf hcf hcfH heta cm hcm hcmU n E hE heps H hH hH0 hdom hbudget
  let eta := cf * (k : ℝ) ^ (-C.smoothness)
  let Bl := highRowTotalMass R.rowMass / highCenterMix C
  let B := (3 ^ d : ℕ) * (k : ℝ) ^ d * E
  let I := Real.sqrt B
  let T := localScorePathLength c Bl I
  have hBl : 0 ≤ Bl := div_nonneg G.total_positive.le (highCenterMix_mem C).1.le
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hI : 0 ≤ I := Real.sqrt_nonneg _
  have hT : 0 < T := localScorePathLength_pos hc hBl hI
  have hsmall : T * Bl / historyReferenceRho (3 ^ d) ≤ 1 / (2 + 8 * ((3 ^ d : ℕ) : ℝ) ^ 2) := by
    have hb : T * Bl ≤ c := by
      simpa only [T, localScorePathLength, add_right_comm 1 I Bl] using localScorePathLength_energy_le hc.le hI hBl
    have hcb : c ≤ historyReferenceRho (3 ^ d) / (2 + 8 * ((3 ^ d : ℕ) : ℝ) ^ 2) :=
      (min_le_right _ _).trans (min_le_left _ _)
    refine (div_le_iff₀ (historyReferenceRho_pos (3 ^ d))).mpr ?_
    simpa only [one_div, div_eq_mul_inv, mul_comm, one_mul] using hb.trans hcb
  have hVbudget : eta ^ 2 * T ≤ Q.ρ :=
    highPath_variance_budget (3 ^ d) Q.ρ_pos heta0 hBl hI
      (mul_nonneg hcf (Real.rpow_nonneg (Nat.cast_nonneg _) _)) heta
  let p := highUnionSourceDensity C R
  let F := highUnionSourceRegression C R eta
  have hp : Measurable (Function.uncurry p) := highUnionSourceDensity_joint_measurable C R G
  have hF : Measurable (Function.uncurry F) := highUnionSourceRegression_joint_measurable C R G eta
  let π := highUnionLaw R (highCenterMix C)
  let act := highUnionActivation R (highCenterMix C)
  let ν (t : ℝ) := historyMarkedPrior (fun i j => j ∈ highNeighborLabels d k i) (3 ^ d) t π act
  have hν (t : ℝ) (ht : t ∈ Icc 0 T) : IsProbabilityMeasure (ν t) :=
    completeSourcePrior_probability C hD hq hM Cfr lam ell N mu hCfr hell hellN T hT.le hsmall t ht
  have hV (t : ℝ) (ht : t ∈ Icc 0 T) : |(Q.v - eta ^ 2 * t) - Q.v| ≤ Q.ρ := by
    simp only [sub_sub_cancel_left, abs_neg, abs_mul, abs_of_nonneg (sq_nonneg eta), abs_of_nonneg ht.1]
    exact (mul_le_mul_of_nonneg_left ht.2 (sq_nonneg eta)).trans hVbudget
  have hqFloor (t : ℝ) (ht : t ∈ Icc 0 T) (h : Ω) (x : Covariate d) (y : Fin 3) :
      Q.c ≤ ternaryMass Q.a (F h x) (Q.v - eta ^ 2 * t) y :=
    hfloor k D hk0 horder hk _ inferInstance Emark inferInstance R (M : ℝ)
      (G.mono_frame hCfq hCfqfr) cf hcf (heta.trans (min_le_right _ _)) h _ (hV t ht) x y
  have hqPos (t : ℝ) (ht : t ∈ Icc 0 T) (h : Ω) (x : Covariate d) (y : Fin 3) :
      0 < ternaryMass Q.a (F h x) (Q.v - eta ^ 2 * t) y := Q.c_pos.trans_le (hqFloor t ht h x y)
  have hqNonneg := fun t ht h x y => (hqPos t ht h x y).le
  let θ := highNormalizedParameterPath T hT.le Q.a Q.v eta Q.a_pos.ne' p F hF hqNonneg
  let bad : ℝ → Set Ω := fun _ => {h | cm / (M : ℝ) < |highUnionSourceMass C R h - 1|}
  let eps := 2 * Real.exp (-(cm / (M : ℝ)) ^ 2 / (8 * highHistoryMassParameter d k C.densityLower C.densityUpper))
  have hm : Measurable (highUnionSourceMass C R) := highUnionSourceMass_measurable C R G
  have hbad (t : ℝ) (_ : t ∈ Icc 0 T) : MeasurableSet (bad t) :=
    measurableSet_lt measurable_const ((hm.sub_const 1).abs)
  have hlegal (t : ℝ) (ht : t ∈ Icc 0 T) (h : Ω) (hh : h ∉ bad t) :
      Admissible (C.withDomain U) (θ t h) := by
    obtain ⟨_, hleg⟩ := hmodel U k D hk0 horder hk _ inferInstance Emark inferInstance inferInstance
      R (M : ℝ) (G.mono_frame hCfm hCfmfr) cf hcf hcfH
      (heta.trans (min_le_left _ _)) cm hcm hcmU h (le_of_not_gt hh) _ (hV t ht)
    change Admissible (C.withDomain U) (highNormalizedParameterPath T hT.le Q.a Q.v eta Q.a_pos.ne' p F hF hqNonneg t h)
    rwa [highNormalizedParameterPath_apply T hT.le Q.a Q.v eta Q.a_pos.ne' p F hF hqNonneg t ht h]
  have hmassEq : (fun h => highRawDensityMass (p h)) = highUnionSourceMass C R :=
    funext fun _ => by simp only [p, highRawDensityMass, highUnionSourceMass]
  have hmass (t : ℝ) (ht : t ∈ Icc 0 T) :
      Measure.map (fun h => highRawDensityMass (p h)) (ν t) =
      Measure.map (fun h => highRawDensityMass (p h)) (ν 0) := by
    rw [hmassEq]
    exact (completeSourceMass_prior_law C hD hq hM Cfr lam ell N mu hCfr hell hellN T hT.le hsmall t ht).trans
      (completeSourceMass_prior_law C hD hq hM Cfr lam ell N mu hCfr hell hellN T hT.le hsmall 0 ⟨le_rfl, hT.le⟩).symm
  have hbadmass (t : ℝ) (ht : t ∈ Icc 0 T) :
      (massPowerTilt (ν t) (fun h => highRawDensityMass (p h)) n).real (bad t) ≤ eps := by
    rw [hmassEq]
    exact completeSourceMass_prior_tilted_tail C hD hq hM Cfr lam ell N mu hCfr hell hellN
      (by omega) T hT.le hsmall n (cm / (M : ℝ)) heps t ht
  have hfisher (t : ℝ) (ht : t ∈ Icc 0 T) := by
    letI := hν t ht
    exact highUnionSource_raw_fisher_bound C R G hpos (ν t) n hk Q.a (Q.v - eta ^ 2 * t) eta Q.c
      Q.a_pos.ne' Q.c_pos (hqFloor t ht)
      (fun j h x => completeSourceDensity_product_zero C hD hq hM Cfr lam ell N mu hCfr hell hellN j h n x)
      (fun _ _ => H) (fun _ _ => hH) (fun _ _ => hH0) (hdom t ht) B hB (fun _ => hbudget)
  have hactm := highUnionActivation_measurable R G.activation_measurable (highCenterMix C)
  have hact := highUnionSourceActivation_centered C R G hpos
  have hab := highUnionSourceActivation_bound C R G hpos
  have hh := historyMarkedPrior_original_minimax_path_bound
    (fun i j => j ∈ highNeighborLabels d k i) (highNeighborLabels_self_mem d k)
    (fun {_ _} h => highNeighborLabels_symmetric d k _ _ h) (3 ^ d)
    (one_le_pow₀ (by norm_num : (1 : ℕ) ≤ 3)) (highNeighbor_dependency_card d k)
    π act hactm hact Bl T hBl hT.le hab hsmall (C.withDomain U) n Q.a Q.v eta
    C.densityLower C.densityUpper B eps Q.a_pos C.densityLower_pos p F hp hF
    (highUnionSourceDensity_coarse_interval C R G) hqPos hmass θ
    (fun t ht h => highNormalizedParameterPath_apply T hT.le Q.a Q.v eta Q.a_pos.ne' p F hF hqNonneg t ht h)
    (fun t ht => Q.effective_interval (hV t ht)) bad hbad hlegal hbadmass
    (fun t ht => (hfisher t ht).1) (fun t ht => (hfisher t ht).2)
  let P (t : ℝ) := (highRealSampleKernel n Q.a (Q.v - eta ^ 2 * t) p F hp hF) ∘ₘ
    massPowerTilt (ν t) (fun h => highRawDensityMass (p h)) n
  let Score (t : ℝ) := highMarginalRealScore (fun i j => j ∈ highNeighborLabels d k i)
    (fun {_ _} h => highNeighborLabels_symmetric d k _ _ h)
    (ν t) π act n Q.a (Q.v - eta ^ 2 * t) eta p F
  letI := historyMarkedReference_probability (fun i j => j ∈ highNeighborLabels d k i)
    (highNeighborLabels_self_mem d k)
    (fun {_ _} h => highNeighborLabels_symmetric d k _ _ h) (3 ^ d)
    (one_le_pow₀ (by norm_num : (1 : ℕ) ≤ 3)) (highNeighbor_dependency_card d k) π
  have hInt := highHistoryScore_sqrt_energy_intervalIntegrable
    (fun i j => j ∈ highNeighborLabels d k i)
    (fun {_ _} h => highNeighborLabels_symmetric d k _ _ h) (3 ^ d) π act hactm
    Bl hBl hab n Q.a Q.v eta C.densityLower C.densityUpper T B Q.a_pos C.densityLower_pos
    hT.le p F hp hF hν (highUnionSourceDensity_coarse_interval C R G) hqPos
    (fun t ht => (hfisher t ht).1) (fun t ht => (hfisher t ht).2)
  have henergy (t : ℝ) (ht : t ∈ Icc 0 T) : (∫ z, (Score t z) ^ 2 ∂P t) ≤ B := by
    letI := hν t ht
    exact ((highMarginalRealScore_memLp_energy _ _ (ν t) π act hactm Bl hBl hab n Q.a
      (Q.v - eta ^ 2 * t) eta C.densityLower C.densityUpper Q.a_pos C.densityLower_pos
      p F hp hF (highUnionSourceDensity_coarse_interval C R G) (hqPos t ht)
      (hfisher t ht).1).2).trans (hfisher t ht).2
  have hscore := intervalIntegral_sqrt_energy_le (fun t => ∫ z, (Score t z) ^ 2 ∂P t) T B hT.le hInt henergy
  have hsc0 : 0 ≤ ∫ t in (0 : ℝ)..T, Real.sqrt (∫ z, (Score t z) ^ 2 ∂P t) :=
    intervalIntegral.integral_nonneg hT.le fun _ _ => Real.sqrt_nonneg _
  have hK : (1 : ℝ) ≤ (3 ^ d : ℕ) := by exact_mod_cast one_le_pow₀ (by norm_num : (1 : ℕ) ≤ 3)
  have hIE : I ^ 2 = (3 ^ d : ℕ) * ((k : ℝ) ^ d * E) := by simpa only [I, B, mul_assoc] using Real.sq_sqrt hB
  have hden : 1 + Bl ^ 2 + I ^ 2 ≤ (3 ^ d : ℕ) * (1 + Bl ^ 2 + (k : ℝ) ^ d * E) := by
    rw [hIE]
    have hm_le := mul_le_mul_of_nonneg_right hK (by positivity : 0 ≤ 1 + Bl ^ 2)
    nlinarith only [hm_le]
  have hh_num := div_le_div_of_nonneg_left (by positivity : 0 ≤ c ^ 2 / (3 * (2 + c) ^ 2) * eta ^ 4)
    (by positivity : 0 < 1 + Bl ^ 2 + I ^ 2) hden
  have hnum1 : ctr * eta ^ 4 / (1 + Bl ^ 2 + (k : ℝ) ^ d * E) ≤
      eta ^ 4 * T ^ 2 / (2 + ∫ t in (0 : ℝ)..T, Real.sqrt (∫ z, (Score t z) ^ 2 ∂P t)) ^ 2 := by
    refine le_trans ?_ (score_cost_numeric (η := eta) hc hBl hI hsc0 hscore)
    convert hh_num using 1 <;> dsimp [ctr] <;> field_simp <;> ring
  have hout := (ENNReal.ofReal_le_ofReal (sub_le_sub_right hnum1 _)).trans hh
  simpa only [ModelConstants.withDomain, effectiveVarianceUpper] using hout

end PathRisk

-- 5. Saddle parameters, activity, energy guards & witness
--    (`SourceSaddleActivity`, `CompleteSourceSaddleParameters`, `FineFieldScaleBudget`,
--     `SourceSaddleHigherSelection`, `CompleteSaddleEnergyGuards`, `CompleteSaddleEnergy`,
--     `CompleteSaddleEnergyWitness`, `RawCostAlgebra`, `LowerRawCostReduction`, `LowerPenaltyReduction`)

section SaddleAssembly
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
attribute [local irreducible] sourceRowData highRowTotalMass
  highUnionSourceDensity highUnionSourceState historyMarkedAppend

private def sourceSaddleActivityConstant (d q : ℕ) (a b C lam : ℝ) : ℝ :=
  1 + sourceActivityConstant d q C (uniformOrdinaryDensityActivityBase a b (densityIntervalExponent a b + 1)) lam

private def completeSourceSaddleRows {d : ℕ} (C : ModelConstants d) (q : ℕ) (Cfr lam Cω x : ℝ) :=
  let m := highCompleteSourceSaddleCoefficient C
  let theta := highCompleteSourceSaddleTheta C
  completeSourceRows C (lowerSaddleGrid d m theta Cω x)
    (lowerSaddleD d m x) (lowerSaddleM m x) q Cfr lam
    (lowerAliasCutoff C.smoothness d m theta Cω
      (densityIntervalExponent C.densityLower C.densityUpper + 1)
      (shrunkDensityExponent C.densityLower C.densityUpper) x)
    (lowerSaddleN C.smoothness d m theta Cω (shrunkDensityExponent C.densityLower C.densityUpper) x)
    (lowerSaddleMu d m theta Cω x)

private def completeSourceSaddleActivity {d : ℕ} (C : ModelConstants d) (q : ℕ) (Cfr lam Cω x : ℝ) : ℝ :=
  highRowTotalMass (completeSourceSaddleRows C q Cfr lam Cω x).rowMass / highCenterMix C

private def completeSourceSaddleActivityConstant {d : ℕ} (C : ModelConstants d) (q : ℕ) (Cfr lam : ℝ) : ℝ :=
  sourceSaddleActivityConstant d q C.densityLower C.densityUpper Cfr lam / highCenterMix C

private theorem completeSourceSaddleActivityConstant_pos {d : ℕ} (C : ModelConstants d) (q : ℕ) (Cfr lam : ℝ) :
    0 < completeSourceSaddleActivityConstant C q Cfr lam := by
  have hab := C.densityLower_lt_one.trans C.one_lt_densityUpper
  have hB : 0 ≤ uniformOrdinaryDensityActivityBase C.densityLower C.densityUpper
      (densityIntervalExponent C.densityLower C.densityUpper + 1) := by
    unfold uniformOrdinaryDensityActivityBase
    exact mul_nonneg (Real.exp_pos _).le (div_nonneg (sub_pos.mpr hab).le C.densityLower_pos.le)
  have hs : 0 < sourceSaddleActivityConstant d q C.densityLower C.densityUpper Cfr lam := by
    unfold sourceSaddleActivityConstant; linarith [sourceActivityConstant_nonneg d q Cfr _ lam hB]
  exact div_pos hs (highCenterMix_mem C).1

private theorem completeSourceSaddleActivity_eventually_bound {d : ℕ} [NeZero d]
    (C : ModelConstants d) (hs : 1 < C.smoothness) (hd : 4 * C.smoothness < (d : ℝ))
    (q : ℕ) (Cfr lam Cω : ℝ) :
    ∀ᶠ x : ℝ in atTop,
      completeSourceSaddleActivity C q Cfr lam Cω x ≤
        completeSourceSaddleActivityConstant C q Cfr lam *
          lowerSaddleActivity C.smoothness d (highCompleteSourceSaddleCoefficient C)
            (highCompleteSourceSaddleTheta C) Cω (shrunkDensityExponent C.densityLower C.densityUpper) x := by
  let a := C.densityLower; let b := C.densityUpper
  have ha := C.densityLower_pos; have hab := C.densityLower_lt_one.trans C.one_lt_densityUpper
  let tau := densityIntervalExponent a b
  let c0 := tau + 1
  let m := lowerSaddleCoefficient C.smoothness (d : ℝ) tau
  let theta := lowerSaddleTheta C.smoothness (d : ℝ) tau
  have hτ : 0 < tau := densityIntervalExponent_pos ha hab
  have hc0 : 1 ≤ c0 := by dsimp [c0]; linarith
  have hm : 0 < m := lowerSaddleCoefficient_pos hs hd hτ
  have htheta : 0 < theta := lowerSaddleTheta_pos hs hd hτ
  obtain ⟨_, _, hcontrol⟩ := exists_actual_lowerExponentControl ha hab
  have hhier := actual_lowerAlias_hierarchy (Cact := higherBandSourceCact d a b c0 lam)
    (Cs := 1) hs hd ha hab (higherBandSourceCact_positive d ha hab) (by norm_num) Cω
  have hM := lowerSaddleM_tendsto_atTop hm
  have hN := lowerSaddleN_tendsto_atTop hs hd hm htheta hcontrol Cω
  filter_upwards [hhier, hM.inv_tendsto_atTop.eventually (gt_mem_nhds (by linarith : (0 : ℝ) < (b - a) / 2)),
    hM.eventually (eventually_ge_atTop (1 : ℝ)), hN.eventually (eventually_ge_atTop (1 : ℝ)),
    eventually_gt_atTop (0 : ℝ)] with x hx hsh hMx hNx hxp
  change LowerAliasHierarchy C.smoothness (d : ℝ) m theta Cω (higherBandSourceCact d a b c0 lam) 1 c0
    (shrunkDensityExponent a b) x at hx
  rcases hx with ⟨_, htau_le, hbase, _, _, hq21, hq1, hDq, _, hsingle, _, _⟩
  let M := lowerSaddleM m x; let D := lowerSaddleD (d : ℝ) m x
  let k := lowerSaddleGrid d m theta Cω x
  let N := lowerSaddleN C.smoothness (d : ℝ) m theta Cω (shrunkDensityExponent a b) x
  let mu := lowerSaddleMu (d : ℝ) m theta Cω x
  let ell := lowerAliasCutoff C.smoothness (d : ℝ) m theta Cω c0 (shrunkDensityExponent a b) x
  have hD : 1 ≤ D := by
    have hc : ((d : ℝ) + 8) / 4 * (M : ℝ) ≤ (D : ℝ) := Nat.le_ceil _
    have hh : (1 : ℝ) ≤ D := by change (1 : ℝ) ≤ lowerSaddleD (d : ℝ) m x; change (1 : ℝ) ≤ M at hMx; nlinarith
    exact_mod_cast hh
  have hmu : 0 ≤ mu := by dsimp [mu]; rw [lowerSaddleMu_eq_exp hxp]; exact (Real.exp_pos _).le
  have hshrink : a + (M : ℝ)⁻¹ < b - (M : ℝ)⁻¹ := by change (M : ℝ)⁻¹ < (b - a) / 2 at hsh; linarith
  have hDN : (D : ℝ) * Real.exp (c0 * (D : ℝ)) ≤ N :=
    (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by nlinarith : c0 * (D : ℝ) ≤ c0 * ((D : ℝ) + 1)))
      (Nat.cast_nonneg D)).trans (by simpa only [one_mul] using hsingle)
  have hb := sourceRows_shrunk_activity_bound (k := k) (M := M) (q := q) (NeZero.pos d) hD
    a b Cfr lam N mu c0
    (lowerAliasQ C.smoothness (d : ℝ) m theta Cω (higherBandSourceCact d a b c0 lam) 1 (shrunkDensityExponent a b) x)
    (lowerAliasQ C.smoothness (d : ℝ) m theta Cω (higherBandSourceCact d a b c0 lam) 2 (shrunkDensityExponent a b) x)
    ha hshrink htau_le hc0 hNx hmu hbase hDN rfl rfl hq1 hq21 hDq
  have hmass_eq : highRowTotalMass (completeSourceSaddleRows C q Cfr lam Cω x).rowMass =
      highRowTotalMass (sourceRowData d k D M q (a + (M : ℝ)⁻¹) (b - (M : ℝ)⁻¹) Cfr lam ell N mu).rowMass := by
    dsimp only [completeSourceSaddleRows, completeSourceRows, a, b, tau, c0, m, theta, M, D, k, N, ell, mu,
      highCompleteSourceSaddleCoefficient, highCompleteSourceSaddleTheta]
    exact @congrArg (ℝ × ℝ) ℝ (C.densityLower + 1 / (M : ℝ), C.densityUpper - 1 / (M : ℝ))
      (C.densityLower + (M : ℝ)⁻¹, C.densityUpper - (M : ℝ)⁻¹)
      (fun z => highRowTotalMass (sourceRowData d k D M q z.1 z.2 Cfr lam ell N mu).rowMass) (by simp [one_div])
  have hc : sourceActivityConstant d q Cfr (uniformOrdinaryDensityActivityBase a b c0) lam ≤
      sourceSaddleActivityConstant d q a b Cfr lam := by unfold sourceSaddleActivityConstant; dsimp [c0, tau]; linarith
  have htot := (hmass_eq.trans_le hb).trans
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hc (sq_nonneg N)) (Real.exp_pos _).le)
  refine (div_le_div_of_nonneg_right htot (highCenterMix_mem C).1.le).trans_eq ?_
  dsimp only [completeSourceSaddleActivityConstant, lowerSaddleActivity, a, b, tau, m, theta, M, N,
    highCompleteSourceSaddleCoefficient, highCompleteSourceSaddleTheta]; ring

private theorem completeSourceSaddle_eta_eq {d : ℕ} (C : ModelConstants d) (Cω cf x : ℝ) :
    cf * (lowerSaddleGrid d (highCompleteSourceSaddleCoefficient C)
      (highCompleteSourceSaddleTheta C) Cω x : ℝ) ^ (-C.smoothness) =
      lowerSaddleEta C.smoothness d (highCompleteSourceSaddleCoefficient C)
        (highCompleteSourceSaddleTheta C) Cω cf x := by
  unfold lowerSaddleEta lowerSaddleH
  rw [Real.inv_rpow (lowerSaddleGrid_positive _ _ _ _ _).le, Real.rpow_neg (lowerSaddleGrid_positive _ _ _ _ _).le]

private theorem eventually_completeSourceSaddle_parameters {d : ℕ} [NeZero d]
    (C : ModelConstants d) (hs : 1 < C.smoothness) (hd : 4 * C.smoothness < (d : ℝ))
    {cf eta0 cm : ℝ} (_hcf : 0 < cf) (heta0 : 0 < eta0) (hcm : 0 < cm) (Cω : ℝ) :
    ∀ᶠ x : ℝ in atTop,
      let m := highCompleteSourceSaddleCoefficient C
      let theta := highCompleteSourceSaddleTheta C
      let k := lowerSaddleGrid d m theta Cω x
      let M := lowerSaddleM m x
      let D := lowerSaddleD d m x
      let N := lowerSaddleN C.smoothness d m theta Cω (shrunkDensityExponent C.densityLower C.densityUpper) x
      let ell := lowerAliasCutoff C.smoothness d m theta Cω
        (densityIntervalExponent C.densityLower C.densityUpper + 1)
        (shrunkDensityExponent C.densityLower C.densityUpper) x
      4 ≤ k ∧ 3 ≤ D ∧ highCenterResolutionThreshold C ≤ (M : ℝ) ∧
      0 < ell ∧ ell < N ∧ cf * (k : ℝ) ^ (-C.smoothness) ≤ eta0 ∧
      8 * highHistoryMassParameter d k C.densityLower C.densityUpper * x ≤ cm / (M : ℝ) ∧
      1 ≤ lowerSaddleActivity C.smoothness d m theta Cω
        (shrunkDensityExponent C.densityLower C.densityUpper) x := by
  let m := highCompleteSourceSaddleCoefficient C
  let theta := highCompleteSourceSaddleTheta C
  let tau := densityIntervalExponent C.densityLower C.densityUpper
  have hab := C.densityLower_lt_one.trans C.one_lt_densityUpper
  have htau : 0 < tau := densityIntervalExponent_pos C.densityLower_pos hab
  have hm : 0 < m := lowerSaddleCoefficient_pos hs hd htau
  have htheta : 0 < theta := lowerSaddleTheta_pos hs hd htau
  have hd0 : (0 : ℝ) < d := by linarith
  obtain ⟨_, _, hcontrol⟩ := exists_actual_lowerExponentControl C.densityLower_pos hab
  have hgrid : Tendsto (lowerSaddleGrid d m theta Cω) atTop atTop :=
    tendsto_natCast_atTop_iff.mp (lowerSaddleGrid_tendsto_atTop hd0 hm htheta Cω)
  filter_upwards [hgrid.eventually (eventually_ge_atTop 4),
    (lowerSaddleM_tendsto_atTop hm).eventually (eventually_ge_atTop (max (highCenterResolutionThreshold C) 3)),
    (lowerSaddleN_tendsto_atTop hs hd hm htheta hcontrol Cω).eventually (eventually_ge_atTop (1 : ℝ)),
    (lowerSaddleEta_tends_zero C.smoothness_pos hd0 hm htheta Cω cf).eventually (gt_mem_nhds heta0),
    eventually_highHistoryMass_saddle_guard (NeZero.pos d) hm htheta hcm Cω C.densityLower C.densityUpper hab,
    (lowerSaddleM_nat_tendsto_atTop hm).eventually hcontrol] with x hk hM hN heta heps htauMx
  dsimp only
  have hM3 : (3 : ℝ) ≤ lowerSaddleM m x := (le_max_right _ _).trans hM
  have hD : 3 ≤ lowerSaddleD d m x := by
    have hceil := Nat.le_ceil ((d + 8) / 4 * (lowerSaddleM m x : ℝ))
    have hDr : (3 : ℝ) ≤ lowerSaddleD d m x := by dsimp only [lowerSaddleD] at ⊢; nlinarith
    exact_mod_cast hDr
  have hDpos : (0 : ℝ) < lowerSaddleD d m x := by exact_mod_cast (by omega : 0 < lowerSaddleD d m x)
  have hcut : Real.exp (-(tau + 1) * (lowerSaddleD d m x : ℝ)) < 1 := Real.exp_lt_one_iff.mpr (by nlinarith)
  have hell : 0 < lowerAliasCutoff C.smoothness d m theta Cω (tau + 1)
      (shrunkDensityExponent C.densityLower C.densityUpper) x :=
    mul_pos (lowerSaddleN_positive _ _ _ _ _ _ _) (Real.exp_pos _)
  have hellN : lowerAliasCutoff C.smoothness d m theta Cω (tau + 1)
      (shrunkDensityExponent C.densityLower C.densityUpper) x <
      lowerSaddleN C.smoothness d m theta Cω (shrunkDensityExponent C.densityLower C.densityUpper) x := by
    unfold lowerAliasCutoff
    simpa only [mul_one] using mul_lt_mul_of_pos_left hcut (lowerSaddleN_positive _ _ _ _ _ _ _)
  have hB : 1 ≤ lowerSaddleActivity C.smoothness d m theta Cω
      (shrunkDensityExponent C.densityLower C.densityUpper) x :=
    one_le_mul_of_one_le_of_one_le (by nlinarith only [hN])
      (Real.one_le_exp_iff.mpr (mul_nonneg (htau.le.trans htauMx.1) (Nat.cast_nonneg _)))
  exact ⟨hk, hD, (le_max_left _ _).trans hM, hell, hellN,
    (completeSourceSaddle_eta_eq C Cω cf x).trans_le heta.le, heps.2, hB⟩

private theorem eventually_lowerSaddle_fine_field_energy_scale {s d m theta tau Ctau : ℝ}
    {tauM : ℕ → ℝ} (hs : 1 < s) (hd : 4 * s < d) (hm : 0 < m) (htheta : 0 < theta)
    (hcontrol : LowerExponentControl tauM tau Ctau) (C c0 : ℝ) :
    ∀ᶠ x : ℝ in atTop,
      Real.exp (2 * tauM (lowerSaddleM m x) * lowerSaddleM m x) *
        lowerSaddleMu d m theta C x ^ 4 *
        lowerAliasCutoff s d m theta C c0 tauM x ^ (4 - 2 * d) ≤
          lowerSaddleMu d m theta C x ^ 2 * lowerSaddleN s d m theta C tauM x ^ (-d) := by
  have hd0 : 0 < d := by linarith only [hs, hd]
  have hd4 : 4 < d := by linarith only [hs, hd]
  have hM := lowerSaddleM_tendsto_atTop hm
  have hM2 : Tendsto (fun x : ℝ => (lowerSaddleM m x : ℝ) ^ 2) atTop atTop :=
    (tendsto_pow_atTop (by decide : (2 : ℕ) ≠ 0)).comp hM
  let scale (x : ℝ) := Real.exp (2 * tauM (lowerSaddleM m x) * lowerSaddleM m x) *
    lowerSaddleN s d m theta C tauM x ^ (4 - d) * Real.exp (c0 * (2 * d - 4) * lowerSaddleD d m x)
  have hscale0 : Tendsto scale atTop (𝓝 0) := by
    have hh := (((lowerSaddleTau_limit hm hcontrol).mul hM.inv_tendsto_atTop).const_mul 2).add
      (lowerSaddleLogN_div_M_sq_limit hd0 hm htheta hcontrol s C |>.const_mul (4 - d)) |>.add
      ((lowerSaddleD_div_M_sq_tends_zero hd0 hm).const_mul (c0 * (2 * d - 4)))
    simp only [mul_zero, zero_add, add_zero] at hh
    refine positive_profile_tends_zero_of_log_div_negative
      (c := (4 - d) * (((d - 4 * s) / (d * (d + 4))) / m ^ 2)) hM2
      (mul_neg_of_neg_of_pos (by linarith only [hd4]) (by positivity))
      (Filter.Eventually.of_forall fun x => by dsimp [scale]; positivity [lowerSaddleN_positive s d m theta C tauM x])
      (hh.congr' ?_)
    filter_upwards [hM.eventually (eventually_gt_atTop (0 : ℝ))] with x hMx
    dsimp [scale]
    have hNp := lowerSaddleN_positive s d m theta C tauM x
    rw [Real.log_mul (by positivity) (Real.exp_pos _).ne',
      Real.log_mul (Real.exp_pos _).ne' (Real.rpow_pos_of_pos hNp _).ne',
      Real.log_exp, Real.log_exp, Real.log_rpow hNp]
    field_simp [hMx.ne']
  filter_upwards [hscale0.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1)),
    (lowerSaddleMu_tends_zero hd0 hm htheta C).eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1)),
    eventually_gt_atTop (0 : ℝ)] with x hsc hmu hx
  have hN := lowerSaddleN_positive s d m theta C tauM x
  have hmu0 : 0 ≤ lowerSaddleMu d m theta C x :=
    mul_nonneg hx.le (Real.rpow_pos_of_pos (lowerSaddleH_positive d m theta C x) _).le
  unfold lowerAliasCutoff
  rw [Real.mul_rpow hN.le (Real.exp_pos _).le, ← Real.exp_mul,
    show (-c0 * ↑(lowerSaddleD d m x)) * (4 - 2 * d) = c0 * (2 * d - 4) * lowerSaddleD d m x by ring]
  have hprod : lowerSaddleMu d m theta C x ^ 2 * scale x ≤ 1 := by
    simpa only [one_mul] using mul_le_mul (pow_le_one₀ hmu0 hmu.le) hsc.le (by dsimp [scale]; positivity) zero_le_one
  have hNadd : lowerSaddleN s d m theta C tauM x ^ (-d) * lowerSaddleN s d m theta C tauM x ^ (4 - d) =
      lowerSaddleN s d m theta C tauM x ^ (4 - 2 * d) := by rw [← Real.rpow_add hN]; congr 1; ring
  calc _ = (lowerSaddleMu d m theta C x ^ 2 * lowerSaddleN s d m theta C tauM x ^ (-d)) *
        (lowerSaddleMu d m theta C x ^ 2 * scale x) := by dsimp [scale]; rw [← hNadd]; ring
    _ ≤ (lowerSaddleMu d m theta C x ^ 2 * lowerSaddleN s d m theta C tauM x ^ (-d)) * 1 :=
        mul_le_mul_of_nonneg_left hprod (by positivity)
    _ = _ := mul_one _

private abbrev completeSaddleM {d : ℕ} (C : ModelConstants d) (x : ℝ) :=
  lowerSaddleM (highCompleteSourceSaddleCoefficient C) x
private abbrev completeSaddleD {d : ℕ} (C : ModelConstants d) (x : ℝ) :=
  lowerSaddleD d (highCompleteSourceSaddleCoefficient C) x
private abbrev completeSaddleN {d : ℕ} (C : ModelConstants d) (Cω x : ℝ) :=
  lowerSaddleN C.smoothness d (highCompleteSourceSaddleCoefficient C)
    (highCompleteSourceSaddleTheta C) Cω (shrunkDensityExponent C.densityLower C.densityUpper) x
private abbrev completeSaddleMu {d : ℕ} (C : ModelConstants d) (Cω x : ℝ) :=
  lowerSaddleMu d (highCompleteSourceSaddleCoefficient C) (highCompleteSourceSaddleTheta C) Cω x
private abbrev completeSaddleEta {d : ℕ} (C : ModelConstants d) (Cω cf x : ℝ) :=
  lowerSaddleEta C.smoothness d (highCompleteSourceSaddleCoefficient C)
    (highCompleteSourceSaddleTheta C) Cω cf x
private abbrev completeSaddleC0 {d : ℕ} (C : ModelConstants d) :=
  densityIntervalExponent C.densityLower C.densityUpper + 1
private abbrev completeSaddleEll {d : ℕ} (C : ModelConstants d) (Cω x : ℝ) :=
  lowerAliasCutoff C.smoothness d (highCompleteSourceSaddleCoefficient C)
    (highCompleteSourceSaddleTheta C) Cω (completeSaddleC0 C)
    (shrunkDensityExponent C.densityLower C.densityUpper) x
private abbrev completeSaddleTau {d : ℕ} (C : ModelConstants d) (x : ℝ) :=
  shrunkDensityExponent C.densityLower C.densityUpper (completeSaddleM C x)
private abbrev completeSaddleAD {d : ℕ} (C : ModelConstants d) (x : ℝ) :=
  C.densityLower + 1 / (completeSaddleM C x : ℝ)
private abbrev completeSaddleBD {d : ℕ} (C : ModelConstants d) (x : ℝ) :=
  C.densityUpper - 1 / (completeSaddleM C x : ℝ)

private structure CompleteSaddleEnergyGuards {d : ℕ} (C : ModelConstants d) (Cω cf x : ℝ) : Prop where
  resolution : highCenterResolutionThreshold C ≤ (completeSaddleM C x : ℝ)
  N_one : 1 ≤ completeSaddleN C Cω x
  mu_positive : 0 < completeSaddleMu C Cω x
  mu_one : completeSaddleMu C Cω x ≤ 1
  mu_log : completeSaddleMu C Cω x * (1 + Real.log (completeSaddleN C Cω x)) ≤ 1
  response_taylor : (completeSaddleEta C Cω cf x) ^ (4 * lowerSaddleResponseOrder C.smoothness d) *
    (completeSaddleN C Cω x) ^ d ≤ 1
  tau_nonneg : 0 ≤ completeSaddleTau C x
  tau_le : completeSaddleTau C x ≤ completeSaddleC0 C
  degree_multiple : (completeSaddleD C x : ℝ) ≤ (((d : ℝ) + 8) / 4 + 1) * (completeSaddleM C x : ℝ)
  ell_one : 1 ≤ completeSaddleEll C Cω x
  ell_lt_N : completeSaddleEll C Cω x < completeSaddleN C Cω x
  field_scale_square : Real.exp (2 * completeSaddleTau C x * (completeSaddleM C x : ℝ)) *
    (completeSaddleMu C Cω x) ^ 4 * ((completeSaddleEll C Cω x) ^ (2 - (d : ℝ))) ^ 2 ≤
      (completeSaddleMu C Cω x) ^ 2 * (completeSaddleN C Cω x) ^ (-(d : ℝ))
  bd_nonneg : 0 ≤ completeSaddleBD C x
  bd_le : completeSaddleBD C x ≤ C.densityUpper
  ad_positive : 0 < completeSaddleAD C x
  density_interval : completeSaddleAD C x < completeSaddleBD C x

private theorem eventually_completeSaddleEnergyGuards {d : ℕ} [NeZero d]
    (C : ModelConstants d) (hs : 1 < C.smoothness) (hd : 4 * C.smoothness < (d : ℝ))
    {cf : ℝ} (hcf : 0 < cf) (Cω : ℝ) :
    ∀ᶠ n : ℕ in atTop, CompleteSaddleEnergyGuards C Cω cf n := by
  let m := highCompleteSourceSaddleCoefficient C
  let theta := highCompleteSourceSaddleTheta C
  let tau := densityIntervalExponent C.densityLower C.densityUpper
  have hab := C.densityLower_lt_one.trans C.one_lt_densityUpper
  have htau : 0 < tau := densityIntervalExponent_pos C.densityLower_pos hab
  have hm : 0 < m := lowerSaddleCoefficient_pos hs hd htau
  have htheta : 0 < theta := lowerSaddleTheta_pos hs hd htau
  obtain ⟨_, _, hcontrol⟩ := exists_actual_lowerExponentControl C.densityLower_pos hab
  obtain ⟨K, _, hreg⟩ := actual_lowerSaddle_fixed_regime_window hs hd C.densityLower_pos hab hcf
  have hhier := actual_lowerAlias_hierarchy (Cact := 1) (Cs := 1) hs hd
    C.densityLower_pos hab (by norm_num) (by norm_num) Cω
  have hscale := eventually_lowerSaddle_fine_field_energy_scale hs hd hm htheta hcontrol Cω (tau + 1)
  have hparams := eventually_completeSourceSaddle_parameters C hs hd hcf
    (by norm_num : (0 : ℝ) < 1) (by norm_num : (0 : ℝ) < 1) Cω
  filter_upwards [tendsto_natCast_atTop_atTop.eventually (hreg Cω 1 0 (by norm_num)),
    tendsto_natCast_atTop_atTop.eventually hhier,
    tendsto_natCast_atTop_atTop.eventually hscale,
    tendsto_natCast_atTop_atTop.eventually hparams,
    tendsto_natCast_atTop_atTop.eventually ((lowerSaddleM_tendsto_atTop hm).eventually (eventually_ge_atTop (1 : ℝ)))]
    with n hregn hhiern hscalen hpn hMone
  change LowerSaddleReg K 1 C.smoothness d m theta Cω cf 0
    (shrunkDensityExponent C.densityLower C.densityUpper) n at hregn
  rcases hregn with ⟨_, _, hN, hmu, hmu1, _, _, _, _, _, _, hqt⟩
  change LowerAliasHierarchy C.smoothness d m theta Cω 1 1 (tau + 1)
    (shrunkDensityExponent C.densityLower C.densityUpper) n at hhiern
  rcases hhiern with ⟨hell, htaule, hmulog, _, _, _, _, _, _, _, _, _⟩
  dsimp only at hpn
  obtain ⟨had, hadb⟩ := high_source_interval_numeric C (completeSaddleM C n : ℝ) hpn.2.2.1
  have htn : 0 ≤ completeSaddleTau C n :=
    (densityIntervalExponent_pos (by simpa only [one_div] using had) (by simpa only [one_div] using hadb)).le
  have hDM : (completeSaddleD C n : ℝ) ≤ (((d : ℝ) + 8) / 4 + 1) * (completeSaddleM C n : ℝ) := by
    have h := Nat.ceil_lt_add_one (mul_nonneg (by positivity : 0 ≤ ((d : ℝ) + 8) / 4) (Nat.cast_nonneg (completeSaddleM C n)))
    change (completeSaddleD C n : ℝ) < ((d : ℝ) + 8) / 4 * (completeSaddleM C n : ℝ) + 1 at h
    nlinarith only [h, hMone]
  have hsquare : ((completeSaddleEll C Cω n) ^ (2 - (d : ℝ))) ^ 2 = (completeSaddleEll C Cω n) ^ (4 - 2 * (d : ℝ)) := by
    rw [← Real.rpow_mul_natCast (by linarith only [hell] : 0 ≤ completeSaddleEll C Cω n)]; congr 1; ring
  refine ⟨hpn.2.2.1, hN, hmu, hmu1.le, hmulog,
    by simpa only [lowerSaddleResponseQuantity, Real.rpow_natCast] using hqt,
    htn, htaule, hDM, hell.le, hpn.2.2.2.2.1, by rw [hsquare]; exact hscalen,
    had.le.trans hadb.le, sub_le_self _ (one_div_nonneg.mpr (Nat.cast_nonneg _)), had, hadb⟩

private def completeSaddleGeometryEnvelope {d : ℕ} (C : ModelConstants d)
    (Q : LowSmoothnessTernaryConstants C) (Cfr cf Cω : ℝ) (n : ℕ) :
    (r : ℕ) → (Fin r → Covariate d) → ℝ :=
  completeSourceGeometryEnvelope (completeSaddleD C n) (completeSaddleM C n)
    (ordinaryFineAliasSaddleTargetBound C.smoothness d C.densityLower C.densityUpper)
    (lowerSaddleResponseOrder C.smoothness d) C.densityLower C.densityUpper (completeSaddleC0 C)
    (completeSaddleEll C Cω n) (completeSaddleN C Cω n) (completeSaddleMu C Cω n) Cfr Q.a Q.ρ
    (completeSaddleEta C Cω cf n) (highSeparatedScoreExponentialConstant Q.a Q.ρ C.densityUpper 1 1)
    (completeSourceSaddleActivity C (lowerSaddleResponseOrder C.smoothness d) Cfr (spatialInterpolationLambda d) Cω n)

private def completeSaddleScoreFactor {d : ℕ} (C : ModelConstants d) (Q : LowSmoothnessTernaryConstants C) : ℝ :=
  highFixedScoreDenominator C.densityLower Q.c * (2 : ℝ) ^ d
private def completeSaddleDegreeFactor (d : ℕ) : ℝ := ((d : ℝ) + 8) / 4 + 1
private def completeSaddleOrdinaryConstant {d : ℕ} (C : ModelConstants d) (Q : LowSmoothnessTernaryConstants C) (Cfr : ℝ) : ℝ :=
  ordinaryFineAliasFactorialConstant C.smoothness d (lowerSaddleResponseOrder C.smoothness d)
    C.densityLower C.densityUpper Cfr Q.a Q.ρ (completeSaddleScoreFactor C Q)
private def completeSaddleDefectConstant {d : ℕ} (C : ModelConstants d) (Q : LowSmoothnessTernaryConstants C) (Cfr : ℝ) : ℝ :=
  completeGeometryDefectConstant d (lowerSaddleResponseOrder C.smoothness d) C.densityUpper Cfr Q.a Q.ρ
    (completeSaddleScoreFactor C Q)
private def completeSaddleFieldConstant {d : ℕ} (C : ModelConstants d) (Q : LowSmoothnessTernaryConstants C) (Cfr : ℝ) : ℝ :=
  completeGeometryFieldConstant d (lowerSaddleResponseOrder C.smoothness d) C.densityLower C.densityUpper Cfr Q.a Q.ρ
    (completeSaddleC0 C) (completeSaddleScoreFactor C Q)
private def completeSaddleAliasConstant {d : ℕ} (C : ModelConstants d) (Q : LowSmoothnessTernaryConstants C) (Cfr : ℝ) : ℝ :=
  completeGeometryAliasConstant d (lowerSaddleResponseOrder C.smoothness d) C.densityLower C.densityUpper Cfr Q.a Q.ρ
    (completeSaddleC0 C) (completeSaddleDegreeFactor d) (completeSaddleScoreFactor C Q) (completeSaddleOrdinaryConstant C Q Cfr)
private def completeSaddleExteriorConstant {d : ℕ} (C : ModelConstants d) (Q : LowSmoothnessTernaryConstants C) : ℝ :=
  completeGeometryExteriorConstant d (completeSaddleScoreFactor C Q)
    (highSeparatedScoreExponentialConstant Q.a Q.ρ C.densityUpper 1 1)

private def lowerSaddleRawEnergyBound (s d m θ C cf C5 C6 C7 ch Bl : ℝ) (τM : ℕ → ℝ) (x : ℝ) : ℝ :=
  let η := lowerSaddleEta s d m θ C cf x
  let μ := lowerSaddleMu d m θ C x
  let N := lowerSaddleN s d m θ C τM x
  let M := lowerSaddleM m x
  let D := lowerSaddleD d m x
  3 * (C5 + C7) * η ^ 4 * μ ^ 2 * N ^ (-d) +
    3 * C6 * η ^ 4 * (Real.exp (2 * τM M * M) * N ^ (4 - d)) * (C6 * μ) ^ (M + 1) / (M + 1).factorial +
    Real.exp ch * η ^ 4 * (Bl + 1) ^ 2 * (ch * μ) ^ (D + 1) / (D + 1).factorial

private def completeSaddleEnergyBudget {d : ℕ} (C : ModelConstants d) (Q : LowSmoothnessTernaryConstants C)
    (Cfr cf Cω : ℝ) (n : ℕ) : ℝ :=
  lowerSaddleRawEnergyBound C.smoothness d (highCompleteSourceSaddleCoefficient C)
    (highCompleteSourceSaddleTheta C) Cω cf (completeSaddleDefectConstant C Q Cfr)
    (completeSaddleAliasConstant C Q Cfr) (completeSaddleFieldConstant C Q Cfr) (completeSaddleExteriorConstant C Q)
    (completeSourceSaddleActivity C (lowerSaddleResponseOrder C.smoothness d) Cfr (spatialInterpolationLambda d) Cω n)
    (shrunkDensityExponent C.densityLower C.densityUpper) n

private theorem completeSaddleScoreFactor_pos {d : ℕ} (C : ModelConstants d) (Q : LowSmoothnessTernaryConstants C) :
    0 < completeSaddleScoreFactor C Q := by
  unfold completeSaddleScoreFactor highFixedScoreDenominator; positivity [C.densityLower_pos, Q.c_pos]

private theorem eventually_completeSaddleGeometry_factorial {d : ℕ} [NeZero d]
    (C : ModelConstants d) (Q : LowSmoothnessTernaryConstants C) (hs : 1 < C.smoothness)
    (hd : 4 * C.smoothness < (d : ℝ)) {cf : ℝ} (hcf : 0 < cf) (Cfr Cω : ℝ) :
    ∀ᶠ n : ℕ in atTop,
      (∑ r ∈ Finset.range (n + 1), poissonCountWeight (completeSaddleScoreFactor C Q * completeSaddleMu C Cω n) r *
        ∫ U, completeSaddleGeometryEnvelope C Q Cfr cf Cω n r U ∂fullSpatialPatchDesign d r) ≤
          completeSaddleEnergyBudget C Q Cfr cf Cω n := by
  have hCs := (completeSaddleScoreFactor_pos C Q).le
  have hd5 : 5 ≤ d := by
    have h : (4 : ℝ) < d := by linarith only [hs, hd]
    have h' : 4 < d := by exact_mod_cast h
    omega
  have hbd : 0 ≤ C.densityUpper := (zero_lt_one.trans C.one_lt_densityUpper).le
  have hOrdConst : 0 ≤ completeSaddleOrdinaryConstant C Q Cfr :=
    zero_le_one.trans (ordinaryFineAliasFactorialConstant_ge_one hbd hCs)
  have hCal : 0 ≤ finePairSaddleAliasFactorialConstant d (lowerSaddleResponseOrder C.smoothness d)
      C.densityLower C.densityUpper Cfr Q.a Q.ρ (completeSaddleC0 C) (completeSaddleDegreeFactor d)
        (3 * completeSaddleScoreFactor C Q) := by
    unfold finePairSaddleAliasFactorialConstant aliasTailConstant
    have := finePairUniformSpatialPrefactor_nonneg d (lowerSaddleResponseOrder C.smoothness d)
      C.densityLower C.densityUpper Cfr Q.a Q.ρ (completeSaddleC0 C)
    have := spatialInverseFourConstant_nonneg d
    have := finePairAliasGeometricBase_nonneg d C.densityUpper
    positivity
  filter_upwards [eventually_completeSaddleEnergyGuards C hs hd hcf Cω,
    tendsto_natCast_atTop_atTop.eventually (eventually_ordinaryFineAlias_factorial_tail
      hs hd C.densityLower_pos (C.densityLower_lt_one.trans C.one_lt_densityUpper) Cω cf
      (lowerSaddleResponseOrder C.smoothness d) Cfr Q.a Q.ρ (completeSaddleScoreFactor C Q) hCs),
    tendsto_natCast_atTop_atTop.eventually (eventually_completeSourceSaddle_parameters C hs hd hcf
      (by norm_num : (0 : ℝ) < 1) (by norm_num : (0 : ℝ) < 1) Cω)] with n G hO hphysical
  let M := completeSaddleM C n; let D := completeSaddleD C n
  let q := lowerSaddleResponseOrder C.smoothness d
  let N := completeSaddleN C Cω n; let mu := completeSaddleMu C Cω n
  let ell := completeSaddleEll C Cω n; let eta := completeSaddleEta C Cω cf n
  let tau := completeSaddleTau C n; let c0 := completeSaddleC0 C
  let Cs := completeSaddleScoreFactor C Q; let K := completeSaddleDegreeFactor d
  let R := ordinaryFineAliasSaddleTargetBound C.smoothness d C.densityLower C.densityUpper
  let Cord := completeSaddleOrdinaryConstant C Q Cfr
  let Bl := completeSourceSaddleActivity C q Cfr (spatialInterpolationLambda d) Cω n
  let Chi := highSeparatedScoreExponentialConstant Q.a Q.ρ C.densityUpper 1 1
  have hext : exteriorTau (((C.densityLower + (M : ℝ)⁻¹) + (C.densityUpper - (M : ℝ)⁻¹)) /
      ((C.densityUpper - (M : ℝ)⁻¹) - (C.densityLower + (M : ℝ)⁻¹))) = tau := by
    simpa only [tau, completeSaddleTau, shrunkDensityExponent, densityIntervalExponent,
      completeSaddleAD, completeSaddleBD, one_div] using
      exteriorTau_sqrt_ratio (completeSaddleAD C n) (completeSaddleBD C n) G.ad_positive G.density_interval
  have hfield : Real.exp (2 * exteriorTau (((C.densityLower + (M : ℝ)⁻¹) + (C.densityUpper - (M : ℝ)⁻¹)) /
      ((C.densityUpper - (M : ℝ)⁻¹) - (C.densityLower + (M : ℝ)⁻¹))) * M) * (ell ^ (2 - (d : ℝ))) ^ 2 * mu ^ 4 ≤
      mu ^ 2 * N ^ (-(d : ℝ)) := by rw [hext]; convert G.field_scale_square using 1 <;> ring
  have hOrd : (∑ j ∈ Finset.range (D - M), poissonCountWeight (Cs * mu) (M + 1 + j) *
      ∫ U, ordinaryFineAliasFamilyResponseSquareEnvelope (d := d) (n := M + 1 + j) (F := D)
        (ordinaryFineAliasTargetSet d D ell N mu) M R q C.densityLower C.densityUpper c0 Cfr Q.a Q.ρ eta ell
        (fun t => higherBandTargetScale d t N mu) U ∂fullSpatialPatchDesign d (M + 1 + j)) ≤
      Cord * (eta ^ 4 * Real.exp (2 * tau * M) * N ^ (4 - (d : ℝ))) * poissonCountWeight (Cord * mu) (M + 1) := by
    simpa only [M, D, q, N, mu, ell, eta, tau, c0, Cs, R, Cord, completeSaddleOrdinaryConstant,
      highCompleteSourceSaddleCoefficient, highCompleteSourceSaddleTheta, completeSaddleM, completeSaddleD,
      completeSaddleN, completeSaddleMu, completeSaddleEll, completeSaddleEta, completeSaddleTau, completeSaddleC0] using hO
  have hHigher := finite_complete_higher_geometry_energy_le hd5 hphysical.2.1 C.densityLower C.densityUpper c0 K ell N mu
    M R q Cfr Q.a Q.ρ eta Cs _ C.densityLower_pos Q.a_pos
    (by simpa only [completeSaddleAD, completeSaddleBD, one_div] using G.density_interval) (hext.trans_le G.tau_le)
    (by dsimp [c0, completeSaddleC0]; linarith [densityIntervalExponent_pos C.densityLower_pos (C.densityLower_lt_one.trans C.one_lt_densityUpper)])
    (by dsimp [K, completeSaddleDegreeFactor]; positivity) hCs G.ell_one G.ell_lt_N.le rfl G.degree_multiple
    G.mu_positive G.mu_one G.mu_log G.response_taylor hfield hOrd
  have h := completeSourceGeometryEnvelope_factorial_from_higher (NeZero.pos d) D M R q n hphysical.2.1
    C.densityLower C.densityUpper c0 K ell N mu Cfr Q.a Q.ρ eta Chi Bl Cs Cord tau
    (lt_of_lt_of_le zero_lt_one G.N_one) hCs G.mu_positive.le G.mu_one
    (by simpa only [completeSaddleBD, one_div] using G.bd_nonneg) (by simpa only [completeSaddleBD, one_div] using G.bd_le)
    hOrdConst hCal G.tau_nonneg hHigher
  convert h using 1 <;> (try dsimp only [completeSaddleGeometryEnvelope, completeSaddleEnergyBudget,
    completeSaddleDefectConstant, completeSaddleAliasConstant, completeSaddleFieldConstant, completeSaddleExteriorConstant,
    lowerSaddleRawEnergyBound, M, D, q, N, mu, ell, eta, tau, c0, Cs, K, R, Cord, Bl, Chi,
    completeSaddleM, completeSaddleD, completeSaddleN, completeSaddleMu, completeSaddleEll,
    completeSaddleEta, completeSaddleTau, completeSaddleC0]) <;> (try simp only [poissonCountWeight]) <;> ring

private theorem sourceSaddleHigherFamily_eventually_legal (d : ℕ)
    (s a b shift : ℝ) (hs : 1 < s) (hd : 4 * s < (d : ℝ)) (ha : 0 < a) (hab : a < b) :
    let tau := densityIntervalExponent a b
    let m := lowerSaddleCoefficient s (d : ℝ) tau
    let theta := lowerSaddleTheta s (d : ℝ) tau
    ∀ᶠ x in atTop,
      let M := lowerSaddleM m x
      let N := lowerSaddleN s (d : ℝ) m theta shift (shrunkDensityExponent a b) x
      let mu := lowerSaddleMu (d : ℝ) m theta shift x
      let ell := lowerAliasCutoff s (d : ℝ) m theta shift (tau + 1) (shrunkDensityExponent a b) x
      1 ≤ ell ∧ (∀ r : ℕ, 0 < higherBandTargetScale d r N mu) ∧
        (∀ r : ℕ, ell < higherBandTargetScale d r N mu → r ≤ M) := by
  dsimp only
  let tau := densityIntervalExponent a b
  let m := lowerSaddleCoefficient s (d : ℝ) tau
  let theta := lowerSaddleTheta s (d : ℝ) tau
  have hτ := densityIntervalExponent_pos ha hab
  have hm := lowerSaddleCoefficient_pos hs hd hτ
  have htheta := lowerSaddleTheta_pos hs hd hτ
  obtain ⟨_, _, hcontrol⟩ := exists_actual_lowerExponentControl ha hab
  have hN := lowerSaddleN_tendsto_atTop hs hd hm htheta hcontrol shift
  have hhier := actual_lowerAlias_hierarchy (Cact := 1) (Cs := 1) hs hd ha hab (by norm_num) (by norm_num) shift
  filter_upwards [hhier, hN.eventually (eventually_ge_atTop (1 : ℝ)), eventually_gt_atTop (0 : ℝ)]
    with x hx hNx hxp
  change LowerAliasHierarchy s (d : ℝ) m theta shift 1 1 (tau + 1) (shrunkDensityExponent a b) x at hx
  rcases hx with ⟨hell, _, _, _, _, _, _, _, _, _, hRM, hFine⟩
  have hmu : 0 < lowerSaddleMu (d : ℝ) m theta shift x := by rw [lowerSaddleMu_eq_exp hxp]; exact Real.exp_pos _
  have hH : 0 < 1 + Real.log (lowerSaddleN s (d : ℝ) m theta shift (shrunkDensityExponent a b) x) := by
    linarith [Real.log_nonneg hNx]
  refine ⟨hell.le, fun r => mul_pos (by linarith) (Real.rpow_pos_of_pos (mul_pos hmu hH) _),
    fun r hr => (hFine r hr).trans hRM⟩

private theorem completeSaddleGeometry_witness {d : ℕ} [NeZero d]
    (C : ModelConstants d) (Q : LowSmoothnessTernaryConstants C)
    (hs : 1 < C.smoothness) (hd : 4 * C.smoothness < (d : ℝ)) :
    ∃ Cfr0 eta0 : ℝ, 1 ≤ Cfr0 ∧ 0 < eta0 ∧
      ∀ Cfr cf : ℝ, Cfr0 ≤ Cfr → 0 < cf → ∀ Cω : ℝ,
      ∀ᶠ n : ℕ in atTop,
      let m := highCompleteSourceSaddleCoefficient C
      let theta := highCompleteSourceSaddleTheta C
      let k := lowerSaddleGrid d m theta Cω n
      let D := completeSaddleD C n
      let M := completeSaddleM C n
      let q := lowerSaddleResponseOrder C.smoothness d
      let ell := completeSaddleEll C Cω n
      let N := completeSaddleN C Cω n
      let mu := completeSaddleMu C Cω n
      let eta := completeSaddleEta C Cω cf n
      ∀ (_ : NeZero k) (_ : LinearOrder (HighWindowLabels d k)),
      let R := completeSourceRows C k D M q Cfr (spatialInterpolationLambda d) ell N mu
      ∃ E : ℝ, 0 ≤ E ∧
        E ≤ lowerSaddleRawEnergyBound C.smoothness d m theta Cω cf (completeSaddleDefectConstant C Q Cfr)
          (completeSaddleAliasConstant C Q Cfr) (completeSaddleFieldConstant C Q Cfr) (completeSaddleExteriorConstant C Q)
          (highRowTotalMass R.rowMass / highCenterMix C) (shrunkDensityExponent C.densityLower C.densityUpper) n ∧
        (∀ r, Integrable (completeSaddleGeometryEnvelope C Q Cfr cf Cω n r) (fullSpatialPatchDesign d r)) ∧
        (∀ r U, 0 ≤ completeSaddleGeometryEnvelope C Q Cfr cf Cω n r U) ∧
        (∀ V : ℝ, |V - Q.v| ≤ Q.ρ →
          ∀ h : HighCompleteSourceHistory C k D M q Cfr (spatialInterpolationLambda d) ell N mu,
          ∀ j r x, (∀ i, x i ∈ highTorusPatch d k j) →
          selectedRawSquareEnergy (highUnionSourceRawNumerator C R r Q.a V eta h j) x ≤
            completeSaddleGeometryEnvelope C Q Cfr cf Cω n r (highPatchProductChart d k j x)) ∧
        highSourceSpatialSeries d k n C.densityLower Q.c (fun _j => completeSaddleGeometryEnvelope C Q Cfr cf Cω n) ≤
          (3 ^ d : ℕ) * (k : ℝ) ^ d * E := by
  obtain ⟨Cfr0, eta0, hfr0, heta0, hcap⟩ := completeSource_original_all_geometry C Q
  refine ⟨Cfr0, eta0, hfr0, heta0, fun Cfr cf hfr hcf Cω => ?_⟩
  have hd5 : 5 ≤ d := by
    have h : (4 : ℝ) < d := by linarith only [hs, hd]
    have h' : 4 < d := by exact_mod_cast h
    omega
  filter_upwards [eventually_completeSaddleGeometry_factorial C Q hs hd hcf Cfr Cω,
    eventually_completeSaddleEnergyGuards C hs hd hcf Cω,
    tendsto_natCast_atTop_atTop.eventually
      (sourceSaddleHigherFamily_eventually_legal d C.smoothness C.densityLower C.densityUpper Cω
        hs hd C.densityLower_pos (C.densityLower_lt_one.trans C.one_lt_densityUpper)),
    tendsto_natCast_atTop_atTop.eventually (eventually_ordinaryFineAlias_saddle_guards hs hd
      C.densityLower_pos (C.densityLower_lt_one.trans C.one_lt_densityUpper) Cω),
    tendsto_natCast_atTop_atTop.eventually (eventually_completeSourceSaddle_parameters C hs hd hcf
      heta0 (by norm_num : (0 : ℝ) < 1) Cω)] with n henergy G hselection GO hphysical
  dsimp only
  let m := highCompleteSourceSaddleCoefficient C
  let theta := highCompleteSourceSaddleTheta C
  let k := lowerSaddleGrid d m theta Cω n
  let D := completeSaddleD C n; let M := completeSaddleM C n
  let q := lowerSaddleResponseOrder C.smoothness d
  let ell := completeSaddleEll C Cω n; let N := completeSaddleN C Cω n
  let mu := completeSaddleMu C Cω n; let eta := completeSaddleEta C Cω cf n
  let lam := spatialInterpolationLambda d
  let Rbound := ordinaryFineAliasSaddleTargetBound C.smoothness d C.densityLower C.densityUpper
  intro hk0 horder
  letI := hk0; letI := horder
  let R := completeSourceRows C k D M q Cfr lam ell N mu
  have GS := completeSourceRows_guards C k D M q hphysical.2.1 (by dsimp [q, lowerSaddleResponseOrder]; omega)
    G.resolution Cfr lam ell N mu (hfr0.trans hfr) (lt_of_lt_of_le zero_lt_one G.ell_one) G.ell_lt_N
  let E := completeSaddleEnergyBudget C Q Cfr cf Cω n
  have hE0 : 0 ≤ E := by
    unfold E completeSaddleEnergyBudget lowerSaddleRawEnergyBound
    have h5 : 0 < completeSaddleDefectConstant C Q Cfr := by unfold completeSaddleDefectConstant completeGeometryDefectConstant; positivity
    have h6 : 0 < completeSaddleAliasConstant C Q Cfr := by unfold completeSaddleAliasConstant completeGeometryAliasConstant; positivity
    have h7 : 0 < completeSaddleFieldConstant C Q Cfr := by unfold completeSaddleFieldConstant completeGeometryFieldConstant; positivity
    have hch : 0 < completeSaddleExteriorConstant C Q := by unfold completeSaddleExteriorConstant completeGeometryExteriorConstant; positivity
    have hN := lowerSaddleN_positive C.smoothness d m theta Cω (shrunkDensityExponent C.densityLower C.densityUpper) n
    have hmu : 0 ≤ lowerSaddleMu d m theta Cω n := by unfold lowerSaddleMu; positivity [lowerSaddleH_positive d m theta Cω n]
    positivity
  refine ⟨E, hE0, le_rfl,
    fun r => completeSourceGeometryEnvelope_integrable hd5 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ G.ell_one G.ell_lt_N.le r,
    fun r U => completeSourceGeometryEnvelope_nonneg _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ r U, ?_, ?_⟩
  · intro V hV h j r x hx
    have hI (t : ℕ) (ht : t ∈ ordinaryFineAliasTargetSet d D ell N mu) : 1 ≤ t ∧ t ≤ Rbound :=
      ⟨by have hh := (GO.targets t ht).1; omega, (GO.targets t ht).2⟩
    have hdom := hcap k D M q hk0 horder hphysical.1 hphysical.2.1 (le_max_left _ _) G.resolution
      Cfr (completeSaddleC0 C) ell N mu cf hfr G.ell_one G.ell_lt_N hcf.le hphysical.2.2.2.2.2.1 G.tau_le
      (fun j => hselection.2.1 (j.val + 3)) (fun j => hselection.2.2 (j.val + 3)) Rbound hI V hV j h r x hx
    have hmass : 0 ≤ highRowTotalMass R.rowMass := GS.total_positive.le
    have hB : highRowTotalMass R.rowMass ≤ highRowTotalMass R.rowMass / highCenterMix C :=
      (le_div_iff₀ (highCenterMix_mem C).1).mpr (mul_le_of_le_one_right hmass (highCenterMix_mem C).2.le)
    have hm := completeSourceGeometryEnvelope_mono_total (d := d) D M Rbound q C.densityLower C.densityUpper
      (completeSaddleC0 C) ell N mu Cfr Q.a Q.ρ eta
      (highSeparatedScoreExponentialConstant Q.a Q.ρ C.densityUpper 1 1) hmass hB r (highPatchProductChart d k j x)
    dsimp only at hdom
    rw [completeSourceSaddle_eta_eq C Cω cf n] at hdom
    exact hdom.trans hm
  · have hmu_eq : completeSaddleMu C Cω n = (n : ℝ) / (k : ℝ) ^ d := by
      dsimp only [completeSaddleMu, lowerSaddleMu, lowerSaddleH, k, m, theta]
      rw [Real.rpow_natCast, inv_pow]; rfl
    have hparam : (n : ℝ) * highFixedScoreDenominator C.densityLower Q.c * (2 / (k : ℝ)) ^ d =
        completeSaddleScoreFactor C Q * completeSaddleMu C Cω n :=
      high_design_factorial_parameter (highFixedScoreDenominator C.densityLower Q.c) (completeSaddleMu C Cω n) hmu_eq
    change highSourceSpatialSeries d k n C.densityLower Q.c _ ≤ _
    have hser : highSourceSpatialSeries d k n C.densityLower Q.c (fun _j => completeSaddleGeometryEnvelope C Q Cfr cf Cω n) =
        (3 ^ d : ℕ) * (k : ℝ) ^ d * ∑ r ∈ Finset.range (n + 1),
          poissonCountWeight (completeSaddleScoreFactor C Q * completeSaddleMu C Cω n) r *
          ∫ u, completeSaddleGeometryEnvelope C Q Cfr cf Cω n r u ∂fullSpatialPatchDesign d r := by
      simp only [highSourceSpatialSeries, hparam, Finset.sum_const, Finset.card_univ,
        highWindowLabels_card, nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat, poissonCountWeight, fullSpatialPatchDesign]
      ring
    rw [hser]
    exact mul_le_mul_of_nonneg_left henergy (by positivity)

private def rawCostConstants (CB C5 C6 C7 cf ch : ℝ) : Fin 7 → ℝ :=
  ![1, C6, ch, 1 + CB ^ 2, 3 * (C5 + C7) * cf ^ 4,
    3 * C6 ^ 2 * cf ^ 4, Real.exp ch * ch * cf ^ 4 * (CB + 1) ^ 2]

private def rawCostConstant (CB C5 C6 C7 cf ch : ℝ) : ℝ :=
  Finset.univ.sup' (by simp) (rawCostConstants CB C5 C6 C7 cf ch)

private theorem completeSourceSaddle_penalized_numeric_envelope {d : ℕ} [NeZero d]
    (C : ModelConstants d) (hs : 1 < C.smoothness) (hd : 4 * C.smoothness < (d : ℝ))
    {cf CB C5 C6 C7 ch ctr cm Cω : ℝ}
    (hcf : 0 < cf) (hCB : 0 ≤ CB) (hC5 : 0 ≤ C5) (hC6 : 0 ≤ C6)
    (hC7 : 0 ≤ C7) (hch : 0 ≤ ch) (hctr : 0 < ctr) (hcm : 0 < cm)
    (hshift : 1 + Real.log (rawCostConstant CB C5 C6 C7 cf ch) +
      ((d : ℝ) ^ 2 - 16 * C.smoothness) / ((d : ℝ) * ((d : ℝ) + 4)) * highCompleteSourceSaddleTheta C +
      2 * d * densityIntervalExponent C.densityLower C.densityUpper / ((d : ℝ) + 4) < Cω) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ n : ℕ in atTop,
      let m := highCompleteSourceSaddleCoefficient C
      let theta := highCompleteSourceSaddleTheta C
      let tauM := shrunkDensityExponent C.densityLower C.densityUpper
      let k := lowerSaddleGrid d m theta Cω n
      let eta := cf * (k : ℝ) ^ (-C.smoothness)
      let B := lowerSaddleActivity C.smoothness d m theta Cω tauM n
      ∀ Bl E : ℝ, 1 ≤ B → 0 ≤ Bl → 0 ≤ E → Bl ≤ CB * B →
      E ≤ lowerSaddleRawEnergyBound C.smoothness d m theta Cω cf C5 C6 C7 ch Bl tauM n →
      (c * paperRiskScale C n) ^ 2 ≤ ctr * eta ^ 4 / (1 + Bl ^ 2 + (k : ℝ) ^ d * E) -
        (effectiveVarianceUpper C - C.varianceLower) ^ 2 * highCompleteSourceSaddleTail C Cω cm n := by
  have hab := C.densityLower_lt_one.trans C.one_lt_densityUpper
  let CG := rawCostConstant CB C5 C6 C7 cf ch
  have hCG1 : 1 ≤ CG := Finset.le_sup' (rawCostConstants CB C5 C6 C7 cf ch) (Finset.mem_univ 0)
  have hCG : 0 < CG := zero_lt_one.trans_le hCG1
  have hmgf := highHistoryMassMomentConstant_pos d C.densityLower C.densityUpper hab
  obtain ⟨c₀, _, hc₀, _, hbracket⟩ := actual_lowerSaddleRisk_rate_bracket hs hd C.densityLower_pos hab hcf Cω
  let α := ctr / (3 * CG)
  have hα : 0 < α := by dsimp [α]; positivity
  let q_val := α * c₀ ^ 2 / 2
  have hq : 0 < q_val := by dsimp [q_val]; positivity
  let c := Real.sqrt q_val
  have hc : 0 < c := Real.sqrt_pos.mpr hq
  let DV := effectiveVarianceUpper C - C.varianceLower
  have ht := (actual_lowerSaddle_exceptionalTail_over_Psi_tends_zero
    hs hd C.densityLower_pos hab hcm hmgf Cω).eventually (eventually_lt_nhds (by positivity : 0 < q_val / (DV ^ 2 + 1)))
  have hnum_cost := eventually_actual_lowerSaddle_numeric_cost hs hd C.densityLower_pos hab hCG hshift
  refine ⟨c, hc, ?_⟩
  filter_upwards [tendsto_natCast_atTop_atTop.eventually hbracket,
    tendsto_natCast_atTop_atTop.eventually ht,
    tendsto_natCast_atTop_atTop.eventually hnum_cost,
    eventually_ge_atTop (2 : ℕ)] with n hb htx hcst hn2
  dsimp only at hb htx hcst ⊢
  intro Bl E hB hBl hE hBlcap hEcap
  let m := highCompleteSourceSaddleCoefficient C
  let theta := highCompleteSourceSaddleTheta C
  let tauM := shrunkDensityExponent C.densityLower C.densityUpper
  let x : ℝ := n
  let h := lowerSaddleH d m theta Cω x
  have hh : 0 < h := lowerSaddleH_positive _ _ _ _ _
  have hv : 0 < h ^ (d : ℝ) := Real.rpow_pos_of_pos hh _
  let mu := lowerSaddleMu d m theta Cω x
  let N := lowerSaddleN C.smoothness d m theta Cω tauM x
  let M := lowerSaddleM m x; let D := lowerSaddleD d m x
  let B := lowerSaddleActivity C.smoothness d m theta Cω tauM x
  have hNpos := lowerSaddleN_positive C.smoothness d m theta Cω tauM x
  have hmu0 : 0 ≤ mu := mul_nonneg (Nat.cast_nonneg n) hv.le
  have hC6G : C6 ≤ CG := Finset.le_sup' (rawCostConstants CB C5 C6 C7 cf ch) (Finset.mem_univ 1)
  have hchG : ch ≤ CG := Finset.le_sup' (rawCostConstants CB C5 C6 C7 cf ch) (Finset.mem_univ 2)
  have hBG : 1 + CB ^ 2 ≤ CG := Finset.le_sup' (rawCostConstants CB C5 C6 C7 cf ch) (Finset.mem_univ 3)
  have hpG : 3 * (C5 + C7) * cf ^ 4 ≤ CG := Finset.le_sup' (rawCostConstants CB C5 C6 C7 cf ch) (Finset.mem_univ 4)
  have haG : 3 * C6 ^ 2 * cf ^ 4 ≤ CG := Finset.le_sup' (rawCostConstants CB C5 C6 C7 cf ch) (Finset.mem_univ 5)
  have htG : Real.exp ch * ch * cf ^ 4 * (CB + 1) ^ 2 ≤ CG := Finset.le_sup' (rawCostConstants CB C5 C6 C7 cf ch) (Finset.mem_univ 6)
  have heta4 : (lowerSaddleEta C.smoothness d m theta Cω cf x) ^ 4 = cf ^ 4 * h ^ (4 * C.smoothness) := by
    unfold lowerSaddleEta; rw [mul_pow, ← Real.rpow_mul_natCast hh.le]; congr 2; ring
  have hfact_red {cr F : ℝ} (hcr : 0 ≤ cr) (hcrG : cr ≤ CG) (hF : 0 ≤ F) (K : ℕ) :
      (h ^ (d : ℝ))⁻¹ * ((lowerSaddleEta C.smoothness d m theta Cω cf x) ^ 4 * F * (cr * mu) ^ (K + 1) / (K + 1).factorial) ≤
        cr * cf ^ 4 * x * h ^ (4 * C.smoothness) * F * (CG * mu) ^ K / (K + 1).factorial := by
    have hp_pow : (cr * mu) ^ (K + 1) ≤ cr * mu * (CG * mu) ^ K := by
      rw [pow_succ]
      simpa only [mul_comm] using mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ (mul_nonneg hcr hmu0) (mul_le_mul_of_nonneg_right hcrG hmu0) K) (mul_nonneg hcr hmu0)
    calc _ ≤ (h ^ (d : ℝ))⁻¹ * ((lowerSaddleEta C.smoothness d m theta Cω cf x) ^ 4 * F * (cr * mu * (CG * mu) ^ K) / (K + 1).factorial) :=
          mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hp_pow (by positivity)) (Nat.cast_nonneg _)) (by positivity)
      _ = _ := by
          rw [heta4]
          have hmu_eq : mu = x * h ^ (d : ℝ) := rfl
          rw [hmu_eq]; field_simp [hv.ne']
  have hbase : 1 + Bl ^ 2 ≤ CG * B ^ 2 := by
    have hb2 : Bl ^ 2 ≤ CB ^ 2 * B ^ 2 := ((sq_le_sq₀ hBl (by positivity)).mpr hBlcap).trans_eq (mul_pow _ _ _)
    have hb1 : 1 ≤ B ^ 2 := by nlinarith only [hB]
    have hh_bg := mul_le_mul_of_nonneg_right hBG (sq_nonneg B)
    nlinarith only [hh_bg, hb1, hb2]
  have hp_term : (h ^ (d : ℝ))⁻¹ * (3 * (C5 + C7) * (lowerSaddleEta C.smoothness d m theta Cω cf x) ^ 4 * mu ^ 2 * N ^ (-(d : ℝ))) ≤
      CG * lowerSaddleEnergyOne C.smoothness d m theta Cω tauM x := by
    have heq_p : (h ^ (d : ℝ))⁻¹ * (3 * (C5 + C7) * (lowerSaddleEta C.smoothness d m theta Cω cf x) ^ 4 * mu ^ 2 * N ^ (-(d : ℝ))) =
        3 * (C5 + C7) * cf ^ 4 * lowerSaddleEnergyOne C.smoothness d m theta Cω tauM x := by
      have hmu_eq : mu = x * h ^ (d : ℝ) := rfl
      rw [heta4, hmu_eq]; unfold lowerSaddleEnergyOne
      change (h ^ (d : ℝ))⁻¹ * (3 * (C5 + C7) * (cf ^ 4 * h ^ (4 * C.smoothness)) * (x * h ^ (d : ℝ)) ^ 2 * N ^ (-(d : ℝ))) =
        3 * (C5 + C7) * cf ^ 4 * (x ^ 2 * h ^ ((d : ℝ) + 4 * C.smoothness) * N ^ (-(d : ℝ)))
      rw [Real.rpow_add hh]; field_simp [hv.ne']
    rw [heq_p]
    exact mul_le_mul_of_nonneg_right hpG (by unfold lowerSaddleEnergyOne; positivity)
  have ha_term : (h ^ (d : ℝ))⁻¹ * (3 * C6 * (lowerSaddleEta C.smoothness d m theta Cω cf x) ^ 4 *
      (Real.exp (2 * tauM M * M) * N ^ (4 - (d : ℝ))) * (C6 * mu) ^ (M + 1) / (M + 1).factorial) ≤
      CG * lowerSaddleEnergyTwo C.smoothness d m theta Cω CG tauM x := by
    have hr := mul_le_mul_of_nonneg_left
      (hfact_red (F := Real.exp (2 * tauM M * M) * N ^ (4 - (d : ℝ))) hC6 hC6G (by positivity) M)
      (by positivity : 0 ≤ 3 * C6)
    refine le_trans (by convert hr using 1 <;> ring) ?_
    unfold lowerSaddleEnergyTwo
    convert mul_le_mul_of_nonneg_right haG
      (by positivity : 0 ≤ x * h ^ (4 * C.smoothness) * (Real.exp (2 * tauM M * M) * N ^ (4 - (d : ℝ))) *
        (CG * mu) ^ M / (M + 1).factorial) using 1 <;> dsimp [mu, N, M, h] <;> ring
  have ht_term : (h ^ (d : ℝ))⁻¹ * (Real.exp ch * (lowerSaddleEta C.smoothness d m theta Cω cf x) ^ 4 *
      (Bl + 1) ^ 2 * (ch * mu) ^ (D + 1) / (D + 1).factorial) ≤
      CG * lowerSaddleEnergyThree C.smoothness d m theta Cω CG tauM x := by
    have hr := mul_le_mul_of_nonneg_left (hfact_red hch hchG zero_le_one D)
      (by positivity : 0 ≤ Real.exp ch * (Bl + 1) ^ 2)
    have hab1 : (Bl + 1) ^ 2 ≤ (CB + 1) ^ 2 * B ^ 2 :=
      ((sq_le_sq₀ (by linarith) (by positivity)).mpr (by nlinarith only [hBlcap, hB])).trans_eq (mul_pow _ _ _)
    have hk := mul_le_mul_of_nonneg_right hab1
      (by positivity : 0 ≤ Real.exp ch * ch * cf ^ 4 * x * h ^ (4 * C.smoothness) * (CG * mu) ^ D / (D + 1).factorial)
    refine le_trans (by convert hr using 1 <;> ring) (le_trans (by convert hk using 1 <;> ring) ?_)
    unfold lowerSaddleEnergyThree
    convert mul_le_mul_of_nonneg_right htG
      (by positivity : 0 ≤ x * h ^ (4 * C.smoothness) * B ^ 2 * (CG * mu) ^ D / (D + 1).factorial) using 1
      <;> dsimp [mu, B, D, h] <;> ring
  have hscaled := mul_le_mul_of_nonneg_left hEcap (inv_nonneg.mpr hv.le)
  dsimp only [lowerSaddleRawEnergyBound, m, theta, tauM, x, mu, N, M, D] at hscaled
  have hvol : (lowerSaddleGrid d m theta Cω x : ℝ) ^ d = (h ^ (d : ℝ))⁻¹ := by
    dsimp [h]; unfold lowerSaddleH
    rw [Real.inv_rpow (Nat.cast_nonneg _), Real.rpow_natCast, inv_inv]
  have hcost_den : 1 + Bl ^ 2 + (lowerSaddleGrid d m theta Cω x : ℝ) ^ d * E ≤ 3 * CG * B ^ 2 := by
    rw [hvol]
    dsimp only [m, theta, tauM, x, mu, N, M, D] at hp_term ha_term ht_term hbase
    exact (by nlinarith only [hscaled, hbase, hp_term, ha_term, ht_term] :
      1 + Bl ^ 2 + (h ^ (d : ℝ))⁻¹ * E ≤ CG * (B ^ 2 + lowerSaddleEnergyOne C.smoothness d m theta Cω tauM x +
        lowerSaddleEnergyTwo C.smoothness d m theta Cω CG tauM x +
        lowerSaddleEnergyThree C.smoothness d m theta Cω CG tauM x)).trans hcst
  have hdenpos : 0 < 1 + Bl ^ 2 + (lowerSaddleGrid d m theta Cω x : ℝ) ^ d * E := by positivity
  have hBpos := lowerSaddleActivity_positive C.smoothness d m theta Cω tauM x
  have hmain : α * (lowerSaddleRisk C.smoothness d m theta Cω cf tauM x) ^ 2 ≤
      ctr * (cf * (lowerSaddleGrid d m theta Cω x : ℝ) ^ (-C.smoothness)) ^ 4 /
        (1 + Bl ^ 2 + (lowerSaddleGrid d m theta Cω x : ℝ) ^ d * E) := by
    dsimp only [m, theta]
    rw [completeSourceSaddle_eta_eq C Cω cf x]
    refine le_trans (le_of_eq ?_) (div_le_div_of_nonneg_left (by positivity) hdenpos hcost_den)
    dsimp [α, B, m, theta]; unfold lowerSaddleRisk; field_simp
  let S := rateScale (rateExponent C.smoothness d)
    (stretchConstant C.smoothness d (densityIntervalExponent C.densityLower C.densityUpper))
    (lowerLogPower C.smoothness d) x
  have hS : 0 < S := rateScale_pos _ _ _ _
  have hR : 0 < lowerSaddleRisk C.smoothness d m theta Cω cf tauM x := lowerSaddleRisk_positive hcf _
  have hsq : (c₀ * S) ^ 2 ≤ (lowerSaddleRisk C.smoothness d m theta Cω cf tauM x) ^ 2 :=
    (sq_le_sq₀ (by positivity) hR.le).mpr hb.1
  let ε := lowerSaddleExceptionalTail d m theta Cω ((cm) ^ 2 / (8 * highHistoryMassMomentConstant d C.densityLower C.densityUpper)) x
  have hε : ε ≤ (q_val / (DV ^ 2 + 1)) * S ^ 2 := (div_le_iff₀ (by positivity : 0 < S ^ 2)).mp htx.le
  have hfrac : DV ^ 2 * (q_val / (DV ^ 2 + 1)) ≤ q_val := by
    rw [show DV ^ 2 * (q_val / (DV ^ 2 + 1)) = (DV ^ 2 * q_val) / (DV ^ 2 + 1) by ring]
    exact (div_le_iff₀ (by positivity : 0 < DV ^ 2 + 1)).mpr (by nlinarith only [hq.le])
  have hp1 := mul_le_mul_of_nonneg_left hε (sq_nonneg DV)
  have hp2 := mul_le_mul_of_nonneg_right hfrac (sq_nonneg S)
  have hpen : DV ^ 2 * ε ≤ q_val * S ^ 2 := by nlinarith only [hp1, hp2]
  have hm_sq := mul_le_mul_of_nonneg_left hsq hα.le
  rw [paperRiskScale_eq_rateScale C hn2]
  change (c * S) ^ 2 ≤ _ - DV ^ 2 * ε
  rw [mul_pow, Real.sq_sqrt hq.le]
  dsimp [q_val] at hpen ⊢
  nlinarith only [hpen, hm_sq, hmain]

theorem paper_lower_sharp {d : ℕ} (C : ModelConstants d) : LowerSharpClaim C := by
  intro ⟨hs, hd⟩
  letI : NeZero d := NeZero.of_pos C.dimension_pos
  obtain ⟨Q⟩ := lowSmoothnessTernaryConstants_exists C
  obtain ⟨Cfr0, etaG, hCfr0, hetaG, hgeometry⟩ := completeSaddleGeometry_witness C Q hs hd
  obtain ⟨Cfr, eta0, ctr, hCfr, hmin, heta0, hctr, hcost⟩ :=
    highCompleteSource_cost_risk_uniform_above C Q Cfr0
  let cf := C.holderBound / highWindowHolderConstant C
  let cm := 1 / C.densityUpper
  have hcf : 0 < cf := div_pos C.holderBound_pos (highWindowHolderConstant_pos C)
  have hHolder : highWindowHolderConstant C * cf ≤ C.holderBound :=
    le_of_eq (mul_div_cancel₀ _ (highWindowHolderConstant_pos C).ne')
  have hcm : 0 < cm := one_div_pos.mpr (zero_lt_one.trans C.one_lt_densityUpper)
  let q := lowerSaddleResponseOrder C.smoothness d
  let lam := spatialInterpolationLambda d
  let CB := completeSourceSaddleActivityConstant C q Cfr lam
  let C5 := completeSaddleDefectConstant C Q Cfr
  let C6 := completeSaddleAliasConstant C Q Cfr
  let C7 := completeSaddleFieldConstant C Q Cfr
  let ch := completeSaddleExteriorConstant C Q
  have hCB : 0 ≤ CB := (completeSourceSaddleActivityConstant_pos C q Cfr lam).le
  have hC5 : 0 ≤ C5 := by unfold C5 completeSaddleDefectConstant completeGeometryDefectConstant; positivity
  have hC6 : 0 ≤ C6 := by unfold C6 completeSaddleAliasConstant completeGeometryAliasConstant; positivity
  have hC7 : 0 ≤ C7 := by unfold C7 completeSaddleFieldConstant completeGeometryFieldConstant; positivity
  have hch : 0 ≤ ch := by unfold ch completeSaddleExteriorConstant completeGeometryExteriorConstant; positivity
  let Cω := 1 + Real.log (rawCostConstant CB C5 C6 C7 cf ch) +
    ((d : ℝ) ^ 2 - 16 * C.smoothness) / ((d : ℝ) * ((d : ℝ) + 4)) * highCompleteSourceSaddleTheta C +
    2 * d * densityIntervalExponent C.densityLower C.densityUpper / ((d : ℝ) + 4) + 1
  obtain ⟨c_rate, hc_rate, hrate⟩ := completeSourceSaddle_penalized_numeric_envelope C hs hd
    hcf hCB hC5 hC6 hC7 hch hctr hcm (Cω := Cω) (by dsimp only [Cω]; linarith)
  have hall : ∀ᶠ n : ℕ in atTop,
      2 ≤ n ∧ ∀ U : ExtensionDomain d,
        ENNReal.ofReal (c_rate * paperRiskScale C n) ≤ minimaxRMS (C.withDomain U) n := by
    filter_upwards [hgeometry Cfr cf hmin hcf Cω,
      tendsto_natCast_atTop_atTop.eventually (eventually_completeSourceSaddle_parameters C hs hd hcf heta0 hcm Cω),
      tendsto_natCast_atTop_atTop.eventually (completeSourceSaddleActivity_eventually_bound C hs hd q Cfr lam Cω),
      hrate, eventually_ge_atTop (2 : ℕ)] with n hgeo hp hactivity hraten hn2
    let m := highCompleteSourceSaddleCoefficient C
    let theta := highCompleteSourceSaddleTheta C
    let k := lowerSaddleGrid d m theta Cω n
    let M := completeSaddleM C n
    let D := completeSaddleD C n
    let N := completeSaddleN C Cω n
    let ell := completeSaddleEll C Cω n
    let mu := completeSaddleMu C Cω n
    let eta := cf * (k : ℝ) ^ (-C.smoothness)
    dsimp only at hp hgeo
    obtain ⟨hk, hD, hM, hell, hellN, heta, heps, hB⟩ := hp
    have hk' : 4 ≤ k := hk
    letI : NeZero k := ⟨by omega⟩
    letI : LinearOrder (HighWindowLabels d k) :=
      LinearOrder.lift' (Fintype.equivFin (HighWindowLabels d k)) (Fintype.equivFin (HighWindowLabels d k)).injective
    let R := completeSourceRows C k D M q Cfr lam ell N mu
    obtain ⟨E, hE, hEcap, hHI, hH0, hdom, hseries⟩ := hgeo inferInstance inferInstance
    have hq1 : 1 ≤ q := by dsimp only [q, lowerSaddleResponseOrder]; omega
    have G := completeSourceRows_guards C k D M q hD hq1 hM Cfr lam ell N mu hCfr hell hellN
    let Bl := highRowTotalMass R.rowMass / highCenterMix C
    have hBl : 0 ≤ Bl := div_nonneg G.total_positive.le (highCenterMix_mem C).1.le
    refine ⟨hn2, fun U => ?_⟩
    let I := Real.sqrt ((3 ^ d : ℕ) * (k : ℝ) ^ d * E)
    let delta := localScorePathLength (highPathConstant (3 ^ d) Q.ρ eta0) Bl I
    have hvariance : eta ^ 2 * delta ≤ Q.ρ := highPath_variance_budget (3 ^ d) Q.ρ_pos heta0 hBl
      (Real.sqrt_nonneg _) (mul_nonneg hcf.le (Real.rpow_nonneg (Nat.cast_nonneg _) _)) heta
    have hV (t : ℝ) (ht : t ∈ Icc 0 delta) : |(Q.v - eta ^ 2 * t) - Q.v| ≤ Q.ρ := by
      simp only [sub_sub_cancel_left, abs_neg, abs_mul, abs_of_nonneg (sq_nonneg eta), abs_of_nonneg ht.1]
      exact (mul_le_mul_of_nonneg_left ht.2 (sq_nonneg eta)).trans hvariance
    have hetaEq : eta = completeSaddleEta C Cω cf n := completeSourceSaddle_eta_eq C Cω cf n
    have hout := hcost U k D M q inferInstance inferInstance hk hD hq1 hM lam ell N mu hell hellN
      cf hcf.le hHolder heta cm hcm.le le_rfl n E hE heps
      (completeSaddleGeometryEnvelope C Q Cfr cf Cω n) hHI hH0
      (fun t ht h j r x hx => by simpa only [← hetaEq] using hdom (Q.v - eta ^ 2 * t) (hV t ht) h j r x hx)
      hseries
    have htail : 2 * Real.exp (-(cm / (M : ℝ)) ^ 2 / (8 * highHistoryMassParameter d k C.densityLower C.densityUpper)) =
        highCompleteSourceSaddleTail C Cω cm n :=
      highHistoryMass_saddle_tail_eq d m theta Cω cm C.densityLower C.densityUpper n
    rw [htail] at hout
    have hsq_le : ENNReal.ofReal ((c_rate * paperRiskScale C n) ^ 2) ≤ minimaxRisk (C.withDomain U) n :=
      (ENNReal.ofReal_le_ofReal (hraten Bl E hB hBl hE hactivity hEcap)).trans hout
    rw [ENNReal.ofReal_pow (mul_pos hc_rate (paperRiskScale_pos C hn2)).le] at hsq_le
    have hh_rms := ENNReal.rpow_le_rpow hsq_le (by norm_num : (0 : ℝ) ≤ 1 / 2)
    rw [← ENNReal.rpow_natCast_mul] at hh_rms
    norm_num only [Nat.cast_ofNat, mul_one_div_cancel, ENNReal.rpow_one] at hh_rms
    exact hh_rms
  obtain ⟨n₀, hn₀⟩ := eventually_atTop.1 hall
  exact ⟨c_rate, hc_rate, n₀, (hn₀ n₀ le_rfl).1, fun U n hn => (hn₀ n hn).2 U⟩

end SaddleAssembly
end NearlyMinimax
