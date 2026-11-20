module

public import NearlyMinimax.SourceRowActivity
public import NearlyMinimax.FinePairRowActivity
public import NearlyMinimax.HighActivitySummation
public import NearlyMinimax.HigherBandActivityConversion

@[expose] public section

/-! Summation of the actual selected higher rows under elementary source
scale inequalities. All component cap estimates come from actual measures. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
attribute [local instance] Classical.propDecidable

private theorem finite_activity_fin_tail_le {K q : ℝ} (hK : 0 ≤ K) (hq : 0 ≤ q)
    (hqh : q ≤ 1/2) (m : ℕ) (B : Fin m → ℝ) (hB : ∀ j, B j ≤ K*q^(j.val+1)) :
    (∑ j, B j) ≤ 2*K*q := by
  calc
    _ ≤ ∑ j : Fin m, K*q^(j.val+1) := Finset.sum_le_sum fun j _ => hB j
    _ = K * ∑ j ∈ Finset.range m, q^(j+1) := by rw [Finset.mul_sum, Fin.sum_univ_eq_sum_range (fun j => K*q^(j+1))]
    _ ≤ K*(2*q) := mul_le_mul_of_nonneg_left (finite_geometric_tail_le_two_mul hq hqh m) hK
    _ = _ := by ring

theorem source_exteriorTau_nonneg {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    0 ≤ exteriorTau ((a+b)/(b-a)) :=
  exteriorTau_nonneg _ ((le_div_iff₀ (sub_pos.mpr hab)).mpr (by linarith))

theorem source_exterior_exp_ge_one {a b : ℝ} (ha : 0 < a) (hab : a < b) (m : ℕ) :
    1 ≤ Real.exp ((m : ℝ)*exteriorTau ((a+b)/(b-a))) :=
  Real.one_le_exp (mul_nonneg (Nat.cast_nonneg _) (source_exteriorTau_nonneg ha hab))

private theorem higherBandFilteredMass_geometric_le {d D M q : ℕ} (hD : 1 ≤ D)
    (a b C lam ℓ N μ B : ℝ) (ha : 0 < a) (hab : a < b)
    (hℓ : 0 ≤ ℓ) (hN : 1 ≤ N) (hμ : 0 ≤ μ) (hbase1 : μ*(1+Real.log N) ≤ 1)
    (hB : 0 ≤ B) (hbB : ordinaryDensityActivityBase a b ≤ B) (j : Fin (D-2)) (fine : Bool) :
    higherBandFilteredMass d D M q a b C lam ℓ N μ (j,fine) ≤
      higherBandGeometricPrefactor B (higherBandInterpolationBase d lam) (sourceResponseCost q C) *
      (D : ℝ)^2 * Real.exp ((higherBandFamilyGuardDegree M (j,fine) : ℝ)*exteriorTau ((a+b)/(b-a))) *
      (if fine then N^2 else N*ℓ) * (higherBandSourceRatio d D B lam N μ (if fine then 2 else 1))^(j.val+1) := by
  let r := higherBandFamilyTarget (j,fine)
  let T := higherBandFamilyUpper d ℓ N μ (j,fine)
  have hr : 2 ≤ r := by dsimp [r, higherBandFamilyTarget]; omega
  have hN0 : 0 ≤ N := by linarith
  have hH : 0 ≤ 1+Real.log N := by linarith [Real.log_nonneg hN]
  have hbase := mul_nonneg hμ hH
  have hP : 0 ≤ (if fine then N^2 else N*ℓ) := by split_ifs <;> positivity
  have hcost := sourceResponseCost_nonneg q C
  unfold higherBandFilteredMass
  by_cases hi : HigherBandFamilySelected d D M q a b C lam ℓ N μ (j,fine)
  · rw [if_pos hi]
    have hmass := higherBandRowMass_le_activityCap_of_fine d r (higherBandFamilyGuardDegree M (j,fine)) D q
      hr hD a b ha hab C lam ℓ T hi.1 fine
      (fun hf => by simpa [T, higherBandFamilyUpper, hf] using (hi.2.1 hf).le)
    refine hmass.trans ?_
    have hν := higherBandTargetScale_le_N (d := d) hr hN hbase hbase1
    have hTν : T ≤ higherBandTargetScale d r N μ := by
      cases fine <;> simp [T, r, higherBandFamilyUpper]
    rw [show j.val+1 = r-2 by dsimp [r, higherBandFamilyTarget]; omega]
    apply higherBandRowActivityCap_geometric_le hr a b C lam T B _ _ _ _ hi.1 hB hbase hP hbB
    · exact add_le_add_right (Real.log_le_log (lt_of_lt_of_le zero_lt_one hi.1) (hTν.trans hν)) _
    · cases fine
      · change T^2 ≤ (N*ℓ)*((μ*(1+Real.log N))^(1/(d : ℝ)))^(r-2)
        calc
          _ ≤ ℓ * higherBandTargetScale d r N μ := by
            rw [pow_two]
            exact mul_le_mul (min_le_left _ _) (min_le_right _ _) (zero_le_one.trans hi.1) hℓ
          _ = _ := by rw [higherBandTargetScale_eq hr N μ hbase]; ring
      · change (higherBandTargetScale d r N μ)^2 ≤ N^2*((μ*(1+Real.log N))^(2/(d : ℝ)))^(r-2)
        apply le_of_eq
        rw [higherBandTargetScale_eq hr N μ hbase, mul_pow, ← pow_mul, Nat.mul_comm (r-2), pow_mul,
          ← Real.rpow_mul_natCast hbase]
        ring
  · rw [if_neg hi]
    have hR := higherBandSourceRatio_nonneg (d := d) (D := D) (lam := lam) (α := if fine then 2 else 1) hB hN hμ
    unfold higherBandGeometricPrefactor higherBandInterpolationBase
    positivity

/-- The entire actual selected higher family obeys the paper's geometric
activity estimate. Only elementary inequalities on the computed source scales
are inputs; every component measure estimate is derived above. -/
theorem higherBandFamily_activity_bound {d k D M q : ℕ} (hD : 1 ≤ D)
    (a b C lam ℓ N μ B q1 q2 : ℝ) (ha : 0 < a) (hab : a < b)
    (hℓ : 0 ≤ ℓ) (hN : 1 ≤ N) (hμ : 0 ≤ μ) (hbase1 : μ*(1+Real.log N) ≤ 1)
    (hB : 0 ≤ B) (hbB : ordinaryDensityActivityBase a b ≤ B)
    (hq1 : q1 = higherBandSourceRatio d D B lam N μ 1)
    (hq2 : q2 = higherBandSourceRatio d D B lam N μ 2)
    (hq1h : q1 ≤ 1/2) (hq21 : q2 ≤ q1) (hsmall : (D : ℝ)^2*q1 ≤ 1)
    (hcoarse : Real.exp ((D : ℝ)*exteriorTau ((a+b)/(b-a)))*ℓ ≤ N) :
    highRowTotalMass (higherBandFamilyData d k D M q a b C lam ℓ N μ).rowMass ≤
      4 * higherBandGeometricPrefactor B (higherBandInterpolationBase d lam) (sourceResponseCost q C) *
        N^2 * Real.exp ((M : ℝ)*exteriorTau ((a+b)/(b-a))) := by
  let K := higherBandGeometricPrefactor B (higherBandInterpolationBase d lam) (sourceResponseCost q C)
  let ED := Real.exp ((D : ℝ)*exteriorTau ((a+b)/(b-a)))
  let EM := Real.exp ((M : ℝ)*exteriorTau ((a+b)/(b-a)))
  have hK : 0 ≤ K := by
    dsimp [K, higherBandGeometricPrefactor, higherBandInterpolationBase, sourceResponseCost]
    positivity
  have hq10 : 0 ≤ q1 := by rw [hq1]; exact higherBandSourceRatio_nonneg hB hN hμ
  have hc := finite_activity_fin_tail_le (K := K*(D : ℝ)^2*ED*(N*ℓ)) (by positivity)
    hq10 hq1h (D-2) _ (fun j => by
      simpa [K, ED, higherBandFamilyGuardDegree, hq1] using
        higherBandFilteredMass_geometric_le (M := M) (q := q) hD a b C lam ℓ N μ B ha hab hℓ hN hμ hbase1 hB hbB j false)
  have hf := finite_activity_fin_tail_le (K := K*(D : ℝ)^2*EM*N^2) (by positivity)
    (by rw [hq2]; exact higherBandSourceRatio_nonneg hB hN hμ) (hq21.trans hq1h) (D-2) _ (fun j => by
      simpa [K, EM, higherBandFamilyGuardDegree, hq2] using
        higherBandFilteredMass_geometric_le (M := M) (q := q) hD a b C lam ℓ N μ B ha hab hℓ hN hμ hbase1 hB hbB j true)
  have hEM : 1 ≤ EM := source_exterior_exp_ge_one ha hab M
  have hc' : (∑ j, higherBandFilteredMass d D M q a b C lam ℓ N μ (j,false)) ≤ 2*K*N^2*EM := by
    refine hc.trans ?_
    calc
      _ = (2*K*N)*(ED*ℓ)*((D : ℝ)^2*q1) := by ring
      _ ≤ (2*K*N)*N*1 := by gcongr
      _ = 2*K*N^2 := by ring
      _ ≤ _ := le_mul_of_one_le_right (by positivity) hEM
  have hf' : (∑ j, higherBandFilteredMass d D M q a b C lam ℓ N μ (j,true)) ≤ 2*K*N^2*EM := by
    have hsmall2 := (mul_le_mul_of_nonneg_left hq21 (sq_nonneg _)).trans hsmall
    refine hf.trans ?_
    calc
      _ = (2*K*N^2*EM)*((D : ℝ)^2*q2) := by ring
      _ ≤ (2*K*N^2*EM)*1 := by gcongr
      _ = _ := mul_one _
  rw [higherBandFamily_totalMass_eq]
  change _ ≤ 4*K*N^2*EM
  linarith only [hc', hf']

end NearlyMinimax
