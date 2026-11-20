module

public import NearlyMinimax.SourceShrunkActivity


@[expose] public section

/-! Eventual total activity of the actual complete row family at the
paper's rounded canonical saddle parameters. -/
noncomputable section
open MeasureTheory Filter Set
open scoped BigOperators Topology
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

variable (d q : ℕ) (a b C lam : ℝ)

def sourceSaddleActivityConstant : ℝ :=
  1 + sourceActivityConstant d q C
    (uniformOrdinaryDensityActivityBase a b (densityIntervalExponent a b+1)) lam

theorem sourceSaddleActivityConstant_positive
    (ha : 0 < a) (hab : a < b) : 0 < sourceSaddleActivityConstant d q a b C lam := by
  have hB : 0 ≤ uniformOrdinaryDensityActivityBase a b (densityIntervalExponent a b+1) := mul_nonneg (Real.exp_pos _).le (div_nonneg (sub_pos.mpr hab).le ha.le)
  have h := (by unfold sourceActivityConstant higherBandGeometricPrefactor higherBandInterpolationBase sourceResponseCost; positivity : 0 ≤ sourceActivityConstant d q C (uniformOrdinaryDensityActivityBase a b (densityIntervalExponent a b + 1)) lam)
  unfold sourceSaddleActivityConstant
  linarith

def sourceSaddleTotalMass (k q : ℕ) (s a b C lam shift x : ℝ) : ℝ :=
  let tau := densityIntervalExponent a b
  let m := lowerSaddleCoefficient s d tau
  let theta := lowerSaddleTheta s d tau
  let M := lowerSaddleM m x
  let D := lowerSaddleD d m x
  let N := lowerSaddleN s d m theta shift (shrunkDensityExponent a b) x
  let mu := lowerSaddleMu d m theta shift x
  let ell := lowerAliasCutoff s d m theta shift (tau+1) (shrunkDensityExponent a b) x
  highRowTotalMass (sourceRowData d k D M q (a+(M : ℝ)⁻¹) (b-(M : ℝ)⁻¹) C lam ell N mu).rowMass

/-- A fixed positive constant bounds the entire actual row activity for
all sufficiently large sample scales and every spatial grid. No activity,
row-budget, density-neighborhood, or selected-target hypothesis is assumed. -/
theorem sourceSaddleTotalMass_eventually_bound [NeZero d]
    (s a b C lam shift : ℝ) (hs : 1 < s) (hd : 4*s < d)
    (ha : 0 < a) (hab : a < b) :
    let coefficient := lowerSaddleCoefficient s d (densityIntervalExponent a b)
    ∀ᶠ x in atTop, ∀ k,
      sourceSaddleTotalMass d k q s a b C lam shift x ≤
        sourceSaddleActivityConstant d q a b C lam *
          (lowerSaddleN s d (coefficient)
            (lowerSaddleTheta s d (densityIntervalExponent a b)) shift (shrunkDensityExponent a b) x)^2 *
          Real.exp (shrunkDensityExponent a b (lowerSaddleM (coefficient) x)*
            (lowerSaddleM (coefficient) x : ℝ)) := by
  let tau := densityIntervalExponent a b
  let c0 := tau+1
  let m := lowerSaddleCoefficient s d tau
  let theta := lowerSaddleTheta s d tau
  have hτ  := densityIntervalExponent_pos ha hab
  have hc0 : 1 ≤ c0 := by linarith
  have hm  := lowerSaddleCoefficient_pos hs hd hτ
  have htheta  := lowerSaddleTheta_pos hs hd hτ
  have hdR : (0 : ℝ) < d := by linarith
  have hdNat : 0 < d := by exact_mod_cast hdR
  obtain ⟨Cτ, _, hcontrol⟩ := exists_actual_lowerExponentControl ha hab
  have hhier := actual_lowerAlias_hierarchy (Cact := higherBandSourceCact d a b c0 lam)
    (Cs := 1) hs hd ha hab (by have hB : 0 < uniformOrdinaryDensityActivityBase a b c0 := mul_pos (Real.exp_pos _) (by positivity); unfold higherBandSourceCact higherBandGeometricConstant higherBandInterpolationBase; positivity) (by norm_num) shift
  have hM := lowerSaddleM_tendsto_atTop hm
  have hsmall := hM.inv_tendsto_atTop.eventually (gt_mem_nhds (by linarith : 0 < (b-a)/2))
  filter_upwards [hhier, hsmall, hM.eventually (eventually_ge_atTop 1),
    (lowerSaddleN_tendsto_atTop hs hd hm htheta hcontrol shift).eventually (eventually_ge_atTop 1), eventually_gt_atTop 0] with x hx hsh hMx hNx hxp
  intro k
  let M := lowerSaddleM m x
  let D := lowerSaddleD d m x
  let N := lowerSaddleN s d m theta shift (shrunkDensityExponent a b) x
  let mu := lowerSaddleMu d m theta shift x
  rcases hx with ⟨hell, htau, hbase, _, _, hq21, hq1, hDq, _, hsingle, _, _⟩
  have hD : 1 ≤ D := by
    have hc : (d+8)/4*M ≤ (D : ℝ) := Nat.le_ceil _
    have hh : (1 : ℝ) ≤ D := by change (1 : ℝ) ≤ D; change (1 : ℝ) ≤ M at hMx; nlinarith
    exact_mod_cast hh
  have hmu : 0 ≤ mu := by
    dsimp [mu]
    rw [lowerSaddleMu_eq_exp hxp]
    exact (Real.exp_pos _).le
  have hshrink : a+(M : ℝ)⁻¹ < b-(M : ℝ)⁻¹ := by
    change (M : ℝ)⁻¹ < _ at hsh
    linarith
  have hDN : D*Real.exp (c0*D) ≤ N := by
    have he : Real.exp (c0*D) ≤ Real.exp (c0*(D+1)) := Real.exp_le_exp.mpr (by nlinarith)
    linarith [mul_le_mul_of_nonneg_left he (Nat.cast_nonneg D)]
  have hb := sourceRows_shrunk_activity_bound (k := k) (q := q) hdNat hD
    a b C lam
    ha hshrink htau hc0 hNx hmu hbase hDN rfl rfl hq1 hq21 hDq
  have hc : sourceActivityConstant d q C (uniformOrdinaryDensityActivityBase a b c0) lam ≤
      sourceSaddleActivityConstant d q a b C lam := by grind [sourceSaddleActivityConstant]
  apply hb.trans
  gcongr <;> assumption

end NearlyMinimax
