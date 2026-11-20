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

def sourceSaddleActivityConstant (d q : ℕ) (a b C lam : ℝ) : ℝ :=
  1 + sourceActivityConstant d q C
    (uniformOrdinaryDensityActivityBase a b (densityIntervalExponent a b+1)) lam

theorem sourceSaddleActivityConstant_positive (d q : ℕ) (a b C lam : ℝ)
    (ha : 0 < a) (hab : a < b) : 0 < sourceSaddleActivityConstant d q a b C lam := by
  have hB : 0 ≤ uniformOrdinaryDensityActivityBase a b (densityIntervalExponent a b+1) := by
    apply mul_nonneg <;> positivity
  have h := sourceActivityConstant_nonneg d q C _ lam hB
  unfold sourceSaddleActivityConstant
  linarith

def sourceSaddleTotalMass (d k q : ℕ) (s a b C lam shift x : ℝ) : ℝ :=
  let tau := densityIntervalExponent a b
  let m := lowerSaddleCoefficient s (d : ℝ) tau
  let theta := lowerSaddleTheta s (d : ℝ) tau
  let M := lowerSaddleM m x
  let D := lowerSaddleD (d : ℝ) m x
  let N := lowerSaddleN s (d : ℝ) m theta shift (shrunkDensityExponent a b) x
  let mu := lowerSaddleMu (d : ℝ) m theta shift x
  let ell := lowerAliasCutoff s (d : ℝ) m theta shift (tau+1) (shrunkDensityExponent a b) x
  highRowTotalMass (sourceRowData d k D M q (a+1/(M : ℝ)) (b-1/(M : ℝ)) C lam ell N mu).rowMass

/-- A fixed positive constant bounds the entire actual row activity for
all sufficiently large sample scales and every spatial grid. No activity,
row-budget, density-neighborhood, or selected-target hypothesis is assumed. -/
theorem sourceSaddleTotalMass_eventually_bound (d q : ℕ) [NeZero d]
    (s a b C lam shift : ℝ) (hs : 1 < s) (hd : 4*s < (d : ℝ))
    (ha : 0 < a) (hab : a < b) :
    ∀ᶠ x in atTop, ∀ k : ℕ,
      sourceSaddleTotalMass d k q s a b C lam shift x ≤
        sourceSaddleActivityConstant d q a b C lam *
          lowerSaddleActivity s d (lowerSaddleCoefficient s d (densityIntervalExponent a b))
            (lowerSaddleTheta s d (densityIntervalExponent a b)) shift (shrunkDensityExponent a b) x := by
  let tau := densityIntervalExponent a b
  let c0 := tau+1
  let m := lowerSaddleCoefficient s (d : ℝ) tau
  let theta := lowerSaddleTheta s (d : ℝ) tau
  have hτ := densityIntervalExponent_pos ha hab
  have hc0 : 1 ≤ c0 := by linarith
  have hm := lowerSaddleCoefficient_pos hs hd hτ
  have htheta := lowerSaddleTheta_pos hs hd hτ
  have hdR : (0 : ℝ) < d := by linarith
  have hdNat : 0 < d := by simp_all
  obtain ⟨Cτ, _, hcontrol⟩ := exists_actual_lowerExponentControl ha hab
  have hguards := actual_lowerAlias_guards hs hd ha hab shift
  have hrows := eventually_lowerAlias_row_smallness hs hd hm htheta hcontrol
    (higherBandSourceCact_positive d ha hab (c0 := c0) (lam := lam)) shift
  have hsingle := eventually_lowerAlias_singleton_le hs hd hm htheta hcontrol shift c0
  have hM := lowerSaddleM_tendsto_atTop hm
  have hN := lowerSaddleN_tendsto_atTop hs hd hm htheta hcontrol shift
  have hsmall := hM.inv_tendsto_atTop.eventually (gt_mem_nhds (by linarith : (0 : ℝ) < (b-a)/2))
  filter_upwards [hguards, hrows, hsingle, hsmall, hM.eventually (eventually_ge_atTop (1 : ℝ)),
    hN.eventually (eventually_ge_atTop (1 : ℝ)), eventually_gt_atTop (0 : ℝ)] with x hx hrowsx hDN hsh hMx hNx hxp
  intro k
  let M := lowerSaddleM m x
  let D := lowerSaddleD (d : ℝ) m x
  let N := lowerSaddleN s (d : ℝ) m theta shift (shrunkDensityExponent a b) x
  let mu := lowerSaddleMu (d : ℝ) m theta shift x
  rcases hrowsx with ⟨hq21, hq1, hDq⟩
  have hD : 1 ≤ D := by
    have hc : ((d : ℝ)+8)/4*(M : ℝ) ≤ (D : ℝ) := Nat.le_ceil _
    have hh : (1 : ℝ) ≤ D := by change (1 : ℝ) ≤ lowerSaddleD (d : ℝ) m x; change (1 : ℝ) ≤ M at hMx; nlinarith
    exact_mod_cast hh
  have hmu : 0 ≤ mu := by unfold mu lowerSaddleMu lowerSaddleH; positivity
  have hshrink : a+(M : ℝ)⁻¹ < b-(M : ℝ)⁻¹ := by
    change (M : ℝ)⁻¹ < (b-a)/2 at hsh
    linarith
  have hb := sourceRows_shrunk_activity_bound (k := k) (M := M) (q := q) hdNat hD
    a b C lam N mu c0
    (lowerAliasQ s (d : ℝ) m theta shift (higherBandSourceCact d a b c0 lam) 1 (shrunkDensityExponent a b) x)
    (lowerAliasQ s (d : ℝ) m theta shift (higherBandSourceCact d a b c0 lam) 2 (shrunkDensityExponent a b) x)
    ha hshrink hx.exponent_le hc0 hNx hmu hx.base_le hDN rfl rfl hq1 hq21 hDq
  have hc : sourceActivityConstant d q C (uniformOrdinaryDensityActivityBase a b c0) lam ≤
      sourceSaddleActivityConstant d q a b C lam := by unfold sourceSaddleActivityConstant; dsimp [c0, tau]; linarith
  apply hb.trans
  unfold lowerSaddleActivity
  rw [← mul_assoc]
  gcongr

end NearlyMinimax
