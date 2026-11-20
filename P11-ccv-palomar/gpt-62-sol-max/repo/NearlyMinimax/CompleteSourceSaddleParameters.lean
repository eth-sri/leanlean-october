module

public import NearlyMinimax.CompleteSourceSaddleMassTail
public import NearlyMinimax.SourceSaddleActivity
public import NearlyMinimax.HighUnionRawFisher
public import NearlyMinimax.CompleteSourceMassAnnihilation
public import NearlyMinimax.HighPriorRisk
public import NearlyMinimax.HighParameterPath
public import NearlyMinimax.HighUnionSourceUniformModel
public import NearlyMinimax.TernaryEffectiveInterval
public import NearlyMinimax.HighPathBudget


@[expose] public section

/-! Exact canonical complete-row parameters and their eventual numerical guards.
All constants in these statements precede the extension domain. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology
namespace NearlyMinimax
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
attribute [local irreducible] sourceRowData highRowTotalMass

def completeSourceSaddleRows {d : ℕ} (C : ModelConstants d)
    (q : ℕ) (Cfr lam Cω x : ℝ) :=
  completeSourceRows C (completeSaddleGrid C Cω x) (completeSaddleD C x) (completeSaddleM C x)
    q Cfr lam (completeSaddleEll C Cω x) (completeSaddleN C Cω x) (completeSaddleMu C Cω x)

def completeSourceSaddleActivity {d : ℕ} (C : ModelConstants d)
    (q : ℕ) (Cfr lam Cω x : ℝ) : ℝ :=
  highRowTotalMass (completeSourceSaddleRows C q Cfr lam Cω x).rowMass/highCenterMix C

def completeSourceSaddleActivityConstant {d : ℕ} (C : ModelConstants d)
    (q : ℕ) (Cfr lam : ℝ) : ℝ :=
  sourceSaddleActivityConstant d q C.densityLower C.densityUpper Cfr lam/highCenterMix C

section
variable {d : ℕ}

theorem completeSourceSaddleActivityConstant_pos (C : ModelConstants d)
    (q : ℕ) (Cfr lam : ℝ) : 0 < completeSourceSaddleActivityConstant C q Cfr lam := by
  exact div_pos (sourceSaddleActivityConstant_positive d q _ _ _ _ C.densityLower_pos
    (C.densityLower_lt_one.trans C.one_lt_densityUpper)) (highCenterMix_mem C).1

/-- The row-budget constant includes the balancing reference factor exactly. -/
theorem completeSourceSaddleActivity_eventually_bound [NeZero d]
    (C : ModelConstants d) (hs : 1 < C.smoothness) (hd : 4*C.smoothness < (d : ℝ))
    (q : ℕ) (Cfr lam Cω : ℝ) :
    ∀ᶠ x : ℝ in atTop,
      completeSourceSaddleActivity C q Cfr lam Cω x ≤
        completeSourceSaddleActivityConstant C q Cfr lam * completeSaddleActivityScale C Cω x := by
  filter_upwards [sourceSaddleTotalMass_eventually_bound d q C.smoothness
    C.densityLower C.densityUpper Cfr lam Cω hs hd C.densityLower_pos
    (C.densityLower_lt_one.trans C.one_lt_densityUpper)] with x hx
  simpa only [completeSourceSaddleActivity, completeSourceSaddleActivityConstant, completeSourceSaddleRows,
    completeSourceRows, sourceSaddleTotalMass, completeSaddleD, completeSaddleM, completeSaddleEll,
    completeSaddleN, completeSaddleMu, completeSaddleActivityScale, completeSaddleC0,
    highCompleteSourceSaddleCoefficient, highCompleteSourceSaddleTheta, mul_div_right_comm] using
    div_le_div_of_nonneg_right (hx (completeSaddleGrid C Cω x)) (highCenterMix_mem C).1.le

section
variable (C : ModelConstants d)

/-- The source's physical amplitude is exactly the rounded saddle amplitude. -/
theorem completeSourceSaddle_eta_eq (Cω cf x : ℝ) :
    cf*(completeSaddleGrid C Cω x : ℝ)^(-C.smoothness) =
      lowerSaddleEta C.smoothness d (highCompleteSourceSaddleCoefficient C)
        (highCompleteSourceSaddleTheta C) Cω cf x := by
  unfold lowerSaddleEta lowerSaddleH
  rw [Real.inv_rpow (lowerSaddleGrid_positive _ _ _ _ _).le,
    Real.rpow_neg (lowerSaddleGrid_positive _ _ _ _ _).le]

/-- Exact inverse-volume accounting for the physical rounded grid. -/
theorem completeSourceSaddle_inverse_volume (Cω x : ℝ) :
    (completeSaddleGrid C Cω x : ℝ)^d =
      (lowerSaddleH d (highCompleteSourceSaddleCoefficient C)
        (highCompleteSourceSaddleTheta C) Cω x)^(-(d : ℝ)) := by
  unfold lowerSaddleH
  simp

/-- Fixed positive amplitudes and mass tolerances satisfying the original model budgets. -/
theorem completeSourceSaddle_numeric_constants :
    ∃ cf cm : ℝ, 0 < cf ∧ highWindowHolderConstant C*cf ≤ C.holderBound ∧
      0 < cm ∧ cm ≤ 1/C.densityUpper := by
  let cf := C.holderBound/highWindowHolderConstant C
  let cm := 1/C.densityUpper
  refine ⟨cf,cm,div_pos C.holderBound_pos (highWindowHolderConstant_pos C),?_,
    one_div_pos.mpr (lt_trans zero_lt_one C.one_lt_densityUpper),le_rfl⟩
  rw [mul_div_cancel₀ _ (highWindowHolderConstant_pos C).ne']

end

structure CompleteSaddleParameters (C : ModelConstants d) (Cω cf eta0 cm x : ℝ) : Prop where
  grid_min : 4 ≤ completeSaddleGrid C Cω x
  degree_min : 3 ≤ completeSaddleD C x
  resolution_min : highCenterResolutionThreshold C ≤ (completeSaddleM C x : ℝ)
  cutoff_pos : 0 < completeSaddleEll C Cω x
  cutoff_lt : completeSaddleEll C Cω x < completeSaddleN C Cω x
  amplitude : cf*(completeSaddleGrid C Cω x : ℝ)^(-C.smoothness) ≤ eta0
  mass : 8*highHistoryMassParameter d (completeSaddleGrid C Cω x) C.densityLower C.densityUpper*x ≤
    cm/(completeSaddleM C x : ℝ)
  activity : 1 ≤ completeSaddleActivityScale C Cω x

/-- All elementary source, amplitude and mass guards hold at the actual
rounded grid, for constants fixed independently of the extension domain. -/
theorem eventually_completeSourceSaddle_parameters [NeZero d]
    (C : ModelConstants d) (hs : 1 < C.smoothness) (hd : 4*C.smoothness < (d : ℝ))
    {cf eta0 cm : ℝ} (heta0 : 0 < eta0) (hcm : 0 < cm) (Cω : ℝ) :
    ∀ᶠ x : ℝ in atTop, CompleteSaddleParameters C Cω cf eta0 cm x := by
  let m := highCompleteSourceSaddleCoefficient C
  let theta := highCompleteSourceSaddleTheta C
  let tau := densityIntervalExponent C.densityLower C.densityUpper
  have hab := C.densityLower_lt_one.trans C.one_lt_densityUpper
  have htau : 0 < tau := densityIntervalExponent_pos C.densityLower_pos hab
  have hm : 0 < m := lowerSaddleCoefficient_pos hs hd htau
  have htheta : 0 < theta := lowerSaddleTheta_pos hs hd htau
  have hd0 : (0 : ℝ) < d := by linarith
  obtain ⟨Ctau,_,hcontrol⟩ := exists_actual_lowerExponentControl C.densityLower_pos hab
  have hgrid : Tendsto (lowerSaddleGrid d m theta Cω) atTop atTop :=
    tendsto_natCast_atTop_iff.mp (lowerSaddleGrid_tendsto_atTop hd0 hm htheta Cω)
  have htauM := (lowerSaddleM_nat_tendsto_atTop hm).eventually hcontrol
  filter_upwards [hgrid.eventually (eventually_ge_atTop 4),
    (lowerSaddleM_tendsto_atTop hm).eventually
      (eventually_ge_atTop (max (highCenterResolutionThreshold C) 3)),
    (lowerSaddleN_tendsto_atTop hs hd hm htheta hcontrol Cω).eventually
      (eventually_ge_atTop (1 : ℝ)),
    (lowerSaddleEta_tends_zero C.smoothness_pos hd0 hm htheta Cω cf).eventually
      (gt_mem_nhds heta0),
    eventually_highHistoryMass_saddle_guard (NeZero.pos d) hm htheta hcm Cω
      C.densityLower C.densityUpper hab,htauM] with x hk hM hN heta heps htauMx
  have hM3 : (3 : ℝ) ≤ lowerSaddleM m x := (le_max_right _ _).trans hM
  have hD : 3 ≤ lowerSaddleD d m x := by
    have hceil := Nat.le_ceil ((d+8)/4*(lowerSaddleM m x : ℝ))
    have hDr : (3 : ℝ) ≤ lowerSaddleD d m x := by
      dsimp only [lowerSaddleD] at ⊢
      nlinarith
    exact_mod_cast hDr
  have hDpos : (0 : ℝ) < lowerSaddleD d m x := by positivity
  have hcut : Real.exp (-(tau+1)*(lowerSaddleD d m x : ℝ)) < 1 := by
    apply Real.exp_lt_one_iff.mpr
    nlinarith
  have hell : 0 < lowerAliasCutoff C.smoothness d m theta Cω (tau+1)
      (shrunkDensityExponent C.densityLower C.densityUpper) x := by
    apply mul_pos <;> positivity
  have hellN : lowerAliasCutoff C.smoothness d m theta Cω (tau+1)
      (shrunkDensityExponent C.densityLower C.densityUpper) x <
      lowerSaddleN C.smoothness d m theta Cω
        (shrunkDensityExponent C.densityLower C.densityUpper) x := by
    unfold lowerAliasCutoff
    simpa only [mul_one] using mul_lt_mul_of_pos_left hcut (lowerSaddleN_positive _ _ _ _ _ _ _)
  have hB : 1 ≤ lowerSaddleActivity C.smoothness d m theta Cω
      (shrunkDensityExponent C.densityLower C.densityUpper) x := by
    have hexp : 1 ≤ Real.exp (shrunkDensityExponent C.densityLower C.densityUpper
        (lowerSaddleM m x)*(lowerSaddleM m x : ℝ)) := by
      simpa using mul_nonneg (htau.le.trans htauMx.1) (Nat.cast_nonneg _)
    exact one_le_mul_of_one_le_of_one_le (by nlinarith only [hN]) hexp
  exact ⟨hk,hD,(le_max_left _ _).trans hM,hell,hellN,
    (completeSourceSaddle_eta_eq C Cω cf x).trans_le heta.le,heps.2,hB⟩

end

end NearlyMinimax
