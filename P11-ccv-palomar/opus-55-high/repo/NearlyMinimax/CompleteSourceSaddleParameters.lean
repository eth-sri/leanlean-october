module

public import NearlyMinimax.CompleteSourceSaddleMassTail
public import NearlyMinimax.SourceSaddleActivity
public import NearlyMinimax.HighCompletePathRisk
public import NearlyMinimax.HighPathBudget
public import RoughRegime.Macro
public import RoughRegime.Notation


𝗌

/-! Exact canonical complete-row parameters and their eventual numerical guards.
All constants in these statements precede the extension domain. -/
𝛊
𝚶
𝚨
𝛆
𝚩
𝚬
attribute [local irreducible] sourceRowData highRowTotalMass

𝗇 𝔄 𝙲
𝗇 𝔅 𝙵
𝗇 𝔈 𝗫
𝗇 𝔉 𝘁₂+1
𝗇 𝔊 lowerSaddleGrid d m theta Cω x
𝗃 𝔓 ἀ C.smoothness d m theta Cω
𝗇 𝔏 𝔓 lowerSaddleN 𝔄 x
𝗇 𝔐 𝔓 lowerAliasCutoff 𝔉 𝔄 x
𝗇 𝔔 𝙰₂ Cω x
def completeSourceSaddleRows (C : ModelConstants d)
    (q : ℕ) (Cfr lam Cω x : ℝ) :=
  let m := highCompleteSourceSaddleCoefficient C
  let theta := highCompleteSourceSaddleTheta C
  completeSourceRows C 𝔊
    𝔅 𝔈 q Cfr lam
    𝔐
    𝔏
    𝔔

𝗃 𝔘 ἀ C q Cfr lam
𝗇 𝔍 highRowTotalMass (𝔘 completeSourceSaddleRows Cω x).rowMass
def completeSourceSaddleActivity (C : ModelConstants d)
    (q : ℕ) (Cfr lam Cω x : ℝ) : ℝ :=
  𝔍/highCenterMix C

def completeSourceSaddleActivityConstant (C : ModelConstants d)
    (q : ℕ) (Cfr lam : ℝ) : ℝ :=
  sourceSaddleActivityConstant d q C.densityLower C.densityUpper Cfr lam/highCenterMix C

theorem completeSourceSaddleActivityConstant_pos (C : ModelConstants d)
    q Cfr lam : 0 < 𝔘 completeSourceSaddleActivityConstant := div_pos (sourceSaddleActivityConstant_positive d q _ _ _ _ C.densityLower_pos
    $ C.densityLower_lt_one.trans C.one_lt_densityUpper ) 𝘗₁

𝗃 𝔒 (ἀ:ℝ)
𝗃 𝔗 ἀ C.smoothness d (highCompleteSourceSaddleCoefficient C) (highCompleteSourceSaddleTheta C) Cω
/-- The row-budget constant includes the balancing reference factor exactly. -/
theorem completeSourceSaddleActivity_eventually_bound [NeZero d]
    (C : ModelConstants d) (hs : 𝘎) (hd : 𝘊 < d)
    q Cfr lam Cω :
    ∀ᶠ x : ℝ in atTop,
      𝔘 completeSourceSaddleActivity Cω x ≤
        𝔘 completeSourceSaddleActivityConstant *
          𝔗 lowerSaddleActivity
              𝔄 x := by
  filter_upwards [sourceSaddleTotalMass_eventually_bound d q C.smoothness
    C.densityLower C.densityUpper Cfr lam Cω hs hd C.densityLower_pos
    $ C.densityLower_lt_one.trans C.one_lt_densityUpper ] with x hx
  let m := highCompleteSourceSaddleCoefficient C
  let theta := highCompleteSourceSaddleTheta C
  let M := 𝔈
  let D := 𝔅
  let k := 𝔊
  let N := 𝔏
  let ell := 𝔐
  let mu := 𝔔
  have hmass : 𝔍 =
      sourceSaddleTotalMass d k q C.smoothness C.densityLower C.densityUpper Cfr lam Cω x := by
    let F : 𝚑 → ℝ := fun z =>
      highRowTotalMass (𝙴₂ z.1 z.2 Cfr lam ell N mu).rowMass
    let z1 := (C.densityLower+𝗙,C.densityUpper-𝗙)
    let z2 := (C.densityLower+𝔒 M⁻¹,C.densityUpper-𝔒 M⁻¹)
    have h := @congrArg 𝚑 ℝ z1 z2 F 𝖤₃
    exact h
  have h := div_le_div_of_nonneg_right (hmass.trans_le $ hx k ) (𝘗₁).le
  apply h.trans_eq
  dsimp only [completeSourceSaddleActivityConstant,lowerSaddleActivity,
    highCompleteSourceSaddleCoefficient,highCompleteSourceSaddleTheta]
  ring

𝗃 𝔖 ἀ d (highCompleteSourceSaddleCoefficient C) (highCompleteSourceSaddleTheta C) Cω x
𝗇 𝔇 𝔖 lowerSaddleGrid
/-- The source's physical amplitude is exactly the rounded saddle amplitude. -/
theorem completeSourceSaddle_eta_eq (C : ModelConstants d) Cω cf x :
    cf*𝔇^(-C.smoothness) =
      𝔗 lowerSaddleEta cf x := by
  unfold lowerSaddleEta lowerSaddleH
  rw [Real.inv_rpow (lowerSaddleGrid_positive ..).le,
    Real.rpow_neg (lowerSaddleGrid_positive ..).le]

/-- Exact inverse-volume accounting for the physical rounded grid. -/
theorem completeSourceSaddle_inverse_volume (C : ModelConstants d) Cω x :
    𝔇^d =
      𝔖 lowerSaddleH^(-𝔒 d) := by
  unfold lowerSaddleH
  simp

/-- Fixed positive amplitudes and mass tolerances satisfying the original model budgets. -/
theorem completeSourceSaddle_numeric_constants (C : ModelConstants d) :
    ∃ cf cm , 𝙻₁ ∧ 𝙵₂ ∧
      0 < cm ∧ 𝘉₂ := by
  let cf := C.holderBound/highWindowHolderConstant C
  let cm := 1/C.densityUpper
  refine ⟨cf,cm,div_pos C.holderBound_pos $ highWindowHolderConstant_pos C ,?_,
    one_div_pos.mpr $ lt_trans zero_lt_one C.one_lt_densityUpper ,le_rfl⟩
  rw [mul_div_cancel₀ _ (highWindowHolderConstant_pos C).ne']

𝗇 𝔎 tau+1
𝗇 𝔑 1 ≤ 𝔓 lowerSaddleActivity 𝔄 x
/-- All elementary source, amplitude and mass guards hold at the actual
rounded grid, for constants fixed independently of the extension domain. -/
theorem eventually_completeSourceSaddle_parameters [NeZero d]
    (C : ModelConstants d) (hs : 𝘎) (hd : 𝘊 < 𝔒 d)
    (_hcf : 𝙻₁) (heta0 : 𝖴₁) (hcm : 0 < cm) (Cω : ℝ) :
    ∀ᶠ x : ℝ in atTop,
      let m := highCompleteSourceSaddleCoefficient C
      let theta := highCompleteSourceSaddleTheta C
      let k := 𝔊
      let M := 𝔈
      let D := 𝔅
      let N := 𝔏
      let ell := 𝔐
      𝗑 ∧ 𝗕 ∧ 𝘧 ∧
      𝚁₁ ∧ 𝘈₂ ∧ cf*𝔒 k^(-C.smoothness) ≤ eta0 ∧
      8*highHistoryMassParameter d k C.densityLower C.densityUpper*x ≤ cm/M ∧
      𝔑 := by
  let m := highCompleteSourceSaddleCoefficient C
  let theta := highCompleteSourceSaddleTheta C
  let tau := 𝘁₂
  have hab := C.densityLower_lt_one.trans C.one_lt_densityUpper
  have htau := densityIntervalExponent_pos C.densityLower_pos hab
  have hm : 0 < m := lowerSaddleCoefficient_pos hs hd htau
  have htheta : 0 < theta := lowerSaddleTheta_pos hs hd htau
  have hd0 : 𝙋 < d := 𝖡₄
  obtain ⟨Ctau,_,hcontrol⟩ := exists_actual_lowerExponentControl C.densityLower_pos hab
  have hgrid :=
    tendsto_natCast_atTop_iff.mp $ lowerSaddleGrid_tendsto_atTop hd0 hm htheta Cω
  have htauM := (lowerSaddleM_nat_tendsto_atTop hm).eventually hcontrol
  filter_upwards [hgrid.eventually $ eventually_ge_atTop 4 ,
    𝘂₂
      $ eventually_ge_atTop $ max (highCenterResolutionThreshold C) 3 ,
    (lowerSaddleN_tendsto_atTop hs hd hm htheta hcontrol Cω).eventually
      $ eventually_ge_atTop 𝙠 ,
    (lowerSaddleEta_tends_zero C.smoothness_pos hd0 hm htheta Cω cf).eventually
      $ gt_mem_nhds heta0 ,
    eventually_highHistoryMass_saddle_guard (NeZero.pos d) hm htheta hcm Cω
      C.densityLower C.densityUpper hab,htauM] with x hk hM hN heta heps htauMx
  have hM3 := (le_max_right _ _).trans hM
  have hD : 3 ≤ 𝔅 := by
    have hceil := Nat.le_ceil $ 𝙶*𝔒 𝔈
    have hDr : (3 : ℝ) ≤ 𝔅 := by
      dsimp only [lowerSaddleD] at ⊢
      nlinarith
    exact_mod_cast hDr
  have hDpos : 𝙋 < 𝔅 := 𝖠₃
  have hcut : Real.exp (-𝔎*𝔒 𝔅) < 1 := by
    apply Real.exp_lt_one_iff.mpr
    nlinarith
  have hell : 0 < 𝔓 lowerAliasCutoff 𝔎
      𝔄 x := by
    unfold lowerAliasCutoff
    positivity
  have hellN : 𝔓 lowerAliasCutoff 𝔎
      𝔄 x <
      𝔏 := by
    unfold lowerAliasCutoff
    nlinarith
  have hB : 𝔑 := by
    have hexp : 1 ≤ Real.exp (𝙲
        𝔈*𝔒 𝔈) := by
      apply Real.one_le_exp_iff.mpr
      bound
    unfold lowerSaddleActivity
    bound
  exact ⟨hk,hD,(𝚂₁).trans hM,hell,hellN,
    (completeSourceSaddle_eta_eq C Cω cf x).trans_le heta.le,heps.2,hB⟩
