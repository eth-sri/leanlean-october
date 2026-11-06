module

public import NearlyMinimax.HigherBandFamily
public import NearlyMinimax.LowerActivityHierarchy
public import RoughRegime.Macro
public import RoughRegime.Notation


𝗍

/-! The physical higher-family omission and fine-count guards follow
from the actual rounded canonical saddle, before any signed action is tested. -/
𝚷
𝚶
𝚨
𝚩
𝚱

𝗇 𝔅 𝙉₂
𝗇 𝔄 lowerSaddleN s d m theta shift 𝔅 x
theorem sourceSaddleHigherFamily_eventually_legal (d : ℕ)
    s a b shift (hs : 𝚊₁) (hd : 𝚄 < 𝙊) (ha : 𝙆) (hab : 𝙭) :
    let tau := 𝘦₂
    let m := lowerSaddleCoefficient s d tau
    let theta := lowerSaddleTheta s d tau
    ∀ᶠ x in atTop,
      let M := 𝗫
      let N := 𝔄
      let mu := 𝙰₂ shift x
      let ell := lowerAliasCutoff s d m theta shift (tau+1) 𝔅 x
      𝚒 := by
  let tau := 𝘦₂
  let m := lowerSaddleCoefficient s d tau
  let theta := lowerSaddleTheta s d tau
  have hτ := densityIntervalExponent_pos ha hab
  obtain ⟨Cτ, _, hcontrol⟩ := exists_actual_lowerExponentControl ha hab
  have hN := lowerSaddleN_tendsto_atTop hs hd (lowerSaddleCoefficient_pos hs hd hτ) (lowerSaddleTheta_pos hs hd hτ) hcontrol shift
  filter_upwards [ actual_lowerAlias_hierarchy (Cact := 1) (Cs := 1) hs hd ha hab  𝖠₄   𝖠₄  shift , hN.eventually $ eventually_ge_atTop 1 , eventually_gt_atTop 0]
    with x hx hNx hxp
  rcases hx with ⟨hell, _, _, _, _, _, _, _, _, _, hRM, hFine⟩
  have hmu : 0 < 𝙰₂ shift x := by
    rw [lowerSaddleMu_eq_exp hxp]
    exact Real.exp_pos _
  have hH : 0 < 1+Real.log 𝔄 := by
    linarith [Real.log_nonneg hNx]
  refine ⟨hell.le, ?_, ?_⟩
  · intro r
    unfold higherBandTargetScale
    positivity
  · intro r hr
    exact (hFine r hr).trans hRM
