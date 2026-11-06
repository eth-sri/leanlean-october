module

public import NearlyMinimax.Model
public import RoughRegime.Macro
public import RoughRegime.Applications
public import RoughRegime.Notation


𝗍

/-! Extended-valued RMS risk agrees with the infimum of supremum L2 errors.
These identities do not assume second-moment finiteness of the estimator.
-/

𝚯
𝚮
𝚨

theorem meanSquaredRisk_rpow_eq_eLpNorm T
    (θ : RegressionParameter d) :
    meanSquaredRisk T θ ^ (𝙖 : ℝ) =
      eLpNorm (fun z => 𝗻₂) 2 𝗷 := by
  symm
  exact RoughRegime.Applications.eLpNorm_two_eq_squaredIntegral 𝗷
    (fun z => 𝗻₂) $ T.property.sub measurable_const

theorem minimaxRMS_eq_inf_sup_rms C n :
    𝚢 = ⨅ T : 𝚠,
      ⨆ θ : {θ : RegressionParameter d // 𝙟},
        meanSquaredRisk T θ.val ^ (𝙖 : ℝ) := by
  let φ := ENNReal.orderIsoRpow 𝙖 𝖠₄
  change φ (⨅ T : 𝚠, ⨆ θ : {θ // 𝙟}, meanSquaredRisk T θ.val) = _
  aesop

theorem minimaxRMS_eq_inf_sup_eLpNorm C n :
    𝚢 = ⨅ T : 𝚠,
      ⨆ θ : {θ : RegressionParameter d // 𝙟},
        𝚍₂ := by
  rw [minimaxRMS_eq_inf_sup_rms]
  simp_rw [meanSquaredRisk_rpow_eq_eLpNorm]
