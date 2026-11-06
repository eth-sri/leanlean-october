module

public import NearlyMinimax.HighMassTilt
public import RoughRegime.Macro
public import RoughRegime.Notation


𝗍

/-! Exact observable cancellation for genuine mass-tilted high-prior experiments. -/
𝚴
𝛉
𝚨
𝚱
𝚩
𝛂

𝗇 𝔄 Ω × 𝙇 × 𝙈
𝗇 𝔅 𝘂₁
𝗇 𝔇 𝙙
𝗇 𝔈 𝘱
𝗃 𝔉 ἀ n a V p F hp hF
/-- Actual tilted-prior/data integration cancels m^n against the true sample density.
This identity holds for arbitrary real observables, with the usual total Bochner integral. -/
theorem massPowerTilt_highSample_integral (ν : Measure Ω) [IsProbabilityMeasure ν]
    (n : ℕ) (a V : ℝ) (p F : Ω → 𝙀)
    hp hF
    aRaw bRaw (haRaw : 𝙓)
    (hraw : 𝙄)
    (hq : ∀ ω x y, 0 ≤ 𝙅 V y)
    (H : 𝔄 → ℝ) :
     ∫ z, H z ∂(massPowerTilt ν 𝔇 n).compProd
      𝔉 highSampleIndexKernel =
      (massPowerNormalizer ν 𝔇 n)⁻¹ *
        ∫ z, 𝔅 * H z
          ∂ν.prod 𝔈 := by
  let m := 𝔇
  have hm := 𝙨
  have hbound ω :=
    𝖤₁
  have hG := 𝘰₁ hbound
  have hu0 (z : 𝔄) :
      0 ≤ 𝔅 :=
    Finset.prod_nonneg fun i _ => mul_nonneg (haRaw.le.trans (hraw z.1 $ z.2.1 i ).1)
      $ hq z.1 (z.2.1 i) $ z.2.2 i
  have hD : Measurable fun z : 𝔄 =>
      ENNReal.ofReal $ 𝔅 /
        𝖡₁ :=
    ENNReal.measurable_ofReal.comp $ (𝔉 highRawSampleLikelihood_joint_measurable).div_const _
  rw [massPowerTilt_highSample_compProd ν n a V p F hp hF aRaw bRaw haRaw hraw,
    integral_withDensity_eq_integral_toReal_smul hD
      $ Filter.Eventually.of_forall 𝘕 ]
  simp_rw [ENNReal.toReal_ofReal $ div_nonneg (hu0 _) hG.le , smul_eq_mul]
  calc
    _ = ∫ z, 𝖡₁⁻¹ *
        (𝔅 * H z)
          ∂ν.prod 𝔈 := by
      field_simp
    𝘿 := integral_const_mul ..
