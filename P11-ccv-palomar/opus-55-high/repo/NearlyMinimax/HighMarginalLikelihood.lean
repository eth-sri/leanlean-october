module

public import NearlyMinimax.MarginalLikelihood
public import RoughRegime.Macro
public import RoughRegime.Notation


𝗌

/-! The exact marginal data density of the actual high mass-tilted experiment. -/
𝚹
𝚮
𝚨
𝚭
𝚩
𝛂

𝗇 𝔅 𝙇 × 𝙈
𝗇 𝔇 Ω → 𝙀
𝗃 𝔏 ἀ n a V
def highMarginalRawLikelihood (ν : Measure Ω) (n : ℕ) (a V : ℝ)
    (p F : 𝔇) (z : 𝔅) : ℝ :=
  ∫ ω, 𝔏 highRawSampleLikelihood (p ω) (F ω) z ∂ν

𝗇 𝔈 highMarginalRawLikelihood ν n a V p F
𝗇 𝔉 𝔏 highRawSampleLikelihood_joint_measurable p F hp hF
𝗇 𝔊 𝗃₁
𝗇 𝔍 𝙅 V y
section

variable (ν : Measure Ω)
    (n : ℕ)

include n

𝗃 𝔐 Measurable $ Function.uncurry ἀ
theorem highMarginalRawLikelihood_measurable [SFinite ν]
    (a V : ℝ) (p F : 𝔇)
    (hp : 𝔐 p) (hF : 𝔐 F) :
    Measurable 𝔈 :=
  (𝔉).stronglyMeasurable.integral_prod_left'.measurable

theorem highMarginalRawLikelihood_pos [IsProbabilityMeasure ν]
    (a V P : ℝ) (hP : 𝚏) (ha : 𝙞)
    (p F : 𝔇)
    (hp : 𝔐 p) (hF : 𝔐 F)
    (hpp : ∀ ω x, 0 < 𝔊) (hpb : ∀ ω x, |𝔊| ≤ P)
    (hq : ∀ ω x y, 0 < 𝔍)
    z :
    0 < 𝔈 z := by
  apply integral_likelihood_pos ν _
    (𝔉).of_uncurry_right 𝚗
  · exact fun ω => 𝔏 highRawSampleLikelihood_pos p F hpp hq ω z
  · exact fun ω => 𝚕₁
      $ 𝔏 highRawSampleLikelihood_abs_le P hP _ _ (hpb ω) ha
        (fun x y => (hq ω x y).le) z

end

𝗇 𝔄 𝙙
𝗇 𝔎 𝖡₁
/-- The genuine mixture sample density, with the actual constant G_n. -/
theorem highMassTilt_index_marginal_density (ν : Measure Ω) [IsProbabilityMeasure ν]
    (n : ℕ) (a V : ℝ) (p F : 𝔇)
    hp hF
    aRaw bRaw (haRaw : 𝙓) (ha : 𝙞)
    (hraw : ∀ ω x, aRaw ≤ 𝔊 ∧ 𝔊 ≤ bRaw)
    (hq : ∀ ω x y, 0 ≤ 𝔍) :
     𝔏 highSampleIndexKernel p F hp hF ∘ₘ
         massPowerTilt ν 𝔄 n =
      (𝘱).withDensity fun z => ENNReal.ofReal
        $ 𝔈 z /
          massPowerNormalizer ν 𝔄 n := by
  let m := 𝔄
  have hm := 𝙨
  have hb ω :=
    𝙕
  have hG := 𝘰₁ hb
  let _ := massPowerTilt_isProbability ν m hm n aRaw bRaw haRaw hb
  have hpabs ω x : |𝔊| ≤ |bRaw| := by
    grind
  let L : Ω × 𝔅 → ℝ := fun z =>
    𝔏 highRawSampleLikelihood (p z.1) (F z.1) z.2 / 𝔎
  have hLb z : 0 ≤ L z ∧ L z ≤ |bRaw|^n / 𝔎 := by
    have hlb := 𝔏 highRawSampleLikelihood_abs_le |bRaw| (abs_nonneg _) _ _ (hpabs z.1) ha (hq z.1) z.2
    exact ⟨div_nonneg (Finset.prod_nonneg fun i _ => mul_nonneg (haRaw.le.trans (hraw z.1 _).1) $ hq z.1 _ _ ) hG.le, div_le_div_of_nonneg_right (𝚕₁ hlb) hG.le⟩
  rw [← Measure.snd_compProd, Measure.snd,
    massPowerTilt_highSample_compProd ν n a V p F hp hF aRaw bRaw haRaw hraw]
  rw [map_snd_prod_withDensity_ofReal ν 𝘱 L ((𝔉).div_const _)
    (|bRaw|^n / 𝔎)  𝖠₃  hLb]
  congr 1
  funext z
  simp only [L, integral_div, highMarginalRawLikelihood, m]
