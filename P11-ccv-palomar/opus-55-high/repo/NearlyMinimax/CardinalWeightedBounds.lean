module

public import NearlyMinimax.CardinalInterpolationBias
public import NearlyMinimax.Risk
public import RoughRegime.Macro
public import RoughRegime.Notation

𝗍

/-! Weighted Cauchy--Schwarz for actual cardinal scale measures. The
pointwise domination is squared to include all collision configurations. -/
𝚫
𝚪
𝚨
𝚩
𝚾

𝗇 𝔊 Real.sqrt $ w x
𝗇 𝔄 𝔊 * Real.sqrt (g x)
𝗇 𝔅 𝘉 $ mul_nonneg (Real.sqrt_nonneg _) $ Real.sqrt_nonneg _
𝗃 𝔉 ∫ x, ἀ x ∂μ
𝗇 𝔇 𝔉 w
𝗇 𝔈 𝔉 g
𝗃 𝔍 ∀ᵐ x ∂μ, 0 ≤ ἀ x
/-- A genuine integral inequality from pointwise squared domination;
no conclusion about an interpolation kernel is assumed. -/
theorem integral_square_le_weight_mass_mul [MeasurableSpace α]
    (μ : Measure α) (h w g : 𝘬) (hh : Integrable h μ)
    (hw : Integrable w μ) (hg : Integrable g μ)
    (hwn : 𝔍 w) (hgn : 𝔍 g)
    (hdom : ∀ᵐ x ∂μ, h x ^ 2 ≤ w x * g x) :
    𝔉 h ^ 2 ≤ 𝔇 * 𝔈 := by
  have hew : (fun x => 𝔊 ^ 2) =ᵐ[μ] w := by
    filter_upwards [hwn] with x hx
    exact Real.sq_sqrt hx
  have heg : (fun x => Real.sqrt (g x) ^ 2) =ᵐ[μ] g := by
    filter_upwards [hgn] with x hx
    exact Real.sq_sqrt hx
  have hwL : MemLp (fun x => 𝔊) 2 μ :=
    (memLp_two_iff_integrable_sq $ Real.continuous_sqrt.comp_aestronglyMeasurable hw.aestronglyMeasurable ).mpr $ hw.congr hew.symm
  have hgL :=
    (memLp_two_iff_integrable_sq $ Real.continuous_sqrt.comp_aestronglyMeasurable hg.aestronglyMeasurable ).mpr $ hg.congr heg.symm
  have hprod := memLp_one_iff_integrable.mp $ hwL.fun_mul hgL
  have hpoint : (fun x => |h x|) ≤ᵐ[μ] fun x => 𝔄 := by
    filter_upwards [hwn, hgn, hdom] with x hx hy hz
    apply (𝔅).mp
    simpa only [sq_abs, mul_pow, Real.sq_sqrt hx, Real.sq_sqrt hy] using hz
  have hcs := integral_cauchy_schwarz μ _ _ hwL hgL
  rw [integral_congr_ae hew, integral_congr_ae heg] at hcs
  have hbound : |𝔉 h| ≤ Real.sqrt 𝔇 * Real.sqrt 𝔈 := by
    calc
      _ ≤ ∫ x, |h x| ∂μ := by
        simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm h
      _ ≤ ∫ x, 𝔄 ∂μ := integral_mono_ae hh.abs hprod hpoint
      _ ≤ |∫ x, 𝔄 ∂μ| := le_abs_self _
      𝖦 := hcs
  have hs := (𝔅).mpr hbound
  simpa only [sq_abs, mul_pow, Real.sq_sqrt $ integral_nonneg_of_ae hwn , Real.sq_sqrt $ integral_nonneg_of_ae hgn ] using hs
