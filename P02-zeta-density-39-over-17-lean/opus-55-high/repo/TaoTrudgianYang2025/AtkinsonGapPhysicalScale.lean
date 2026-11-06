module
public import TaoTrudgianYang2025.AtkinsonGapExponentPair
import WeylPort.Analytic.RealLaplace

@[expose] public section

/-! The true Atkinson gap frequency has uniform physical square-root scales. -/

noncomputable section
namespace TaoTrudgianYang2025
open MathCollab.Density.Stronger MathCollab.Density.Stronger.Atkinson MathCollab.Density.Stronger.Fourth

section
variable {H M t u : ℝ} (hH : 0 < H) (hM : 0 < M) (hu : H ≤ u) (hu2 : u ≤ 2*H) (ht : u < t) (ht2 : t ≤ 2*u)
include H M t u hH hM hu hu2 ht ht2
theorem atkinsonGap_denominator_bounds :
    Real.sqrt (H*M) ≤
        M*Real.sqrt (2*Real.pi*u/M)*(Real.sqrt (t/u)+1) ∧
      M*Real.sqrt (2*Real.pi*u/M)*(Real.sqrt (t/u)+1) ≤
        12*Real.sqrt (H*M) := by
  pm_4278 hup u hH.trans_le hu htp t hup.trans ht
  pm_976 hs
  pm_7157
  have ha : 0 < M*Real.sqrt (2*Real.pi*u/M) := mul_pos hM hs
  have he : (M*Real.sqrt (2*Real.pi*u/M))^2 = 2*Real.pi*M*u := by
    rw [mul_pow,Real.sq_sqrt (by positivity : 0 ≤ 2*Real.pi*u/M)]
    field_simp
  have hR2 := Real.sq_sqrt (show 0 ≤ H*M by positivity)
  have hl : H ≤ 2*Real.pi*u := by
    have hp : 0 ≤ (2*Real.pi-1)*u :=
      mul_nonneg (by linarith [Real.pi_gt_three]) hup.le
    linarith
  have hpiu : Real.pi*u ≤ 8*H := by
    have h := mul_le_mul Real.pi_lt_four.le hu2 hup.le (by norm_num : (0 : ℝ) ≤ 4)
    nlinarith
  have hal : Real.sqrt (H*M) ≤ M*Real.sqrt (2*Real.pi*u/M) := by
    have hh := mul_le_mul_of_nonneg_right hl hM.le
    nlinarith
  have hau : M*Real.sqrt (2*Real.pi*u/M) ≤ 4*Real.sqrt (H*M) := by
    pm_513 hh hpiu M
    nlinarith
  have hr : t/u ≤ 2 := (div_le_iff₀ hup).mpr ht2
  have hrs : Real.sqrt (t/u) ≤ 2 := by
    apply (Real.sqrt_le_iff).mpr
    exact ⟨by norm_num,by linarith⟩
  constructor
  · exact hal.trans (le_mul_of_one_le_right ha.le (by linarith [Real.sqrt_nonneg (t/u)]))
  · calc
      _ ≤ (4*Real.sqrt (H*M))*3 :=
        mul_le_mul hau (by linarith : Real.sqrt (t/u)+1 ≤ 3)
          (by positivity) (by positivity)
      _ = _ := by ring

theorem atkinsonGap_frequency_physical_bounds :
    atkinsonGapFrequency M t u/(2*Real.pi*M) ≤ (t-u)/Real.sqrt (H*M) ∧
      2*Real.pi*M/atkinsonGapFrequency M t u ≤
        12*Real.sqrt (H*M)/(t-u) := by
  have hup : 0 < u := hH.trans_le hu
  pm_5221 hgap t u ht
  pm_7157
  pm_976 hs
  obtain ⟨hl,hh⟩ := atkinsonGap_denominator_bounds hH hM hu hu2 ht ht2
  have he : atkinsonGapFrequency M t u/(2*Real.pi*M) =
      (t-u)/(M*Real.sqrt (2*Real.pi*u/M)*(Real.sqrt (t/u)+1)) := by
    unfold atkinsonGapFrequency
    field_simp
  have he' : 2*Real.pi*M/atkinsonGapFrequency M t u =
      (M*Real.sqrt (2*Real.pi*u/M)*(Real.sqrt (t/u)+1))/(t-u) := by
    unfold atkinsonGapFrequency
    field_simp
  rw [he,he']
  exact ⟨div_le_div_of_nonneg_left hgap.le hR hl,
    div_le_div_of_nonneg_right hh hgap.le⟩
end

end TaoTrudgianYang2025
