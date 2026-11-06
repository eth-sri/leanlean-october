module
/-
Copyright (c) 2026 S. McColm. Released under the MIT-0 license.
Selected exact source slices from revision 6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1.
See third_party/twelfth/ATKINSON_FINITE_ERROR_MANIFEST.json. Mathlib/PNT foundations retain Apache-2.0 attribution.
-/
public import MathCollab.Density.Stronger.Atkinson.AtkinsonStationarySumScale
public import MathCollab.Density.Stronger.Atkinson.SmoothDivisorSupport
import WeylPort.Analytic.RealLaplace

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open Complex Filter
open MathCollab.Density.Stronger.Fourth
namespace MathCollab.Density.Stronger.Atkinson

section
variable {δ ε : ℝ} (hδ : 0 < δ) (hε : 0 < ε)
include δ ε hδ hε
theorem exists_atkinsonStationary_finite_log_error (hεmax : ε ≤ 1/4) :
    ∃ C : ℝ, 0 < C ∧ ∃ T₀ : ℝ, 40000 ≤ T₀ ∧ ∀ T G : ℝ,
      T₀ ≤ T → T^δ ≤ G → G ≤ T^(1/2-δ) → T^(1/4 : ℝ) ≤ G →
      ‖atkinsonLeadingFiniteSum T G (Real.log T) (atkinsonSourceCutoff T G (Real.log T)) -
        atkinsonStationaryLeadingSum T G (Real.log T)‖ ≤
          C*T^(1/4+ε)*(Real.log T)^2 := by
  obtain ⟨C,hC,hbound⟩ := exists_norm_atkinsonLeadingFiniteSum_sub_stationary_le hε
  have hev : ∀ᶠ T : ℝ in atTop, ∀ G : ℝ, T^δ ≤ G → G ≤ T^(1/2-δ) →
      T^(1/4 : ℝ) ≤ G →
      ‖atkinsonLeadingFiniteSum T G (Real.log T) (atkinsonSourceCutoff T G (Real.log T)) -
        atkinsonStationaryLeadingSum T G (Real.log T)‖ ≤
          (37*C)*T^(1/4+ε)*(Real.log T)^2 := by
    filter_upwards [eventually_zetaSmoothDivisorTest_support_physical hδ,
      eventually_zeta_source_log_window_scales hδ,eventually_atkinsonSourceCutoff_small hδ]
      with T hsupport hscale hcut
    intro G hlower hupper hquarter
    pm_7852
    have hT0 : 0 < T := by linarith
    obtain ⟨hG0,hlog0,hwidth,_⟩ := hsupport.2 G hlower
    pm_5433 hquarter
    have hGS : G ≤ Real.sqrt T := hupper.trans (by
      rw [Real.sqrt_eq_rpow]
      exact Real.rpow_le_rpow_of_exponent_le hT (by linarith))
    rw [atkinsonStationaryLeadingSum_eq_finite hT0 hG0 hlog0 hwidth]
    apply (hbound T G (Real.log T) hT hquarter hGS hscale.2.1 hwidth
      (atkinsonSourceCutoff T G (Real.log T)) (hcut G hlower)).trans
    have he := atkinsonStationary_cutoff_scale_le hT hG1 hGS hscale.2.1
      (q := 3/4+ε) (by linarith) (by linarith)
    have h := mul_le_mul_of_nonneg_left he hC.le
    norm_num only [show (3/4+ε-1/2 : ℝ) = 1/4+ε by ring] at h
    convert h using 1 <;> ring
  obtain ⟨B,hB⟩ := eventually_atTop.mp hev
  refine ⟨37*C,by positivity,max 40000 B,le_max_left _ _,?_⟩
  pm_5986 hB

theorem exists_atkinsonStationary_finite_power_error :
    ∃ C : ℝ, 0 < C ∧ ∃ T₀ : ℝ, 40000 ≤ T₀ ∧ ∀ T G : ℝ,
      T₀ ≤ T → T^δ ≤ G → G ≤ T^(1/2-δ) → T^(1/4 : ℝ) ≤ G →
      ‖atkinsonLeadingFiniteSum T G (Real.log T) (atkinsonSourceCutoff T G (Real.log T)) -
        atkinsonStationaryLeadingSum T G (Real.log T)‖ ≤ C*T^(1/4+ε) := by
  let e : ℝ := min (ε/2) (1/4)
  pm_251 he e
  pm_5315 hemax e min_le_right
  have heε : e ≤ ε/2 := min_le_left _ _
  have hη : 0 < ε-e := by linarith
  obtain ⟨C,hC,B,hB,hbound⟩ := exists_atkinsonStationary_finite_log_error hδ he hemax
  obtain ⟨D,hD⟩ := eventually_atTop.mp (eventually_const_log_pow_le_rpow 1 (by norm_num) 2 hη)
  pm_1071 B D hB.trans
  intro T G hT hlower hupper hquarter
  pm_207 hTB B T le_max_left hT
  have hT0 : 0 < T := by linarith
  have hlog := hD T ((le_max_right _ _).trans hT)
  simp only [one_mul] at hlog
  apply (hbound T G hTB hlower hupper hquarter).trans
  calc
    _ ≤ C*T^(1/4+e)*T^(ε-e) := mul_le_mul_of_nonneg_left hlog (by positivity)
    _ = C*T^(1/4+ε) := by
      rw [mul_assoc,← Real.rpow_add hT0]
      congr 2
      ring
end

end MathCollab.Density.Stronger.Atkinson
