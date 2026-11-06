module
public import TaoTrudgianYang2025.BProcessBaseline
public import TaoTrudgianYang2025.BetaBufferedInteriorStationary
public import TaoTrudgianYang2025.BetaClosedSlopeInverseAdapter
import WeylPort.Analytic.RealLaplace

@[expose] public section

/-!
# Stationary errors in actual frequency-distance units

The original derivative's upper curvature bound converts a gap from
the two plateau endpoint slopes to a physical distance of the actual
critical point. The physical N/T scaling then cancels in the remainder.
-/

noncomputable section

open Set Expdb
open scoped ContDiff FourierTransform

namespace TaoTrudgianYang2025
open MathCollab.Density.Stronger.Atkinson MathCollab.Density.Stronger.PointMean MathCollab.Density.Stronger.Fourth

theorem modelPhaseInverseSlope_interior_of_gap
    {F : ℝ → ℝ} {σ δ v a b w : ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ)
    (hv : v ∈ modelPhaseSlopeRange F)
    (ha : a ∈ Ioo (1 : ℝ) 2) (hb : b ∈ Ioo (1 : ℝ) 2) (hw : 0 < w)
    (hleft : v+w ≤ deriv F a) (hright : deriv F b+w ≤ v) :
    a+w/(σ+1) ≤ modelPhaseInverseSlope F v ∧
      modelPhaseInverseSlope F v+w/(σ+1) ≤ b := by
  have hu := modelPhaseInverseSlope_mem hv
  pm_5045 hm approximateModelPhase_deriv_strictAntiOn
  have hau : a < modelPhaseInverseSlope F v := by
    pm_7628 hu ha
  have hub : modelPhaseInverseSlope F v < b := by
    pm_7628 hb hu
  have hL := approximateModelPhase_slope_gap_upper_abs hσ hδ hF ha hu
  have hR := approximateModelPhase_slope_gap_upper_abs hσ hδ hF hu hb
  rw [deriv_modelPhaseInverseSlope_apply hv,
    abs_of_nonneg (by linarith : 0 ≤ deriv F a-v),
    abs_of_nonpos (sub_nonpos.mpr hau.le)] at hL
  rw [deriv_modelPhaseInverseSlope_apply hv,
    abs_of_nonneg (by linarith : 0 ≤ v-deriv F b),
    abs_of_nonpos (sub_nonpos.mpr hub.le)] at hR
  have hs : 0 < σ+1 := by linarith
  have hL' : w/(σ+1) ≤ modelPhaseInverseSlope F v-a :=
    (div_le_iff₀ hs).mpr (by nlinarith)
  have hR' : w/(σ+1) ≤ b-modelPhaseInverseSlope F v :=
    (div_le_iff₀ hs).mpr (by nlinarith)
  grind

theorem modelPhaseBufferedFourierMode_interior_frequency_uniform
    {σ : ℝ} (hσ : 0 < σ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (l r η : ℝ), 1 ≤ l → r ≤ 2 → 0 < η → l+4*η < r →
      ∀ (F : ℝ → ℝ) (δ T N q lam : ℝ),
        δ ≤ min (modelPhaseCurvatureLower σ) 1 →
        IsApproximateModelPhaseFunction F σ bufferedLocalStationaryOrder δ →
        0 < T → 0 < N → 0 < lam →
        (T/N)*deriv F (r-2*η)+lam ≤ q →
        q+lam ≤ (T/N)*deriv F (l+2*η) →
        ‖modelPhaseFourierMode (modelPhaseBufferedCutoff l r η) F T N q-
          modelPhaseStationaryMainTerm F T N q‖ ≤ C/lam := by
  obtain ⟨C,hC,hmode⟩ := modelPhaseBufferedFourierMode_interior_uniform hσ
  have hσ₁ : 0 < σ+1 := by linarith
  refine ⟨C*(σ+1),by nlinarith,?_⟩
  intro l r η hl hr hη hflat F δ T N q lam hδ hF hT hN hlam hright hleft
  have hF₁ := approximateModelPhase_mono hF bufferedLocalStationaryOrder_pos le_rfl
  pm_6528 hscale N T hN hT
  pm_194 hL mul_le_mul_of_nonneg_right hleft hscale.le hR hright
  have he (u : ℝ) : ((T/N)*u)*(N/T) = u := by field_simp
  rw [add_mul,he] at hL hR
  have hL' : q*N/T+N*lam/T ≤ deriv F (l+2*η) := by
    convert hL using 1
    ring
  have hR' : deriv F (r-2*η)+N*lam/T ≤ q*N/T := by
    convert hR using 1 <;> ring
  pm_1637
  have hw : 0 < N*lam/T := div_pos (mul_pos hN hlam) hT
  have hv : q*N/T ∈ modelPhaseSlopeRange F := by
    pm_5275 hF₁
  have hi := modelPhaseInverseSlope_interior_of_gap hσ hδ hF₁ hv
    ha hb hw hL' hR'
  have hd : 0 < (N*lam/T)/(σ+1) := div_pos (div_pos (mul_pos hN hlam) hT) hσ₁
  have h := hmode l r η ((N*lam/T)/(σ+1)) hl hr hη hd F δ T N q
    hδ hF hT hN hv hi.1 hi.2
  apply h.trans_eq
  field_simp

end TaoTrudgianYang2025
