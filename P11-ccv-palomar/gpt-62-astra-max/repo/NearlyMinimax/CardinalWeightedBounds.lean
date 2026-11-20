module

public import NearlyMinimax.CardinalInterpolationBias
public import NearlyMinimax.Risk

@[expose] public section

/-! Weighted Cauchy--Schwarz for actual cardinal scale measures. The
pointwise domination is squared to include all collision configurations. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 700000

/-- A genuine integral inequality from pointwise squared domination;
no conclusion about an interpolation kernel is assumed. -/
theorem integral_square_le_weight_mass_mul {α : Type*} [MeasurableSpace α]
    {μ : Measure α} (h : α → ℝ) {w g : α → ℝ} (hh : Integrable h μ)
    (hw : Integrable w μ) (hg : Integrable g μ)
    (hwn : ∀ᵐ x ∂μ, 0 ≤ w x) (hgn : ∀ᵐ x ∂μ, 0 ≤ g x)
    (hdom : ∀ᵐ x ∂μ, (h x) ^ 2 ≤ w x * g x) :
    (∫ x, h x ∂μ) ^ 2 ≤ (∫ x, w x ∂μ) * (∫ x, g x ∂μ) := by
  have hew : (fun x => Real.sqrt (w x) ^ 2) =ᵐ[μ] w := by
    filter_upwards [hwn] with x hx
    exact Real.sq_sqrt hx
  have heg : (fun x => Real.sqrt (g x) ^ 2) =ᵐ[μ] g := by
    filter_upwards [hgn] with x hx
    exact Real.sq_sqrt hx
  have hwL  :=
    (memLp_two_iff_integrable_sq (Real.continuous_sqrt.comp_aestronglyMeasurable hw.aestronglyMeasurable)).mpr (hw.congr hew.symm)
  have hgL  :=
    (memLp_two_iff_integrable_sq (Real.continuous_sqrt.comp_aestronglyMeasurable hg.aestronglyMeasurable)).mpr (hg.congr heg.symm)
  have hprod := memLp_one_iff_integrable.mp (hwL.fun_mul hgL)
  have hpoint : (fun x => |h x|) ≤ᵐ[μ] (fun x => Real.sqrt (w x) * Real.sqrt (g x)) := by
    filter_upwards [hwn, hgn, hdom] with x hx hy hz
    apply (sq_le_sq₀ (abs_nonneg _) (by positivity)).mp
    simpa only [sq_abs, mul_pow, Real.sq_sqrt hx, Real.sq_sqrt hy] using hz
  have hcs := integral_cauchy_schwarz hwL hgL
  rw [integral_congr_ae hew, integral_congr_ae heg] at hcs
  have hW  := integral_nonneg_of_ae hwn
  have hG  := integral_nonneg_of_ae hgn
  have hbound : |∫ x, h x ∂μ| ≤ Real.sqrt (∫ x, w x ∂μ) * Real.sqrt (∫ x, g x ∂μ) := by
    calc
      _ ≤ _ := norm_integral_le_integral_norm h
      _ ≤ _ := integral_mono_ae hh.abs hprod hpoint
      _ ≤ _ := le_abs_self _
      _ ≤ _ := hcs
  simpa only [sq_abs, mul_pow, Real.sq_sqrt hW, Real.sq_sqrt hG] using (sq_le_sq₀ (abs_nonneg _) (by positivity)).mpr hbound

end NearlyMinimax
