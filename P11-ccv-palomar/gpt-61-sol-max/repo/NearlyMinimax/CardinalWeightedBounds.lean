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
    (μ : Measure α) (h w g : α → ℝ) (hh : Integrable h μ)
    (hw : Integrable w μ) (hg : Integrable g μ)
    (hwn : ∀ᵐ x ∂μ, 0 ≤ w x) (hgn : ∀ᵐ x ∂μ, 0 ≤ g x)
    (hdom : ∀ᵐ x ∂μ, (h x) ^ 2 ≤ w x * g x) :
    (∫ x, h x ∂μ) ^ 2 ≤ (∫ x, w x ∂μ) * (∫ x, g x ∂μ) := by
  have hws  :=
    Real.continuous_sqrt.comp_aestronglyMeasurable hw.aestronglyMeasurable
  have hgs  :=
    Real.continuous_sqrt.comp_aestronglyMeasurable hg.aestronglyMeasurable
  have hew : (fun x => Real.sqrt (w x) ^ 2) =ᵐ[μ] w := by
    filter_upwards [hwn] with x hx
    exact Real.sq_sqrt hx
  have heg : (fun x => Real.sqrt (g x) ^ 2) =ᵐ[μ] g := by
    filter_upwards [hgn] with x hx
    exact Real.sq_sqrt hx
  have hwL  :=
    (memLp_two_iff_integrable_sq hws).mpr (hw.congr hew.symm)
  have hgL  :=
    (memLp_two_iff_integrable_sq hgs).mpr (hg.congr heg.symm)
  have hprodL : MemLp (fun x => Real.sqrt (w x) * Real.sqrt (g x)) 1 μ := hwL.fun_mul hgL
  have hprod := memLp_one_iff_integrable.mp hprodL
  have hpoint : (fun x => |h x|) ≤ᵐ[μ] (fun x => Real.sqrt (w x) * Real.sqrt (g x)) := by
    filter_upwards [hwn, hgn, hdom] with x hx hy hz
    apply (sq_le_sq₀ (abs_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))).mp
    simpa only [sq_abs, mul_pow, Real.sq_sqrt hx, Real.sq_sqrt hy] using hz
  have hcs := integral_cauchy_schwarz μ _ _ hwL hgL
  rw [integral_congr_ae hew, integral_congr_ae heg] at hcs
  have hW  := integral_nonneg_of_ae hwn
  have hG  := integral_nonneg_of_ae hgn
  have hbound : |∫ x, h x ∂μ| ≤ Real.sqrt (∫ x, w x ∂μ) * Real.sqrt (∫ x, g x ∂μ) := by
    calc
      _ ≤ ∫ x, |h x| ∂μ := by
        simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm h
      _ ≤ ∫ x, Real.sqrt (w x) * Real.sqrt (g x) ∂μ := integral_mono_ae hh.abs hprod hpoint
      _ ≤ |∫ x, Real.sqrt (w x) * Real.sqrt (g x) ∂μ| := le_abs_self _
      _ ≤ _ := hcs
  have hs := (sq_le_sq₀ (abs_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))).mpr hbound
  simpa only [sq_abs, mul_pow, Real.sq_sqrt hW, Real.sq_sqrt hG] using hs

end NearlyMinimax
