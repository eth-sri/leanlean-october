/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import BergmanWeakType.Rigidity.KernelTransform
public import BergmanWeakType.WeightedSharp

public section

open Set MeasureTheory Metric Filter
open scoped ENNReal

namespace BergmanWeakType

/-- Similarities preserve the set of weak bounds, hence the optimal disk constant. -/
theorem weakTypeConstant_domainPositiveProjection_ball_eq_one (a : ℂ) {R : ℝ} (hR : 0 < R)
    {K : ℂ → ℂ → ℂ} (hK : IsBergmanKernel (ball a R) K) :
    weakTypeConstant (area.restrict (ball a R)) (domainPositiveProjection (ball a R) K) = 1 := by
  let e := diskChart a hR.ne'
  let c := ENNReal.ofReal (R ^ 2)
  let μ := area.restrict (ball a R)
  let T := domainPositiveProjection (ball a R) K
  have hc : c ≠ 0 := by positivity
  have hμ : μ = c • Measure.map e diskArea := by
    simpa [abs_of_pos hR] using area_restrict_ball_eq_map a hR.ne'
  have he : DifferentiableOn ℂ e disk := by
    change DifferentiableOn ℂ (fun x : ℂ ↦ a + (R : ℂ) * x) _
    fun_prop
  have hde (w : ℂ) : deriv e w = (R : ℂ) := by
    change deriv (fun x : ℂ ↦ a + (R : ℂ) * x) _ = _
    simp
  have hb := e.injective.injOn.bijOn_image (s := disk)
  rw [show e '' disk = ball a R by simpa [abs_of_pos hR] using diskChart_image a hR.ne'] at hb
  have hinv : InvOn e.symm e disk (ball a R) :=
    ⟨fun _ _ ↦ e.symm_apply_apply _, fun _ _ ↦ e.apply_symm_apply _⟩
  have heinv : DifferentiableOn ℂ e.symm (ball a R) := by
    change DifferentiableOn ℂ (fun x : ℂ ↦ (R : ℂ)⁻¹ * (-a + x)) _
    fun_prop
  have hcoef {z w : ℂ} (hz : z ∈ disk) (hw : w ∈ disk) :
      c * ENNReal.ofReal ‖K (e z) (e w)‖ = ENNReal.ofReal ‖kernel z w‖ := by
    dsimp only [c]
    rw [hK.disk_formula isOpen_ball he heinv hb hinv hz hw, hde, hde, norm_div,
      norm_mul, Complex.norm_conj, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR,
      ← pow_two, ← ENNReal.ofReal_mul (sq_nonneg R), mul_div_cancel₀ _ (pow_ne_zero 2 hR.ne')]
  have hproj (f : ℂ → ℂ) {z : ℂ} (hz : z ∈ disk) : T f (e z) = positiveProjection (f ∘ e) z := by
    change (∫⁻ w, ENNReal.ofReal ‖K (e z) w‖ * ‖f w‖ₑ ∂μ) = _
    rw [hμ, lintegral_smul_measure, e.measurableEmbedding.lintegral_map, smul_eq_mul,
      ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    apply lintegral_congr_ae
    filter_upwards [ae_mem_disk] with w hw
    rw [← mul_assoc, hcoef hz hw]
    rfl
  have hlevel (f : ℂ → ℂ) (t : ℝ) : diskArea (e ⁻¹' {z | ENNReal.ofReal t < T f z}) =
      diskArea {z | ENNReal.ofReal t < positiveProjection (f ∘ e) z} := by
    apply measure_congr
    filter_upwards [ae_mem_disk] with w hw
    simp [hproj f hw]
  have h (C : ℝ≥0∞) : IsWeakTypeBound μ T C ↔ IsWeakTypeBound diskArea positiveProjection C := by
    simp only [IsWeakTypeBound, hμ, integrable_smul_measure hc ENNReal.ofReal_ne_top,
      e.measurableEmbedding.integrable_map_iff, Measure.smul_apply, smul_eq_mul, e.map_apply, hlevel,
      lintegral_smul_measure, e.measurableEmbedding.lintegral_map,
      mul_left_comm _ c, ENNReal.mul_le_mul_iff_right hc ENNReal.ofReal_ne_top]
    refine ⟨fun h g ↦ ?_, fun h f ↦ h (f ∘ e)⟩
    simpa only [Function.comp_def, MeasurableEquiv.symm_apply_apply] using h (g ∘ e.symm)
  change weakTypeConstant μ T = 1
  simpa [weakTypeConstant, h] using positiveProjection_constant_eq_one

end BergmanWeakType
