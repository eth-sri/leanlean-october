module
public import MathCollab.Density.Stronger.WeightedTwelfth
import WeylPort.Analytic.RealLaplace

@[expose] public section

open MeasureTheory Set Filter
open scoped BigOperators
set_option autoImplicit false
noncomputable section
namespace MathCollab.Density.Stronger

/-- Outside the physical interval, every sample in [T,2T] is at distance at
least T; its physical ordinate is controlled by three times that distance. -/
theorem physical_tail_geometry {T u t : ℝ} (hT : 1 ≤ T) (hu : u ∈ Icc T (2*T))
    (ht : t ∉ Icc 0 (3*T)) : T ≤ |t-u| ∧ |t| ≤ 3*|t-u| := by grind

/-- The 128-decay weight leaves a quadratic integrable factor after the
twelfth power of coarse actual-zeta growth and a T^(-114) saving. -/
theorem weightedCriticalTwelfth_tail_pointwise {T u t : ℝ}
    (hT : 1 ≤ T) (hu : u ∈ Icc T (2*T)) (ht : t ∉ Icc 0 (3*T)) :
    momentDecay 128 (t-u)*zetaMomentCriticalNorm t^12 ≤
      (12:ℝ)^12*T^(-114 : ℝ)*momentDecay 2 (t-u) := by
  pm_4493
  have hpow : T^114 ≤ (1+|t-u|)^114 := pow_le_pow_left₀ hTp.le (by linarith) _
  calc
    _ = zetaMomentCriticalNorm t^12/(1+|t-u|)^128 := by unfold momentDecay; ring
    _ ≤ (12*(1+|t-u|))^12/(1+|t-u|)^128 :=
      div_le_div_of_nonneg_right (pow_le_pow_left₀ (zetaMomentCriticalNorm_nonneg _) hz _) (by positivity)
    _ = (12:ℝ)^12 / ((1+|t-u|)^114 * (1+|t-u|)^2) := by
      rw [mul_pow]
      field_simp
    _ ≤ (12:ℝ)^12 / (T^114 * (1+|t-u|)^2) := by
      apply div_le_div_of_nonneg_left (by positivity) (by positivity)
      exact mul_le_mul_of_nonneg_right hpow (by positivity)
    _ = (12:ℝ)^12*T^(-114 : ℝ)*momentDecay 2 (t-u) := by
      rw [Real.rpow_neg hTp.le, show (114:ℝ)=((114:ℕ):ℝ) by norm_num,Real.rpow_natCast]
      unfold momentDecay
      simp only [div_eq_mul_inv,mul_inv_rev]
      ring

theorem integrable_translated_critical_twelfth {A : ℕ} (hA : 14 ≤ A) (u : ℝ) :
    Integrable (fun t : ℝ => momentDecay A (t-u)*zetaMomentCriticalNorm t^12) := by
  have hh := (integrable_weightedCriticalTwelfth A hA u).comp_sub_right u
  simpa only [add_sub_cancel] using hh

/-- The full complementary tail is bounded using genuine integrability. -/
theorem weightedCriticalTwelfth_physical_tail {T u : ℝ} (hT : 1 ≤ T)
    (hu : u ∈ Icc T (2*T)) :
    (∫ t in (Icc 0 (3*T))ᶜ, momentDecay 128 (t-u)*zetaMomentCriticalNorm t^12) ≤
      (12:ℝ)^12*T^(-114 : ℝ)*Real.pi := by
  have hi := integrable_translated_critical_twelfth (by norm_num : 14 ≤ 128) u
  pm_4494
  let C : ℝ := (12:ℝ)^12*T^(-114 : ℝ)
  pm_61 hC C
  pm_4495 weightedCriticalTwelfth_tail_pointwise

end MathCollab.Density.Stronger
