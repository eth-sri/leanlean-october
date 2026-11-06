module

public import HypoellipticAleksandrov.Parabolic.TimeVelocityMultiIndexLocalCalculus
public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-!
# Finite-support `L¹`--`L²` conversion

This module records the Cauchy--Schwarz estimate for a real-valued function
supported in one measurable set of finite volume.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace HypoellipticAleksandrov.Parabolic

/-- A globally `L²` function supported in a measurable finite-volume set is integrable, with
the exact Cauchy--Schwarz bound determined by that support volume. -/
theorem integral_abs_le_sqrt_volume_mul_eLpNorm
    {d : ℕ}
    (K : Set (TimeVelocity d))
    (hKmeas : MeasurableSet K)
    (hKfinite : (volume : Measure (TimeVelocity d)) K < ∞)
    (g : TimeVelocity d → ℝ)
    (hgmem : MemLp g (2 : ℝ≥0∞)
      (volume : Measure (TimeVelocity d)))
    (hgsupp : Function.support g ⊆ K) :
    (∫ x : TimeVelocity d, |g x|
      ∂(volume : Measure (TimeVelocity d))) ≤
      Real.sqrt (volume.real K) *
        ENNReal.toReal (eLpNorm g (2 : ℝ≥0∞)
          (volume : Measure (TimeVelocity d))) := by
  let μ : Measure (TimeVelocity d) := volume
  have hKind : K.indicator g = g := by
    simp_all
  have hgKmem : MemLp (K.indicator g) _ μ :=
    hgmem.indicator hKmeas
  have honeKmem : MemLp (K.indicator fun _ : TimeVelocity d => (1 : ℝ))
      _ μ :=
    memLp_indicator_const 2 hKmeas 1 (Or.inr hKfinite.ne)
  have hgKmem' : MemLp (K.indicator g) (ENNReal.ofReal (2)) μ := by
    simp_all
  have honeKmem' : MemLp (K.indicator fun _ : TimeVelocity d => (1 : ℝ))
      (ENNReal.ofReal (2)) μ := by
    simp_all
  have hcs := integral_mul_norm_le_Lp_mul_Lq
    (p := (2)) (q := (2))
    (Real.holderConjugate_iff.mpr ⟨by norm_num, by norm_num⟩)
    hgKmem' honeKmem'
  have hgNorm :
      (∫ x, ‖K.indicator g x‖ ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ)) =
        ENNReal.toReal (eLpNorm g (2) μ) := by
    rw [hKind]
    change
      (∫ x, ‖g x‖ ^ (2) ∂volume) ^ (1 / (2)) =
        ENNReal.toReal (eLpNorm g _
          volume)
    have he := hgmem.eLpNorm_eq_integral_rpow_norm
      (by norm_num) (by norm_num)
    rw [he, ENNReal.toReal_ofReal]
    · norm_num
    positivity
  have honeNorm :
      (∫ x, ‖K.indicator (fun _ : TimeVelocity d => (1 : ℝ)) x‖ ^ (2 : ℝ) ∂μ) ^
          (1 / (2 : ℝ)) = Real.sqrt (μ.real K) := by
    have honeIntegral :
        (∫ x, ‖K.indicator (fun _ : TimeVelocity d => (1 : ℝ)) x‖ ^ (2 : ℝ) ∂μ) =
          μ.real K := by
      calc
        (∫ x, ‖K.indicator _ x‖ ^ (2 : ℝ) ∂μ) =
            ∫ x, K.indicator _ x ∂μ := by
              apply integral_congr_ae
              filter_upwards [] with x
              by_cases hx : x ∈ K <;> simp [hx]
        _ = μ.real K := integral_indicator_one hKmeas
    rw [honeIntegral, Real.sqrt_eq_rpow]
  calc
    (∫ x : TimeVelocity d, |g x| ∂volume) =
        ∫ x, ‖K.indicator g x‖ *
          ‖K.indicator _ x‖ ∂μ := by
            apply integral_congr_ae
            filter_upwards [] with x
            by_cases hx : x ∈ K
            · simp [hx]
            · have hgx : g x = 0 := by
                by_contra hne
                simp_all
              aesop
    _ ≤ (∫ x, ‖K.indicator g x‖ ^ (2) ∂μ) ^ (1 / (2)) *
          (∫ x, ‖K.indicator _ x‖ ^ (2) ∂μ) ^
            (1 / (2)) := hcs
    _ = Real.sqrt _ * ENNReal.toReal _ := by
      grind

end HypoellipticAleksandrov.Parabolic
