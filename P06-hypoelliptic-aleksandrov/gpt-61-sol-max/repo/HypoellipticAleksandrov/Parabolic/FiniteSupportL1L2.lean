module

public import HypoellipticAleksandrov.Parabolic.TimeVelocityMultiIndexLocalCalculus
public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
public import HypoellipticAleksandrov.Measure.TimeVelocity


/-!
# Finite-support `L¹`--`L²` conversion

This module records the Cauchy--Schwarz estimate for a real-valued function
supported in one measurable set of finite volume.
-/

 public section

open MeasureTheory
open scoped ENNReal

namespace HypoellipticAleksandrov.Parabolic

/-- A globally `L²` function supported in a measurable finite-volume set is integrable, with
the exact Cauchy--Schwarz bound determined by that support volume. -/
theorem integral_abs_le_sqrt_volume_mul_eLpNorm
    {d : ℕ}
    (K : HypoellipticAleksandrov.Parabolic.Region d)
    (hKmeas : MeasurableSet K)
    (hKfinite : (HypoellipticAleksandrov.Parabolic.timeVelocityVolume d) K < ∞)
    (g : HypoellipticAleksandrov.Parabolic.ScalarField d)
    (hgmem : MemLp g (2 )
      )
    (hgsupp : Function.support g ⊆ K) :
    (∫ x : TimeVelocity d, |g x|
      ∂(HypoellipticAleksandrov.Parabolic.timeVelocityVolume d)) ≤
      Real.sqrt (volume.real K) *
        ENNReal.toReal (eLpNorm g (2 )
          ) := by
  let sharedTerm_7c02f4e150 := ((1 / (2 : ℝ)))
  let μ : Measure (TimeVelocity d) := volume
  have hKind : K.indicator g = g := by
    funext x
    by_cases hx : x ∈ K
    · exact Set.indicator_of_mem hx g
    · rw [Set.indicator_of_notMem hx]
      by_contra hgx

      exact hx (hgsupp (Function.mem_support.mpr (fun h => hgx h.symm)))

  have hgKmem  :=
    hgmem.indicator hKmeas



  have hcs := integral_mul_norm_le_Lp_mul_Lq
    (p := (2 )) (q := (2 ))
    (Real.holderConjugate_iff.mpr ⟨by norm_num, by norm_num⟩)
    (by
        norm_num
        exact hgKmem) (by
        norm_num
        exact (show MemLp (K.indicator fun _  => (1 : ℝ))
      (2 ) μ from memLp_indicator_const 2 hKmeas 1 (Or.inr hKfinite.ne)))
  have hgNorm :
      (∫ x, ‖K.indicator g x‖ ^ (2 : ℝ) ∂μ) ^ sharedTerm_7c02f4e150 =
        ENNReal.toReal (eLpNorm g (2 ) μ) := by
    rw [hKind]
    change
      (∫ x, ‖g x‖ ^ (2 : ℝ) ∂(HypoellipticAleksandrov.Parabolic.timeVelocityVolume d)) ^ sharedTerm_7c02f4e150 =
        ENNReal.toReal (eLpNorm g (2 )
          )
    have he := hgmem.eLpNorm_eq_integral_rpow_norm
      (by norm_num : (2 : ℝ≥0∞) ≠ 0) (by norm_num : (2 : ℝ≥0∞) ≠ ∞)
    rw [he, ENNReal.toReal_ofReal]
    · norm_num
    · positivity
  have honeNorm :
      (∫ x, ‖K.indicator (fun _  => (1 : ℝ)) x‖ ^ (2 : ℝ) ∂μ) ^
          sharedTerm_7c02f4e150 = Real.sqrt (μ.real K) := by
    have honeIntegral :
        (∫ x, ‖K.indicator (fun _  => (1 : ℝ)) x‖ ^ (2 : ℝ) ∂μ) =
          μ.real K := by
      calc
        (∫ x, ‖K.indicator (fun _  => (1 : ℝ)) x‖ ^ (2 : ℝ) ∂μ) =
            ∫ x, K.indicator (fun _  => (1 : ℝ)) x ∂μ := by
              apply integral_congr_ae
              filter_upwards [] with x
              by_cases hx : x ∈ K <;> simp [hx]
        _ = μ.real K := integral_indicator_one hKmeas
    rw [honeIntegral, Real.sqrt_eq_rpow]
  calc
    (∫ x : TimeVelocity d, |g x| ∂(HypoellipticAleksandrov.Parabolic.timeVelocityVolume d)) =
        ∫ x, ‖K.indicator g x‖ *
          ‖K.indicator (fun _  => (1 : ℝ)) x‖ ∂μ := by
            apply integral_congr_ae
            filter_upwards [] with x
            by_cases hx : x ∈ K
            · simp [hx, Real.norm_eq_abs]
            · have hgx : g x = 0 := by
                by_contra hne

                exact hx (hgsupp (Function.mem_support.mpr hne))
              simp [hx, hgx]
    _ ≤ (∫ x, ‖K.indicator g x‖ ^ (2 : ℝ) ∂μ) ^ sharedTerm_7c02f4e150 *
          (∫ x, ‖K.indicator (fun _  => (1 : ℝ)) x‖ ^ (2 : ℝ) ∂μ) ^
            sharedTerm_7c02f4e150 := hcs
    _ = Real.sqrt (μ.real K) * ENNReal.toReal (eLpNorm g (2 ) μ) := by
      rw [hgNorm, honeNorm, mul_comm]

end HypoellipticAleksandrov.Parabolic
