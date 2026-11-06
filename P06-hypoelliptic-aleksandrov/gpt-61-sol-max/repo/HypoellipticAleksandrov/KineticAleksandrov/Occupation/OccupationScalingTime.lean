module

public import HypoellipticAleksandrov.KineticAleksandrov.SectionTwo.Elapsed
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-! # Elapsed-time dilation for the occupation characterization -/

 public section

namespace HypoellipticAleksandrov.KineticAleksandrov.Occupation
open MeasureTheory Set


variable {T : ℝ} (hT : 0 < T)

include hT
/-- Multiplication by T maps unit-interval volume to inverse-T times slab volume. -/
theorem occupation_map_timeVolume  :
    Measure.map (fun t  => T * t) (volume.restrict (Ioo 0 1)) =
      ENNReal.ofReal T⁻¹ • volume.restrict (Ioo 0 T) := by
  have he : MeasurableEmbedding (fun t  => T * t) :=
    (Homeomorph.mulLeft₀ T hT.ne').measurableEmbedding
  have hp : (fun t  => T * t) ⁻¹' Ioo 0 T = Ioo 0 1 := by
    ext t
    simp only [mem_preimage, mem_Ioo]
    constructor
    · simp_all
    · simp_all
  calc
    _ = (Measure.map (fun t  => T * t) volume).restrict (Ioo 0 T) := by
      have hh := (he.restrict_map volume (Ioo 0 T)).symm
      simpa only [hp] using hh
    _ = _ := by
      rw [Real.map_volume_mul_left hT.ne', abs_of_pos (inv_pos.mpr hT),
        Measure.restrict_smul]

/-- Ordinary interval integrals under positive elapsed-time dilation. -/
theorem occupation_integral_time_dilation  (f : ℝ → ℝ) :
    ∫ t in Ioo 0 1, f (T * t) = T⁻¹ * ∫ t in Ioo 0 T, f t := by
  have he : MeasurableEmbedding (fun t  => T * t) :=
    (Homeomorph.mulLeft₀ T hT.ne').measurableEmbedding
  rw [← he.integral_map, occupation_map_timeVolume hT, integral_smul_measure,
    ENNReal.toReal_ofReal (inv_pos.mpr hT).le, smul_eq_mul]

end HypoellipticAleksandrov.KineticAleksandrov.Occupation
