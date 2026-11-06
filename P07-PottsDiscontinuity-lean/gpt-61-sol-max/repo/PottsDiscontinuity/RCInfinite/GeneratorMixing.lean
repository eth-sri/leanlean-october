module
public import Mathlib

public import PottsDiscontinuity.RCInfinite.LimitComparison
public import PottsDiscontinuity.RCInfinite.TranslationSupport
public import PottsDiscontinuity.RCInfinite.CylinderApproximation

@[expose] public section

open MeasureTheory Filter Topology Set
open scoped symmDiff

namespace PottsDiscontinuity.RCInfinite
open FK

def covariance (μ : Measure LatticeConfiguration) (A B : Set LatticeConfiguration)  :=
  μ.real (A ∩ B) - μ.real A * μ.real B

theorem covariance_change_right (μ : Measure LatticeConfiguration) [IsProbabilityMeasure μ]
    {A B C : Set LatticeConfiguration} (hA : MeasurableSet A)
    (hB : MeasurableSet B) (hC : MeasurableSet C) :
    |covariance μ A B - covariance μ A C| ≤ 2 * μ.real (B ∆ C) := by
  
  
  have hsub : (A ∩ B) ∆ (A ∩ C) ⊆ B ∆ C := by
    grind
  have hjoint'  :=
    (abs_measureReal_sub_le_symmDiff μ (hA.inter hB) (hA.inter hC)).trans (measureReal_mono hsub)
  
  calc
    |covariance μ A B - covariance μ A C| =
        |(μ.real (A ∩ B) - μ.real (A ∩ C)) - μ.real A * (μ.real B - μ.real C)| := by
          grind +locals
    _ ≤ |μ.real (A ∩ B) - μ.real (A ∩ C)| + |μ.real A * (μ.real B - μ.real C)| := by
      grind
    _ ≤ μ.real (B ∆ C) + μ.real (B ∆ C) := add_le_add hjoint' (by
                                                                 rw [abs_mul, abs_of_nonneg measureReal_nonneg]
                                                                 have hm := mul_le_mul_of_nonneg_left (abs_measureReal_sub_le_symmDiff μ hB hC) (measureReal_nonneg (μ := μ) (s := A))
                                                                 nlinarith [mul_nonneg (sub_nonneg.mpr (measureReal_le_one (μ := μ) (s := A)))
                                                                   (measureReal_nonneg (μ := μ) (s := B ∆ C))])
    _ = 2 * μ.real (B ∆ C) := by ring

section

variable (θ : Parameters) (i : Fin 2) (μ : Measure LatticeConfiguration) (hμ : IsRCInfiniteVolumeLimit θ.toP θ.toQ i μ) (F : Finset Edge) {B : Set LatticeConfiguration}
include hμ F B

theorem allOpen_cylinder_covariance_tendsto_zero  (hB : IsCylinder B) :
    Tendsto (fun n : ℕ => covariance μ (LatticeConfiguration.allOpen F)
      ( edgeTranslate ((n : ℤ), 0)  ⁻¹' B)) atTop (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have herror : Tendsto (fun m =>
      |(boxMeasure θ i (0, 0) m : Measure LatticeConfiguration).real
        (LatticeConfiguration.allOpen F) - μ.real (LatticeConfiguration.allOpen F)|)
      atTop (𝓝 0) := by
    simpa only [sub_self, abs_zero] using
      ((tendsto_cylinder_probability θ i μ hμ (isCylinder_allOpen F)).sub
        (tendsto_const_nhds (x := μ.real (LatticeConfiguration.allOpen F)))).abs
  
  obtain ⟨m, hFm, hm⟩ := ((eventually_finset_in_box F).and (herror.eventually (gt_mem_nhds hε))).exists
  filter_upwards [eventually_cylinder_translate_outside m hB] with n hn
  
  simpa only [Real.dist_eq, sub_zero, covariance] using (cylinder_exterior_covariance_bound θ i μ hμ m F hFm
                                                           ( edgeTranslate (n, 0)  ⁻¹' B) (hB.preimage_translate _) hn).trans_lt hm

/-- Mixing of every all-open generator against any measurable event, along
horizontal translations. This already suffices for full translation ergodicity. -/
theorem allOpen_measurable_covariance_tendsto_zero  (hB : MeasurableSet B) :
    Tendsto (fun n : ℕ => covariance μ (LatticeConfiguration.allOpen F)
      ( edgeTranslate ((n : ℤ), 0)  ⁻¹' B)) atTop (𝓝 0) := by
  have : IsProbabilityMeasure μ := hμ.1
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨C, hC, hCB⟩ := exists_cylinder_approx μ hB (show 0 < ε / 4 by positivity)
  
  
  filter_upwards [ (Metric.tendsto_nhds.mp (allOpen_cylinder_covariance_tendsto_zero θ i μ hμ F hC)) (ε / 2) (half_pos hε) ] with n hn
  let a : LatticeVertex := (n, 0)
  have hchange := covariance_change_right μ (isCylinder_allOpen F).measurableSet
    ((edgeTranslate_measurable a) hB) ((edgeTranslate_measurable a) hC.measurableSet)
  have hmass : μ.real (( edgeTranslate a  ⁻¹' B) ∆ ( edgeTranslate a  ⁻¹' C)) =
      μ.real (C ∆ B) := by
    rw [← Set.preimage_symmDiff, limit_translate_real θ i μ hμ a (hB.symmDiff hC.measurableSet),
      symmDiff_comm]
  
  
  simp only [Real.dist_eq] at hn ⊢
  grind

theorem allOpen_measurable_joint_tendsto  (hB : MeasurableSet B) :
    Tendsto (fun n : ℕ => μ.real (LatticeConfiguration.allOpen F ∩
       edgeTranslate ((n : ℤ), 0)  ⁻¹' B)) atTop
      (𝓝 (μ.real (LatticeConfiguration.allOpen F) * μ.real B)) := by
  
  have hmean (n : ℕ) := limit_translate_real θ i μ hμ (n, 0) hB
  simpa only [covariance, hmean, sub_add_cancel, zero_add] using  (allOpen_measurable_covariance_tendsto_zero θ i μ hμ F hB).add
                                                                    (tendsto_const_nhds (x := μ.real (LatticeConfiguration.allOpen F) * μ.real B)) 

end

end PottsDiscontinuity.RCInfinite
