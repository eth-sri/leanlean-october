module

public import PottsDiscontinuity.RCInfinite.LimitComparison
public import PottsDiscontinuity.RCInfinite.TranslationSupport
public import PottsDiscontinuity.RCInfinite.CylinderApproximation

@[expose] public section

open MeasureTheory Filter Topology Set
open scoped symmDiff

namespace PottsDiscontinuity.RCInfinite
open FK

def covariance (μ : Measure LatticeConfiguration) (A B : Set LatticeConfiguration) : ℝ :=
  μ.real (A ∩ B) - μ.real A * μ.real B

theorem covariance_change_right (μ : Measure LatticeConfiguration) [IsProbabilityMeasure μ]
    {A B C : Set LatticeConfiguration} (hA : MeasurableSet A)
    (hB : MeasurableSet B) (hC : MeasurableSet C) :
    |covariance μ A B - covariance μ A C| ≤ 2 * μ.real (B ∆ C) := by
  have hdiff := abs_measureReal_sub_le_symmDiff μ hB hC
  have hjoint := abs_measureReal_sub_le_symmDiff μ (hA.inter hB) (hA.inter hC)
  have hsub : (A ∩ B) ∆ (A ∩ C) ⊆ B ∆ C := by
    intro x hx
    simp only [mem_symmDiff, mem_inter_iff] at hx ⊢
    tauto
  have hjoint' : |μ.real (A ∩ B) - μ.real (A ∩ C)| ≤ μ.real (B ∆ C) :=
    hjoint.trans (measureReal_mono hsub)
  have hprod : |μ.real A * (μ.real B - μ.real C)| ≤ μ.real (B ∆ C) := by
    rw [abs_mul, abs_of_nonneg measureReal_nonneg]
    have hm := mul_le_mul_of_nonneg_left hdiff (measureReal_nonneg (μ := μ) (s := A))
    nlinarith [mul_nonneg (sub_nonneg.mpr (measureReal_le_one (μ := μ) (s := A)))
      (measureReal_nonneg (μ := μ) (s := B ∆ C))]
  calc
    |covariance μ A B - covariance μ A C| =
        |(μ.real (A ∩ B) - μ.real (A ∩ C)) - μ.real A * (μ.real B - μ.real C)| := by
          unfold covariance
          congr 1
          ring
    _ ≤ |μ.real (A ∩ B) - μ.real (A ∩ C)| + |μ.real A * (μ.real B - μ.real C)| := by
      simpa only [sub_zero, zero_sub, abs_neg] using
        abs_sub_le (μ.real (A ∩ B) - μ.real (A ∩ C)) 0 (μ.real A * (μ.real B - μ.real C))
    _ ≤ μ.real (B ∆ C) + μ.real (B ∆ C) := add_le_add hjoint' hprod
    _ = 2 * μ.real (B ∆ C) := by ring




end PottsDiscontinuity.RCInfinite
