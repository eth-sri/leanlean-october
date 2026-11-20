module

public import Mathlib.MeasureTheory.Function.AbsolutelyContinuous
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

@[expose] public section

open MeasureTheory Set Filter
open scoped ENNReal Topology

variable {E : Type*} [NormedAddCommGroup E] {f : ℝ → E} {a b : ℝ}

theorem ContDiff.absolutelyContinuousOnInterval [NormedSpace ℝ E] (hf : ContDiff ℝ 1 f) :
    AbsolutelyContinuousOnInterval f a b :=
  hf.contDiffOn.absolutelyContinuousOnInterval

theorem ContinuousOn.memLp_Ioc (hf : ContinuousOn f (Icc a b)) {p : ℝ≥0∞} :
    MemLp f p (volume.restrict (Ioc a b)) := by
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hf
  exact MemLp.of_bound ((hf.mono Ioc_subset_Icc_self).aestronglyMeasurable measurableSet_Ioc)
    C (ae_restrict_of_forall_mem measurableSet_Ioc fun _ hx => hC _ (Ioc_subset_Icc_self hx))

theorem ContinuousOn.mul_memLp_Ioc {c f : ℝ → ℂ} {p : ℝ≥0∞} (hc : ContinuousOn c (Icc a b))
    (hf : MemLp f p (volume.restrict (Ioc a b))) :
    MemLp (fun x => c x * f x) p (volume.restrict (Ioc a b)) := by
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hc
  refine hf.of_le_mul (c := C)
    (((hc.mono Ioc_subset_Icc_self).aestronglyMeasurable measurableSet_Ioc).mul hf.aestronglyMeasurable) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
  simpa using mul_le_mul_of_nonneg_right (hC x (Ioc_subset_Icc_self hx)) (norm_nonneg (f x))

