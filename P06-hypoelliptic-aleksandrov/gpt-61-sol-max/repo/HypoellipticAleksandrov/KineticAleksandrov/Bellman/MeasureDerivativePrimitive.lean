module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic

/-! # Actual interval primitives of locally finite weighted real measures -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov
open MeasureTheory Set

variable (μ : Measure ℝ)

/-- The oriented interval primitive of a real measure with a continuous scalar weight. -/
def bellmanMeasurePrimitive  (g : ℝ → ℝ) (a y : ℝ) : ℝ :=
  ∫ z in a..y, g z ∂μ

/-- A continuous weight is integrable on every finite interval of a locally finite real
measure. -/
theorem bellmanMeasureWeight_intervalIntegrable
    [IsFiniteMeasureOnCompacts μ] (g : ℝ → ℝ) (hg : Continuous g) (a b : ℝ) :
    IntervalIntegrable g μ a b := hg.continuousOn.intervalIntegrable

/-- The interval primitive of an arbitrary locally finite measure is measurable, even with
atoms. -/
theorem bellmanMeasurePrimitive_stronglyMeasurable  [SFinite μ]
    (g : ℝ → ℝ) (hg : Measurable g) (a : ℝ) :
    StronglyMeasurable (bellmanMeasurePrimitive μ g a) := by
  let sharedTerm_2c022b6e10 := ((fun w : ℝ × ℝ => g w.2))
  let A : Set (ℝ × ℝ) := {w | a < w.2 ∧ w.2 ≤ w.1}
  let B : Set (ℝ × ℝ) := {w | w.1 < w.2 ∧ w.2 ≤ a}




  have ha := (((hg.comp measurable_snd).indicator (show MeasurableSet A by
      exact (measurableSet_lt measurable_const measurable_snd).inter
        (measurableSet_le measurable_snd measurable_fst))).stronglyMeasurable).integral_prod_right' (ν := μ)
  have hb := (((hg.comp measurable_snd).indicator (show MeasurableSet B by
      exact (measurableSet_lt measurable_fst measurable_snd).inter
        (measurableSet_le measurable_snd measurable_const))).stronglyMeasurable).integral_prod_right' (ν := μ)
  have he : bellmanMeasurePrimitive μ g a =
      (fun y => ∫ z, A.indicator sharedTerm_2c022b6e10 (y, z) ∂μ) -
      (fun y => ∫ z, B.indicator sharedTerm_2c022b6e10 (y, z) ∂μ) := by
    funext y
    unfold bellmanMeasurePrimitive intervalIntegral
    have heA : (fun z => A.indicator sharedTerm_2c022b6e10 (y, z)) =
        (Ioc a y).indicator g := by
      funext z
      rfl
    have heB : (fun z => B.indicator sharedTerm_2c022b6e10 (y, z)) =
        (Ioc y a).indicator g := by
      funext z
      rfl
    simp only [Pi.sub_apply]
    rw [heA, heB, integral_indicator measurableSet_Ioc, integral_indicator measurableSet_Ioc]
  rw [he]
  exact ha.sub hb

/-- Oriented measure primitives have the exact additive interval increment. -/
theorem bellmanMeasurePrimitive_sub  [IsFiniteMeasureOnCompacts μ]
    (g : ℝ → ℝ) (hg : Continuous g) (a b y : ℝ) :
    bellmanMeasurePrimitive μ g a y - bellmanMeasurePrimitive μ g a b =
      ∫ z in b..y, g z ∂μ := by
  have he := intervalIntegral.integral_add_adjacent_intervals
    (bellmanMeasureWeight_intervalIntegrable μ g hg a b)
    (bellmanMeasureWeight_intervalIntegrable μ g hg b y)
  change (∫ z in a..y, g z ∂μ) - (∫ z in a..b, g z ∂μ) = _
  linarith

end HypoellipticAleksandrov.KineticAleksandrov
