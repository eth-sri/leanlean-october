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

section
variable (μ : Measure ℝ)
include μ

/-- The oriented interval primitive of a real measure with a continuous scalar weight. -/
def bellmanMeasurePrimitive (g : ℝ → ℝ) (a y : ℝ) : ℝ :=
  ∫ z in a..y, g z ∂μ

/-- The interval primitive of an arbitrary locally finite measure is measurable, even with
atoms. -/
theorem bellmanMeasurePrimitive_stronglyMeasurable [SFinite μ]
    (g : ℝ → ℝ) (hg : Measurable g) (a : ℝ) :
    StronglyMeasurable (bellmanMeasurePrimitive μ g a) := by
  let A : Set (ℝ × ℝ) := {w | a < w.2 ∧ w.2 ≤ w.1}
  let B : Set (ℝ × ℝ) := {w | w.1 < w.2 ∧ w.2 ≤ a}
  have hA : MeasurableSet A := by
    exact (measurableSet_lt measurable_const measurable_snd).inter
      (measurableSet_le measurable_snd measurable_fst)
  have hB : MeasurableSet B := by
    exact (measurableSet_lt measurable_fst measurable_snd).inter
      (measurableSet_le measurable_snd measurable_const)
  have hfa : StronglyMeasurable (A.indicator (fun w : ℝ × ℝ => g w.2)) :=
    ((hg.comp measurable_snd).indicator hA).stronglyMeasurable
  have hfb : StronglyMeasurable (B.indicator (fun w : ℝ × ℝ => g w.2)) :=
    ((hg.comp measurable_snd).indicator hB).stronglyMeasurable
  have ha := hfa.integral_prod_right' (ν := μ)
  have hb := hfb.integral_prod_right' (ν := μ)
  have he : bellmanMeasurePrimitive μ g a =
      (fun y => ∫ z, A.indicator (fun w : ℝ × ℝ => g w.2) (y, z) ∂μ) -
      (fun y => ∫ z, B.indicator (fun w : ℝ × ℝ => g w.2) (y, z) ∂μ) := by
    funext y
    unfold bellmanMeasurePrimitive intervalIntegral
    have heA : (fun z => A.indicator (fun w : ℝ × ℝ => g w.2) (y, z)) =
        (Ioc a y).indicator g := by
      funext z
      rfl
    have heB : (fun z => B.indicator (fun w : ℝ × ℝ => g w.2) (y, z)) =
        (Ioc y a).indicator g := by
      funext z
      rfl
    simp only [Pi.sub_apply]
    rw [heA, heB, integral_indicator measurableSet_Ioc, integral_indicator measurableSet_Ioc]
  rw [he]
  exact ha.sub hb

end

end HypoellipticAleksandrov.KineticAleksandrov
