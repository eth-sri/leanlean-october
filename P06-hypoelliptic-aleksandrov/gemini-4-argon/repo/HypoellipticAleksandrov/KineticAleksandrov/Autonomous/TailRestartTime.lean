module

public import HypoellipticAleksandrov.KineticAleksandrov.SectionTwo.Elapsed
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.Tactic

/-! # Exact translation of the positive elapsed-time measure -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory SectionTwo
open scoped ENNReal

/- Shift a positive elapsed time by a nonnegative restart delay. -/
def tailElapsedShift (t : ℝ) (ht : 0 ≤ t) (tau : ElapsedTime ⊤) : ElapsedTime ⊤ :=
  ⟨t + tau.1, add_pos_of_nonneg_of_pos ht tau.2.1, ENNReal.ofReal_lt_top⟩

/- The restart translation is Borel. -/
theorem measurable_tailElapsedShift (t : ℝ) (ht : 0 ≤ t) :
    Measurable (tailElapsedShift t ht) :=
  (measurable_const.add measurable_subtype_coe).subtype_mk

/- Translation gives precisely the strict later-time restriction of elapsed Lebesgue measure. -/
end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
