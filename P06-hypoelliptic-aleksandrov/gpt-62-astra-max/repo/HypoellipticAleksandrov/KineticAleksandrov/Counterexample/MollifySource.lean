module

public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.MollifyApproximateIdentity
import Mathlib.Tactic.Linarith

/-!
# Positivity and order for the normalized spatial mollifier

These are scalar convolution facts, to be applied after the operator identity is proved.
-/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample
open MeasureTheory ContinuousLinearMap
open scoped Convolution
variable {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
  [MeasureSpace G] [BorelSpace G] [FiniteDimensional ℝ G]
  [Measure.IsAddHaarMeasure (volume : Measure G)]

/-- The scalar positive-part estimate used to absorb an operator commutator. -/
theorem positive_part_add_le (a f e : ℝ) (hf : 0 ≤ f) (haf : a ≤ f) :
    max (a + e) 0 ≤ f + |e| := by
  bound

end HypoellipticAleksandrov.KineticAleksandrov.Counterexample
