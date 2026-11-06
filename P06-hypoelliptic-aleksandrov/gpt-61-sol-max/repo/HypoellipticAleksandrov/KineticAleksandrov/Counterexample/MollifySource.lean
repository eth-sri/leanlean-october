module

public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.MollifyApproximateIdentity
import Mathlib.Tactic.Linarith
import Lean.Elab.Tactic.Grind



/-!
# Positivity and order for the normalized spatial mollifier

These are scalar convolution facts, to be applied after the operator identity is proved.
-/

 public section

namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample
open MeasureTheory
open scoped Convolution
variable {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
  [MeasureSpace G] [BorelSpace G] [FiniteDimensional ℝ G]
  [Measure.IsAddHaarMeasure (volume : Measure G)]

omit [BorelSpace G] [Measure.IsAddHaarMeasure (volume : Measure G)] in
/-- Nonnegative spatial data remain nonnegative after normalized convolution. -/
theorem spatialMollify_nonneg (phi : ContDiffBump (0 : G)) (f : G → ℝ)
    (hf : ∀ y, 0 ≤ f y) (q : G) : 0 ≤ spatialMollify phi f q := by
  unfold spatialMollify
  apply integral_nonneg
  intro y
  exact mul_nonneg (phi.nonneg_normed y) (hf (q - y))

/-- The scalar positive-part estimate used to absorb an operator commutator. -/
theorem positive_part_add_le (a f e : ℝ) (hf : 0 ≤ f) (haf : a ≤ f) :
    max (a + e) 0 ≤ f + |e| := by
  grind

end HypoellipticAleksandrov.KineticAleksandrov.Counterexample
