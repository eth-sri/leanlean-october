module

public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.AngularEquationVelocity
import Mathlib.Topology.Algebra.Support
import Mathlib.Tactic

/-! # Smooth extension of a separated test across the position axis -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov
open Set Filter
open scoped Topology

/- A separated angular test, extended by zero to nonpositive position. -/
def bellmanAngularTest (ζ φ : ℝ → ℝ) (q : ℝ × ℝ) : ℝ :=
  if 0 < q.1 then bellmanSeparatedExpression ζ φ q else 0

/- On positive position, the zero extension agrees locally with the separated expression. -/
theorem bellmanAngularTest_eventuallyEq_positive (ζ φ : ℝ → ℝ)
    (q : ℝ × ℝ) (hq : 0 < q.1) :
    bellmanAngularTest ζ φ =ᶠ[𝓝 q] bellmanSeparatedExpression ζ φ := by
  have ho : IsOpen {q : ℝ × ℝ | 0 < q.1} := isOpen_lt continuous_const continuous_fst
  filter_upwards [ho.mem_nhds hq] with z hz
  exact ite_eq_left hz

/- The separated expression is smooth at every point with positive position. -/
end HypoellipticAleksandrov.KineticAleksandrov
