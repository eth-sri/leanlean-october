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

variable (ζ φ : ℝ → ℝ) (hζ : ContDiff ℝ (⊤ : ℕ∞) ζ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (q : ℝ × ℝ)
    (hq : 0 < q.1)

include ζ φ q in
/-- A separated angular test, extended by zero to nonpositive position. -/
def bellmanAngularTest : ℝ :=
  if 0 < q.1 then bellmanSeparatedExpression ζ φ q else 0

include hq in
/-- On positive position, the zero extension agrees locally with the separated expression. -/
theorem bellmanAngularTest_eventuallyEq_positive :
    bellmanAngularTest ζ φ =ᶠ[𝓝 q] bellmanSeparatedExpression ζ φ := by
  filter_upwards [(isOpen_lt continuous_const continuous_fst).mem_nhds hq] with z hz
  exact ite_eq_left hz

include hζ hφ hq in
/-- The separated expression is smooth at every point with positive position. -/
theorem bellmanSeparatedExpression_contDiffAt :
    ContDiffAt ℝ (⊤ : ℕ∞) (bellmanSeparatedExpression ζ φ) q := by
  have hr : ContDiffAt ℝ (⊤ : ℕ∞) bellmanTestRadius q :=
    contDiffAt_fst.rpow_const_of_ne hq.ne'
  have hn : bellmanTestRadius q ≠ 0 :=
    (Real.rpow_pos_of_pos hq _).ne'
  have ha : ContDiffAt ℝ (⊤ : ℕ∞) bellmanTestAngle q :=
    contDiffAt_snd.div hr hn
  exact (hζ.contDiffAt.comp q hr).mul (hφ.contDiffAt.comp q ha)

include hζ hφ in
/-- The separated test extended by zero is smooth, including on the position axis. -/
theorem bellmanAngularTest_contDiff
    (hs : tsupport ζ ⊆ Ioi (0 : ℝ)) :
    ContDiff ℝ (⊤ : ℕ∞) (bellmanAngularTest ζ φ) := by
  apply contDiff_iff_contDiffAt.mpr
  intro q
  by_cases hq : 0 < q.1
  · exact ContDiffAt.congr_of_eventuallyEq
      (bellmanSeparatedExpression_contDiffAt ζ φ hζ hφ q hq)
      (bellmanAngularTest_eventuallyEq_positive ζ φ q hq)
  · by_cases hn : q.1 = 0
    · have hz := fun h => (lt_irrefl 0) (hs h)
      have hr : ContinuousAt bellmanTestRadius q :=
        continuousAt_fst.rpow_const (Or.inr (by norm_num))
      have hr0 : bellmanTestRadius q = 0 := by simp [bellmanTestRadius, hn]
      have hec : ∀ᶠ z in 𝓝 q, ζ (bellmanTestRadius z) = 0 := by
        have ht : Tendsto bellmanTestRadius (𝓝 q) (𝓝 0) := hr0 ▸ hr
        exact ht.eventually (notMem_tsupport_iff_eventuallyEq.mp hz)
      apply (contDiffAt_const (c := 0)).congr_of_eventuallyEq
      filter_upwards [hec] with z hz
      simp [bellmanAngularTest, bellmanSeparatedExpression, hz]
    · apply (contDiffAt_const (c := 0)).congr_of_eventuallyEq
      filter_upwards [(isOpen_lt continuous_fst continuous_const).mem_nhds (lt_of_le_of_ne (le_of_not_gt hq) hn)] with z hz
      exact ite_eq_right (not_lt_of_gt hz)

end HypoellipticAleksandrov.KineticAleksandrov
