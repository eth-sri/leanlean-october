module

public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.AngularEquationVelocity
import Mathlib.Topology.Algebra.Support
import Mathlib.Tactic
public import PDEFoundation.Calculus.RegularityOrder


/-! # Smooth extension of a separated test across the position axis -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov
open Set Filter
open scoped Topology

variable (ζ φ : ℝ → ℝ)

variable (q : ℝ × ℝ)

/-- A separated angular test, extended by zero to nonpositive position. -/
def bellmanAngularTest   : ℝ :=
  if 0 < q.1 then bellmanSeparatedExpression ζ φ q else 0

/-- On positive position, the zero extension agrees locally with the separated expression. -/
theorem bellmanAngularTest_eventuallyEq_positive
     (hq : 0 < q.1) :
    bellmanAngularTest ζ φ =ᶠ[𝓝 q] bellmanSeparatedExpression ζ φ := (mp_mem (IsOpen.mem_nhds (isOpen_lt continuous_const continuous_fst) hq) (univ_mem' (id fun z hz => ite_eq_left hz)))

variable (hζ : ContDiff ℝ PDE.smoothOrder ζ) (hφ : ContDiff ℝ PDE.smoothOrder φ)

include hζ hφ
/-- The separated expression is smooth at every point with positive position. -/
theorem bellmanSeparatedExpression_contDiffAt

    (q : ℝ × ℝ) (hq : 0 < q.1) :
    ContDiffAt ℝ PDE.smoothOrder (bellmanSeparatedExpression ζ φ) q := (ContDiffAt.mul (ContDiffAt.comp q (ContDiff.contDiffAt hζ) (ContDiffAt.rpow_const_of_ne contDiffAt_fst (LT.lt.ne' hq)))
  (ContDiffAt.comp q (ContDiff.contDiffAt hφ)
    (ContDiffAt.div contDiffAt_snd (ContDiffAt.rpow_const_of_ne contDiffAt_fst (LT.lt.ne' hq))
      (LT.lt.ne' (Real.rpow_pos_of_pos hq 3⁻¹)))))

/-- The separated test extended by zero is smooth, including on the position axis. -/
theorem bellmanAngularTest_contDiff

    (hs : tsupport ζ ⊆ Ioi (0 )) :
    ContDiff ℝ PDE.smoothOrder (bellmanAngularTest ζ φ) := by
  apply contDiff_iff_contDiffAt.mpr
  intro q
  by_cases hq : 0 < q.1
  · exact ContDiffAt.congr_of_eventuallyEq
      (bellmanSeparatedExpression_contDiffAt ζ φ hζ hφ q hq)
      (bellmanAngularTest_eventuallyEq_positive ζ φ q hq)
  · by_cases hn : q.1 = 0
    · have hz  := fun h => (lt_irrefl 0) (hs h)
      have he := notMem_tsupport_iff_eventuallyEq.mp hz
      have hr : ContinuousAt bellmanTestRadius q :=
        continuousAt_fst.rpow_const (Or.inr (by norm_num : 0 ≤ (3 : ℝ)⁻¹))
      have hr0 : bellmanTestRadius q = 0 := by simp [bellmanTestRadius, hn]
      have hec : ∀ᶠ z in 𝓝 q, ζ (bellmanTestRadius z) = 0 := by
        have ht : Tendsto bellmanTestRadius (𝓝 q) (𝓝 0) := hr0 ▸ hr
        exact ht.eventually he
      apply (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
      filter_upwards [hec] with z hz
      simp only [bellmanAngularTest, bellmanSeparatedExpression, hz, zero_mul, ite_self]
    · have hneg  := lt_of_le_of_ne (le_of_not_gt hq) hn
      have ho : IsOpen {q : ℝ × ℝ | q.1 < 0} := isOpen_lt continuous_fst continuous_const
      apply (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
      filter_upwards [ho.mem_nhds hneg] with z hz
      exact ite_eq_right (not_lt_of_gt hz)

end HypoellipticAleksandrov.KineticAleksandrov
