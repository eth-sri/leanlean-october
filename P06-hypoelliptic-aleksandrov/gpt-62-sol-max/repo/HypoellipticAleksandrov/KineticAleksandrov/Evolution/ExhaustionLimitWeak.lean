module

public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ExhaustionLimitUniform
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ExhaustionLimitAdjoint
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.TruncationWeak
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ExhaustionLimitGeometry
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ExhaustionLimitMeasure
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# The weak equation on strict bounded inner cylinders

The actual limit is continuous, hence locally integrable. Its compact-test
identity is the proved limit of the finite Dirichlet weak equations.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov

open HypoellipticAleksandrov HypoellipticAleksandrov.Parabolic Set Filter MeasureTheory
open Evolution
open scoped Topology MatrixOrder

/-- The actual Dirichlet exhaustion limit solves the regularized kinetic equation
weakly on every strict bounded inner cylinder. -/
theorem weakRegularized_innerBall_dirichlet_limit
    {n : ℕ} (E : InnerBallExhaustion n)
    {δ0 S0 : ℝ} (hδ0 : 0 < δ0) (hδr : δ0 < E.r0) :
    IsKineticWeakRegularizedSolution E.B E.b E.ε
      (E.innerOpen δ0 S0)
      (fun p => E.pointLimit p)
      (fun _ => 0) := by
  let U := (E.innerOpen δ0 S0)
  have hU : IsOpen U := isOpen_boundedInnerOpenCylinder _ E.hΓ _ _ _
  have ht := tendstoUniformlyOn_innerBall_dirichlet (S0 := S0) E hδ0 hδr
  refine weakRegularized_of_tendstoUniformlyOn E.hBs E.hbs hU
    (boundedInnerOpenCylinder_subset_closed _ E.Γ E.α E.τ S0)
    (isCompact_movingClosedSlab_inter E.hΓ E.α E.τ S0) ht
    (eventually_continuousOn_abs_le_innerBall E hδ0 hδr) ?_
  filter_upwards [eventually_innerCylinder_mem_straightenedEllipsoid (S := S0)
    hδ0 hδr E.β E.R E.tendsto_gap E.tendsto_radius E.g E.close] with k hk
  refine ⟨_, ?_, weakRegularized_of_straightened_dirichlet E.hBs E.hbs
    (E.smooth k) (E.solution k).2.1 (E.solution k).2.2.1⟩
  intro p hp
  exact ⟨E.haα.trans hp.1, hp.2.1, hk.2.2 _ (boundedInnerOpenCylinder_subset_closed _ E.Γ E.α E.τ S0 hp)⟩

end HypoellipticAleksandrov.KineticAleksandrov
