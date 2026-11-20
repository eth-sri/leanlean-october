module

public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Setting
public import PDEFoundation.Geometry.EuclideanBall.Topology
import Mathlib.Tactic.Linarith

/-! # Fixed cylinder and genuine interior height points for the Appendix C construction -/

@[expose] public section

namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample

open Set

/-- With a stationary spatial base point, the cylinder is the literal product cylinder. -/
theorem construction_mem_cylinder_iff {d : ℕ} (T S : ℝ) (hS : 0 < S) (P : KineticPoint d) :
    P ∈ backwardCylinder (⟨T, 0, 0⟩) S ↔
      T - S ^ 2 < P.time ∧ P.time < T ∧
      PDE.vecEuclideanNorm P.velocity < S ∧ PDE.vecEuclideanNorm P.position < S ^ 3 := by
  simp [backwardCylinder, relativePosition,
    PDE.mem_euclideanBall_iff_vecEuclideanNorm_lt hS,
    PDE.mem_euclideanBall_iff_vecEuclideanNorm_lt (pow_pos hS 3)]

end HypoellipticAleksandrov.KineticAleksandrov.Counterexample
