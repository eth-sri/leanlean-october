module

public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ExhaustionLimitCollar
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ExhaustionLimitCover
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ExhaustionCollarApproximation
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ExhaustionLimitGeometry
public import Mathlib.Topology.UniformSpace.UniformApproximation

/-!
# Continuous lateral-zero extension of the actual ball exhaustion limit

The limit is extended by zero outside the original diffused interior. Inner
cylinder continuity controls interior points and the proved collar controls the boundary.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov

open HypoellipticAleksandrov HypoellipticAleksandrov.Parabolic Set Filter
open scoped Topology MatrixOrder

/- The actual pointwise exhaustion limit on the original diffused interior,
extended by zero outside that interior. -/
def innerBallDirichletLimit {n } (r0 : ℝ) (Γ : ℝ → PDE.Vec n)
    (g : ℕ → ℝ → PDE.Vec n) (u : ℕ → TimeVelocity (n + n) → ℝ)
    (p : KineticPoint n) : ℝ := by
  classical
  exact if p.position ∈ movingDomain (PDE.euclideanBall 0 r0) Γ p.time then
    limUnder atTop (fun k => straightenedPullback (g k) (u k) p) else 0

/- On the original diffused interior the zero extension is the actual limit. -/
theorem innerBallDirichletLimit_eq_limit {n } (r0 : ℝ) (Γ : ℝ → PDE.Vec n)
    (g : ℕ → ℝ → PDE.Vec n) (u : ℕ → TimeVelocity (n + n) → ℝ)
    {p : KineticPoint n}
    (hp : p.position ∈ movingDomain (PDE.euclideanBall 0 r0) Γ p.time) :
    innerBallDirichletLimit r0 Γ g u p =
      limUnder atTop (fun k => straightenedPullback (g k) (u k) p) := by
  classical
  simp only [innerBallDirichletLimit, ite_eq_left hp]

/- The zero extension inherits the collar estimate on the entire original closed slab. -/
end HypoellipticAleksandrov.KineticAleksandrov
