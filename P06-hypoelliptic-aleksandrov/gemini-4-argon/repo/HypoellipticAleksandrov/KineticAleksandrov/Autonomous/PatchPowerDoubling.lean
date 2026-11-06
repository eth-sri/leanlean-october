module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.SmoothAutonomousP6Statement
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.FullCoefficientAdapters
public import HypoellipticAleksandrov.KineticAleksandrov.Holder.Growth.MacroscopicPropagationPhysical
import HypoellipticAleksandrov.KineticAleksandrov.Holder.OscillationContractionGeometry
import Mathlib.Tactic

/-! # One radius doubling in the return-time propagation argument

The macroscopic propagation theorem supplies a uniform loss at each doubling.
-/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open HypoellipticAleksandrov Parabolic Set MeasureTheory Holder Holder.Growth

/- The homogeneous solutions used for propagation live on the full positive-time slab. -/
def IsNonnegativeHomogeneousSolution {lam Lam } (A : SmoothAutonomous lam Lam)
    (u : Point → ℝ) : Prop :=
  (∃ M : ℝ, ∀ p, 0 < p.time → |u p| ≤ M) ∧
    (∀ p, 0 < p.time → 0 ≤ u p) ∧
    IsKineticC112On u {p | 0 < p.time} ∧
    (∀ p, 0 < p.time → autonomousScalarOperator A.a u p = 0)

/- The later cylinder follows the same transport centre and doubles the radius. -/
def returnDoubleCenter (z : Point) (ell : ℝ) : Point :=
  ⟨z.time + 8 * ell ^ 2, z.position + (8 * ell ^ 2) • z.velocity, z.velocity⟩

/- Smooth autonomous scalar coefficients satisfy the full ellipticity predicate. -/
theorem autonomous_fullElliptic {lam Lam } (A : SmoothAutonomous lam Lam) :
    FullElliptic lam Lam (autonomousCoefficient A.a) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · have hc : Continuous (fullKineticCoefficientAt (autonomousCoefficient A.a)) := by
      apply continuous_pi
      intro i
      apply continuous_pi
      intro j
      exact A.smooth.continuous.comp
        ((continuous_apply 0 |>.comp continuous_position).prodMk
          (continuous_apply 0 |>.comp continuous_velocity))
    exact hc.measurable
  · intro p
    exact autonomousCoefficient_symmetric A.a p.time p.position p.velocity
  · exact Filter.Eventually.of_forall fun p =>
      (autonomousCoefficient_bounds A p.time p.position p.velocity).1
  · exact Filter.Eventually.of_forall fun p =>
      (autonomousCoefficient_bounds A p.time p.position p.velocity).2

/- The p-six hypothesis supplies admissibility on the positive-time slab. -/
theorem return_solution_admissible {lam Lam }
    (hp6 : SmoothAutonomousP6Statement lam Lam) :
    ∃ C_A : ℝ, 0 < C_A ∧ ∀ (A : SmoothAutonomous lam Lam) (u : Point → ℝ),
      IsNonnegativeHomogeneousSolution A u →
      IsAdmissibleSolution (autonomousCoefficient A.a) {p | 0 < p.time} 6 C_A u := by
  obtain ⟨C_A, hC, h⟩ := hp6
  refine ⟨C_A, hC, ?_⟩
  intro A u hu
  exact h A _ (isOpen_lt continuous_const continuous_time) u hu.2.2.1
    (ae_restrict_of_forall_mem (measurableSet_lt measurable_const continuous_time.measurable)
      (fun p hp => hu.2.2.2 p hp))

/- Each sufficiently small doubling loses the same factor, uniformly over its radius. -/
end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
