module

public import HypoellipticAleksandrov.KineticAleksandrov.LocalA.BoundedSourceBarrier
public import HypoellipticAleksandrov.KineticAleksandrov.LocalA.BallEvolution
import HypoellipticAleksandrov.KineticAleksandrov.SectionTwo.DuhamelEquation
import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ComparisonNodes
import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ComparisonRadial
import HypoellipticAleksandrov.KineticAleksandrov.LocalA.BoundedSourceTraces
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul

/-! # Uniform quadratic comparison for smooth compact sources

The bound depends on the source supremum, rather than its distance to the boundary.
-/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.SectionTwo
open HypoellipticAleksandrov Parabolic Evolution Set
open scoped Topology
open Matrix
open scoped MatrixOrder

/- The stationary moving-domain convention recovers exactly the given ball. -/
theorem boundedSource_stationary_domain {d } (c : PDE.Vec d) (R t : ℝ) :
    movingDomain (PDE.euclideanBall c R) (fun _ => 0) t = PDE.euclideanBall c R := by
  ext y
  rw [mem_movingDomain_iff]
  simp only [sub_zero]

/- Smooth compact sources bounded by one satisfy the uniform quadratic comparison. -/
end HypoellipticAleksandrov.KineticAleksandrov.SectionTwo
