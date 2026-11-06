module

public import HypoellipticAleksandrov.Parabolic.ScalarClassical
public import HypoellipticAleksandrov.Parabolic.LocalClassical
public import PDEFoundation.Geometry.EuclideanBall.Basic
import HypoellipticAleksandrov.Parabolic.HarnackUnitCylinder.Assembly
import Batteries.Tactic.Alias



/-!
# Parabolic Harnack inequality (Krylov–Safonov)

Companion paper, Theorem 3.5.
-/

 public section

namespace HypoellipticAleksandrov.Parabolic

open scoped MatrixOrder

/-- The parabolic Harnack inequality, expressed as a comparison of every pair
of points in the lower and upper cylinders, with a uniform positive constant. -/
alias parabolic_harnack_unit_cylinder := _root_.HypoellipticAleksandrov.Parabolic.parabolic_harnack_unit_cylinder_aux

end HypoellipticAleksandrov.Parabolic
