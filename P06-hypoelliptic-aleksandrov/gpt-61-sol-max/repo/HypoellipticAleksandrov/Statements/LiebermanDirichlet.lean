module

public import HypoellipticAleksandrov.KineticAleksandrov.Lieberman.Assembly
public import HypoellipticAleksandrov.KineticAleksandrov.EllipsoidDirichlet
public import HypoellipticAleksandrov.Parabolic.ScalarDirichletData
import Batteries.Tactic.Alias



/-!
# Classical Dirichlet solvability (Lieberman)

Existence and uniqueness for the terminal Cauchy–Dirichlet problem with smooth data on a
smooth ellipsoidal cylinder (Lieberman, Theorem 5.14).
-/

 public section


set_option autoImplicit false

open Set
open HypoellipticAleksandrov
open HypoellipticAleksandrov.Parabolic
open scoped MatrixOrder

namespace HypoellipticAleksandrov.KineticAleksandrov

/-- The smooth ellipsoidal Dirichlet statement, with
uniqueness on the closed cylinder. -/
alias exists_isClassicalBackwardDirichletSolution_openEllipsoid_uniqueOn_of_lieberman := _root_.HypoellipticAleksandrov.KineticAleksandrov.ellipsoidDirichlet_aux

end HypoellipticAleksandrov.KineticAleksandrov
