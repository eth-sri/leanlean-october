module

public import HypoellipticAleksandrov.KineticAleksandrov.MainAssembly
public import HypoellipticAleksandrov.KineticAleksandrov.TheoremA.Final
public import HypoellipticAleksandrov.KineticAleksandrov.Geometry
public import HypoellipticAleksandrov.KineticAleksandrov.Operator
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import HypoellipticAleksandrov.Geometry.KineticPointMeasure
import Batteries.Tactic.Alias



/-!
# Kinetic Aleksandrov estimate for time–velocity coefficients

Companion paper, Theorem 1.1: the Aleksandrov estimate for kinetic operators with
coefficients depending on time and velocity. The Hörmander hypoellipticity theorem is
supplied by the `hormander` package and classical Dirichlet solvability (Lieberman,
Theorem 5.14) is proved in this library, so the statement carries no extra hypotheses.
-/

 public section



namespace HypoellipticAleksandrov

open MeasureTheory Set
open scoped ENNReal MatrixOrder

namespace KineticAleksandrov

/-- Companion paper, Theorem 1.1, with the uniform constant quantified before the data. -/
alias kinetic_aleksandrov_timeVelocity := _root_.HypoellipticAleksandrov.KineticAleksandrov.kinetic_aleksandrov_timeVelocity_proof

end KineticAleksandrov

end HypoellipticAleksandrov
