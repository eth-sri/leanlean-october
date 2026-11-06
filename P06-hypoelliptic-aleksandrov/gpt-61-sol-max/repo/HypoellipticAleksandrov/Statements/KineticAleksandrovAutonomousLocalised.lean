module

public import HypoellipticAleksandrov.KineticAleksandrov.MainAssembly
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.FinalAutonomous
public import HypoellipticAleksandrov.KineticAleksandrov.Geometry
public import HypoellipticAleksandrov.KineticAleksandrov.Operator
public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.Exponent
public import HypoellipticAleksandrov.Geometry.KineticPointMeasure
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Batteries.Tactic.Alias



/-!
# Localised kinetic Aleksandrov estimate for autonomous coefficients

Companion paper, Corollary 1.3 (localised form of Theorem 1.2). The Hörmander
hypoellipticity theorem is supplied by the `hormander` package and classical Dirichlet
solvability (Lieberman, Theorem 5.14) is proved in this library, so the statement carries
no extra hypotheses.
-/

 public section

namespace HypoellipticAleksandrov.KineticAleksandrov
open HypoellipticAleksandrov MeasureTheory Set
open scoped ENNReal

/-- Localized autonomous scalar Aleksandrov estimate (companion paper, Corollary 1.3). -/
alias kinetic_aleksandrov_autonomous_localised := _root_.HypoellipticAleksandrov.KineticAleksandrov.kinetic_aleksandrov_autonomous_localised_proof

end HypoellipticAleksandrov.KineticAleksandrov
