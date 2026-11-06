module

public import HypoellipticAleksandrov.KineticAleksandrov.MainAssembly
public import HypoellipticAleksandrov.KineticAleksandrov.TheoremA.LocalisedFinal
public import HypoellipticAleksandrov.KineticAleksandrov.Geometry
public import HypoellipticAleksandrov.KineticAleksandrov.Operator
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import HypoellipticAleksandrov.Geometry.KineticPointMeasure
import Batteries.Tactic.Alias



/-!
# Localised kinetic Aleksandrov estimate for time–velocity coefficients

Companion paper, Corollary 1.3 (localised form of Theorem 1.1). The Hörmander
hypoellipticity theorem is supplied by the `hormander` package and classical Dirichlet
solvability (Lieberman, Theorem 5.14) is proved in this library, so the statement carries
no extra hypotheses.
-/

 public section



namespace HypoellipticAleksandrov

open MeasureTheory Set
open scoped ENNReal MatrixOrder

namespace KineticAleksandrov

/-- Companion paper, Corollary 1.3, with the uniform constant quantified before the data. -/
alias kinetic_aleksandrov_timeVelocity_localised := _root_.HypoellipticAleksandrov.KineticAleksandrov.kinetic_aleksandrov_timeVelocity_localised_proof

end KineticAleksandrov

end HypoellipticAleksandrov
