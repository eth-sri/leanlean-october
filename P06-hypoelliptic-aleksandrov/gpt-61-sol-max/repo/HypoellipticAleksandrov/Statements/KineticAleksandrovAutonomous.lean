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
# Kinetic Aleksandrov estimate for autonomous coefficients (d = 1)

Companion paper, Theorem 1.2: the Aleksandrov estimate for autonomous coefficients above
the exponent threshold. The Hörmander hypoellipticity theorem is supplied by the `hormander`
package and classical Dirichlet solvability (Lieberman, Theorem 5.14) is proved in this
library, so the statement carries no extra hypotheses.
-/

 public section

namespace HypoellipticAleksandrov.KineticAleksandrov
open HypoellipticAleksandrov MeasureTheory Set
open scoped ENNReal

/-- Companion paper, Theorem 1.2: the autonomous scalar Aleksandrov estimate above the threshold
`p_* = 1 + beta_*(Lam / lam)`. -/
alias kinetic_aleksandrov_autonomous := _root_.HypoellipticAleksandrov.KineticAleksandrov.kinetic_aleksandrov_autonomous_proof

end HypoellipticAleksandrov.KineticAleksandrov
