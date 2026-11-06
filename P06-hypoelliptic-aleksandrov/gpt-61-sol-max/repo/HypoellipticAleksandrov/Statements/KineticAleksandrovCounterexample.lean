module

public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Construction
public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Setting
public import HypoellipticAleksandrov.KineticAleksandrov.Operator
public import HypoellipticAleksandrov.Geometry.KineticPointMeasure
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Batteries.Tactic.Alias



/-!
# Counterexample below the critical exponent

Companion paper, Proposition C.1.
-/

 public section

open Filter MeasureTheory
open scoped MatrixOrder

namespace HypoellipticAleksandrov.KineticAleksandrov

/-- Autonomous counterexamples below `4d`, with shared fixed bounds and cylinder. -/
alias kinetic_aleksandrov_autonomous_counterexample := _root_.HypoellipticAleksandrov.KineticAleksandrov.kinetic_aleksandrov_autonomous_counterexample_aux

end HypoellipticAleksandrov.KineticAleksandrov
