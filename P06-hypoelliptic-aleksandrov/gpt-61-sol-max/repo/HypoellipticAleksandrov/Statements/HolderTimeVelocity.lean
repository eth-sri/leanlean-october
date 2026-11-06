module

public import HypoellipticAleksandrov.KineticAleksandrov.MainAssembly
public import HypoellipticAleksandrov.KineticAleksandrov.LocalA.FinalA
public import HypoellipticAleksandrov.KineticAleksandrov.Holder.Setting
import Batteries.Tactic.Alias



/-!
# Hölder continuity for time–velocity coefficients

Companion paper, Corollary 9.9. The Hörmander hypoellipticity theorem is supplied by the
`hormander` package and classical Dirichlet solvability (Lieberman, Theorem 5.14) is proved
in this library, so the statement carries no extra hypotheses.
-/

 public section

namespace HypoellipticAleksandrov.KineticAleksandrov
open Set MeasureTheory Holder
open scoped MatrixOrder

/-- Companion paper, Corollary 9.9. -/
alias kinetic_holder_timeVelocity := _root_.HypoellipticAleksandrov.KineticAleksandrov.kinetic_holder_timeVelocity_proof

end HypoellipticAleksandrov.KineticAleksandrov
