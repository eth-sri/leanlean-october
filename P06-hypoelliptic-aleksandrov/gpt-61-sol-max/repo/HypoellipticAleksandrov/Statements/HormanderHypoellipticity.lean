module

public import HypoellipticAleksandrov.KineticAleksandrov.HormanderBridge
public import HypoellipticAleksandrov.KineticAleksandrov.Hormander
import Batteries.Tactic.Alias



/-!
# Hörmander's hypoellipticity theorem

Let `L = Σ Xᵢ² + X₀ + c` be built from smooth vector fields whose Lie algebra spans at every
point of an open set, and let `u` be a locally integrable weak solution of `L u = g` with
smooth `c, g`. Then `u` agrees almost everywhere with a smooth function. The proof is by
the `hormander` package.
-/

 public section


set_option autoImplicit false

open Set MeasureTheory
open HypoellipticAleksandrov
open HypoellipticAleksandrov.KineticAleksandrov
open scoped BigOperators

namespace HypoellipticAleksandrov.KineticAleksandrov

/-- The locally integrable Hörmander regularity statement. -/
alias exists_smooth_aeRepresentative_of_hormander := _root_.HypoellipticAleksandrov.KineticAleksandrov.exists_smooth_aeRepresentative_of_hormander_aux

end HypoellipticAleksandrov.KineticAleksandrov
