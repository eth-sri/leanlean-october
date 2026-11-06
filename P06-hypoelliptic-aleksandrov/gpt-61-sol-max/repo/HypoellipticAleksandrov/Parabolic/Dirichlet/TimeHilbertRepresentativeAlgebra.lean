module

public import HypoellipticAleksandrov.Parabolic.Dirichlet.TimeHilbertTraces
import Batteries.Tactic.Alias
import Batteries.Tactic.OpenPrivate
import all HypoellipticAleksandrov.Parabolic.Dirichlet.VariationalEnergy

open private HypoellipticAleksandrov.Parabolic.Dirichlet.reverseTimeHilbertRepresentative_sub_eq from HypoellipticAleksandrov.Parabolic.Dirichlet.VariationalEnergy


/-!
# Algebra of canonical reverse-time Hilbert representatives

This module records algebraic identities for the canonical continuous
spatial-`L²` representatives of reverse-time Gelfand curves.
-/

 public section

open MeasureTheory Set




namespace HypoellipticAleksandrov.Parabolic.Dirichlet

/-- The canonical Hilbert representative of a difference is the difference
of the canonical representatives whenever the corresponding weak derivative
data are available. -/
alias reverseTimeHilbertRepresentative_sub_eq := _root_.HypoellipticAleksandrov.Parabolic.Dirichlet.reverseTimeHilbertRepresentative_sub_eq


end HypoellipticAleksandrov.Parabolic.Dirichlet
