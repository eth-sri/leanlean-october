module

public import HypoellipticAleksandrov.Parabolic.KrylovCylinder
public import HypoellipticAleksandrov.Measure.TimeVelocity
public import HypoellipticAleksandrov.Ambient.MatrixContraction
import HypoellipticAleksandrov.Parabolic.KrylovEstimate.Assembly
import Batteries.Tactic.Alias



/-!
# Parabolic Aleksandrov estimate (Krylov)

Companion paper, Theorem 4.1: Krylov's parabolic Aleksandrov estimate.
-/

 public section


open MeasureTheory
open scoped MatrixOrder Matrix.Norms.Elementwise

namespace HypoellipticAleksandrov.Parabolic

/-- Krylov's parabolic Aleksandrov estimate, uniformly over location and height. -/
alias parabolic_aleksandrov := _root_.HypoellipticAleksandrov.Parabolic.parabolic_aleksandrov_aux

end HypoellipticAleksandrov.Parabolic
