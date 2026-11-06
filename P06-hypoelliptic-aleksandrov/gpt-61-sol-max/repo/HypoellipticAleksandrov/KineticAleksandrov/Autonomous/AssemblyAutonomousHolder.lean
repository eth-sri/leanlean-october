module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.AssemblyDensity
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.AutonomousHolder

/-! # Exact autonomous headline surface relative to the remaining frontier

Pure composition of results. The four source steps and three
classical inputs remain explicit; this is a conditional theorem.
-/

 public section

namespace HypoellipticAleksandrov.KineticAleksandrov
open MeasureTheory Set Autonomous Holder


/-- The conclusion, conditional on the remaining open steps and the two classical theorems. -/
theorem kinetic_holder_autonomous_relative_of_frontier
    (hfront : Autonomous.AutonomousRemainingFrontier)
    (hH : HormanderHypoellipticityStatement)
    (hLE : LiebermanEllipsoidDirichletStatement)
    (lam Lam : ℝ) (hlam : 0 < lam) (hLam : lam ≤ Lam) : type_of% (kinetic_holder_autonomous_relative_of_below_four_density
    (below_four_density_of_frontier hfront hH hLE) hH hLE lam Lam hlam hLam) := kinetic_holder_autonomous_relative_of_below_four_density
    (below_four_density_of_frontier hfront hH hLE) hH hLE lam Lam hlam hLam

end HypoellipticAleksandrov.KineticAleksandrov
