module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.AssemblyDensity
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.TheoremAutonomous

/-! # Exact autonomous headline surface relative to the remaining frontier

Pure composition of results. The four source steps and three
classical inputs remain explicit; this is a conditional theorem.
-/

 public section

namespace HypoellipticAleksandrov.KineticAleksandrov
open MeasureTheory Autonomous


/-- The conclusion, conditional on the remaining open steps and the two classical theorems. -/
theorem kinetic_aleksandrov_autonomous_relative_of_frontier
    (hfront : Autonomous.AutonomousRemainingFrontier)
    (hH : HormanderHypoellipticityStatement)
    (hLE : LiebermanEllipsoidDirichletStatement)
    (lam Lam p : ℝ) (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (hp : 1 + bellmanAdjointExponent (Lam / lam)
      ((le_div_iff₀ hlam).2 (by simpa)) < p) : type_of% (kinetic_aleksandrov_autonomous_relative_of_below_four_density
    (below_four_density_of_frontier hfront hH hLE) hH hLE lam Lam p hlam hLam hp) := kinetic_aleksandrov_autonomous_relative_of_below_four_density
    (below_four_density_of_frontier hfront hH hLE) hH hLE lam Lam p hlam hLam hp

end HypoellipticAleksandrov.KineticAleksandrov
