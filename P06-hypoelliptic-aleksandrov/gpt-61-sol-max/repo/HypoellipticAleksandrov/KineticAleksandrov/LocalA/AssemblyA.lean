module

public import HypoellipticAleksandrov.KineticAleksandrov.Holder.TimeVelocityCorollary
public import HypoellipticAleksandrov.KineticAleksandrov.LocalA.Assembly

/-! # Time–velocity Hölder assembly from the smooth joint local statement -/

 public section

namespace HypoellipticAleksandrov.KineticAleksandrov
open Set MeasureTheory Holder LocalA
open scoped MatrixOrder

/-- The exact relative Hölder conclusion conditional on the smooth joint local statement. -/
theorem kinetic_holder_timeVelocity_relative_of_smooth
    (h : SmoothLocalRegularityStatement)
    (hH : HormanderHypoellipticityStatement)
    (hLE : LiebermanEllipsoidDirichletStatement)
    (d : ℕ) (hd : 1 ≤ d) (lam Lam : ℝ) (hlam : 0 < lam) (hLam : lam ≤ Lam) : type_of% (kinetic_holder_timeVelocity_relative_of_local
    (localTimeVelocityRegularity_of_smooth h) hH hLE d hd lam Lam hlam hLam) := kinetic_holder_timeVelocity_relative_of_local
    (localTimeVelocityRegularity_of_smooth h) hH hLE d hd lam Lam hlam hLam

end HypoellipticAleksandrov.KineticAleksandrov
