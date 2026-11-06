module

public import HypoellipticAleksandrov.KineticAleksandrov.Holder.Covering.NullFacesSphere
public import HypoellipticAleksandrov.KineticAleksandrov.Holder.Covering.Inflation
import Mathlib.Tactic

/-! # Null boundaries of positive-radius kinetic cylinders -/

 public section



namespace HypoellipticAleksandrov.KineticAleksandrov.Holder.Covering

open Set MeasureTheory

/-- The closure of a kinetic cylinder satisfies all four weak coordinate inequalities. -/
theorem closure_cylinder_bounds {d : ℕ} (P : KineticPoint d) (r : ℝ) :
    closure (backwardCylinder P r) ⊆ {X | P.time-r^2 ≤ X.time ∧ X.time ≤ P.time ∧
      PDE.vecNormSq (X.velocity-P.velocity) ≤ r^2 ∧
      PDE.vecNormSq (relativePosition P X) ≤ (r^3)^2} := by
  have hx : Continuous (relativePosition P) :=
    (continuous_position.sub continuous_const).sub
      ((continuous_time.sub continuous_const).smul continuous_const)
  apply closure_minimal
  · intro X hX
    have hp : PDE.vecNormSq (relativePosition P X) < (r^3)^2 := by
      simpa only [PDE.euclideanBall, PDE.euclideanSqDist, mem_ofPred_eq, sub_zero]
        using hX.2.2.2
    exact ⟨hX.1.le, hX.2.1.le, hX.2.2.1.le, hp.le⟩
  · exact (isClosed_le continuous_const continuous_time).inter
      ((isClosed_le continuous_time continuous_const).inter
        ((isClosed_le (PDE.continuous_vecNormSq.comp
          (continuous_velocity.sub continuous_const)) continuous_const).inter
          (isClosed_le (PDE.continuous_vecNormSq.comp hx) continuous_const)))

end HypoellipticAleksandrov.KineticAleksandrov.Holder.Covering
