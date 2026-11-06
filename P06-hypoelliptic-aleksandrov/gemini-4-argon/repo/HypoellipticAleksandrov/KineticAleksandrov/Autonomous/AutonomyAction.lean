module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.AutonomyGenerator
import HypoellipticAleksandrov.KineticAleksandrov.Evolution.PastGluingLocality

/-! # The literal physical full-space action and its generator equation -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open HypoellipticAleksandrov HypoellipticAleksandrov.Parabolic Set MeasureTheory Filter
open HypoellipticAleksandrov.KineticAleksandrov.SectionTwo
open scoped Topology

/-- Elapsed-time kernel action, with physical state order `(X,v)`. -/
def fullSpaceAction (E : FullSpaceEvolution) (F : BoundedBorel (EvolutionAmbientState 1))
    (p : Point) : ℝ :=
  if hp : 0 ≤ p.time then
    ∫ x, F (x.2, x.1) ∂E.2.master
      (wholeSpaceQuery (-p.time) 0 (neg_nonpos.mpr hp) p.velocity p.position)
  else F (p.position, p.velocity)

/-- The definition agrees exactly with the source kernel formula at times `0,t`. -/
theorem fullSpaceAction_eq_zeroTime {lam Lam } (A : SmoothAutonomous lam Lam)
    (E : FullSpaceEvolution) (hE : IsFullSpaceEvolution A E)
    (F : BoundedBorel (EvolutionAmbientState 1)) (p : Point) (hp : 0 ≤ p.time) :
    fullSpaceAction E F p = ∫ x, F (x.2, x.1) ∂E.2.master
      (wholeSpaceQuery 0 p.time hp p.velocity p.position) := by
  rw [fullSpaceAction, dite_eq_left hp]
  have hk := fullspace_kernel_timeShift A E hE p.time
    (wholeSpaceQuery (-p.time) 0 (neg_nonpos.mpr hp) p.velocity p.position)
  have hq : autonomousQueryShift p.time
      (wholeSpaceQuery (-p.time) 0 (neg_nonpos.mpr hp) p.velocity p.position) =
      wholeSpaceQuery 0 p.time hp p.velocity p.position := by
    apply Subtype.ext
    dsimp only [autonomousQueryShift, wholeSpaceQuery]
    congr 1 <;> ring
  rw [hq] at hk
  exact congrArg (fun μ => ∫ x, F (x.2, x.1) ∂μ) hk.symm

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
