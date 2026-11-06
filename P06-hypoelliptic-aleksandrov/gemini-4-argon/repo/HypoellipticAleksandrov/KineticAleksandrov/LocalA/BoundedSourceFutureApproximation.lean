module

public import HypoellipticAleksandrov.KineticAleksandrov.LocalA.BoundedSourceFutureRegularity
public import HypoellipticAleksandrov.KineticAleksandrov.LocalA.BoundedSourceSmoothApproximation
public import HypoellipticAleksandrov.KineticAleksandrov.LocalA.BoundedSourceActionConvergence
import HypoellipticAleksandrov.KineticAleksandrov.SectionTwo.DuhamelBoundary

/-! # Actual homogeneous approximations before the forcing starts -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.SectionTwo
open MeasureTheory Set Filter Evolution
open scoped Topology
variable {d : ℕ} {Ω : Set (PDE.Vec d)} {γ : ℝ → PDE.Vec d}

/- The literal source domain strictly after a chosen separating time. -/
def boundedSourceFutureSet (Ω : Set (PDE.Vec d)) (γ : ℝ → PDE.Vec d) (s T : ℝ) :
    Set (ℝ × EvolutionAmbientState d) :=
  {q | s < q.1 ∧ q ∈ boundedSourcePast Ω γ T}

/- The future source region is open with the original moving geometry. -/
theorem isOpen_boundedSourceFutureSet (hΩ : IsOpen Ω) (hγ : Continuous γ) (s T : ℝ) :
    IsOpen (boundedSourceFutureSet Ω γ s T) :=
  (isOpen_lt continuous_const continuous_fst).inter (isOpen_boundedSourcePast hΩ hγ T)

/- Actual positive bounded future potentials have continuous homogeneous approximants
converging for any supplied finite starting measure. -/
end HypoellipticAleksandrov.KineticAleksandrov.SectionTwo
