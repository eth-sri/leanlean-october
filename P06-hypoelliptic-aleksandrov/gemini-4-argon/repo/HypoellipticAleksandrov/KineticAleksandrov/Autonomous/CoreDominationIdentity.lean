module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.VisitMassCount
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.CoreDominationWaiting
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.CoreDominationGreenRemainder
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.CoreDominationLimit

/-! # The actual core occupation identity after removing the continuation remainder -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov ProbabilityTheory Filter
open scoped Topology

/- Restriction distributes over every finite measure sum. -/
theorem visit_restrict_finset_sum (mu : ℕ → Measure Point) (N : ℕ) (B : Set Point) :
    (∑ n ∈ Finset.range N, mu n).restrict B = ∑ n ∈ Finset.range N, (mu n).restrict B :=
  map_sum (Measure.restrictₗ B) mu (Finset.range N)

/- The genuine outer Green continuation tends to zero for the actual entrance recursion. -/
end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
