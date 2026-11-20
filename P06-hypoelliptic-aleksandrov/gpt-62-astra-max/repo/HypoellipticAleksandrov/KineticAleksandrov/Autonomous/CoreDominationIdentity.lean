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

/-- Restriction distributes over every finite measure sum. -/
theorem visit_restrict_finset_sum (mu : ℕ → Measure Point) (N : ℕ) (B : Set Point) :
    (∑ n ∈ Finset.range N, mu n).restrict B = ∑ n ∈ Finset.range N, (mu n).restrict B :=
  map_sum (Measure.restrictₗ B) mu (Finset.range N)

variable {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam) (A : SmoothAutonomous lam Lam)
    (c : Clock) (J : Interval) (s T : ℝ) (hT : s < T) (P : Point)
    (hP : s < P.time ∧ P.time < T ∧ P.velocity 0 ∈ J.carrier)
include hT hP

/-- The genuine outer Green continuation tends to zero for the actual entrance recursion. -/
theorem visitOuterGreen_remainder_tendsto_zero :
    Tendsto (fun n => (visitUnionGreenKernel hlam hLam A J.toFiniteUnion s T ∘ₘ
      visitEntrancePiece hlam hLam A c J s T P n) univ) atTop (𝓝 0) := by
  let := visitCount_isFiniteMeasure hlam hLam A c J s T hT P hP
  apply visit_green_mixture_remainder_tendsto_zero

/-- The actual outer core occupation is exactly the sum of its active visit occupations. -/
theorem visitOuterGreen_core_identity :
    (visitUnionGreenKernel hlam hLam A J.toFiniteUnion s T P).restrict
      {q | q.velocity 0 ∈ c.core} =
    Measure.sum (fun n => (visitUnionGreenKernel hlam hLam A (visitActiveUnion c J)
      s T ∘ₘ visitEntrancePiece hlam hLam A c J s T P n).restrict
        {q | q.velocity 0 ∈ c.core}) := by
  let C : Set Point := {q | q.velocity 0 ∈ c.core}
  let GW := visitUnionGreenKernel hlam hLam A (visitWaitingUnion c J) s T
  let GO := visitUnionGreenKernel hlam hLam A J.toFiniteUnion s T
  let gamma := visitEntrancePiece hlam hLam A c J s T P
  let beta := visitOutgoingPiece hlam hLam A c J s T P
  have hi : (visitInitialGreen P (visitEntranceInterval c) GW).restrict C = 0 := by
    classical
    unfold visitInitialGreen
    split
    · apply Measure.restrict_zero
    · exact Measure.restrict_eq_zero.mpr
        (visitWaitingGreenKernel_core_zero hlam hLam A c J s T P)
  have hw (n : ℕ) : (GW ∘ₘ beta n).restrict C = 0 :=
    Measure.restrict_eq_zero.mpr
      (visitWaitingGreenMixture_core_zero hlam hLam A c J s T (beta n))
  apply measure_eq_sum_of_remainder_mass_tendsto_zero _ _
    (fun n => (GO ∘ₘ gamma n).restrict C)
  · intro N
    have h := congrArg (fun m : Measure Point => m.restrict C)
      (visitAlternating_green hlam hLam A c J s T hT P hP N)
    change (GO P).restrict C =
      (visitInitialGreen P (visitEntranceInterval c) GW +
        ∑ n ∈ Finset.range N, ((visitUnionGreenKernel hlam hLam A (visitActiveUnion c J) s T) ∘ₘ gamma n + GW ∘ₘ beta n) + GO ∘ₘ gamma N).restrict C at h
    simpa [Measure.restrict_add, visit_restrict_finset_sum, hi, hw] using h
  · exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (visitOuterGreen_remainder_tendsto_zero hlam hLam A c J s T hT P hP)
      (fun _ => zero_le) (fun n => Measure.restrict_le_self univ)

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
