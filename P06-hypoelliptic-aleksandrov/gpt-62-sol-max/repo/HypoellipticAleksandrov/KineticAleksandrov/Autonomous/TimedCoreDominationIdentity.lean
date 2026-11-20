module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.EnlargedVisitMassGreen
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.TimedCoreDominationWaiting
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.CoreDominationGreenRemainder
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.CoreDominationIdentity

/-! # The actual core occupation identity after removing the continuation remainder -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov ProbabilityTheory Filter
open scoped Topology

section
variable {lam Lam : ℝ} (A : SmoothAutonomous lam Lam) (c : Clock) (J : Interval) (s T : ℝ)

/-- The genuine outer Green continuation tends to zero for the actual entrance recursion. -/
theorem enlargedOuterGreen_remainder_tendsto_zero (_hT : s < T)
    (P : Point) (hP : s ≤ P.time ∧ P.time < T ∧ P.velocity 0 ∈ J.carrier)
    [IsFiniteMeasure (enlargedVisitStarts A c J s T P)] :
    Tendsto (fun n => (enlargedVisitGreenKernel A J.toFiniteUnion T ∘ₘ
      enlargedVisitEntrance A c J s T P n) univ) atTop (𝓝 0) := by
  have he (n : ℕ) := enlargedVisitGreen_comp_eq_clipped A
    J.toFiniteUnion s T (enlargedVisitEntrance A c J s T P n)
      ((enlargedVisitEntrance_ae_support A c J s T P hP.1 hP.2.1 n).mono
        fun _ hp => hp.1)
  have : IsFiniteMeasure (Measure.sum
      (enlargedVisitEntrance A c J s T P)) := by
    assumption
  have hz := visit_green_mixture_remainder_tendsto_zero A
    J.toFiniteUnion (s - 1) T (enlargedVisitEntrance A c J s T P)
  simpa only [he] using hz

/-- The actual outer core occupation is exactly the sum of its active visit occupations. -/
theorem enlargedOuterGreen_core_identity_of_finite_count (hT : s < T)
    (P : Point) (hP : s ≤ P.time ∧ P.time < T ∧ P.velocity 0 ∈ J.carrier)
    [IsFiniteMeasure (enlargedVisitStarts A c J s T P)] :
    (enlargedVisitGreenKernel A J.toFiniteUnion T P).restrict
      {q | q.velocity 0 ∈ c.core} =
    Measure.sum (fun n => (enlargedVisitGreenKernel A (visitActiveUnion c J)
      T ∘ₘ enlargedVisitEntrance A c J s T P n).restrict
        {q | q.velocity 0 ∈ c.core}) := by
  let C : Set Point := {q | q.velocity 0 ∈ c.core}
  let GA := enlargedVisitGreenKernel A (visitActiveUnion c J) T
  let GW := enlargedVisitGreenKernel A (visitWaitingUnion c J) T
  let GO := enlargedVisitGreenKernel A J.toFiniteUnion T
  let gamma := enlargedVisitEntrance A c J s T P
  let beta := enlargedVisitOutgoing A c J s T P
  have hi : (visitInitialGreen P (visitEntranceInterval c) GW).restrict C = 0 := by
    classical
    unfold visitInitialGreen
    split
    · exact Measure.restrict_zero C
    · exact Measure.restrict_eq_zero.mpr
        (enlargedWaitingGreenKernel_core_zero A c J T P)
  have hw (n : ℕ) : (GW ∘ₘ beta n).restrict C = 0 :=
    Measure.restrict_eq_zero.mpr
      (enlargedWaitingGreenMixture_core_zero A c J T (beta n))
  apply measure_eq_sum_of_remainder_mass_tendsto_zero _ _
    (fun n => (GO ∘ₘ gamma n).restrict C)
  · intro N
    have h := congrArg (fun m : Measure Point => m.restrict C)
      (enlargedAlternating_green A c J s T hT P hP N)
    change (GO P).restrict C =
      (visitInitialGreen P (visitEntranceInterval c) GW +
        ∑ n ∈ Finset.range N, (GA ∘ₘ gamma n + GW ∘ₘ beta n) + GO ∘ₘ gamma N).restrict C at h
    simpa only [Measure.restrict_add, visit_restrict_finset_sum, hi, hw,
      add_zero, zero_add] using h
  · have hz := enlargedOuterGreen_remainder_tendsto_zero A c J s T hT P hP
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hz
      (fun _ => zero_le) (fun n => Measure.restrict_le_self univ)

end

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
