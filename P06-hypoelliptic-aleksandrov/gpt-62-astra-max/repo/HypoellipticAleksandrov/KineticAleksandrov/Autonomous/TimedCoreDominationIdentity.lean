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

variable {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam) (A : SmoothAutonomous lam Lam)
    (c : Clock) (J : Interval) (s T : ℝ)

/-- The genuine outer Green continuation tends to zero for the actual entrance recursion. -/
theorem enlargedOuterGreen_remainder_tendsto_zero (_hT : s < T)
    (P : Point) (hP : s ≤ P.time ∧ P.time < T ∧ P.velocity 0 ∈ J.carrier)
    [IsFiniteMeasure (enlargedVisitStarts hlam hLam A c J s T P)] :
    Tendsto (fun n => (enlargedVisitGreenKernel hlam hLam A J.toFiniteUnion T ∘ₘ
      enlargedVisitEntrance hlam hLam A c J s T P n) univ) atTop (𝓝 0) := by
  have he (n : ℕ) := enlargedVisitGreen_comp_eq_clipped hlam hLam A
    J.toFiniteUnion s T (enlargedVisitEntrance hlam hLam A c J s T P n)
      ((enlargedVisitEntrance_ae_support hlam hLam A c J s T P hP.1 hP.2.1 n).mono
        fun _ hp => hp.1)
  have : IsFiniteMeasure (Measure.sum
      (enlargedVisitEntrance hlam hLam A c J s T P)) := by
    change IsFiniteMeasure (enlargedVisitStarts hlam hLam A c J s T P)
    infer_instance
  simpa only [he] using (visit_green_mixture_remainder_tendsto_zero hlam hLam A J.toFiniteUnion (s - 1) T (enlargedVisitEntrance hlam hLam A c J s T P))

/-- The actual outer core occupation is exactly the sum of its active visit occupations. -/
theorem enlargedOuterGreen_core_identity_of_finite_count (hT : s < T)
    (P : Point) (hP : s ≤ P.time ∧ P.time < T ∧ P.velocity 0 ∈ J.carrier)
    [IsFiniteMeasure (enlargedVisitStarts hlam hLam A c J s T P)] :
    (enlargedVisitGreenKernel hlam hLam A J.toFiniteUnion T P).restrict
      {q | q.velocity 0 ∈ c.core} =
    Measure.sum (fun n => (enlargedVisitGreenKernel hlam hLam A (visitActiveUnion c J)
      T ∘ₘ enlargedVisitEntrance hlam hLam A c J s T P n).restrict
        {q | q.velocity 0 ∈ c.core}) := by
  let C : Set Point := {q | q.velocity 0 ∈ c.core}
  let GW := enlargedVisitGreenKernel hlam hLam A (visitWaitingUnion c J) T
  let GO := enlargedVisitGreenKernel hlam hLam A J.toFiniteUnion T
  let gamma := enlargedVisitEntrance hlam hLam A c J s T P
  let beta := enlargedVisitOutgoing hlam hLam A c J s T P
  have hi : (visitInitialGreen P (visitEntranceInterval c) GW).restrict C = 0 := by
    classical
    unfold visitInitialGreen
    split
    · apply Measure.restrict_zero
    · exact Measure.restrict_eq_zero.mpr
        (enlargedWaitingGreenKernel_core_zero hlam hLam A c J T P)
  have hw (n : ℕ) : (GW ∘ₘ beta n).restrict C = 0 :=
    Measure.restrict_eq_zero.mpr
      (enlargedWaitingGreenMixture_core_zero hlam hLam A c J T (beta n))
  apply measure_eq_sum_of_remainder_mass_tendsto_zero _ _
    (fun n => (GO ∘ₘ gamma n).restrict C)
  · intro N
    have h := congrArg (fun m : Measure Point => m.restrict C)
      (enlargedAlternating_green hlam hLam A c J s T hT P hP N)
    change (GO P).restrict C =
      (visitInitialGreen P (visitEntranceInterval c) GW +
        ∑ n ∈ Finset.range N, ((enlargedVisitGreenKernel hlam hLam A (visitActiveUnion c J) T) ∘ₘ gamma n + GW ∘ₘ beta n) + GO ∘ₘ gamma N).restrict C at h
    simpa [Measure.restrict_add, visit_restrict_finset_sum, hi, hw] using h
  · exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (enlargedOuterGreen_remainder_tendsto_zero hlam hLam A c J s T hT P hP)
      (fun _ => zero_le) (fun n => Measure.restrict_le_self univ)

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
