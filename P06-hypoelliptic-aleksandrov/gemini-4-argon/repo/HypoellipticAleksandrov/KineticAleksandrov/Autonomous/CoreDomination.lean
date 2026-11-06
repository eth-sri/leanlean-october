module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.CoreDominationEnlarged
import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.CoreDominationAllTimeKernel
import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.CoreDominationGreenRemainder
import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.CoreDominationIdentity
import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.CoreDominationLimit
import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.CoreDominationWaiting
import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.InfiniteHorizonOrder
import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.VisitMassCount

/-! # The cylinder core domination and continuation conclusions -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov ProbabilityTheory Filter
open scoped Topology

/- The original cylinder strip Green is dominated on the core by the actual visit Green measure. -/
theorem core_green_le_visitGreen
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam } (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (c : Clock) (Z0 : Point) (R : ℝ) (hR : 0 < R)
    (P : Point) (hP : P ∈ forwardCylinder Z0 R hR) :
    (stripGreen hH hLE hlam hLam A (capacityCylinderInterval Z0 R hR)
      (Z0.time + R ^ 2) (capacityCylinderPole Z0 P R hR hP)).restrict
        {q | q.velocity 0 ∈ c.core} ≤
    (coreAllTimeGreenMeasure hH hLE hlam hLam A c
      (visitStartsQ hH hLE hlam hLam A c Z0 R hR P hP)).restrict
        {q | q.velocity 0 ∈ c.core} := by
  have hp := visitCylinderStart_mem Z0 R hR P hP
  have hd : (visitUnionGreenKernel hH hLE hlam hLam A (capacityCylinderInterval Z0 R hR).toFiniteUnion Z0.time (Z0.time + R ^ 2) P).restrict {q | q.velocity 0 ∈ c.core} ≤ (coreAllTimeGreenMeasure hH hLE hlam hLam A c (Measure.sum (visitEntrancePiece hH hLE hlam hLam A c (capacityCylinderInterval Z0 R hR) Z0.time (Z0.time + R ^ 2) P))).restrict {q | q.velocity 0 ∈ c.core} := by
    let J := (capacityCylinderInterval Z0 R hR)
    let s := Z0.time
    let T := (Z0.time + R ^ 2)
    have hT : Z0.time < (Z0.time + R ^ 2) := by
      nlinarith [sq_pos_of_pos hR]
    let C : Set Point := {q | q.velocity 0 ∈ c.core}
    have hC : MeasurableSet C :=
      isClosed_Icc.measurableSet.preimage ((continuous_apply 0).comp continuous_velocity).measurable
    have _h_xinl_0 : (visitUnionGreenKernel hH hLE hlam hLam A J.toFiniteUnion s T P).restrict
        {q | q.velocity 0 ∈ c.core} =
      Measure.sum (fun n => (visitUnionGreenKernel hH hLE hlam hLam A (visitActiveUnion c J)
        s T ∘ₘ visitEntrancePiece hH hLE hlam hLam A c J s T P n).restrict
          {q | q.velocity 0 ∈ c.core}) := by
      let C : Set Point := {q | q.velocity 0 ∈ c.core}
      let GA := visitUnionGreenKernel hH hLE hlam hLam A (visitActiveUnion c J) s T
      let GW := visitUnionGreenKernel hH hLE hlam hLam A (visitWaitingUnion c J) s T
      let GO := visitUnionGreenKernel hH hLE hlam hLam A J.toFiniteUnion s T
      let gamma := visitEntrancePiece hH hLE hlam hLam A c J s T P
      let beta := visitOutgoingPiece hH hLE hlam hLam A c J s T P
      have hi : (visitInitialGreen P (visitEntranceInterval c) GW).restrict C = 0 := by
        classical
        unfold visitInitialGreen
        split
        · exact Measure.restrict_zero C
        · exact Measure.restrict_eq_zero.mpr
            (visitWaitingGreenKernel_core_zero hH hLE hlam hLam A c J s T P)
      have hw (n : ℕ) : (GW ∘ₘ beta n).restrict C = 0 :=
        Measure.restrict_eq_zero.mpr
          (visitWaitingGreenMixture_core_zero hH hLE hlam hLam A c J s T (beta n))
      apply measure_eq_sum_of_remainder_mass_tendsto_zero _ _
        (fun n => (GO ∘ₘ gamma n).restrict C)
      · intro N
        have h := congrArg (fun m : Measure Point => m.restrict C)
          (visitAlternating_green hH hLE hlam hLam A c J s T hT P hp N)
        change (GO P).restrict C =
          (visitInitialGreen P (visitEntranceInterval c) GW +
            ∑ n ∈ Finset.range N, (GA ∘ₘ gamma n + GW ∘ₘ beta n) + GO ∘ₘ gamma N).restrict C at h
        simpa only [Measure.restrict_add, visit_restrict_finset_sum, hi, hw,
          add_zero, zero_add] using h
      · have hz : Tendsto (fun n => (visitUnionGreenKernel hH hLE hlam hLam A J.toFiniteUnion s T ∘ₘ
          visitEntrancePiece hH hLE hlam hLam A c J s T P n) univ) atTop (𝓝 0) := by
            let := visitCount_isFiniteMeasure hH hLE hlam hLam A c J s T hT P hp
            exact visit_green_mixture_remainder_tendsto_zero hH hLE hlam hLam A J.toFiniteUnion s T _


        exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hz
          (fun _ => zero_le) (fun n => Measure.restrict_le_self univ)
    rw [_h_xinl_0]
    unfold coreAllTimeGreenMeasure
    rw [Measure.bind_sum _ _ (Kernel.aemeasurable _), Measure.restrict_sum _ hC]
    apply Measure.le_iff.mpr
    intro B hB
    rw [Measure.sum_apply _ hB, Measure.sum_apply _ hB]
    apply ENNReal.tsum_le_tsum
    intro n
    have _h_inl_15 : visitUnionGreenKernel hH hLE hlam hLam A (visitActiveUnion c J) s T ∘ₘ (visitEntrancePiece hH hLE hlam hLam A c J s T P n) ≤ coreAllTimeGreenMeasure hH hLE hlam hLam A c (visitEntrancePiece hH hLE hlam hLam A c J s T P n) := by
      let mu := (visitEntrancePiece hH hLE hlam hLam A c J s T P n)
      unfold coreAllTimeGreenMeasure
      apply Measure.le_iff.mpr
      intro B hB
      rw [Measure.bind_apply hB (Kernel.aemeasurable _),
        Measure.bind_apply hB (Kernel.aemeasurable _)]
      exact lintegral_mono (fun p => visitActiveGreenKernel_le_allTime hH hLE hlam hLam A c J s T p B)
    exact Measure.restrict_mono_measure
      _h_inl_15 C B
  rw [visitOuterGreen_eq_strip hH hLE hlam hLam A _ _ _ P hp] at hd
  exact hd

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
