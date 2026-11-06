module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.CoreDominationIdentity
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.CoreDominationAllTimeKernel
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.InfiniteHorizonOrder
import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.CoreDominationGreenRemainder
import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.CoreDominationLimit
import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.CoreDominationWaiting
import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.VisitMassCount

/-! # Genuine core domination by the all-time Green measure of the actual entrance count -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov ProbabilityTheory
open Filter
open scoped Topology

/- Each actual clipped active Green kernel is bounded by the full all-time active-strip kernel. -/
theorem visitActiveGreenKernel_le_allTime
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam } (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (c : Clock) (J : Interval) (s T : ℝ) (p : Point) :
    visitUnionGreenKernel hH hLE hlam hLam A (visitActiveUnion c J) s T p ≤
      coreAllTimeGreenKernel hH hLE hlam hLam A c p := by
  classical
  by_cases hp : p ∈ visitPoleSet (visitActiveUnion c J) s T
  · have hv : p.velocity 0 ∈ c.active :=
      ((visitActiveUnion_carrier c J).le hp.2.2).1
    let H := visitActiveUnion c J
    let e := visitPoleInclusion H s T ⟨p, hp⟩
    let i := finiteUnionPoleIndex H T e
    have hsub : (H.component i).carrier ⊆ (visitActiveInterval c).carrier := by
      intro v hv'
      exact ((visitActiveUnion_carrier c J).le (H.component_subset i hv')).1
    have h := stripGreen_mono hH hLE hlam hLam A (H.component i) (visitActiveInterval c)
      hsub T ⊤ le_top (finiteUnionComponentPole H T e)
    change (if ht : p ∈ visitPoleSet H s T then
      finiteUnionGreen hH hLE hlam hLam A H T (visitPoleInclusion H s T ⟨p, ht⟩) else 0) ≤
        (if ht : p.velocity 0 ∈ c.active then
          stripGreen hH hLE hlam hLam A (visitActiveInterval c) ⊤
            (coreAllTimePole c ⟨p, ht⟩) else 0)
    rw [dite_eq_left hp, dite_eq_left hv]
    exact h
  · change (if ht : p ∈ visitPoleSet (visitActiveUnion c J) s T then _ else 0) ≤ _
    rw [dite_eq_right hp]
    intro B
    exact zero_le

/- The genuine active Green mixture is bounded by its all-time active-strip extension. -/
end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
