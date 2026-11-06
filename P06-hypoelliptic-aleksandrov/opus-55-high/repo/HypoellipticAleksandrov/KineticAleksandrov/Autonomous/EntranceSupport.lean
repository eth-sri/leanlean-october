module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.CoreDomination
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.EnlargedVisits
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.EntranceStatement
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.InfiniteHorizonGreenSupport

/-! # Coordinate and support bridges for the entrance surface

Mass, short-time counts and core domination are imported from the companion modules unchanged.
-/

@[expose] public section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov ProbabilityTheory
open scoped Classical

variable (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement) {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam) (A : SmoothAutonomous lam Lam)

/-- The two active all-time families use exactly the same canonical strip and physical poles. -/
theorem entrance_coreAllTimeGreen_eq
     (c : Clock) (nu : Measure Point) :
    coreAllTimeGreenMeasure hH hLE hlam hLam A c nu =
      enlargedActiveGreen hH hLE hlam hLam A c nu := by
  aesop

/-- The actual clipped cylinder entrance count retains closed-entrance velocity support. -/
theorem entrance_visitStartsQ_ae_closedEntrance
     (c : Clock) (Z0 : Point) (R : ℝ) (hR : 0 < R)
    (P : Point) (hP : P ∈ forwardCylinder Z0 R hR) :
    ∀ᵐ p ∂visitStartsQ hH hLE hlam hLam A c Z0 R hR P hP,
      p.velocity 0 ∈ closure c.entrance := by
  have hI : (visitEntranceInterval c).carrier = c.entrance := rfl
  apply Measure.ae_sum_iff.mpr
  intro n
  cases n with
  | zero =>
    unfold visitEntrancePiece visitGamma visitInitial
    split
    · simp_all
    · filter_upwards [ae_restrict_mem (measurableSet_visitBoundary Z0.time
        _ _ _)]
        with p hp
      have hv := frontier_subset_closure hp.2.2.1
      simp_all
  | succ n =>
    filter_upwards [ae_restrict_mem (measurableSet_visitBoundary Z0.time
      _ _ _)]
      with p hp
    have hv := frontier_subset_closure hp.2.2.1
    simp_all

/-- The actual cylinder Green measure lies inside its literal observation strip. -/
theorem entrance_cylinderGreen_ae_observation
     (Z0 : Point) (R : ℝ) (hR : 0 < R)
    (P : Point) (hP : P ∈ forwardCylinder Z0 R hR) :
    ∀ᵐ p ∂stripGreen hH hLE hlam hLam A (capacityCylinderInterval Z0 R hR)
      (Z0.time + R ^ 2) (capacityCylinderPole Z0 P R hR hP),
      p ∈ densityObservationStrip Z0 R hR := by
  let H := capacityCylinderInterval Z0 R hR
  let ep := capacityCylinderPole Z0 P R hR hP
  let K := (stripEvolution hH hLE hlam hLam A H).2
  filter_upwards [reconstruction_green_ae_time_gt H K _ ep,
    stripGreenOfKernel_ae_mem_stripPast H K _ ep] with p hp hq
  exact ⟨hP.1.trans hp, hq.1, hq.2⟩

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
