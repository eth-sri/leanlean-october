module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.CoreDomination
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.EnlargedVisits
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.EntranceStatement
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.InfiniteHorizonGreenSupport

/-! # Coordinate and support bridges for the entrance surface

Mass, short-time counts and core domination are imported from the companion modules unchanged.
-/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov ProbabilityTheory
open scoped Classical

variable {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam) (A : SmoothAutonomous lam Lam)
    (c : Clock) (Z0 : Point) (R : ℝ) (hR : 0 < R) (P : Point) (hP : P ∈ forwardCylinder Z0 R hR)

/-- The two active all-time families use exactly the same canonical strip and physical poles. -/
theorem entrance_coreAllTimeGreen_eq (nu : Measure Point) :
    coreAllTimeGreenMeasure hlam hLam A c nu =
      enlargedActiveGreen hlam hLam A c nu := by
  rfl

/-- The actual clipped cylinder entrance count retains closed-entrance velocity support. -/
theorem entrance_visitStartsQ_ae_closedEntrance :
    ∀ᵐ p ∂visitStartsQ hlam hLam A c Z0 R hR P hP,
      p.velocity 0 ∈ closure c.entrance := by
  have hI : (visitEntranceInterval c).carrier = c.entrance := rfl
  apply Measure.ae_sum_iff.mpr
  intro n
  cases n with
  | zero =>
    unfold visitEntrancePiece visitGamma visitInitial
    split
    · rename_i hi
      apply (ae_dirac_iff (isClosed_closure.measurableSet.preimage ((continuous_apply 0).comp continuous_velocity).measurable)).mpr
      exact hi
    · filter_upwards [ae_restrict_mem (measurableSet_visitBoundary Z0.time
        (Z0.time + R ^ 2) (visitEntranceInterval c) (capacityCylinderInterval Z0 R hR))]
        with p hp
      simpa only [hI] using (frontier_subset_closure hp.2.2.1)
  | succ n =>
    unfold visitEntrancePiece visitGamma
    filter_upwards [ae_restrict_mem (measurableSet_visitBoundary Z0.time
      (Z0.time + R ^ 2) (visitEntranceInterval c) (capacityCylinderInterval Z0 R hR))]
      with p hp
    have hv := frontier_subset_closure hp.2.2.1
    exact hv

/-- The actual cylinder Green measure lies inside its literal observation strip. -/
theorem entrance_cylinderGreen_ae_observation :
    ∀ᵐ p ∂stripGreen hlam hLam A (capacityCylinderInterval Z0 R hR)
      (Z0.time + R ^ 2) (capacityCylinderPole Z0 P R hR hP),
      p ∈ densityObservationStrip Z0 R hR := by
  let H := capacityCylinderInterval Z0 R hR
  let ep := capacityCylinderPole Z0 P R hR hP
  let K := (stripEvolution hlam hLam A H).2
  filter_upwards [reconstruction_green_ae_time_gt H K (Z0.time + R ^ 2) ep,
    stripGreenOfKernel_ae_mem_stripPast H K (Z0.time + R ^ 2) ep] with p hp hq
  exact ⟨hP.1.trans hp, hq.1, hq.2⟩

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
