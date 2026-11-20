module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.EnlargedVisitsPieces
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.VisitMassEntranceIntegrals
import Mathlib.Tactic
import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.CoreStartBandVisits

/-! # Support of the canonical enlarged-strip visit count

The initial atom is retained at the starting time; every subsequent entrance
is restricted to the literal internal face in the open observation slab.
-/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory ProbabilityTheory HypoellipticAleksandrov

/-- Every canonical entrance lies between the initial time and the horizon. -/
theorem enlargedVisitEntrance_ae_support
    
    {lam Lam : ℝ} 
    (A : SmoothAutonomous lam Lam) (c : Clock) (J : Interval) (s T : ℝ)
    (P : Point) (hs : s ≤ P.time) (hT : P.time < T) (n : ℕ) :
    ∀ᵐ p ∂enlargedVisitEntrance A c J s T P n,
      s ≤ p.time ∧ p.time < T ∧ p.velocity 0 ∈ closure c.entrance := by
  cases n with
  | zero =>
    unfold enlargedVisitEntrance visitGamma visitInitial
    split
    · rename_i hv
      apply (ae_dirac_iff ?_).mpr
      · exact ⟨hs, hT, hv⟩
      · exact (isClosed_le continuous_const continuous_time).measurableSet.inter
          ((isOpen_lt continuous_time continuous_const).measurableSet.inter
            (isClosed_closure.measurableSet.preimage
              ((continuous_apply 0).comp continuous_velocity).measurable))
    · exact (ae_restrict_mem
        (measurableSet_visitBoundary s T (visitEntranceInterval c) J)).mono
          (fun _ hp => ⟨hp.1.le, hp.2.1, frontier_subset_closure hp.2.2.1⟩)
  | succ n =>
    exact (ae_restrict_mem
      (measurableSet_visitBoundary s T (visitEntranceInterval c) J)).mono
        (fun _ hp => ⟨hp.1.le, hp.2.1, frontier_subset_closure hp.2.2.1⟩)

section
variable {lam Lam : ℝ} (A : SmoothAutonomous lam Lam) (c : Clock) (J : Interval) (s T : ℝ)
  (P : Point) (hs : s ≤ P.time) (hT : P.time < T)
include hs hT

/-- The canonical counting measure has the same time and entrance support as its pieces. -/
theorem enlargedVisitStarts_ae_support :
    ∀ᵐ p ∂enlargedVisitStarts A c J s T P,
      s ≤ p.time ∧ p.time < T ∧ p.velocity 0 ∈ closure c.entrance :=
  Measure.ae_sum_iff.mpr fun n =>
    enlargedVisitEntrance_ae_support A c J s T P hs hT n

/-- The enlarged active-pole carrier includes almost every actual entrance. -/
theorem enlargedVisitEntrance_ae_activePole
    (hJ : closure c.active ⊆ J.carrier) (n : ℕ) :
    ∀ᵐ p ∂enlargedVisitEntrance A c J s T P n,
      p ∈ enlargedVisitPoleSet (visitActiveUnion c J) T := by
  apply (enlargedVisitEntrance_ae_support A c J s T P hs hT n).mono
  intro p hp
  refine ⟨hp.2.1, ?_⟩
  rw [visitActiveUnion_carrier]
  have hv := _root_.HypoellipticAleksandrov.KineticAleksandrov.Autonomous.enlargedEntrance_subset_active c hp.2.2
  exact ⟨hv, hJ (subset_closure hv)⟩

end

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
