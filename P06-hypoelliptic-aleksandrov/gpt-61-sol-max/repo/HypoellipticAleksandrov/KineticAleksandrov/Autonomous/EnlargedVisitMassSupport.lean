module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.EnlargedVisitsPieces
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.VisitMassEntranceIntegrals
import Mathlib.Tactic
import Aesop
import Batteries.Tactic.Alias
import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.VisitRecursionUnconditionalFaces



/-! # Support of the canonical enlarged-strip visit count

The initial atom is retained at the starting time; every subsequent entrance
is restricted to the literal internal face in the open observation slab.
-/

 public section

namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open MeasureTheory

/-- The closed entrance interval lies strictly inside the active interval. -/
alias enlarged_closedEntrance_subset_active := _root_.HypoellipticAleksandrov.KineticAleksandrov.Autonomous.visitClosedEntrance_subset_active


variable (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement) {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam) (A : SmoothAutonomous lam Lam) (c : Clock) (J : Interval) (s T : ℝ) (P : Point) (hs : s ≤ P.time) (hT : P.time < T)

include hs hT
/-- Every canonical entrance lies between the initial time and the horizon. -/
theorem enlargedVisitEntrance_ae_support
     (n : ℕ) :
    ∀ᵐ p ∂enlargedVisitEntrance hH hLE hlam hLam A c J s T P n,
      s ≤ p.time ∧ p.time < T ∧ p.velocity 0 ∈ closure c.entrance := by
  cases n with
  | zero =>
    unfold enlargedVisitEntrance visitGamma visitInitial
    split
    · rename_i hv
      aesop
    · exact (ae_restrict_mem
        (measurableSet_visitBoundary s T (visitEntranceInterval c) J)).mono
          (fun _ hp => ⟨hp.1.le, hp.2.1, frontier_subset_closure hp.2.2.1⟩)
  | succ n =>
    exact (ae_restrict_mem
      (measurableSet_visitBoundary s T (visitEntranceInterval c) J)).mono
        (fun _ hp => ⟨hp.1.le, hp.2.1, frontier_subset_closure hp.2.2.1⟩)

/-- The canonical counting measure has the same time and entrance support as its pieces. -/
theorem enlargedVisitStarts_ae_support
     :
    ∀ᵐ p ∂enlargedVisitStarts hH hLE hlam hLam A c J s T P,
      s ≤ p.time ∧ p.time < T ∧ p.velocity 0 ∈ closure c.entrance :=
  Measure.ae_sum_iff.mpr fun n =>
    enlargedVisitEntrance_ae_support hH hLE hlam hLam A c J s T P hs hT n

/-- The enlarged active-pole carrier includes almost every actual entrance. -/
theorem enlargedVisitEntrance_ae_activePole

    (hJ : closure c.active ⊆ J.carrier) (n : ℕ) :
    ∀ᵐ p ∂enlargedVisitEntrance hH hLE hlam hLam A c J s T P n,
      p ∈ enlargedVisitPoleSet (visitActiveUnion c J) T := by
  apply (enlargedVisitEntrance_ae_support hH hLE hlam hLam A c J s T P hs hT n).mono
  intro p hp
  refine ⟨hp.2.1, ?_⟩
  rw [visitActiveUnion_carrier]
  have hv := enlarged_closedEntrance_subset_active c hp.2.2
  exact ⟨hv, hJ (subset_closure hv)⟩

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
