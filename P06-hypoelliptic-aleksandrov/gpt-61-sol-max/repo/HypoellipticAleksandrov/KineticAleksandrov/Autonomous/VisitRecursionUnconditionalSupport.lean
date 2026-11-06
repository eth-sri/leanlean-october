module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.VisitRecursionUnconditionalFaces

/-! # Actual entrance and outgoing measures satisfy the strict source-pole support -/

 public section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory ProbabilityTheory
open scoped Classical

variable (P : Point) (c : Clock) (J : Interval) (s T : ℝ) (exitActive exitWaiting : Kernel Point Point)

/-- Incoming restriction puts every later entrance strictly inside the active spacetime strip. -/
theorem visitGamma_ae_activePole
    (hP : s < P.time ∧ P.time < T ∧ P.velocity 0 ∈ J.carrier) (n : ℕ) :
    ∀ᵐ p ∂visitGamma P (visitEntranceInterval c)
      (visitBoundary s T (visitEntranceInterval c) J)
      (visitBoundary s T (visitActiveInterval c) J) exitActive exitWaiting n,
      p ∈ visitPoleSet (visitActiveUnion c J) s T := by
  cases n with
  | zero =>
    change ∀ᵐ p ∂visitInitial P (visitEntranceInterval c)
      (visitBoundary s T (visitEntranceInterval c) J) exitWaiting,
      p ∈ visitPoleSet (visitActiveUnion c J) s T
    unfold visitInitial
    split
    · rename_i hi
      apply (ae_dirac_iff (measurableSet_visitPoleSet _ s T)).mpr
      refine ⟨hP.1, hP.2.1, ?_⟩
      rw [visitActiveUnion_carrier]
      exact ⟨visitClosedEntrance_subset_active c hi, hP.2.2⟩
    · exact (ae_restrict_mem
        (measurableSet_visitBoundary s T (visitEntranceInterval c) J)).mono
        (visitIncomingFace_subset_activePole c J s T)
  | succ n =>
    exact (ae_restrict_mem
      (measurableSet_visitBoundary s T (visitEntranceInterval c) J)).mono
      (visitIncomingFace_subset_activePole c J s T)

/-- Every active outgoing measure is supported strictly inside the waiting spacetime strip. -/
theorem visitBeta_ae_waitingPole  (n : ℕ) :
    ∀ᵐ p ∂visitBeta P (visitEntranceInterval c)
      (visitBoundary s T (visitEntranceInterval c) J)
      (visitBoundary s T (visitActiveInterval c) J) exitActive exitWaiting n,
      p ∈ visitPoleSet (visitWaitingUnion c J) s T :=
  (ae_restrict_mem (measurableSet_visitBoundary s T (visitActiveInterval c) J)).mono
    (visitOutgoingFace_subset_waitingPole c J s T)

variable (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement) {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam) (A : SmoothAutonomous lam Lam) (c : Clock) (J : Interval) (s T : ℝ) (P : Point)

/-- The actual entrance family satisfies the corrected nested theorem's source support. -/
theorem visitEntrancePiece_ae_activePole

    (hP : s < P.time ∧ P.time < T ∧ P.velocity 0 ∈ J.carrier) (n : ℕ) :
    ∀ᵐ p ∂visitEntrancePiece hH hLE hlam hLam A c J s T P n,
      p ∈ visitPoleSet (visitActiveUnion c J) s T :=
  visitGamma_ae_activePole P c J s T _ _ hP n

/-- The actual outgoing family satisfies the corrected nested theorem's source support. -/
theorem visitOutgoingPiece_ae_waitingPole

    (n : ℕ) :
    ∀ᵐ p ∂visitOutgoingPiece hH hLE hlam hLam A c J s T P n,
      p ∈ visitPoleSet (visitWaitingUnion c J) s T :=
  visitBeta_ae_waitingPole P c J s T _ _ n

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
