module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.EnlargedRecursionLower
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.VisitMassCount

/-! # Equality with a strictly earlier clipped recursion -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov ProbabilityTheory

/-- On poles after `s`, the enlarged exit kernel agrees with a finite clipped kernel. -/
theorem enlargedVisitExit_comp_eq_clipped
    
    {lam Lam : ℝ} 
    (A : SmoothAutonomous lam Lam) (H : FiniteIntervalUnion) (s T : ℝ)
    (mu : Measure Point) (hs : ∀ᵐ p ∂mu, s ≤ p.time) :
    enlargedVisitExitKernel A H T ∘ₘ mu =
      visitUnionExitKernel A H (s - 1) T ∘ₘ mu :=
  visitExtendKernel_comp_eq_clipped H s T (finiteUnionExit A H T)
    (finiteUnionExit_measurable A H T) mu hs

section
variable {lam Lam : ℝ} (A : SmoothAutonomous lam Lam) (c : Clock) (J : Interval) (s T : ℝ)
  (P : Point)

/-- Lowering the clipped cutoff strictly below the initial pole preserves every entrance. -/
theorem enlargedVisitEntrance_eq_clipped (hs : s ≤ P.time) (hT : P.time < T) (n : ℕ) :
    enlargedVisitEntrance A c J s T P n =
      visitEntrancePiece A c J (s - 1) T P n := by
  let EA := enlargedVisitExitKernel A (visitActiveUnion c J) T
  let EW := enlargedVisitExitKernel A (visitWaitingUnion c J) T
  have he (H : FiniteIntervalUnion) (mu : Measure Point) (hm : ∀ᵐ p ∂mu, s ≤ p.time) :=
    enlargedVisitExit_comp_eq_clipped A H s T mu hm
  have hb (I : Interval) (mu : Measure Point) (hm : ∀ᵐ p ∂mu, s < p.time) :
      mu.restrict (visitBoundary s T I J) =
        mu.restrict (visitBoundary (s - 1) T I J) :=
    (enlargedBoundary_restrict_lower_eq I J (s - 1) s T (by linarith) mu hm).symm
  induction n with
  | zero =>
    unfold enlargedVisitEntrance visitEntrancePiece visitGamma visitInitial
    split
    · rfl
    · have hm : ∀ᵐ p ∂Measure.dirac P, s ≤ p.time :=
        (ae_dirac_iff (isClosed_le continuous_const continuous_time).measurableSet).mpr hs
      have hx := he (visitWaitingUnion c J) (Measure.dirac P) hm
      simp only [visitKernel_comp_dirac] at hx
      rw [← hx]
      exact hb _ _ ((enlargedVisitExitKernel_ae_time_gt A
        (visitWaitingUnion c J) T P).mono fun _ hp => hs.trans_lt hp)
  | succ n ih =>
    change (EW ∘ₘ ((EA ∘ₘ enlargedVisitEntrance A c J s T P n).restrict
      (visitBoundary s T (visitActiveInterval c) J))).restrict
        (visitBoundary s T (visitEntranceInterval c) J) = _
    have hg := (enlargedVisitEntrance_ae_support A c J s T P hs hT n).mono
      fun _ hp => hp.1
    have ha := enlargedExitMixture_ae_time_gt_lower A
      (visitActiveUnion c J) T s _ hg
    have hbeta : ∀ᵐ p ∂((EA ∘ₘ enlargedVisitEntrance A c J s T P n).restrict
        (visitBoundary s T (visitActiveInterval c) J)), s ≤ p.time :=
      (ae_restrict_mem (measurableSet_visitBoundary s T (visitActiveInterval c) J)).mono
        fun _ hp => hp.1.le
    have hw := enlargedExitMixture_ae_time_gt_lower A
      (visitWaitingUnion c J) T s _ hbeta
    rw [hb _ _ hw, he _ _ hbeta, hb _ _ ha, he _ _ hg, ih]
    rfl

/-- The actual enlarged count is finite for every valid outer-strip initial pole. -/
theorem enlargedVisitStarts_finite_of_outer_pole (hP : s ≤ P.time ∧ P.time < T ∧ P.velocity 0 ∈ J.carrier) :
    IsFiniteMeasure (enlargedVisitStarts A c J s T P) := by
  have he : enlargedVisitStarts A c J s T P =
      Measure.sum (visitEntrancePiece A c J (s - 1) T P) := by
    unfold enlargedVisitStarts
    congr 1
    funext n
    exact enlargedVisitEntrance_eq_clipped A c J s T P hP.1 hP.2.1 n
  rw [he]
  exact visitCount_isFiniteMeasure A c J (s - 1) T (by linarith [hP.1])
    P ⟨by linarith [hP.1], hP.2⟩

end

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
