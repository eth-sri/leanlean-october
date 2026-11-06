module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.TimedCoreDominationAllTime
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.EnlargedRecursionClipped
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.CoreDominationStatement
import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.EnlargedRecursionLower
import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.VisitMassCount
import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.EnlargedVisits
import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.InfiniteHorizonOrder
import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.TimedCoreDominationIdentity

/-! # Core occupation exhausted and dominated by the canonical enlarged visits -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov
open ProbabilityTheory

/- The core domination statement, including initial poles at the named lower time. -/
theorem coreDominationStatement_holds : CoreDominationStatement := by
  classical
  intro hH hLE lam Lam hlam hLam A c J s T P hP _hbar _hJ hs
  have : IsFiniteMeasure (enlargedVisitStarts hH hLE hlam hLam A c J s T P) := by
    have hP : s ≤ P.time ∧ P.time < T ∧ P.velocity 0 ∈ J.carrier := ⟨hs, hP⟩
    have he : enlargedVisitStarts hH hLE hlam hLam A c J s T P =
        Measure.sum (visitEntrancePiece hH hLE hlam hLam A c J (s - 1) T P) := by
      unfold enlargedVisitStarts
      congr 1
      funext n
      have hs := hP.1
      have hT := hP.2.1
      let EA := enlargedVisitExitKernel hH hLE hlam hLam A (visitActiveUnion c J) T
      let EW := enlargedVisitExitKernel hH hLE hlam hLam A (visitWaitingUnion c J) T
      have he (H : FiniteIntervalUnion) (mu : Measure Point) (hm : ∀ᵐ p ∂mu, s ≤ p.time) : enlargedVisitExitKernel hH hLE hlam hLam A H T ∘ₘ mu =
          visitUnionExitKernel hH hLE hlam hLam A H (s - 1) T ∘ₘ mu := by
          classical
          apply Measure.comp_congr
          filter_upwards [hm] with p hp
          change (if h : p ∈ enlargedVisitPoleSet H T then
            finiteUnionExit hH hLE hlam hLam A H T (enlargedVisitPole H T ⟨p, h⟩) else 0) =
              (if h : p ∈ visitPoleSet H (s - 1) T then
                finiteUnionExit hH hLE hlam hLam A H T
                  (visitPoleInclusion H (s - 1) T ⟨p, h⟩) else 0)
          have he : p ∈ enlargedVisitPoleSet H T ↔ p ∈ visitPoleSet H (s - 1) T := by
            change (p.time < T ∧ p.velocity 0 ∈ H.carrier) ↔
              (s - 1 < p.time ∧ p.time < T ∧ p.velocity 0 ∈ H.carrier)
            constructor
            · intro h
              exact ⟨by linarith, h⟩
            · exact fun h => h.2
          by_cases h : p ∈ enlargedVisitPoleSet H T
          · rw [dite_eq_left h, dite_eq_left (he.mp h)]
            rfl
          · rw [dite_eq_right h, dite_eq_right (fun hh => h (he.mpr hh))]


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
          exact hb _ _ ((enlargedVisitExitKernel_ae_time_gt hH hLE hlam hLam A
            (visitWaitingUnion c J) T P).mono fun _ hp => hs.trans_lt hp)
      | succ n ih =>
        change (EW ∘ₘ ((EA ∘ₘ enlargedVisitEntrance hH hLE hlam hLam A c J s T P n).restrict
          (visitBoundary s T (visitActiveInterval c) J))).restrict
            (visitBoundary s T (visitEntranceInterval c) J) = _
        have hg := (enlargedVisitEntrance_ae_support hH hLE hlam hLam A c J s T P hs hT n).mono
          fun _ hp => hp.1
        have ha := enlargedExitMixture_ae_time_gt_lower hH hLE hlam hLam A
          (visitActiveUnion c J) T s _ hg
        have hbeta : ∀ᵐ p ∂((EA ∘ₘ enlargedVisitEntrance hH hLE hlam hLam A c J s T P n).restrict
            (visitBoundary s T (visitActiveInterval c) J)), s ≤ p.time :=
          (ae_restrict_mem (measurableSet_visitBoundary s T (visitActiveInterval c) J)).mono
            fun _ hp => hp.1.le
        have hw := enlargedExitMixture_ae_time_gt_lower hH hLE hlam hLam A
          (visitWaitingUnion c J) T s _ hbeta
        rw [hb _ _ hw, he _ _ hbeta, hb _ _ ha, he _ _ hg, ih]
        rfl
    rw [he]
    exact visitCount_isFiniteMeasure hH hLE hlam hLam A c J (s - 1) T (by linarith [hP.1])
      P ⟨by linarith [hP.1], hP.2⟩
  have hT := hs.trans_lt hP.1
  have hi := enlargedOuterGreen_core_identity_of_finite_count hH hLE hlam hLam A c J s T
    hT P ⟨hs, hP⟩
  have hd : (enlargedVisitGreenKernel hH hLE hlam hLam A J.toFiniteUnion T P).restrict {q | q.velocity 0 ∈ c.core} ≤ (enlargedActiveGreen hH hLE hlam hLam A c (Measure.sum (enlargedVisitEntrance hH hLE hlam hLam A c J s T P))).restrict {q | q.velocity 0 ∈ c.core} := by
    have hP : s ≤ P.time ∧ P.time < T ∧ P.velocity 0 ∈ J.carrier := ⟨hs, hP⟩
    let C : Set Point := {q | q.velocity 0 ∈ c.core}
    have hC : MeasurableSet C :=
      isClosed_Icc.measurableSet.preimage ((continuous_apply 0).comp continuous_velocity).measurable
    rw [enlargedOuterGreen_core_identity_of_finite_count hH hLE hlam hLam A c J s T hT P hP]
    unfold enlargedActiveGreen
    rw [Measure.bind_sum _ _ (Kernel.aemeasurable _), Measure.restrict_sum _ hC]
    apply Measure.le_iff.mpr
    intro B hB
    rw [Measure.sum_apply _ hB, Measure.sum_apply _ hB]
    apply ENNReal.tsum_le_tsum
    intro n
    have _h_inl_9 : enlargedVisitGreenKernel hH hLE hlam hLam A (visitActiveUnion c J) T ∘ₘ (enlargedVisitEntrance hH hLE hlam hLam A c J s T P n) ≤ enlargedActiveGreen hH hLE hlam hLam A c (enlargedVisitEntrance hH hLE hlam hLam A c J s T P n) := by
      let mu := (enlargedVisitEntrance hH hLE hlam hLam A c J s T P n)
      unfold enlargedActiveGreen
      apply Measure.le_iff.mpr
      intro B hB
      rw [Measure.bind_apply hB (Kernel.aemeasurable _),
        Measure.bind_apply hB (Kernel.aemeasurable _)]
      exact lintegral_mono (fun p => enlargedActiveGreenKernel_le_allTime hH hLE hlam hLam A c J T p B)
    exact Measure.restrict_mono_measure
      _h_inl_9 C B
  have he : enlargedVisitGreenKernel hH hLE hlam hLam A J.toFiniteUnion T P =
      stripGreen hH hLE hlam hLam A J T ⟨P, WithTop.coe_lt_coe.mpr hP.1, hP.2⟩ := by
    change (if hp : P ∈ enlargedVisitPoleSet J.toFiniteUnion T then _ else 0) = _
    rw [dite_eq_left (show P ∈ enlargedVisitPoleSet J.toFiniteUnion T from
      ⟨hP.1, by simpa only [Interval.toFiniteUnion_carrier] using hP.2⟩)]
    rfl
  rw [he] at hi hd
  exact ⟨hi, hd⟩

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
