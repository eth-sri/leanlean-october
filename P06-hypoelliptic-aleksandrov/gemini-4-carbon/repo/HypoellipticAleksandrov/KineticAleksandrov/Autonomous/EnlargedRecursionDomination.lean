module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.NestedStripUnionPoint
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.EnlargedRecursionPoles
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.EnlargedRecursionSupport
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.VisitRecursionUnconditionalInternalFaces
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.AlternatingGreen
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.AlternatingExit
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.VisitRecursionUnconditionalInitial
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.CoreDominationWaiting
import Mathlib.Tactic

@[expose] public noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov ProbabilityTheory


/-- Actual physical Green and exit kernels satisfy the nested-strip decomposition. -/
theorem enlargedUnion_nested
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (H1 H2 : FiniteIntervalUnion)
    (hsub : H1.carrier ⊆ H2.carrier) (s T : ℝ) (hT : s < T)
    (mu : Measure Point) [IsFiniteMeasure mu]
    (hmu : ∀ᵐ p ∂mu, p ∈ enlargedVisitPoleSet H1 T)
    (htime : ∀ᵐ p ∂mu, s ≤ p.time) :
    let rho := (enlargedVisitExitKernel hH hLE hlam hLam A H1 T ∘ₘ mu).restrict
      (finiteUnionInternalExit H1 H2 s T)
    enlargedVisitGreenKernel hH hLE hlam hLam A H2 T ∘ₘ mu =
      enlargedVisitGreenKernel hH hLE hlam hLam A H1 T ∘ₘ mu +
        enlargedVisitGreenKernel hH hLE hlam hLam A H2 T ∘ₘ rho ∧
    enlargedVisitExitKernel hH hLE hlam hLam A H2 T ∘ₘ mu =
      (enlargedVisitExitKernel hH hLE hlam hLam A H1 T ∘ₘ mu).restrict
        (finiteUnionExitSet H2 s T) +
        enlargedVisitExitKernel hH hLE hlam hLam A H2 T ∘ₘ rho   := by
  have enlargedUnionPoleMeasure_ae_time_ge :
      ∀ᵐ e ∂visitUnionPoleMeasure H1 T mu, s ≤ e.1.time := by
    have ht : ∀ᵐ p ∂(visitUnionPoleMeasure H1 T mu).map Subtype.val, s ≤ p.time := by
      rw [enlargedUnionPoleMeasure_map H1 T mu hmu]
      exact htime
    exact ((MeasurableEmbedding.subtype_coe (measurableSet_finiteUnionPole H1 T)).ae_map_iff).mp ht
  have enlarged_strip_nested (sMinus : ℝ) (_hT : sMinus < T) (nu : Measure (FiniteUnionPole H1 (T : WithTop ℝ))) [IsFiniteMeasure nu] (hnu : ∀ᵐ e ∂nu, sMinus ≤ e.1.time) :
      let nu2 := nu.map (finiteUnionNestedPoleInclusion H1 H2 hsub T)
    let tau := finiteUnionRestartPoleMeasure hH hLE hlam hLam A H1 H2 sMinus T nu
    finiteUnionGreenMixture hH hLE hlam hLam A H2 T nu2 =
      finiteUnionGreenMixture hH hLE hlam hLam A H1 T nu +
        finiteUnionGreenMixture hH hLE hlam hLam A H2 T tau ∧
    finiteUnionExitMixture hH hLE hlam hLam A H2 T nu2 =
      (finiteUnionExitMixture hH hLE hlam hLam A H1 T nu).restrict
        (finiteUnionExitSet H2 sMinus T) +
        finiteUnionExitMixture hH hLE hlam hLam A H2 T tau := by
    have enlarged_nested_union_point (s : ℝ) (e : FiniteUnionPole H1 (T : WithTop ℝ)) (he : s ≤ e.1.time) :
        finiteUnionGreen hH hLE hlam hLam A H2 T
        (finiteUnionNestedPoleInclusion H1 H2 hsub T e) =
        finiteUnionGreen hH hLE hlam hLam A H1 T e +
          (finiteUnionPointRestartPoles hH hLE hlam hLam A H1 H2 s T e).bind
            (finiteUnionGreen hH hLE hlam hLam A H2 T) ∧
      finiteUnionExit hH hLE hlam hLam A H2 T
        (finiteUnionNestedPoleInclusion H1 H2 hsub T e) =
        (finiteUnionExit hH hLE hlam hLam A H1 T e).restrict (finiteUnionExitSet H2 s T) +
          (finiteUnionPointRestartPoles hH hLE hlam hLam A H1 H2 s T e).bind
            (finiteUnionExit hH hLE hlam hLam A H2 T) := by
      have enlarged_outer_restrict_eq (mu : Measure Point) (hmu : ∀ᵐ p ∂mu, p ∈ finiteUnionExitSet H1 s T) :
          mu.restrict (finiteUnionExitSet H2 (s - 1) T) =
          mu.restrict (finiteUnionExitSet H2 s T) := by
        apply Measure.restrict_congr_set
        filter_upwards [hmu] with p hp
        apply propext
        change (p.time = T ∧ p.velocity 0 ∈ closure H2.carrier ∨
            s - 1 < p.time ∧ p.time < T ∧ p.velocity 0 ∈ frontier H2.carrier) ↔
          (p.time = T ∧ p.velocity 0 ∈ closure H2.carrier ∨
            s < p.time ∧ p.time < T ∧ p.velocity 0 ∈ frontier H2.carrier)
        rcases hp with hp | hp
        · rw [hp.1]
          simp
        · constructor
          · rintro (h | h)
            · exact Or.inl h
            · exact Or.inr ⟨hp.1, h.2⟩
          · rintro (h | h)
            · exact Or.inl h
            · exact Or.inr ⟨by linarith [h.1], h.2⟩
      have enlarged_internal_restrict_eq (mu : Measure Point) (hmu : ∀ᵐ p ∂mu, p ∈ finiteUnionExitSet H1 s T) :
          mu.restrict (finiteUnionInternalExit H1 H2 (s - 1) T) =
          mu.restrict (finiteUnionInternalExit H1 H2 s T) := by
        apply Measure.restrict_congr_set
        filter_upwards [hmu] with p hp
        apply propext
        change (s - 1 < p.time ∧ p.time < T ∧
            p.velocity 0 ∈ frontier H1.carrier ∩ H2.carrier) ↔
          (s < p.time ∧ p.time < T ∧ p.velocity 0 ∈ frontier H1.carrier ∩ H2.carrier)
        rcases hp with hp | hp
        · rw [hp.1]
          simp
        · constructor
          · intro h
            exact ⟨hp.1, h.2⟩
          · intro h
            exact ⟨by linarith [h.1], h.2⟩
      have hs : s - 1 < e.1.time := by linarith
      have hm : ∀ᵐ p ∂finiteUnionExit hH hLE hlam hLam A H1 T e,
          p ∈ finiteUnionExitSet H1 s T := by
        rw [ae_iff]
        exact finiteUnionExit_compl_exit hH hLE hlam hLam A H1 s T e he
      have h := strip_nested_union_point hH hLE hlam hLam A H1 H2 hsub (s - 1) T e hs
      have hi : finiteUnionPointRestartPoles hH hLE hlam hLam A H1 H2 (s - 1) T e =
          finiteUnionPointRestartPoles hH hLE hlam hLam A H1 H2 s T e := by
        unfold finiteUnionPointRestartPoles
        rw [enlarged_internal_restrict_eq _ hm]
      rwa [hi, enlarged_outer_restrict_eq _ hm] at h
    let inc := finiteUnionNestedPoleInclusion H1 H2 hsub (T : WithTop ℝ)
    let k := finiteUnionPointRestartPoles hH hLE hlam hLam A H1 H2 sMinus T
    have hinc := measurable_finiteUnionNestedPoleInclusion H1 H2 hsub T
    have hk := finiteUnionPointRestartPoles_measurable
      hH hLE hlam hLam A H1 H2 sMinus T
    have hG2 := finiteUnionGreen_measurable hH hLE hlam hLam A H2 (T : WithTop ℝ)
    have hO1 := finiteUnionExit_measurable hH hLE hlam hLam A H1 T
    have hO2 := finiteUnionExit_measurable hH hLE hlam hLam A H2 T
    have hτ := finiteUnionRestartPoleMeasure_disintegration
      hH hLE hlam hLam A H1 H2 sMinus T nu
    have hpoint : ∀ᵐ e ∂nu,
        finiteUnionGreen hH hLE hlam hLam A H2 T (inc e) =
          finiteUnionGreen hH hLE hlam hLam A H1 T e +
            (k e).bind (finiteUnionGreen hH hLE hlam hLam A H2 T) ∧
        finiteUnionExit hH hLE hlam hLam A H2 T (inc e) =
          (finiteUnionExit hH hLE hlam hLam A H1 T e).restrict
            (finiteUnionExitSet H2 sMinus T) +
              (k e).bind (finiteUnionExit hH hLE hlam hLam A H2 T) := by
      filter_upwards [hnu] with e he
      exact enlarged_nested_union_point sMinus e he
    constructor
    · have hmap := nested_bind_map nu inc hinc _ hG2
      have hp := Measure.bind_congr_right (hpoint.mono (fun _ hp => hp.1))
      have hadd := nested_bind_add nu _ _ (finiteUnionGreen_measurable hH hLE hlam hLam A H1 (T : WithTop ℝ)) ((Measure.measurable_bind' hG2).comp hk)
      have hassoc := Measure.bind_bind hk.aemeasurable hG2.aemeasurable
        (m := nu)
      have hlast := congrArg (fun τ => τ.bind (finiteUnionGreen hH hLE hlam hLam A H2 T)) hτ
      exact hmap.trans (hp.trans (hadd.trans
        (congrArg₂ (· + ·) rfl (hassoc.symm.trans hlast.symm))))
    · have hmap := nested_bind_map nu inc hinc _ hO2
      have hp := Measure.bind_congr_right (hpoint.mono (fun _ hp => hp.2))
      exact hmap.trans (hp.trans ((nested_bind_add nu _ _ (nested_measurable_family_restrict _ hO1 _ (measurableSet_finiteUnionExitSet H2 sMinus T)) ((Measure.measurable_bind' hO2).comp hk)).trans
        (congrArg₂ (· + ·) (nested_bind_restrict nu _ hO1 (finiteUnionExitSet H2 sMinus T) (measurableSet_finiteUnionExitSet H2 sMinus T)).symm ((Measure.bind_bind hk.aemeasurable hO2.aemeasurable (m := nu)).symm.trans (congrArg (fun τ => τ.bind (finiteUnionExit hH hLE hlam hLam A H2 T)) hτ).symm))))
  let nu := visitUnionPoleMeasure H1 T mu
  let rho := (enlargedVisitExitKernel hH hLE hlam hLam A H1 T ∘ₘ mu).restrict
    (finiteUnionInternalExit H1 H2 s T)
  have hlarge : ∀ᵐ p ∂mu, p ∈ enlargedVisitPoleSet H2 T :=
    hmu.mono (fun p hp => ⟨hp.1, hsub hp.2⟩)
  have hrestart : finiteUnionRestartMeasure hH hLE hlam hLam A H1 H2 s T nu = rho := by
    unfold finiteUnionRestartMeasure rho nu
    rw [enlargedExitKernel_comp_poles hH hLE hlam hLam A H1 T mu hmu]
  have hrho : ∀ᵐ p ∂rho, p ∈ enlargedVisitPoleSet H2 T := by
    rw [← hrestart]
    exact (finiteUnionRestartMeasure_ae_valid hH hLE hlam hLam A H1 H2 s T nu).mono
      (fun p hp => ⟨hp.2.1, hp.2.2⟩)
  have htau : finiteUnionRestartPoleMeasure hH hLE hlam hLam A H1 H2 s T nu =
      visitUnionPoleMeasure H2 T rho := by
    unfold finiteUnionRestartPoleMeasure visitUnionPoleMeasure
    rw [hrestart]
  have h := enlarged_strip_nested s hT nu
    (enlargedUnionPoleMeasure_ae_time_ge)
  dsimp only at h
  rw [enlargedUnionPoleMeasure_nested_eq H1 H2 hsub T mu hmu, htau] at h
  rw [← enlargedGreenKernel_comp_poles hH hLE hlam hLam A H2 T mu hlarge,
    ← enlargedGreenKernel_comp_poles hH hLE hlam hLam A H1 T mu hmu,
    ← enlargedGreenKernel_comp_poles hH hLE hlam hLam A H2 T rho hrho,
    ← enlargedExitKernel_comp_poles hH hLE hlam hLam A H2 T mu hlarge,
    ← enlargedExitKernel_comp_poles hH hLE hlam hLam A H1 T mu hmu,
    ← enlargedExitKernel_comp_poles hH hLE hlam hLam A H2 T rho hrho] at h
  exact h


/-- Every actual active visit has the genuine outer Green and exit splitting. -/
theorem enlargedEntrance_nested
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (c : Clock) (J : Interval) (s T : ℝ) (hT : s < T)
    (P : Point) (hP : s ≤ P.time ∧ P.time < T ∧ P.velocity 0 ∈ J.carrier) (n : ℕ) :
    let gamma := enlargedVisitEntrance hH hLE hlam hLam A c J s T P n
    let beta := enlargedVisitOutgoing hH hLE hlam hLam A c J s T P n
    enlargedVisitGreenKernel hH hLE hlam hLam A J.toFiniteUnion T ∘ₘ gamma =
      enlargedVisitGreenKernel hH hLE hlam hLam A (visitActiveUnion c J) T ∘ₘ gamma +
        enlargedVisitGreenKernel hH hLE hlam hLam A J.toFiniteUnion T ∘ₘ beta ∧
    enlargedVisitExitKernel hH hLE hlam hLam A J.toFiniteUnion T ∘ₘ gamma =
      (enlargedVisitExitKernel hH hLE hlam hLam A (visitActiveUnion c J) T ∘ₘ gamma).restrict
        (finiteUnionExitSet J.toFiniteUnion s T) +
        enlargedVisitExitKernel hH hLE hlam hLam A J.toFiniteUnion T ∘ₘ beta := by
  have hsub : (visitActiveUnion c J).carrier ⊆ J.toFiniteUnion.carrier := by
    rw [visitActiveUnion_carrier, Interval.toFiniteUnion_carrier]
    exact inter_subset_right
  simpa only [visitActive_internalExit, enlargedVisitOutgoing, visitBeta,
    enlargedVisitEntrance] using (enlargedUnion_nested hH hLE hlam hLam A (visitActiveUnion c J) J.toFiniteUnion hsub s T hT (enlargedVisitEntrance hH hLE hlam hLam A c J s T P n) ((enlargedEntrance_ae_activePole hH hLE hlam hLam A c J s T P hP n).mono (fun _ hp => hp.2)) ((enlargedEntrance_ae_activePole hH hLE hlam hLam A c J s T P hP n).mono (fun _ hp => hp.1)))

/-- Every actual waiting visit has the genuine outer Green and exit splitting. -/
theorem enlargedOutgoing_nested
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (c : Clock) (J : Interval) (s T : ℝ) (hT : s < T)
    (P : Point) (n : ℕ) :
    let beta := enlargedVisitOutgoing hH hLE hlam hLam A c J s T P n
    let gamma := enlargedVisitEntrance hH hLE hlam hLam A c J s T P (n + 1)
    enlargedVisitGreenKernel hH hLE hlam hLam A J.toFiniteUnion T ∘ₘ beta =
      enlargedVisitGreenKernel hH hLE hlam hLam A (visitWaitingUnion c J) T ∘ₘ beta +
        enlargedVisitGreenKernel hH hLE hlam hLam A J.toFiniteUnion T ∘ₘ gamma ∧
    enlargedVisitExitKernel hH hLE hlam hLam A J.toFiniteUnion T ∘ₘ beta =
      (enlargedVisitExitKernel hH hLE hlam hLam A (visitWaitingUnion c J) T ∘ₘ beta).restrict
        (finiteUnionExitSet J.toFiniteUnion s T) +
        enlargedVisitExitKernel hH hLE hlam hLam A J.toFiniteUnion T ∘ₘ gamma := by
  have hsub : (visitWaitingUnion c J).carrier ⊆ J.toFiniteUnion.carrier := by
    rw [visitWaitingUnion_carrier, Interval.toFiniteUnion_carrier]
    exact sdiff_subset
  simpa only [visitWaiting_internalExit, enlargedVisitEntrance, visitGamma,
    enlargedVisitOutgoing, visitBeta] using (enlargedUnion_nested hH hLE hlam hLam A (visitWaitingUnion c J) J.toFiniteUnion hsub s T hT (enlargedVisitOutgoing hH hLE hlam hLam A c J s T P n) ((enlargedOutgoing_ae_waitingPole hH hLE hlam hLam A c J s T P n).mono (fun _ hp => hp.2)) ((enlargedOutgoing_ae_waitingPole hH hLE hlam hLam A c J s T P n).mono (fun _ hp => hp.1)))


/-- The actual initial visit satisfies both outer Green and exit decompositions. -/
theorem enlargedInitial_nested
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (c : Clock) (J : Interval) (s T : ℝ) (hT : s < T)
    (P : Point) (hP : s ≤ P.time ∧ P.time < T ∧ P.velocity 0 ∈ J.carrier) :
    let gamma := enlargedVisitEntrance hH hLE hlam hLam A c J s T P 0
    let GW := enlargedVisitGreenKernel hH hLE hlam hLam A (visitWaitingUnion c J) T
    let EW := enlargedVisitExitKernel hH hLE hlam hLam A (visitWaitingUnion c J) T
    enlargedVisitGreenKernel hH hLE hlam hLam A J.toFiniteUnion T P =
      visitInitialGreen P (visitEntranceInterval c) GW +
        enlargedVisitGreenKernel hH hLE hlam hLam A J.toFiniteUnion T ∘ₘ gamma ∧
    enlargedVisitExitKernel hH hLE hlam hLam A J.toFiniteUnion T P =
      visitInitialExit P (visitEntranceInterval c) (finiteUnionExitSet J.toFiniteUnion s T) EW +
        enlargedVisitExitKernel hH hLE hlam hLam A J.toFiniteUnion T ∘ₘ gamma := by
  classical
  by_cases hi : P.velocity 0 ∈ closure (visitEntranceInterval c).carrier
  · simp [enlargedVisitEntrance, visitGamma, visitInitial, visitInitialGreen, visitInitialExit, ite_eq_left hi, visitKernel_comp_dirac, and_self]
  · have hsub : (visitWaitingUnion c J).carrier ⊆ J.toFiniteUnion.carrier := by
      rw [visitWaitingUnion_carrier, Interval.toFiniteUnion_carrier]
      exact sdiff_subset
    have hpw : P ∈ enlargedVisitPoleSet (visitWaitingUnion c J) T := by
      refine ⟨hP.2.1, ?_⟩
      rw [visitWaitingUnion_carrier]
      exact ⟨hP.2.2, hi⟩
    have h := enlargedUnion_nested hH hLE hlam hLam A (visitWaitingUnion c J) J.toFiniteUnion
      hsub s T hT (Measure.dirac P) ((ae_dirac_iff (measurableSet_enlargedVisitPoleSet _ T)).mpr hpw)
      ((ae_dirac_iff (isClosed_le continuous_const continuous_time).measurableSet).mpr hP.1)
    simpa only [visitWaiting_internalExit, visitKernel_comp_dirac, enlargedVisitEntrance,
      visitGamma, visitInitial, visitInitialGreen, visitInitialExit, ite_eq_right hi] using h


/-- The actual Green kernels satisfy the source's finite alternating identity. -/
theorem enlargedAlternating_green
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (c : Clock) (J : Interval) (s T : ℝ) (hT : s < T)
    (P : Point) (hP : s ≤ P.time ∧ P.time < T ∧ P.velocity 0 ∈ J.carrier) (N : ℕ) :
    let GA := enlargedVisitGreenKernel hH hLE hlam hLam A (visitActiveUnion c J) T
    let GW := enlargedVisitGreenKernel hH hLE hlam hLam A (visitWaitingUnion c J) T
    let GO := enlargedVisitGreenKernel hH hLE hlam hLam A J.toFiniteUnion T
    let gamma := enlargedVisitEntrance hH hLE hlam hLam A c J s T P
    let beta := enlargedVisitOutgoing hH hLE hlam hLam A c J s T P
    GO P = visitInitialGreen P (visitEntranceInterval c) GW +
      ∑ n ∈ Finset.range N, (GA ∘ₘ gamma n + GW ∘ₘ beta n) + GO ∘ₘ gamma N := by
  apply alternating_green_of_nested_splitting
  · exact (enlargedInitial_nested hH hLE hlam hLam A c J s T hT P hP).1
  · intro n
    exact (enlargedEntrance_nested hH hLE hlam hLam A c J s T hT P hP n).1
  · intro n
    exact (enlargedOutgoing_nested hH hLE hlam hLam A c J s T hT P n).1




/-- Literal finite-piece active domination in the source open physical observation strip. -/
theorem enlarged_piece_domination
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (c : Clock) (J : Interval) (s T : ℝ) (P : Point)
    (hP : s ≤ P.time ∧ P.time < T ∧ P.velocity 0 ∈ J.carrier) (N : ℕ) :
    let gamma := enlargedVisitEntrance hH hLE hlam hLam A c J s T P
    let GA := enlargedVisitGreenKernel hH hLE hlam hLam A (visitActiveUnion c J) T
    let EA := enlargedVisitExitKernel hH hLE hlam hLam A (visitActiveUnion c J) T
    let GO := enlargedVisitGreenKernel hH hLE hlam hLam A J.toFiniteUnion T
    let outer := finiteUnionExitSet J.toFiniteUnion s T
    (∑ n ∈ Finset.range N, ((EA ∘ₘ gamma n).restrict outer)) univ ≤ 1 ∧
      (∑ n ∈ Finset.range N, GA ∘ₘ gamma n) ≤
        (GO P).restrict {p | p.velocity 0 ∈ c.active}   := by
  have enlargedGreenMixture_ae_active (mu : Measure Point) :
      ∀ᵐ q ∂(enlargedVisitGreenKernel hH hLE hlam hLam A (visitActiveUnion c J) T ∘ₘ mu),
      q.velocity 0 ∈ c.active := by
    classical
    apply Measure.ae_comp_of_ae_ae
      (isOpen_Ioo.measurableSet.preimage ((continuous_apply 0).comp continuous_velocity).measurable)
    apply Filter.Eventually.of_forall
    intro p
    change ∀ᵐ q ∂(if hp : p ∈ enlargedVisitPoleSet (visitActiveUnion c J) T then
      finiteUnionGreen hH hLE hlam hLam A (visitActiveUnion c J) T
        (enlargedVisitPole _ T ⟨p, hp⟩) else 0), q.velocity 0 ∈ c.active
    split
    · rename_i hp
      exact (visitUnionGreen_ae_velocity hH hLE hlam hLam A (visitActiveUnion c J) T
        (enlargedVisitPole _ T ⟨p, hp⟩)).mono fun q hq =>
          ((visitActiveUnion_carrier c J).le hq).1
    · simp
  have enlargedAlternating_exit (hT : s < T) :
      let EA := enlargedVisitExitKernel hH hLE hlam hLam A (visitActiveUnion c J) T
    let EW := enlargedVisitExitKernel hH hLE hlam hLam A (visitWaitingUnion c J) T
    let EO := enlargedVisitExitKernel hH hLE hlam hLam A J.toFiniteUnion T
    let gamma := enlargedVisitEntrance hH hLE hlam hLam A c J s T P
    let beta := enlargedVisitOutgoing hH hLE hlam hLam A c J s T P
    let outer := finiteUnionExitSet J.toFiniteUnion s T
    EO P = visitInitialExit P (visitEntranceInterval c) outer EW +
      ∑ n ∈ Finset.range N,
        ((EA ∘ₘ gamma n).restrict outer + (EW ∘ₘ beta n).restrict outer) +
          EO ∘ₘ gamma N := by
    apply alternating_exit_of_nested_splitting
    · exact (enlargedInitial_nested hH hLE hlam hLam A c J s T hT P hP).2
    · intro n
      exact (enlargedEntrance_nested hH hLE hlam hLam A c J s T hT P hP n).2
    · intro n
      exact (enlargedOutgoing_nested hH hLE hlam hLam A c J s T hT P n).2
  classical
  let gamma := enlargedVisitEntrance hH hLE hlam hLam A c J s T P
  let GA := enlargedVisitGreenKernel hH hLE hlam hLam A (visitActiveUnion c J) T
  let EA := enlargedVisitExitKernel hH hLE hlam hLam A (visitActiveUnion c J) T
  let EO := enlargedVisitExitKernel hH hLE hlam hLam A J.toFiniteUnion T
  let beta := enlargedVisitOutgoing hH hLE hlam hLam A c J s T P
  let outer := finiteUnionExitSet J.toFiniteUnion s T
  have hT := hP.1.trans_lt hP.2.1
  have hGle : (∑ n ∈ Finset.range N, GA ∘ₘ gamma n) ≤ (enlargedVisitGreenKernel hH hLE hlam hLam A J.toFiniteUnion T) P := by
    rw [(enlargedAlternating_green hH hLE hlam hLam A c J s T hT P hP N)]
    calc
      _ ≤ ∑ n ∈ Finset.range N, (GA ∘ₘ gamma n + (enlargedVisitGreenKernel hH hLE hlam hLam A (visitWaitingUnion c J) T) ∘ₘ beta n) :=
        Finset.sum_le_sum (fun _ _ => le_add_of_nonneg_right (Measure.zero_le _))
      _ ≤ _ := (le_add_of_nonneg_left (Measure.zero_le _)).trans
        (le_add_of_nonneg_right (Measure.zero_le _))
  have hEle : (∑ n ∈ Finset.range N, (EA ∘ₘ gamma n).restrict outer) ≤ EO P := by
    rw [(enlargedAlternating_exit hT)]
    calc
      _ ≤ ∑ n ∈ Finset.range N,
          ((EA ∘ₘ gamma n).restrict outer + ((enlargedVisitExitKernel hH hLE hlam hLam A (visitWaitingUnion c J) T) ∘ₘ beta n).restrict outer) :=
        Finset.sum_le_sum (fun _ _ => le_add_of_nonneg_right (Measure.zero_le _))
      _ ≤ _ := (le_add_of_nonneg_left (Measure.zero_le _)).trans
        (le_add_of_nonneg_right (Measure.zero_le _))
  have hmass : EO P univ = 1 := by
    have hp : P ∈ enlargedVisitPoleSet J.toFiniteUnion T :=
      ⟨hP.2.1, by simpa only [Interval.toFiniteUnion_carrier] using hP.2.2⟩
    change (if h : P ∈ enlargedVisitPoleSet J.toFiniteUnion T then
      finiteUnionExit hH hLE hlam hLam A J.toFiniteUnion T
        (enlargedVisitPole _ T ⟨P, h⟩) else 0) univ = 1
    rw [dite_eq_left hp, measure_univ]
  refine ⟨(hEle univ).trans_eq hmass, ?_⟩
  have hs : ∀ᵐ p ∂(∑ n ∈ Finset.range N, GA ∘ₘ gamma n), p.velocity 0 ∈ c.active := by
    apply ae_finsetSum_measure_iff.mpr
    intro n _
    exact enlargedGreenMixture_ae_active (gamma n)
  have hrestrict := Measure.restrict_mono (subset_refl {p : Point | p.velocity 0 ∈ c.active})
    hGle
  have hr : (∑ n ∈ Finset.range N, GA ∘ₘ gamma n).restrict
      {p | p.velocity 0 ∈ c.active} = ∑ n ∈ Finset.range N, GA ∘ₘ gamma n :=
    Measure.restrict_eq_self_of_ae_mem hs
  rw [hr] at hrestrict
  exact hrestrict

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous

