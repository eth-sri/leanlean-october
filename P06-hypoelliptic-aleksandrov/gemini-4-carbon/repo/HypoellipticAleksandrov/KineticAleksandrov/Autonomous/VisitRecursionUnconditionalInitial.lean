module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.NestedStripUnionPoint
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.VisitRecursionUnconditionalPoleMixtures
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.VisitRecursionUnconditionalSupport
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.VisitRecursionUnconditionalInternalFaces
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.AlternatingGreen
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.AlternatingExit

@[expose] public noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov ProbabilityTheory

/-- Actual physical Green and exit kernels satisfy the nested-strip decomposition. -/
theorem visitUnion_nested
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (H1 H2 : FiniteIntervalUnion)
    (hsub : H1.carrier ⊆ H2.carrier) (s T : ℝ) (hT : s < T)
    (mu : Measure Point) [IsFiniteMeasure mu]
    (hmu : ∀ᵐ p ∂mu, p ∈ visitPoleSet H1 s T) :
    let rho := (visitUnionExitKernel hH hLE hlam hLam A H1 s T ∘ₘ mu).restrict
      (finiteUnionInternalExit H1 H2 s T)
    visitUnionGreenKernel hH hLE hlam hLam A H2 s T ∘ₘ mu =
      visitUnionGreenKernel hH hLE hlam hLam A H1 s T ∘ₘ mu +
        visitUnionGreenKernel hH hLE hlam hLam A H2 s T ∘ₘ rho ∧
    visitUnionExitKernel hH hLE hlam hLam A H2 s T ∘ₘ mu =
      (visitUnionExitKernel hH hLE hlam hLam A H1 s T ∘ₘ mu).restrict
        (finiteUnionExitSet H2 s T) +
        visitUnionExitKernel hH hLE hlam hLam A H2 s T ∘ₘ rho  := by
  have strip_nested (sMinus : ℝ) (_hT : sMinus < T) (nu : Measure (FiniteUnionPole H1 (T : WithTop ℝ))) [IsFiniteMeasure nu] (hnu : ∀ᵐ e ∂nu, sMinus < e.1.time) :
      let nu2 := nu.map (finiteUnionNestedPoleInclusion H1 H2 hsub T)
    let tau := finiteUnionRestartPoleMeasure hH hLE hlam hLam A H1 H2 sMinus T nu
    finiteUnionGreenMixture hH hLE hlam hLam A H2 T nu2 =
      finiteUnionGreenMixture hH hLE hlam hLam A H1 T nu +
        finiteUnionGreenMixture hH hLE hlam hLam A H2 T tau ∧
    finiteUnionExitMixture hH hLE hlam hLam A H2 T nu2 =
      (finiteUnionExitMixture hH hLE hlam hLam A H1 T nu).restrict
        (finiteUnionExitSet H2 sMinus T) +
        finiteUnionExitMixture hH hLE hlam hLam A H2 T tau := by
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
      exact strip_nested_union_point hH hLE hlam hLam A H1 H2 hsub sMinus T e he
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
  let rho := (visitUnionExitKernel hH hLE hlam hLam A H1 s T ∘ₘ mu).restrict
    (finiteUnionInternalExit H1 H2 s T)
  have hlarge : ∀ᵐ p ∂mu, p ∈ visitPoleSet H2 s T :=
    hmu.mono (fun p hp => ⟨hp.1, hp.2.1, hsub hp.2.2⟩)
  have hrestart : finiteUnionRestartMeasure hH hLE hlam hLam A H1 H2 s T nu = rho := by
    unfold finiteUnionRestartMeasure rho nu
    rw [visitUnionExitKernel_comp_poles hH hLE hlam hLam A H1 s T mu hmu]
  have hrho : ∀ᵐ p ∂rho, p ∈ visitPoleSet H2 s T := by
    rw [← hrestart]
    exact finiteUnionRestartMeasure_ae_valid hH hLE hlam hLam A H1 H2 s T nu
  have htau : finiteUnionRestartPoleMeasure hH hLE hlam hLam A H1 H2 s T nu =
      visitUnionPoleMeasure H2 T rho := by
    unfold finiteUnionRestartPoleMeasure visitUnionPoleMeasure
    rw [hrestart]
  have h := strip_nested s hT nu
    (visitUnionPoleMeasure_ae_time_gt H1 s T mu hmu)
  dsimp only at h
  rw [visitUnionPoleMeasure_nested_eq H1 H2 hsub s T mu hmu, htau] at h
  rw [← visitUnionGreenKernel_comp_poles hH hLE hlam hLam A H2 s T mu hlarge,
    ← visitUnionGreenKernel_comp_poles hH hLE hlam hLam A H1 s T mu hmu,
    ← visitUnionGreenKernel_comp_poles hH hLE hlam hLam A H2 s T rho hrho,
    ← visitUnionExitKernel_comp_poles hH hLE hlam hLam A H2 s T mu hlarge,
    ← visitUnionExitKernel_comp_poles hH hLE hlam hLam A H1 s T mu hmu,
    ← visitUnionExitKernel_comp_poles hH hLE hlam hLam A H2 s T rho hrho] at h
  exact h


/-- Every actual active visit has the genuine outer Green and exit splitting. -/
theorem visitEntrance_nested
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (c : Clock) (J : Interval) (s T : ℝ) (hT : s < T)
    (P : Point) (hP : s < P.time ∧ P.time < T ∧ P.velocity 0 ∈ J.carrier) (n : ℕ) :
    let gamma := visitEntrancePiece hH hLE hlam hLam A c J s T P n
    let beta := visitOutgoingPiece hH hLE hlam hLam A c J s T P n
    visitUnionGreenKernel hH hLE hlam hLam A J.toFiniteUnion s T ∘ₘ gamma =
      visitUnionGreenKernel hH hLE hlam hLam A (visitActiveUnion c J) s T ∘ₘ gamma +
        visitUnionGreenKernel hH hLE hlam hLam A J.toFiniteUnion s T ∘ₘ beta ∧
    visitUnionExitKernel hH hLE hlam hLam A J.toFiniteUnion s T ∘ₘ gamma =
      (visitUnionExitKernel hH hLE hlam hLam A (visitActiveUnion c J) s T ∘ₘ gamma).restrict
        (finiteUnionExitSet J.toFiniteUnion s T) +
        visitUnionExitKernel hH hLE hlam hLam A J.toFiniteUnion s T ∘ₘ beta := by
  have hsub : (visitActiveUnion c J).carrier ⊆ J.toFiniteUnion.carrier := by
    rw [visitActiveUnion_carrier, Interval.toFiniteUnion_carrier]
    exact inter_subset_right
  simpa only [visitActive_internalExit, visitOutgoingPiece, visitBeta,
    visitEntrancePiece] using (visitUnion_nested hH hLE hlam hLam A (visitActiveUnion c J) J.toFiniteUnion hsub s T hT (visitEntrancePiece hH hLE hlam hLam A c J s T P n) (visitEntrancePiece_ae_activePole hH hLE hlam hLam A c J s T P hP n))

/-- Every actual waiting visit has the genuine outer Green and exit splitting. -/
theorem visitOutgoing_nested
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (c : Clock) (J : Interval) (s T : ℝ) (hT : s < T)
    (P : Point) (n : ℕ) :
    let beta := visitOutgoingPiece hH hLE hlam hLam A c J s T P n
    let gamma := visitEntrancePiece hH hLE hlam hLam A c J s T P (n + 1)
    visitUnionGreenKernel hH hLE hlam hLam A J.toFiniteUnion s T ∘ₘ beta =
      visitUnionGreenKernel hH hLE hlam hLam A (visitWaitingUnion c J) s T ∘ₘ beta +
        visitUnionGreenKernel hH hLE hlam hLam A J.toFiniteUnion s T ∘ₘ gamma ∧
    visitUnionExitKernel hH hLE hlam hLam A J.toFiniteUnion s T ∘ₘ beta =
      (visitUnionExitKernel hH hLE hlam hLam A (visitWaitingUnion c J) s T ∘ₘ beta).restrict
        (finiteUnionExitSet J.toFiniteUnion s T) +
        visitUnionExitKernel hH hLE hlam hLam A J.toFiniteUnion s T ∘ₘ gamma := by
  have hsub : (visitWaitingUnion c J).carrier ⊆ J.toFiniteUnion.carrier := by
    rw [visitWaitingUnion_carrier, Interval.toFiniteUnion_carrier]
    exact sdiff_subset
  simpa only [visitWaiting_internalExit, visitEntrancePiece, visitGamma,
    visitOutgoingPiece, visitBeta] using (visitUnion_nested hH hLE hlam hLam A (visitWaitingUnion c J) J.toFiniteUnion hsub s T hT (visitOutgoingPiece hH hLE hlam hLam A c J s T P n) (visitOutgoingPiece_ae_waitingPole hH hLE hlam hLam A c J s T P n))


/-- Composing any physical kernel with a point mass evaluates that kernel. -/
theorem visitKernel_comp_dirac (k : Kernel Point Point) (P : Point) :
    k ∘ₘ Measure.dirac P = k P := Measure.dirac_bind k.measurable P

/-- The actual initial visit satisfies both outer Green and exit decompositions. -/
theorem visitInitial_nested
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (c : Clock) (J : Interval) (s T : ℝ) (hT : s < T)
    (P : Point) (hP : s < P.time ∧ P.time < T ∧ P.velocity 0 ∈ J.carrier) :
    let gamma := visitEntrancePiece hH hLE hlam hLam A c J s T P 0
    let GW := visitUnionGreenKernel hH hLE hlam hLam A (visitWaitingUnion c J) s T
    let EW := visitUnionExitKernel hH hLE hlam hLam A (visitWaitingUnion c J) s T
    visitUnionGreenKernel hH hLE hlam hLam A J.toFiniteUnion s T P =
      visitInitialGreen P (visitEntranceInterval c) GW +
        visitUnionGreenKernel hH hLE hlam hLam A J.toFiniteUnion s T ∘ₘ gamma ∧
    visitUnionExitKernel hH hLE hlam hLam A J.toFiniteUnion s T P =
      visitInitialExit P (visitEntranceInterval c) (finiteUnionExitSet J.toFiniteUnion s T) EW +
        visitUnionExitKernel hH hLE hlam hLam A J.toFiniteUnion s T ∘ₘ gamma := by
  classical
  by_cases hi : P.velocity 0 ∈ closure (visitEntranceInterval c).carrier
  · simp [visitEntrancePiece, visitGamma, visitInitial, visitInitialGreen, visitInitialExit, ite_eq_left hi, visitKernel_comp_dirac, and_self]
  · have hsub : (visitWaitingUnion c J).carrier ⊆ J.toFiniteUnion.carrier := by
      rw [visitWaitingUnion_carrier, Interval.toFiniteUnion_carrier]
      exact sdiff_subset
    have hpw : P ∈ visitPoleSet (visitWaitingUnion c J) s T := by
      refine ⟨hP.1, hP.2.1, ?_⟩
      rw [visitWaitingUnion_carrier]
      exact ⟨hP.2.2, hi⟩
    have h := visitUnion_nested hH hLE hlam hLam A (visitWaitingUnion c J) J.toFiniteUnion
      hsub s T hT (Measure.dirac P) ((ae_dirac_iff (measurableSet_visitPoleSet _ s T)).mpr hpw)
    simpa only [visitWaiting_internalExit, visitKernel_comp_dirac, visitEntrancePiece,
      visitGamma, visitInitial, visitInitialGreen, visitInitialExit, ite_eq_right hi] using h

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous

