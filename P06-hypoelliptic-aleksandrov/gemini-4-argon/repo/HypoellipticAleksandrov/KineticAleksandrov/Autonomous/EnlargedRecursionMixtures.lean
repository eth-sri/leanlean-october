module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.EnlargedRecursionPoles
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.EnlargedRecursionNested
import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.EnlargedVisitsPieces
import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.VisitRecursionUnconditionalPoleMixtures
import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.EnlargedRecursionEndpoint
import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.NestedStripUnionPoint

/-! # Physical nested-strip identities for the actual visit kernels -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov ProbabilityTheory

/- A lower-time bound on a physical source survives its subtype pullback. -/
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
        enlargedVisitExitKernel hH hLE hlam hLam A H2 T ∘ₘ rho := by
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
  have _h_inl_9 : ∀ᵐ e ∂visitUnionPoleMeasure H1 T mu, s ≤ e.1.time := by
    have ht : ∀ᵐ p ∂(visitUnionPoleMeasure H1 T mu).map Subtype.val, s ≤ p.time := by
      rw [enlargedUnionPoleMeasure_map H1 T mu hmu]
      exact htime
    exact ((MeasurableEmbedding.subtype_coe (measurableSet_finiteUnionPole H1 T)).ae_map_iff).mp ht
  have h :
      let nu2 := nu.map (finiteUnionNestedPoleInclusion H1 H2 hsub T)
          let tau := finiteUnionRestartPoleMeasure hH hLE hlam hLam A H1 H2 s T nu
          finiteUnionGreenMixture hH hLE hlam hLam A H2 T nu2 =
            finiteUnionGreenMixture hH hLE hlam hLam A H1 T nu +
              finiteUnionGreenMixture hH hLE hlam hLam A H2 T tau ∧
          finiteUnionExitMixture hH hLE hlam hLam A H2 T nu2 =
            (finiteUnionExitMixture hH hLE hlam hLam A H1 T nu).restrict
              (finiteUnionExitSet H2 s T) +
              finiteUnionExitMixture hH hLE hlam hLam A H2 T tau := by
    let inc := finiteUnionNestedPoleInclusion H1 H2 hsub (T : WithTop ℝ)
    let k := finiteUnionPointRestartPoles hH hLE hlam hLam A H1 H2 s T
    have hinc : Measurable inc := measurable_finiteUnionNestedPoleInclusion H1 H2 hsub T
    have hk : Measurable k := finiteUnionPointRestartPoles_measurable
      hH hLE hlam hLam A H1 H2 s T
    have hG1 := finiteUnionGreen_measurable hH hLE hlam hLam A H1 (T : WithTop ℝ)
    have hG2 := finiteUnionGreen_measurable hH hLE hlam hLam A H2 (T : WithTop ℝ)
    have hO1 := finiteUnionExit_measurable hH hLE hlam hLam A H1 T
    have hO2 := finiteUnionExit_measurable hH hLE hlam hLam A H2 T
    have hτ := finiteUnionRestartPoleMeasure_disintegration
      hH hLE hlam hLam A H1 H2 s T nu
    have hpoint : ∀ᵐ e ∂nu,
        finiteUnionGreen hH hLE hlam hLam A H2 T (inc e) =
          finiteUnionGreen hH hLE hlam hLam A H1 T e +
            (k e).bind (finiteUnionGreen hH hLE hlam hLam A H2 T) ∧
        finiteUnionExit hH hLE hlam hLam A H2 T (inc e) =
          (finiteUnionExit hH hLE hlam hLam A H1 T e).restrict
            (finiteUnionExitSet H2 s T) +
              (k e).bind (finiteUnionExit hH hLE hlam hLam A H2 T) := by
      filter_upwards [_h_inl_9] with e he
      have hs : s - 1 < e.1.time := by linarith
      have hm : ∀ᵐ p ∂finiteUnionExit hH hLE hlam hLam A H1 T e,
          p ∈ finiteUnionExitSet H1 s T := by
        rw [ae_iff]
        exact finiteUnionExit_compl_exit hH hLE hlam hLam A H1 s T e he
      have h := strip_nested_union_point hH hLE hlam hLam A H1 H2 hsub (s - 1) T e hs
      have hi : finiteUnionPointRestartPoles hH hLE hlam hLam A H1 H2 (s - 1) T e =
          finiteUnionPointRestartPoles hH hLE hlam hLam A H1 H2 s T e := by
        unfold finiteUnionPointRestartPoles
        rw [enlarged_internal_restrict_eq H1 H2 s T _ hm]
      rw [hi, enlarged_outer_restrict_eq H1 H2 s T _ hm] at h
      exact h
    constructor
    · have hmap := nested_bind_map nu inc hinc _ hG2
      have hp := Measure.bind_congr_right (hpoint.mono (fun _ hp => hp.1))
      have hadd := nested_bind_add nu _ _ hG1 ((Measure.measurable_bind' hG2).comp hk)
      have hassoc := Measure.bind_bind hk.aemeasurable hG2.aemeasurable
        (m := nu)
      have hlast := congrArg (fun τ => τ.bind (finiteUnionGreen hH hLE hlam hLam A H2 T)) hτ
      exact hmap.trans (hp.trans (hadd.trans
        (congrArg₂ (· + ·) rfl (hassoc.symm.trans hlast.symm))))
    · have hmap := nested_bind_map nu inc hinc _ hO2
      have hp := Measure.bind_congr_right (hpoint.mono (fun _ hp => hp.2))
      have hrestrict := nested_bind_restrict nu _ hO1 (finiteUnionExitSet H2 s T)
        (measurableSet_finiteUnionExitSet H2 s T)
      have hadd := nested_bind_add nu _ _
        (nested_measurable_family_restrict _ hO1 _ (measurableSet_finiteUnionExitSet H2 s T))
        ((Measure.measurable_bind' hO2).comp hk)
      have hassoc := Measure.bind_bind hk.aemeasurable hO2.aemeasurable (m := nu)
      have hlast := congrArg (fun τ => τ.bind (finiteUnionExit hH hLE hlam hLam A H2 T)) hτ
      exact hmap.trans (hp.trans (hadd.trans
        (congrArg₂ (· + ·) hrestrict.symm (hassoc.symm.trans hlast.symm))))
  dsimp only at h
  change _ ∧ _
  have _h_xinl_0 : (visitUnionPoleMeasure H1 T mu).map (finiteUnionNestedPoleInclusion H1 H2 hsub T) =
      visitUnionPoleMeasure H2 T mu := by
    apply (MeasurableEmbedding.subtype_coe (measurableSet_finiteUnionPole H2 T)).map_injective
    have hlarge : ∀ᵐ p ∂mu, p ∈ enlargedVisitPoleSet H2 T :=
      hmu.mono (fun p hp => ⟨hp.1, hsub hp.2⟩)
    have _h_xinl_0 : ((visitUnionPoleMeasure H1 T mu).map
      (finiteUnionNestedPoleInclusion H1 H2 hsub T)).map Subtype.val = mu := by
        rw [Measure.map_map measurable_subtype_coe
          (measurable_finiteUnionNestedPoleInclusion H1 H2 hsub T)]
        exact enlargedUnionPoleMeasure_map H1 T mu hmu

      /- Mapping smaller source poles into the larger domain is exactly the larger pole pullback. -/
    exact _h_xinl_0.trans
      (enlargedUnionPoleMeasure_map H2 T mu hlarge).symm
  rw [_h_xinl_0, htau] at h
  rw [← enlargedGreenKernel_comp_poles hH hLE hlam hLam A H2 T mu hlarge,
    ← enlargedGreenKernel_comp_poles hH hLE hlam hLam A H1 T mu hmu,
    ← enlargedGreenKernel_comp_poles hH hLE hlam hLam A H2 T rho hrho,
    ← enlargedExitKernel_comp_poles hH hLE hlam hLam A H2 T mu hlarge,
    ← enlargedExitKernel_comp_poles hH hLE hlam hLam A H1 T mu hmu,
    ← enlargedExitKernel_comp_poles hH hLE hlam hLam A H2 T rho hrho] at h
  exact h

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
