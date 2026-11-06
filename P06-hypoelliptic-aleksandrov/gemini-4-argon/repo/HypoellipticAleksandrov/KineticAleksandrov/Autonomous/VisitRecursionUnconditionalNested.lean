module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.VisitRecursionUnconditionalPoleMixtures
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.NestedStrip
import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.NestedStripKernelIntegral
import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.NestedStripRestartPoles
import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.VisitRecursionUnconditionalMixtures
import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.NestedStripUnionPoint

/-! # Physical nested-strip identities for the actual visit kernels -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov ProbabilityTheory

/- Actual physical Green and exit kernels satisfy the nested-strip decomposition. -/
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
        visitUnionExitKernel hH hLE hlam hLam A H2 s T ∘ₘ rho := by
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
    have hnu := (visitUnionPoleMeasure_ae_time_gt H1 s T mu hmu)
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
      filter_upwards [hnu] with e he
      exact strip_nested_union_point hH hLE hlam hLam A H1 H2 hsub s T e he
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
    have hlarge : ∀ᵐ p ∂mu, p ∈ visitPoleSet H2 s T :=
      hmu.mono (fun p hp => ⟨hp.1, hp.2.1, hsub hp.2.2⟩)
    have _h_xinl_0 : ((visitUnionPoleMeasure H1 T mu).map
      (finiteUnionNestedPoleInclusion H1 H2 hsub T)).map Subtype.val = mu := by
        rw [Measure.map_map measurable_subtype_coe
          (measurable_finiteUnionNestedPoleInclusion H1 H2 hsub T)]
        exact visitUnionPoleMeasure_map H1 s T mu hmu

      /- Mapping smaller source poles into the larger domain is exactly the larger pole pullback. -/
    exact _h_xinl_0.trans
      (visitUnionPoleMeasure_map H2 s T mu hlarge).symm
  rw [_h_xinl_0, htau] at h
  rw [← visitUnionGreenKernel_comp_poles hH hLE hlam hLam A H2 s T mu hlarge,
    ← visitUnionGreenKernel_comp_poles hH hLE hlam hLam A H1 s T mu hmu,
    ← visitUnionGreenKernel_comp_poles hH hLE hlam hLam A H2 s T rho hrho,
    ← visitUnionExitKernel_comp_poles hH hLE hlam hLam A H2 s T mu hlarge,
    ← visitUnionExitKernel_comp_poles hH hLE hlam hLam A H1 s T mu hmu,
    ← visitUnionExitKernel_comp_poles hH hLE hlam hLam A H2 s T rho hrho] at h
  exact h

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
