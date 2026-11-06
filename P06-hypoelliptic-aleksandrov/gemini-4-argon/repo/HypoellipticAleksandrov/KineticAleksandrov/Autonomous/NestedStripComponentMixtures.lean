module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.NestedStripComponentRestart
import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.FiniteUnionDomainsClosedComponent
import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.NestedStripExit
import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.NestedStripUnionRestart
import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.FiniteUnionDomainsComponents
import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.FiniteUnionDomainsNesting
import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.NestedStripIntervalBoundary
import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.NestedStripKernelIntegral
import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.NestedStripRestartPoles

/-! # Actual restart mixtures are independent of certified component representations -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov

/- Restart mixture transport through a certified component inclusion.
The Green and exit consumers discharge the component-family equality by their proved APIs. -/
theorem nested_restart_bind_component
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam } (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (H1 H2 : FiniteIntervalUnion)
    (i : Fin H1.count) (j : Fin H2.count)
    (hsub : (H1.component i).carrier ⊆ (H2.component j).carrier) (sMinus T : ℝ)
    (e : StripPole (H1.component i) (T : WithTop ℝ)) (he : sMinus < e.1.time)
    (k : FiniteUnionPole H2 (T : WithTop ℝ) → Measure Point) (hk : Measurable k)
    (l : StripPole (H2.component j) (T : WithTop ℝ) → Measure Point)
    (hl : ∀ ep, k (componentPoleInclusion H2 j T ep) = l ep) :
    (finiteUnionPointRestartPoles hH hLE hlam hLam A H1 H2 sMinus T
      (componentPoleInclusion H1 i T e)).bind k =
      (nestedIntervalRestartPoles hH hLE hlam hLam A
        (H1.component i) (H2.component j) sMinus T e).bind l := by
  have hr : finiteUnionPointRestartPoles hH hLE hlam hLam A H1 H2 sMinus T
      (componentPoleInclusion H1 i T e) =
      (nestedIntervalRestartPoles hH hLE hlam hLam A
        (H1.component i) (H2.component j) sMinus T e).map (componentPoleInclusion H2 j T) := by
    apply MeasurableEmbedding.map_injective (MeasurableEmbedding.subtype_coe
      (measurableSet_finiteUnionPole H2 T))
    have hback : ((nestedIntervalRestartPoles hH hLE hlam hLam A
        (H1.component i) (H2.component j) sMinus T e).map
          (componentPoleInclusion H2 j T)).map Subtype.val =
        (stripExit hH hLE hlam hLam A (H1.component i) T e).restrict
          (nestedIntervalInternalExit (H1.component i) (H2.component j) sMinus T) := by
      rw [Measure.map_map measurable_subtype_coe (measurable_componentPoleInclusion H2 j T)]
      exact nestedIntervalRestartPoles_map hH hLE hlam hLam A
        (H1.component i) (H2.component j) sMinus T e
    have hΩ := finiteUnionExit_component hH hLE hlam hLam A H1 i T e
    have hrestrict : (stripExit hH hLE hlam hLam A (H1.component i) T e).restrict
        (finiteUnionInternalExit H1 H2 sMinus T) =
        (stripExit hH hLE hlam hLam A (H1.component i) T e).restrict
          (nestedIntervalInternalExit (H1.component i) (H2.component j) sMinus T) := by
      apply Measure.restrict_congr_set
      have hp : ∀ᵐ p ∂stripExit hH hLE hlam hLam A (H1.component i) T e,
          p ∈ reconstructionExit (H1.component i) sMinus T := by
        rw [ae_iff]
        exact (strip_exit_probability hH hLE hlam hLam A (H1.component i) sMinus T e he.le).2.1
      filter_upwards [hp] with p hp
      have _h_xinl_0 : p ∈ finiteUnionInternalExit H1 H2 sMinus T ↔
      p ∈ nestedIntervalInternalExit (H1.component i) (H2.component j) sMinus T := by
        have hv := (nested_strip_union_exit_subset_closed (H1.component i) (H2.component j)
          hsub sMinus T (Or.inr hp)).2
        have hcl : p.velocity 0 ∈ closure (H2.component j).carrier := by
          change p.velocity 0 ∈ closure (Ioo (H2.component j).lo (H2.component j).hi)
          rwa [closure_Ioo (H2.component j).ordered.ne]
        have hm := H2.mem_carrier_on_component_closure j hcl
        rcases hp with hp | hp
        · constructor <;> intro hs <;> exact False.elim ((ne_of_lt hs.2.1) hp.1)
        · constructor
          · intro hs
            exact ⟨hs.1, hs.2.1, hp.2.2, hm.mp hs.2.2.2⟩
          · intro hs
            refine ⟨hs.1, hs.2.1, ?_, hm.mpr hs.2.2.2⟩
            apply H1.frontier_component_subset i
            change p.velocity 0 ∈ frontier (Ioo (H1.component i).lo (H1.component i).hi)
            rw [frontier_Ioo (H1.component i).ordered]
            simpa only [mem_insert_iff, mem_singleton_iff] using hs.2.2.1
      exact propext _h_xinl_0
    have _h_xinl_0 : (finiteUnionPointRestartPoles hH hLE hlam hLam A H1 H2 sMinus T (componentPoleInclusion H1 i T e)).map Subtype.val =
      (finiteUnionExit hH hLE hlam hLam A H1 T (componentPoleInclusion H1 i T e)).restrict
        (finiteUnionInternalExit H1 H2 sMinus T) := by
      let e := (componentPoleInclusion H1 i T e)
      unfold finiteUnionPointRestartPoles
      refine (map_comap_subtype_coe (measurableSet_finiteUnionPole H2 T) _).trans ?_
      apply Measure.restrict_eq_self_of_ae_mem
      filter_upwards [ae_restrict_mem
        (measurableSet_finiteUnionInternalExit H1 H2 sMinus T)] with p hp
      exact ⟨WithTop.coe_lt_coe.mpr hp.2.1, hp.2.2.2⟩
    exact _h_xinl_0.trans
        ((congrArg (fun μ : Measure Point => μ.restrict
          (finiteUnionInternalExit H1 H2 sMinus T)) hΩ).trans (hrestrict.trans hback.symm))
  have h := congrArg (fun μ => μ.bind k) hr
  exact h.trans ((nested_bind_map _ _ (measurable_componentPoleInclusion H2 j T) k hk).trans
    (Measure.bind_congr_right (Filter.Eventually.of_forall hl)))

/- A nested union inclusion and certified component inclusion are the same physical pole. -/
end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
