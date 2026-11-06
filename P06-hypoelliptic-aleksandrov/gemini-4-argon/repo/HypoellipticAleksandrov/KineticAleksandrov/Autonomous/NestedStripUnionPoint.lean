module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.NestedStripComponentMixtures
import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.FiniteUnionDomainsClosedComponent
import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.FiniteUnionDomainsComponents
import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.FiniteUnionDomainsNesting
import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.NestedStripComponentRestart
import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.NestedStripExit
import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.NestedStripIntervalBoundary
import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.NestedStripKernelIntegral
import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.NestedStripRestartPoles
import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.NestedStripUnionRestart
import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.FiniteUnionDomainsMass
import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.GreenTestExtensionCanonical
import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.NestedStripCoordinates
import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.NestedStripExitIdentity
import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.NestedStripExitTests
import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.NestedStripGreen
import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.NestedStripHomogeneous
import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.NestedStripRepresentation
import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.NestedStripSlab
import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.NestedStripSourceRestart
import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.NestedStripIntervalRestart

/-! # The literal nested Green and exit identities at a finite-union starting pole -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov
open Parabolic
open scoped ENNReal

/- Both actual union measure identities hold on every certified nested component. -/
theorem strip_nested_union_point
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam } (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (H1 H2 : FiniteIntervalUnion)
    (hsub : H1.carrier ⊆ H2.carrier) (sMinus T : ℝ)
    (e : FiniteUnionPole H1 (T : WithTop ℝ)) (he : sMinus < e.1.time) :
    finiteUnionGreen hH hLE hlam hLam A H2 T
      (finiteUnionNestedPoleInclusion H1 H2 hsub T e) =
      finiteUnionGreen hH hLE hlam hLam A H1 T e +
        (finiteUnionPointRestartPoles hH hLE hlam hLam A H1 H2 sMinus T e).bind
          (finiteUnionGreen hH hLE hlam hLam A H2 T) ∧
    finiteUnionExit hH hLE hlam hLam A H2 T
      (finiteUnionNestedPoleInclusion H1 H2 hsub T e) =
      (finiteUnionExit hH hLE hlam hLam A H1 T e).restrict (finiteUnionExitSet H2 sMinus T) +
        (finiteUnionPointRestartPoles hH hLE hlam hLam A H1 H2 sMinus T e).bind
          (finiteUnionExit hH hLE hlam hLam A H2 T) := by
  let i := finiteUnionPoleIndex H1 T e
  let ep := finiteUnionComponentPole H1 T e
  obtain ⟨j, hij⟩ := H1.component_contained H2 hsub i
  have hh :
      let ep := componentPoleInclusion H1 i T ep
          let eb := finiteUnionNestedPoleInclusion H1 H2 hsub T ep
          let τ := finiteUnionPointRestartPoles hH hLE hlam hLam A H1 H2 sMinus T ep
          finiteUnionGreen hH hLE hlam hLam A H2 T eb =
            finiteUnionGreen hH hLE hlam hLam A H1 T ep +
              τ.bind (finiteUnionGreen hH hLE hlam hLam A H2 T) ∧
          finiteUnionExit hH hLE hlam hLam A H2 T eb =
            (finiteUnionExit hH hLE hlam hLam A H1 T ep).restrict
              (finiteUnionExitSet H2 sMinus T) + τ.bind (finiteUnionExit hH hLE hlam hLam A H2 T) := by
    let e := ep
    dsimp only
    let e2 := nestedPoleInclusion (H1.component i) (H2.component j) hij T e
    have hp : finiteUnionNestedPoleInclusion H1 H2 hsub T (componentPoleInclusion H1 i T e) =
        componentPoleInclusion H2 j T
          (nestedPoleInclusion (H1.component i) (H2.component j) hij T e) := by
        apply Subtype.ext
        rfl


    have hGb := (congrArg (finiteUnionGreen hH hLE hlam hLam A H2 T) hp).trans
      (finiteUnionGreen_component hH hLE hlam hLam A H2 j T e2)
    have hOb := (congrArg (finiteUnionExit hH hLE hlam hLam A H2 T) hp).trans
      (finiteUnionExit_component hH hLE hlam hLam A H2 j T e2)
    have hGs := finiteUnionGreen_component hH hLE hlam hLam A H1 i T e
    have hOs := finiteUnionExit_component hH hLE hlam hLam A H1 i T e
    have hGτ := nested_restart_bind_component hH hLE hlam hLam A H1 H2 i j hij sMinus T e he
      (finiteUnionGreen hH hLE hlam hLam A H2 T)
      (finiteUnionGreen_measurable hH hLE hlam hLam A H2 T)
      (stripGreen hH hLE hlam hLam A (H2.component j) T)
      (fun ep => finiteUnionGreen_component hH hLE hlam hLam A H2 j T ep)
    have hOτ := nested_restart_bind_component hH hLE hlam hLam A H1 H2 i j hij sMinus T e he
      (finiteUnionExit hH hLE hlam hLam A H2 T)
      (finiteUnionExit_measurable hH hLE hlam hLam A H2 T)
      (stripExit hH hLE hlam hLam A (H2.component j) T)
      (fun ep => finiteUnionExit_component hH hLE hlam hLam A H2 j T ep)
    have _h_xinl_0 : (stripExit hH hLE hlam hLam A (H1.component i) T e).restrict (finiteUnionExitSet H2 sMinus T) = (stripExit hH hLE hlam hLam A (H1.component i) T e).restrict (reconstructionExit (H2.component j) sMinus T) := by
      apply Measure.restrict_congr_set
      filter_upwards [nested_exit_ae_larger_slab hH hLE hlam hLam A
        (H1.component i) (H2.component j) hij sMinus T e he.le] with p hp
      exact propext (H2.exit_on_component_closure j sMinus T p hp.2.2)
    have houter := (congrArg (fun μ : Measure Point =>
      μ.restrict (finiteUnionExitSet H2 sMinus T)) hOs).trans
        _h_xinl_0
    constructor
    · exact hGb.trans ((nestedIntervalGreen_identity hH hLE hlam hLam A
        (H1.component i) (H2.component j) hij sMinus T e he).trans
          (congrArg₂ (· + ·) hGs.symm hGτ.symm))
    · have _h_xinl_0 : stripExit hH hLE hlam hLam A (H2.component j) T (nestedPoleInclusion (H1.component i) (H2.component j) hij T e) =
        (stripExit hH hLE hlam hLam A (H1.component i) T e).restrict (reconstructionExit (H2.component j) sMinus T) +
          nestedIntervalRestartExit hH hLE hlam hLam A (H1.component i) (H2.component j) sMinus T e := by
        let H1 := (H1.component i)
        let H2 := (H2.component j)
        apply nested_physical_measure_eq univ isOpen_univ
          (Filter.Eventually.of_forall (fun _ => mem_univ _))
          (Filter.Eventually.of_forall (fun _ => mem_univ _))
        intro f _ _
        rw [integral_add_measure (nestedProbe_integrable A f _)
          (nestedProbe_integrable A f _)]
        obtain ⟨u, hc, hb, htrace, hrep, hid⟩ : ∃ u : Point → ℝ,
            ContinuousOn u (reconstructionClosedSlab H2 sMinus T) ∧
            (∃ C : ℝ, 0 ≤ C ∧ ∀ p ∈ reconstructionClosedSlab H2 sMinus T, |u p| ≤ C) ∧
            EqOn u (exitProbePhysical f) (reconstructionExit H2 (sMinus - 1) T) ∧
            (∀ ep : StripPole H2 (T : WithTop ℝ), sMinus ≤ ep.1.time →
              u ep.1 = ∫ p, exitProbePhysical f p ∂stripExit hH hLE hlam hLam A H2 T ep) ∧
            (∫ p, exitProbePhysical f p ∂stripExit hH hLE hlam hLam A H2 T
              (nestedPoleInclusion H1 H2 hij T e)) =
                ∫ p, u p ∂stripExit hH hLE hlam hLam A H1 T e := by
          have ht : e.1.time < T := WithTop.coe_lt_coe.mp e.2.1
          obtain ⟨u, hu, hop, hc, ⟨C, hC, hb⟩, htrace, hrep⟩ : ∃ u : Point → ℝ,
              IsKineticC112On u (reconstructionStrip H2 (sMinus - 1) T) ∧
              (∀ p ∈ reconstructionStrip H2 (sMinus - 1) T, forwardScalarOperator A.a u p = 0) ∧
              ContinuousOn u (reconstructionClosedSlab H2 sMinus T) ∧
              (∃ C : ℝ, 0 ≤ C ∧ ∀ p ∈ reconstructionClosedSlab H2 sMinus T, |u p| ≤ C) ∧
              EqOn u (exitProbePhysical f) (reconstructionExit H2 (sMinus - 1) T) ∧
              (∀ e : StripPole H2 (T : WithTop ℝ), sMinus ≤ e.1.time →
                u e.1 = ∫ p, exitProbePhysical f p ∂stripExit hH hLE hlam hLam A H2 T e) := by
            have hT := (he.trans ht)
            let E := stripEvolution hH hLE hlam hLam A H2
            have hE := stripEvolution_spec hH hLE hlam hLam A H2
            have hphi := exitProbePhysical_isKineticC112On f
              (reconstructionStrip H2 (sMinus - 1) T) (isOpen_reconstructionStrip H2 _ T)
            obtain ⟨M, hM⟩ := exitProbePhysical_bounded_source A f
            have hb : ∃ M : ℝ, ∀ p ∈ reconstructionStrip H2 (sMinus - 1) T,
                |exitProbePhysical f p| ≤ M ∧
                  |forwardScalarOperator A.a (exitProbePhysical f) p| ≤ M := ⟨M, fun p _ => hM p⟩
            obtain ⟨u, hform, hu, hop, hc, htrace⟩ := strip_bounded_source_reconstruction
              hH hlam hLam A H2 E hE (sMinus - 1) T (exitProbePhysical f) hphi
                (exitProbePhysical_continuous_compact f).1.continuousOn hb
            let p : Point := ⟨sMinus, 0, fun _ => (H2.lo + H2.hi) / 2⟩
            have hv : p.velocity 0 ∈ H2.carrier := by
              change H2.lo < (H2.lo + H2.hi) / 2 ∧ (H2.lo + H2.hi) / 2 < H2.hi
              constructor <;> linarith [H2.ordered]
            let e : StripPole H2 (T : WithTop ℝ) := ⟨p, WithTop.coe_lt_coe.mpr hT, hv⟩
            have he : sMinus - 1 < e.1.time := by change sMinus - 1 < sMinus; linarith
            have hbound := reconstruction_uniform_bound H2 E A (sMinus - 1) T e he
              (exitProbePhysical f) u hphi hb hform hc
            refine ⟨u, nested_raw_isKineticC112On (isOpen_reconstructionStrip H2 _ T) hu,
              hop, hc.mono (reconstructionClosedSlab_subset_strip_union_exit H2 he),
              hbound, htrace, ?_⟩
            intro ep hep
            have hepl : sMinus - 1 < ep.1.time := by linarith
            have hvalue := stripExitOfRealization_probe_integral hH hlam hLam A H2 E hE T ep f
            have hformula := hform ep hepl
            rw [integral_neg] at hformula
            change (∫ p, exitProbePhysical f p ∂stripExit hH hLE hlam hLam A H2 T ep) =
              exitProbePhysical f ep.1 + ∫ p, forwardScalarOperator A.a (exitProbePhysical f) p
                ∂stripGreenOfKernel H2 E.2 T ep at hvalue
            linarith
          have hi : reconstructionStrip H1 sMinus T ⊆ reconstructionStrip H2 (sMinus - 1) T := by
            intro p hp
            exact ⟨by linarith [hp.1], hp.2.1, hij hp.2.2⟩
          have hsmall : IsKineticC112On u (reconstructionStrip H1 sMinus T) :=
            ⟨hu.1.mono hi, fun p hp => hu.2.1 p (hi hp),
              fun p hp => hu.2.2.1 p (hi hp), fun p hp => hu.2.2.2.1 p (hi hp),
              hu.2.2.2.2.1.mono hi, hu.2.2.2.2.2.1.mono hi,
              hu.2.2.2.2.2.2.1.mono hi, hu.2.2.2.2.2.2.2.mono hi⟩
          have hclosed : reconstructionStrip H1 sMinus T ∪ reconstructionExit H1 sMinus T ⊆
              reconstructionClosedSlab H2 sMinus T := by
            intro p hp
            have hh := nested_strip_union_exit_subset_closed H1 H2 hij sMinus T hp
            refine ⟨?_, hh⟩
            rcases hp with hp | hp
            · exact hp.1.le
            · rcases hp with hp | hp
              · rw [hp.1]; exact (he.trans ht).le
              · exact hp.1.le
          have hbound : ∃ M : ℝ, ∀ p ∈ reconstructionStrip H1 sMinus T,
              |u p| ≤ M ∧ |forwardScalarOperator A.a u p| ≤ M := by
            refine ⟨C, fun p hp => ⟨hb p (hclosed (Or.inl hp)), ?_⟩⟩
            rw [hop p (hi hp), abs_zero]
            exact hC
          have hid := strip_identity_C112 hH hLE hlam hLam A H1 sMinus T (he.trans ht)
            e he u hsmall (hc.mono hclosed) hbound
          have hz : (fun p => forwardScalarOperator A.a u p) =ᵐ[
              stripGreen hH hLE hlam hLam A H1 T e] fun _ => 0 := by
            filter_upwards [stripGreenOfKernel_ae_mem_stripPast H1
              (stripEvolution hH hLE hlam hLam A H1).2 T e,
              reconstruction_green_ae_time_gt H1 (stripEvolution hH hLE hlam hLam A H1).2 T e]
              with p hp hpt
            apply hop
            exact hi ⟨he.trans hpt, hp⟩
          rw [integral_congr_ae hz, integral_zero, sub_zero] at hid
          refine ⟨u, hc, ⟨C, hC, hb⟩, htrace, hrep, ?_⟩
          rw [← hrep (nestedPoleInclusion H1 H2 hij T e) he.le]
          exact hid
        let μ := stripExit hH hLE hlam hLam A H1 T e
        let τ := nestedIntervalRestartPoles hH hLE hlam hLam A H1 H2 sMinus T e
        have hi : Integrable u μ := by
          have hs := (nested_exit_ae_larger_slab hH hLE hlam hLam A H1 H2 hij sMinus T e he.le)
          obtain ⟨C, -, hC⟩ := hb
          have hμ := Measure.restrict_eq_self_of_ae_mem hs
          have _h_xinl_0 : IsClosed (reconstructionClosedSlab H2 sMinus T) := by
            have hv : Continuous (fun p : Point => p.velocity 0) :=
              (continuous_apply 0).comp continuous_velocity
            exact (isClosed_le continuous_const continuous_time).inter
              ((isClosed_le continuous_time continuous_const).inter (isClosed_Icc.preimage hv))
          have hm := hc.aestronglyMeasurable _h_xinl_0.measurableSet
            (μ := μ)
          rw [hμ] at hm
          apply Integrable.mono' (integrable_const C) hm
          filter_upwards [hs] with p hp
          rw [Real.norm_eq_abs]
          exact hC p hp
        have _h_xinl_0 : stripExit hH hLE hlam hLam A H1 T e = (stripExit hH hLE hlam hLam A H1 T e).restrict (reconstructionExit H2 sMinus T) + (stripExit hH hLE hlam hLam A H1 T e).restrict (nestedIntervalInternalExit H1 H2 sMinus T) := by
          let μ := stripExit hH hLE hlam hLam A H1 T e
          have hm : ∀ᵐ p ∂μ, p ∈ reconstructionExit H1 sMinus T := by
            rw [ae_iff]
            exact (strip_exit_probability hH hLE hlam hLam A H1 sMinus T e he.le).2.1
          have heq : (reconstructionExit H2 sMinus T)ᶜ =ᵐ[μ]
              nestedIntervalInternalExit H1 H2 sMinus T := by
            filter_upwards [hm] with p hp
            have _h_inl_7 : p ∉ reconstructionExit H2 sMinus T ↔ p ∈ nestedIntervalInternalExit H1 H2 sMinus T := by
                have hc := nested_strip_union_exit_subset_closed H1 H2 hij sMinus T (Or.inr hp)
                constructor
                · intro hn
                  rcases hp with hp | hp
                  · exact False.elim (hn (Or.inl ⟨hp.1, hc.2⟩))
                  · refine ⟨hp.1, hp.2.1, hp.2.2, ?_⟩
                    change H2.lo < p.velocity 0 ∧ p.velocity 0 < H2.hi
                    have hl : p.velocity 0 ≠ H2.lo := fun hl => hn (Or.inr ⟨hp.1, hp.2.1, Or.inl hl⟩)
                    have hh : p.velocity 0 ≠ H2.hi := fun hh => hn (Or.inr ⟨hp.1, hp.2.1, Or.inr hh⟩)
                    exact ⟨lt_of_le_of_ne hc.2.1 hl.symm, lt_of_le_of_ne hc.2.2 hh⟩
                · intro hs hn
                  rcases hn with hn | hn
                  · exact (ne_of_lt hs.2.1) hn.1
                  · rcases hn.2.2 with hv | hv
                    · exact (ne_of_gt hs.2.2.2.1) hv
                    · exact (ne_of_lt hs.2.2.2.2) hv



            exact propext _h_inl_7
          have hs := μ.restrict_add_restrict_compl (measurableSet_nestedIntervalExit H2 sMinus T)
          rw [Measure.restrict_congr_set heq] at hs
          exact hs.symm
        have hsplit := congrArg (fun ρ : Measure Point => ∫ p, u p ∂ρ)
          _h_xinl_0
        have hsum := integral_add_measure
          (hi.restrict (s := reconstructionExit H2 sMinus T))
          (hi.restrict (s := nestedIntervalInternalExit H1 H2 sMinus T))
        have houter : (∫ p, u p ∂μ.restrict (reconstructionExit H2 sMinus T)) =
            ∫ p, exitProbePhysical f p ∂μ.restrict (reconstructionExit H2 sMinus T) := by
          apply integral_congr_ae
          filter_upwards [ae_restrict_mem (measurableSet_nestedIntervalExit H2 sMinus T)] with p hp
          apply htrace
          rcases hp with hp | hp
          · exact Or.inl hp
          · exact Or.inr ⟨by linarith [hp.1], hp.2⟩
        have hmap : (∫ p, u p ∂μ.restrict (nestedIntervalInternalExit H1 H2 sMinus T)) =
            ∫ ep, u ep.1 ∂τ := by
          rw [← nestedIntervalRestartPoles_map hH hLE hlam hLam A H1 H2 sMinus T e]
          exact (MeasurableEmbedding.subtype_coe (measurableSet_nestedIntervalPole H2 T)).integral_map u
        have hvalues : (∫ ep, u ep.1 ∂τ) = ∫ ep,
            ∫ p, exitProbePhysical f p ∂stripExit hH hLE hlam hLam A H2 T ep ∂τ := by
          apply integral_congr_ae
          have _h_xinl_0 : ∀ᵐ ep ∂nestedIntervalRestartPoles hH hLE hlam hLam A H1 H2 sMinus T e,
            sMinus < ep.1.time := by
              have ht : ∀ᵐ p ∂(stripExit hH hLE hlam hLam A H1 T e).restrict
                  (nestedIntervalInternalExit H1 H2 sMinus T), sMinus < p.time := by
                filter_upwards [ae_restrict_mem
                  (measurableSet_nestedIntervalInternalExit H1 H2 sMinus T)] with p hp
                exact hp.1
              rw [← nestedIntervalRestartPoles_map hH hLE hlam hLam A H1 H2 sMinus T e] at ht
              exact ((MeasurableEmbedding.subtype_coe (measurableSet_nestedIntervalPole H2 T)).ae_map_iff).mp ht


          filter_upwards [_h_xinl_0] with ep hep
          exact hrep ep hep.le
        have hbind := nested_integral_bind τ (stripExit hH hLE hlam hLam A H2 T)
          (stripExit_measurable hH hLE hlam hLam A H2 T) (exitProbePhysical f)
          (nestedProbe_integrable A f
            (nestedIntervalRestartExit hH hLE hlam hLam A H1 H2 sMinus T e))
        exact hid.trans (hsplit.trans (hsum.trans (congrArg₂ (· + ·) houter
          (hmap.trans (hvalues.trans hbind.symm)))))
      exact hOb.trans (_h_xinl_0.trans
          (congrArg₂ (· + ·) houter.symm hOτ.symm))
  have heq : componentPoleInclusion H1 i T ep = e := by apply Subtype.ext; rfl
  dsimp only at hh
  rw [heq] at hh
  exact hh

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
