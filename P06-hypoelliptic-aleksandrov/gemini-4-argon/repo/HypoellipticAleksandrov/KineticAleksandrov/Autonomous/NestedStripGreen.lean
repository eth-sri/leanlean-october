module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.NestedStripGreenTests
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.NestedStripMeasureExt
import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.NestedStripIntervalRestart
import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.GreenTestExtensionCanonical
import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.NestedStripRepresentation
import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.NestedStripRestartPoles
import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.NestedStripSourceIdentity
import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.BoundedSourceWeakAssembly
import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.NestedStripBoundary

/-! # The exact Green measure decomposition for nested physical velocity intervals -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov
open SectionTwo TheoremA Evolution

/- The actual larger Green measure is the smaller Green plus the actual internal restart Green. -/
theorem nestedIntervalGreen_identity
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam } (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (H1 H2 : Interval)
    (hsub : H1.carrier ⊆ H2.carrier) (sMinus T : ℝ)
    (e : StripPole H1 (T : WithTop ℝ)) (he : sMinus < e.1.time) :
    stripGreen hH hLE hlam hLam A H2 T (nestedPoleInclusion H1 H2 hsub T e) =
      stripGreen hH hLE hlam hLam A H1 T e +
        nestedIntervalRestartGreen hH hLE hlam hLam A H1 H2 sMinus T e := by
  let D := stripPast H2 T
  have hs (ep : StripPole H2 (T : WithTop ℝ)) :
      ∀ᵐ p ∂stripGreen hH hLE hlam hLam A H2 T ep, p ∈ D :=
    stripGreenOfKernel_ae_mem_stripPast H2 (stripEvolution hH hLE hlam hLam A H2).2 T ep
  have hsmall : ∀ᵐ p ∂stripGreen hH hLE hlam hLam A H1 T e, p ∈ D := by
    filter_upwards [stripGreenOfKernel_ae_mem_stripPast H1
      (stripEvolution hH hLE hlam hLam A H1).2 T e] with p hp
    exact ⟨hp.1, hsub hp.2⟩
  have hrestart : ∀ᵐ p ∂nestedIntervalRestartGreen hH hLE hlam hLam A H1 H2 sMinus T e,
      p ∈ D := by
    rw [ae_iff]
    unfold nestedIntervalRestartGreen
    refine (Measure.bind_apply (m := nestedIntervalRestartPoles hH hLE hlam hLam A
      H1 H2 sMinus T e) (isOpen_stripPast H2 T).measurableSet.compl
      (Measure.measurable_measure.mpr (fun B hB =>
        stripGreen_measurable_apply hH hLE hlam hLam A H2 T B hB)).aemeasurable).trans ?_
    apply lintegral_eq_zero_of_ae_eq_zero
    exact Filter.Eventually.of_forall (fun ep => ae_iff.mp (hs ep))
  apply nested_physical_measure_eq D (isOpen_stripPast H2 T)
    (hs (nestedPoleInclusion H1 H2 hsub T e))
  · rw [ae_iff, Measure.add_apply, ae_iff.mp hsmall, ae_iff.mp hrestart]
    exact zero_add 0
  · intro f hfs hfn
    rw [integral_add_measure (nestedProbe_integrable A f _)
      (nestedProbe_integrable A f _)]
    let E := stripEvolution hH hLE hlam hLam A H2
    let u := nestedSourcePotential H2 E T f
    let τ := nestedIntervalRestartPoles hH hLE hlam hLam A H1 H2 sMinus T e
    have hid : (∫ p, exitProbePhysical f p ∂stripGreen hH hLE hlam hLam A H2 T
      (nestedPoleInclusion H1 H2 hsub T e)) =
      (∫ p, exitProbePhysical f p ∂stripGreen hH hLE hlam hLam A H1 T e) +
      ∫ p, nestedSourcePotential H2 (stripEvolution hH hLE hlam hLam A H2) T f p
        ∂(stripExit hH hLE hlam hLam A H1 T e).restrict
          (nestedIntervalInternalExit H1 H2 sMinus T) := by
      let u := nestedSourcePotential H2 (stripEvolution hH hLE hlam hLam A H2) T f
      have hp : ∀ᵐ p ∂stripExit hH hLE hlam hLam A H1 T e,
          p ∈ reconstructionExit H1 sMinus T := by
        rw [ae_iff]
        exact (strip_exit_probability hH hLE hlam hLam A H1 sMinus T e he.le).2.1
      have heq : u =ᵐ[stripExit hH hLE hlam hLam A H1 T e]
          (nestedIntervalInternalExit H1 H2 sMinus T).indicator u := by
        filter_upwards [hp] with p hp
        by_cases hm : p ∈ nestedIntervalInternalExit H1 H2 sMinus T
        · rw [indicator_of_mem hm]
        · rw [indicator_of_notMem hm]
          exact nestedSourcePotential_zero_outer hH hlam hLam A H1 H2 hsub _
            (stripEvolution_spec hH hLE hlam hLam A H2) sMinus T f hfn hfs p hp hm
      have hid : (∫ p, exitProbePhysical f p ∂stripGreen hH hLE hlam hLam A H2 T
          (nestedPoleInclusion H1 H2 hsub T e)) =
          (∫ p, exitProbePhysical f p ∂stripGreen hH hLE hlam hLam A H1 T e) +
          ∫ p, nestedSourcePotential H2 (stripEvolution hH hLE hlam hLam A H2) T f p
            ∂stripExit hH hLE hlam hLam A H1 T e := by
        let E := stripEvolution hH hLE hlam hLam A H2
        have hE := stripEvolution_spec hH hLE hlam hLam A H2
        let u := nestedSourcePotential H2 E T f
        obtain ⟨⟨C, -, hC⟩, hu, hop⟩ :=
          nestedSourcePotential_regular_source hH hlam hLam A H2 E hE T f hfn hfs
        have hc := (nestedSourcePotential_continuous_zero_exit
          hH hlam hLam A H2 E hE T f hfn hfs).1
        have hi : reconstructionStrip H1 sMinus T ⊆
            {p | p.time < T ∧ p.velocity 0 ∈ H2.carrier} :=
          fun _ hp => ⟨hp.2.1, hsub hp.2.2⟩
        obtain ⟨M, hM⟩ := exitProbePhysical_bounded_source A f
        have hb : ∃ M : ℝ, ∀ p ∈ reconstructionStrip H1 sMinus T,
            |u p| ≤ M ∧ |forwardScalarOperator A.a u p| ≤ M := by
          refine ⟨max C M, fun p hp => ⟨(hC p).trans (le_max_left _ _), ?_⟩⟩
          rw [hop p (hi hp).1 (hi hp).2, abs_neg]
          exact (hM p).1.trans (le_max_right _ _)
        have ht : e.1.time < T := WithTop.coe_lt_coe.mp e.2.1
        have hsmall : Parabolic.IsKineticC112On u (reconstructionStrip H1 sMinus T) :=
          ⟨hu.1.mono hi, fun p hp => hu.2.1 p (hi hp),
            fun p hp => hu.2.2.1 p (hi hp), fun p hp => hu.2.2.2.1 p (hi hp),
            hu.2.2.2.2.1.mono hi, hu.2.2.2.2.2.1.mono hi,
            hu.2.2.2.2.2.2.1.mono hi, hu.2.2.2.2.2.2.2.mono hi⟩
        have hid := strip_identity_C112 hH hLE hlam hLam A H1 sMinus T
          (he.trans ht) e he u hsmall
          (hc.mono (nested_strip_union_exit_subset_closed H1 H2 hsub sMinus T)) hb
        have hg : (fun p => forwardScalarOperator A.a u p) =ᵐ[
            stripGreen hH hLE hlam hLam A H1 T e] fun p => -exitProbePhysical f p := by
          filter_upwards [stripGreenOfKernel_ae_mem_stripPast H1
            (stripEvolution hH hLE hlam hLam A H1).2 T e] with p hp
          exact hop p hp.1 (hsub hp.2)
        rw [integral_congr_ae hg, integral_neg] at hid
        have hr := nestedSourcePotential_eq_green A H2 E T f
          (nestedPoleInclusion H1 H2 hsub T e)
        change u e.1 = ∫ p, exitProbePhysical f p ∂stripGreen hH hLE hlam hLam A H2 T
          (nestedPoleInclusion H1 H2 hsub T e) at hr
        rw [← hr]
        linarith
      change _ = _ + ∫ p, u p ∂stripExit hH hLE hlam hLam A H1 T e at hid
      rw [integral_congr_ae heq,
        integral_indicator (measurableSet_nestedIntervalInternalExit H1 H2 sMinus T)] at hid
      exact hid
    have hmap : (∫ p, u p ∂(stripExit hH hLE hlam hLam A H1 T e).restrict
        (nestedIntervalInternalExit H1 H2 sMinus T)) = ∫ ep, u ep.1 ∂τ := by
      rw [← nestedIntervalRestartPoles_map hH hLE hlam hLam A H1 H2 sMinus T e]
      have _h_xinl_0 : Measurable (nestedSourcePotential H2 E T f) := by
        exact (measurable_duhamelPotential E.2 (intervalDomain_measurable H2) continuous_const T
          (exitProbePhysical f ∘ sectionTwoPoint)
          ((exitProbePhysical_continuous_compact f).1.measurable.comp
            (continuous_sectionTwoPoint 1).measurable)).comp
              (continuous_sectionTwoPoint 1).measurable
      exact integral_map measurable_subtype_coe.aemeasurable
        _h_xinl_0.aestronglyMeasurable
    have hrep : (fun ep : StripPole H2 (T : WithTop ℝ) => u ep.1) =
        fun ep => ∫ p, exitProbePhysical f p ∂stripGreen hH hLE hlam hLam A H2 T ep := by
      funext ep
      exact nestedSourcePotential_eq_green A H2 E T f ep
    have hb := nested_integral_bind τ (stripGreen hH hLE hlam hLam A H2 T)
      (Measure.measurable_measure.mpr (fun B hB =>
        stripGreen_measurable_apply hH hLE hlam hLam A H2 T B hB))
      (exitProbePhysical f)
      (nestedProbe_integrable A f
        (nestedIntervalRestartGreen hH hLE hlam hLam A H1 H2 sMinus T e))
    change _ = _ + ∫ p, u p ∂(stripExit hH hLE hlam hLam A H1 T e).restrict
      (nestedIntervalInternalExit H1 H2 sMinus T) at hid
    rw [hmap, hrep, ← hb] at hid
    exact hid

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
