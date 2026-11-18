module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.ExitFunctional
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.ExitMeasureRiesz
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.StripGreenBorel
import HypoellipticAleksandrov.KineticAleksandrov.Evolution.JointQueryBorelDense
import Mathlib.MeasureTheory.Measure.GiryMonad
import HypoellipticAleksandrov.KineticAleksandrov.Evolution.DomainDominationMeasure
import Mathlib.MeasureTheory.Integral.Bochner.Set

@[expose] public noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov SectionTwo TheoremA Evolution
open scoped CompactlySupported ENNReal

/-- The closed exit carrier inherits local compactness from kinetic spacetime. -/
instance stripClosedExit_locallyCompactSpace (H : Interval) (T : ℝ) :
    LocallyCompactSpace (stripClosedExit H T) := by
  let : LocallyCompactSpace Point :=
    (KineticPoint.homeomorphProd 1).isClosedEmbedding.locallyCompactSpace
  exact (isClosed_stripClosedExit H T).locallyCompactSpace

/-- The closed exit carrier has a countable topological basis. -/
instance stripClosedExit_secondCountableTopology (H : Interval) (T : ℝ) :
    SecondCountableTopology (stripClosedExit H T) := by
  let : SecondCountableTopology Point := (KineticPoint.homeomorphProd 1).secondCountableTopology
  infer_instance

/-- There is exactly one subprobability measure with the full boundary-functional action. -/
theorem existsUnique_strip_exit
    (hH : HormanderHypoellipticityStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (H : Interval) (E : StripEvolution H)
    (hE : IsStripEvolution A H E) (T : ℝ) (e : StripPole H (T : WithTop ℝ)) :
    ∃! μ : Measure (stripClosedExit H T), μ univ ≤ 1 ∧
      ∀ f : C_c(stripClosedExit H T, ℝ), ∫ p, f p ∂μ =
        stripBoundaryFunctional hH hlam hLam A H E hE T e f :=
  existsUnique_boundaryFunctional_measure (stripBoundaryFunctional hH hlam hLam A H E hE T e)
    (stripBoundaryFunctional_spec hH hlam hLam A H E hE T e).1

/-- The exit measure is chosen only from the proved unique full compact-test characterization. -/
def stripExitMeasureOnBoundary
    (hH : HormanderHypoellipticityStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (H : Interval) (E : StripEvolution H)
    (hE : IsStripEvolution A H E) (T : ℝ) (e : StripPole H (T : WithTop ℝ)) :
    Measure (stripClosedExit H T) :=
  (existsUnique_strip_exit hH hlam hLam A H E hE T e).exists.choose

/-- Full characterization of the unique exit measure on its closed boundary carrier. -/
theorem stripExitMeasureOnBoundary_spec
    (hH : HormanderHypoellipticityStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (H : Interval) (E : StripEvolution H)
    (hE : IsStripEvolution A H E) (T : ℝ) (e : StripPole H (T : WithTop ℝ)) :
    stripExitMeasureOnBoundary hH hlam hLam A H E hE T e univ ≤ 1 ∧
      ∀ f : C_c(stripClosedExit H T, ℝ),
        ∫ p, f p ∂stripExitMeasureOnBoundary hH hlam hLam A H E hE T e =
          stripBoundaryFunctional hH hlam hLam A H E hE T e f :=
  (existsUnique_strip_exit hH hlam hLam A H E hE T e).exists.choose_spec

/-- Each uniquely characterized exit measure is finite. -/
instance stripExitMeasureOnBoundary_isFiniteMeasure
    (hH : HormanderHypoellipticityStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (H : Interval) (E : StripEvolution H)
    (hE : IsStripEvolution A H E) (T : ℝ) (e : StripPole H (T : WithTop ℝ)) :
    IsFiniteMeasure (stripExitMeasureOnBoundary hH hlam hLam A H E hE T e) :=
  ⟨lt_of_le_of_lt (stripExitMeasureOnBoundary_spec hH hlam hLam A H E hE T e).1 (by simp)⟩

/-- The physical exit measure is the image of that unique boundary measure. -/
def stripExitOfRealization
    (hH : HormanderHypoellipticityStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (H : Interval) (E : StripEvolution H)
    (hE : IsStripEvolution A H E) (T : ℝ) (e : StripPole H (T : WithTop ℝ)) : Measure Point :=
  (stripExitMeasureOnBoundary hH hlam hLam A H E hE T e).map Subtype.val

/-- The physical exit measure is finite. -/
instance stripExitOfRealization_isFiniteMeasure
    (hH : HormanderHypoellipticityStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (H : Interval) (E : StripEvolution H)
    (hE : IsStripEvolution A H E) (T : ℝ) (e : StripPole H (T : WithTop ℝ)) :
    IsFiniteMeasure (stripExitOfRealization hH hlam hLam A H E hE T e) := by
  unfold stripExitOfRealization
  infer_instance


/-- The physical measure is supported on the full closed terminal/lateral exit carrier. -/
theorem stripExitOfRealization_compl_closedExit
    (hH : HormanderHypoellipticityStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (H : Interval) (E : StripEvolution H)
    (hE : IsStripEvolution A H E) (T : ℝ) (e : StripPole H (T : WithTop ℝ)) :
    stripExitOfRealization hH hlam hLam A H E hE T e (stripClosedExit H T)ᶜ = 0 := by
  unfold stripExitOfRealization
  rw [Measure.map_apply measurable_subtype_coe
    (isClosed_stripClosedExit H T).measurableSet.compl]
  have heq : (Subtype.val : stripClosedExit H T → Point) ⁻¹' (stripClosedExit H T)ᶜ = ∅ := by
    ext p
    simp only [mem_preimage, mem_compl_iff, mem_empty_iff_false, iff_false]
    exact not_not.mpr p.2
  rw [heq, measure_empty]

/-- Actual homogeneous probe values are exactly the physical exit integrals. -/
theorem stripExitOfRealization_probe_integral
    (hH : HormanderHypoellipticityStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (H : Interval) (E : StripEvolution H)
    (hE : IsStripEvolution A H E) (T : ℝ) (e : StripPole H (T : WithTop ℝ))
    (f : exitProbeSubmodule) :
    ∫ p, exitProbePhysical f p ∂stripExitOfRealization hH hlam hLam A H E hE T e =
      exitProbeValue A H E T e f := by
  unfold stripExitOfRealization
  rw [integral_map measurable_subtype_coe.aemeasurable
    (exitProbePhysical_continuous_compact f).1.measurable.aestronglyMeasurable]
  change (∫ p, exitProbeCcLinear H T f p
    ∂stripExitMeasureOnBoundary hH hlam hLam A H E hE T e) = _
  rw [(stripExitMeasureOnBoundary_spec hH hlam hLam A H E hE T e).2,
    (stripBoundaryFunctional_spec hH hlam hLam A H E hE T e).2]
  rfl






/-- The canonical exit measure uses the independently characterized autonomous evolution. -/
def stripExit
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (H : Interval) (T : ℝ)
    (e : StripPole H (T : WithTop ℝ)) : Measure Point :=
  stripExitOfRealization hH hlam hLam A H (stripEvolution hH hLE hlam hLam A H)
    (stripEvolution_spec hH hLE hlam hLam A H) T e

/-- Each canonical exit measure is finite. -/
instance stripExit_isFiniteMeasure
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (H : Interval) (T : ℝ)
    (e : StripPole H (T : WithTop ℝ)) : IsFiniteMeasure (stripExit hH hLE hlam hLam A H T e) := by
  unfold stripExit
  infer_instance

/-- The canonical family has Borel dependence on its valid pole. -/
theorem stripExit_measurable
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (H : Interval) (T : ℝ) :
    Measurable (stripExit hH hLE hlam hLam A H T)  := by
  have stripExitOfRealization_measurable (E : StripEvolution H) (hE : IsStripEvolution A H E) :
      Measurable (fun e =>
      stripExitOfRealization hH hlam hLam A H E hE T e) := by
    have exitProbeValue_measurable (f : exitProbeSubmodule) :
        Measurable (fun e => exitProbeValue A H E T e f) := by
      have reconstruction_green_potential_measurable (K : MovingFiberKernel (intervalDomain H) (fun _ => 0)) (g : BoundedBorel Point) :
          Measurable (fun e => stripPotentialOfKernel H K T g e) := by
        have hΓ : Measurable (fun e => stripGreenOfKernel H K T e) :=
          Measure.measurable_measure.mpr (stripGreenOfKernel_measurable_apply H K T)
        have heq : (fun e => stripPotentialOfKernel H K T g e) =
            fun e => (∫⁻ p, ENNReal.ofReal (g p) ∂stripGreenOfKernel H K T e).toReal -
              (∫⁻ p, ENNReal.ofReal (-g p) ∂stripGreenOfKernel H K T e).toReal := by
          funext e
          exact integral_eq_lintegral_pos_part_sub_lintegral_neg_part
            (stripGreen_integrable_boundedBorel H K T e g)
        rw [heq]
        exact ((Measure.measurable_lintegral g.measurable.ennreal_ofReal).comp hΓ).ennreal_toReal.sub ((Measure.measurable_lintegral g.measurable.neg.ennreal_ofReal).comp hΓ).ennreal_toReal
      exact ((exitProbePhysical_continuous_compact f).1.measurable.comp measurable_subtype_coe).add
        (reconstruction_green_potential_measurable E.2 (exitProbeOperatorDatum A f))
    have stripExitOfRealization_mass_le_one (e : StripPole H (T : WithTop ℝ)) :
        stripExitOfRealization hH hlam hLam A H E hE T e univ ≤ 1 := by
      unfold stripExitOfRealization
      rw [Measure.map_apply measurable_subtype_coe MeasurableSet.univ,
        preimage_univ]
      exact (stripExitMeasureOnBoundary_spec hH hlam hLam A H E hE T e).1
    let Ω := stripExitOfRealization hH hlam hLam A H E hE T
    let ν (e : StripPole H (T : WithTop ℝ)) : Measure (EvolutionVec 1) :=
      (Ω e).map reconstructionPhysicalHomeomorph.symm
    have hν : ∀ e, IsFiniteMeasure (ν e) := fun e => by dsimp [ν, Ω]; infer_instance
    let (e : StripPole H (T : WithTop ℝ)) : IsFiniteMeasure (ν e) := hν e
    have hm (e : StripPole H (T : WithTop ℝ)) : ν e univ ≤ 1 := by
      rw [Measure.map_apply reconstructionPhysicalHomeomorph.symm.continuous.measurable
        MeasurableSet.univ, preimage_univ]
      exact stripExitOfRealization_mass_le_one e
    have htest (f : C_c(EvolutionVec 1, ℝ)) (hf : ContDiff ℝ (⊤ : ℕ∞) f) :
        Measurable (fun e => ∫ x, f x ∂ν e) := by
      let F : exitProbeSubmodule := ⟨f, hf, f.hasCompactSupport⟩
      have heq : (fun e => ∫ x, f x ∂ν e) = fun e => exitProbeValue A H E T e F := by
        funext e
        rw [integral_map reconstructionPhysicalHomeomorph.symm.continuous.measurable.aemeasurable
          (show AEStronglyMeasurable (fun x => f x) _ from
            f.continuous.measurable.aestronglyMeasurable)]
        exact stripExitOfRealization_probe_integral hH hlam hLam A H E hE T e F
      rw [heq]
      exact exitProbeValue_measurable F
    have hh := (Measure.measurable_map reconstructionPhysicalHomeomorph
      reconstructionPhysicalHomeomorph.continuous.measurable).comp (measurable_measure_family_of_smooth_tests ν hm htest)
    have heq : (fun e => (ν e).map reconstructionPhysicalHomeomorph) = Ω := by
      funext e
      rw [Measure.map_map reconstructionPhysicalHomeomorph.continuous.measurable
        reconstructionPhysicalHomeomorph.symm.continuous.measurable]
      have hid : reconstructionPhysicalHomeomorph ∘ reconstructionPhysicalHomeomorph.symm =
          (id : Point → Point) := funext reconstructionPhysicalHomeomorph.apply_symm_apply
      rw [hid, Measure.map_id]
    change Measurable (fun e => (ν e).map reconstructionPhysicalHomeomorph) at hh
    rwa [heq] at hh
  exact stripExitOfRealization_measurable _
    (stripEvolution_spec hH hLE hlam hLam A H)


/-- Every derivative term in the packed operator vanishes outside the test's support. -/
theorem reconstruction_operator_zero_off_tsupport
    (B : FullKineticCoefficient 1) (b : PDE.Vec 1 → PDE.Vec 1)
    (f : EvolutionVec 1 → ℝ) (x : EvolutionVec 1) (hx : x ∉ tsupport f) :
    transportedOperator B b f x = 0 := by
  have hh (j : Fin 1) :
      fderiv ℝ (fun y => fderiv ℝ f y (basisV j)) x = 0 :=
    fderiv_of_notMem_tsupport (𝕜 := ℝ)
      (fun h => hx (tsupport_fderiv_apply_subset ℝ (basisV j) h))
  simp [transportedOperator, (fderiv_of_notMem_tsupport (𝕜 := ℝ) hx), hh, zero_apply]

/-- The actual unique exit measure charges no point strictly before its pole. -/
theorem stripExitOfRealization_before_pole
    (hH : HormanderHypoellipticityStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (H : Interval) (E : StripEvolution H)
    (hE : IsStripEvolution A H E) (T : ℝ) (e : StripPole H (T : WithTop ℝ)) :
    stripExitOfRealization hH hlam hLam A H E hE T e {p | p.time < e.1.time} = 0 := by
  let Ω := stripExitOfRealization hH hlam hLam A H E hE T e
  let ν : Measure (EvolutionVec 1) := Ω.map reconstructionPhysicalHomeomorph.symm
  let U : Set (EvolutionVec 1) := {x | timeCoord 1 x < e.1.time}
  have hU : IsOpen U := isOpen_lt (timeCoord 1).continuous continuous_const
  have hle : ν.restrict U ≤ 0 := by
    apply measure_le_of_smooth_integral_le hU (by rw [Measure.restrict_restrict
      hU.measurableSet, inter_self])
    intro f hf hc hs _
    let F : exitProbeSubmodule := ⟨f, hf, hc⟩
    have he : f (reconstructionPhysicalHomeomorph.symm e.1) = 0 := by
      apply image_eq_zero_of_notMem_tsupport
      intro hx
      have ht := hs hx
      change e.1.time < e.1.time at ht
      exact lt_irrefl _ ht
    have hg : (fun p => forwardScalarOperator A.a (exitProbePhysical F) p) =ᵐ[
        stripGreenOfKernel H E.2 T e] 0 := by
      filter_upwards [reconstruction_green_ae_time_gt H E.2 T e] with p hp
      rw [exitProbePhysical_operator]
      apply reconstruction_operator_zero_off_tsupport
      intro hx
      have ht := hs hx
      change p.time < e.1.time at ht
      exact (not_lt_of_ge hp.le) ht
    have hz : exitProbeValue A H E T e F = 0 := by
      change f (reconstructionPhysicalHomeomorph.symm e.1) +
        (∫ p, forwardScalarOperator A.a (exitProbePhysical F) p
          ∂stripGreenOfKernel H E.2 T e) = 0
      rw [he, integral_congr_ae hg]
      simp
    have hm : (∫ x, f x ∂ν) = 0 := by
      rw [integral_map reconstructionPhysicalHomeomorph.symm.continuous.measurable.aemeasurable
        hf.continuous.measurable.aestronglyMeasurable]
      exact (stripExitOfRealization_probe_integral hH hlam hLam A H E hE T e F).trans hz
    rw [integral_zero_measure,
      setIntegral_eq_integral_of_forall_compl_eq_zero
        (fun x hx => image_eq_zero_of_notMem_tsupport (fun ht => hx (hs ht))), hm]
  have hz : ν U = 0 := by
    simpa using (Measure.le_iff.mp hle univ MeasurableSet.univ)
  have hm : ν U = Ω {p | p.time < e.1.time} := by
    rw [Measure.map_apply reconstructionPhysicalHomeomorph.symm.continuous.measurable
      hU.measurableSet]
    rfl
  exact hm.symm.trans hz

/-- Almost every actual exit point has future time and velocity in the closed interval. -/
theorem stripExitOfRealization_ae_closed_future
    (hH : HormanderHypoellipticityStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (H : Interval) (E : StripEvolution H)
    (hE : IsStripEvolution A H E) (T : ℝ) (e : StripPole H (T : WithTop ℝ)) :
    ∀ᵐ p ∂stripExitOfRealization hH hlam hLam A H E hE T e,
      e.1.time ≤ p.time ∧ p.time ≤ T ∧ p.velocity 0 ∈ Icc H.lo H.hi := by
  have hb : ∀ᵐ p ∂stripExitOfRealization hH hlam hLam A H E hE T e,
      p ∈ stripClosedExit H T := by
    rw [ae_iff]
    exact stripExitOfRealization_compl_closedExit hH hlam hLam A H E hE T e
  have ht : ∀ᵐ p ∂stripExitOfRealization hH hlam hLam A H E hE T e,
      e.1.time ≤ p.time := by
    rw [ae_iff]
    simpa using
      stripExitOfRealization_before_pole hH hlam hLam A H E hE T e
  filter_upwards [hb, ht] with p hp ht
  refine ⟨ht, ?_⟩
  rcases hp with hp | hp
  · exact ⟨hp.1.le, hp.2⟩
  · refine ⟨hp.1, ?_⟩
    rcases hp.2 with hv | hv <;> rw [hv]
    · exact ⟨le_rfl, H.ordered.le⟩
    · exact ⟨H.ordered.le, le_rfl⟩

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous

