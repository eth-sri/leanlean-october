module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.NestedStripCoordinates
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.GreenTestExtensionCanonical
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.NestedStripRepresentation
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.FiniteUnionDomains
import Mathlib.Topology.Connected.Basic
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.NestedStripIntervalRestart
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.FiniteUnionDomainsNesting
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.NestedStripGreen
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.NestedStripRestartPoles
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.NestedStripKernelIntegral

@[expose] public noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov Parabolic

/-- The larger strip's genuine homogeneous exit potential restricts to the smaller equation.
The potential and all its regularity and bounds are produced internally from reconstruction. -/
theorem exists_nested_exit_potential
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (H1 H2 : Interval)
    (hsub : H1.carrier ⊆ H2.carrier) (sMinus T : ℝ)
    (e : StripPole H1 (T : WithTop ℝ)) (he : sMinus < e.1.time)
    (f : exitProbeSubmodule) :
    ∃ u : Point → ℝ,
      ContinuousOn u (reconstructionClosedSlab H2 sMinus T) ∧
      (∃ C : ℝ, 0 ≤ C ∧ ∀ p ∈ reconstructionClosedSlab H2 sMinus T, |u p| ≤ C) ∧
      EqOn u (exitProbePhysical f) (reconstructionExit H2 (sMinus - 1) T) ∧
      (∀ ep : StripPole H2 (T : WithTop ℝ), sMinus ≤ ep.1.time →
        u ep.1 = ∫ p, exitProbePhysical f p ∂stripExit hH hLE hlam hLam A H2 T ep) ∧
      (∫ p, exitProbePhysical f p ∂stripExit hH hLE hlam hLam A H2 T
        (nestedPoleInclusion H1 H2 hsub T e)) =
          ∫ p, u p ∂stripExit hH hLE hlam hLam A H1 T e  := by
  have exists_nested_homogeneous_potential (H : Interval) (hT : sMinus < T) :
      ∃ u : Point → ℝ,
      IsKineticC112On u (reconstructionStrip H (sMinus - 1) T) ∧
      (∀ p ∈ reconstructionStrip H (sMinus - 1) T, forwardScalarOperator A.a u p = 0) ∧
      ContinuousOn u (reconstructionClosedSlab H sMinus T) ∧
      (∃ C : ℝ, 0 ≤ C ∧ ∀ p ∈ reconstructionClosedSlab H sMinus T, |u p| ≤ C) ∧
      EqOn u (exitProbePhysical f) (reconstructionExit H (sMinus - 1) T) ∧
      (∀ e : StripPole H (T : WithTop ℝ), sMinus ≤ e.1.time →
        u e.1 = ∫ p, exitProbePhysical f p ∂stripExit hH hLE hlam hLam A H T e) := by
    let E := stripEvolution hH hLE hlam hLam A H
    have hE := stripEvolution_spec hH hLE hlam hLam A H
    have hphi := exitProbePhysical_isKineticC112On f
      (reconstructionStrip H (sMinus - 1) T) (isOpen_reconstructionStrip H _ T)
    obtain ⟨M, hM⟩ := exitProbePhysical_bounded_source A f
    have hb : ∃ M : ℝ, ∀ p ∈ reconstructionStrip H (sMinus - 1) T,
        |exitProbePhysical f p| ≤ M ∧
          |forwardScalarOperator A.a (exitProbePhysical f) p| ≤ M := ⟨M, fun p _ => hM p⟩
    obtain ⟨u, hform, hu, hop, hc, htrace⟩ := strip_bounded_source_reconstruction
      hH hlam hLam A H E hE (sMinus - 1) T (exitProbePhysical f) hphi
        (exitProbePhysical_continuous_compact f).1.continuousOn hb
    let p : Point := ⟨sMinus, 0, fun _ => (H.lo + H.hi) / 2⟩
    have hv : p.velocity 0 ∈ H.carrier := by
      change H.lo < (H.lo + H.hi) / 2 ∧ (H.lo + H.hi) / 2 < H.hi
      constructor <;> linarith [H.ordered]
    let e : StripPole H (T : WithTop ℝ) := ⟨p, WithTop.coe_lt_coe.mpr hT, hv⟩
    have he : sMinus - 1 < e.1.time := by change sMinus - 1 < sMinus; linarith
    have hbound := reconstruction_uniform_bound H E A (sMinus - 1) T e he
      (exitProbePhysical f) u hphi hb hform hc
    refine ⟨u, nested_raw_isKineticC112On (isOpen_reconstructionStrip H _ T) hu,
      hop, hc.mono (reconstructionClosedSlab_subset_strip_union_exit H he),
      hbound, htrace, ?_⟩
    intro ep hep
    have hepl : sMinus - 1 < ep.1.time := by linarith
    have hvalue := stripExitOfRealization_probe_integral hH hlam hLam A H E hE T ep f
    have hformula := hform ep hepl
    rw [integral_neg] at hformula
    change (∫ p, exitProbePhysical f p ∂stripExit hH hLE hlam hLam A H T ep) =
      exitProbePhysical f ep.1 + ∫ p, forwardScalarOperator A.a (exitProbePhysical f) p
        ∂stripGreenOfKernel H E.2 T ep at hvalue
    linarith
  have ht := WithTop.coe_lt_coe.mp e.2.1
  obtain ⟨u, hu, hop, hc, ⟨C, hC, hb⟩, htrace, hrep⟩ :=
    exists_nested_homogeneous_potential H2 (he.trans ht)
  have hi : reconstructionStrip H1 sMinus T ⊆ reconstructionStrip H2 (sMinus - 1) T := by
    intro p hp
    exact ⟨by linarith [hp.1], hp.2.1, hsub hp.2.2⟩
  have hsmall : IsKineticC112On u (reconstructionStrip H1 sMinus T) :=
    ⟨hu.1.mono hi, fun p hp => hu.2.1 p (hi hp),
      fun p hp => hu.2.2.1 p (hi hp), fun p hp => hu.2.2.2.1 p (hi hp),
      hu.2.2.2.2.1.mono hi, hu.2.2.2.2.2.1.mono hi,
      hu.2.2.2.2.2.2.1.mono hi, hu.2.2.2.2.2.2.2.mono hi⟩
  have hclosed : reconstructionStrip H1 sMinus T ∪ reconstructionExit H1 sMinus T ⊆
      reconstructionClosedSlab H2 sMinus T := by
    intro p hp
    refine ⟨?_, (nested_strip_union_exit_subset_closed H1 H2 hsub sMinus T hp)⟩
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
  rw [← hrep (nestedPoleInclusion H1 H2 hsub T e) he.le]
  exact hid



/-- Smaller exits lie in the genuine larger closed future slab. -/
theorem nested_exit_ae_larger_slab
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (H1 H2 : Interval)
    (hsub : H1.carrier ⊆ H2.carrier) (sMinus T : ℝ)
    (e : StripPole H1 (T : WithTop ℝ)) (he : sMinus ≤ e.1.time) :
    ∀ᵐ p ∂stripExit hH hLE hlam hLam A H1 T e,
      p ∈ reconstructionClosedSlab H2 sMinus T := by
  have hcl : Icc H1.lo H1.hi ⊆ Icc H2.lo H2.hi := by
    have h := closure_mono hsub
    change closure (Ioo H1.lo H1.hi) ⊆ closure (Ioo H2.lo H2.hi) at h
    rwa [closure_Ioo H1.ordered.ne, closure_Ioo H2.ordered.ne] at h
  filter_upwards [stripExitOfRealization_ae_closed_future hH hlam hLam A H1 _
    (stripEvolution_spec hH hLE hlam hLam A H1) T e] with p hp
  exact ⟨he.trans hp.1, hp.2.1, hcl hp.2.2⟩

/-- Continuity and a proved uniform bound on the actual supporting slab imply integrability. -/
theorem nestedSlab_integrable (H : Interval) (s T : ℝ) (μ : Measure Point)
    [IsFiniteMeasure μ] (u : Point → ℝ)
    (hs : ∀ᵐ p ∂μ, p ∈ reconstructionClosedSlab H s T)
    (hc : ContinuousOn u (reconstructionClosedSlab H s T))
    (hb : ∃ C : ℝ, 0 ≤ C ∧ ∀ p ∈ reconstructionClosedSlab H s T, |u p| ≤ C) :
    Integrable u μ  := by
  have nestedClosedSlab_isClosed :
      IsClosed (reconstructionClosedSlab H s T) := by
    have hv : Continuous (fun p : Point => p.velocity 0) :=
      (continuous_apply 0).comp continuous_velocity
    exact (isClosed_le continuous_const continuous_time).inter
      ((isClosed_le continuous_time continuous_const).inter (isClosed_Icc.preimage hv))
  obtain ⟨C, -, hC⟩ := hb
  have hμ := Measure.restrict_eq_self_of_ae_mem hs
  have hm := hc.aestronglyMeasurable (nestedClosedSlab_isClosed).measurableSet
    (μ := μ)
  rw [hμ] at hm
  apply Integrable.mono' (integrable_const C) hm
  filter_upwards [hs] with p hp
  rw [Real.norm_eq_abs]
  exact hC p hp


/-- An interval included in a finite disjoint interval union lies in one component. -/
theorem Interval.exists_component_containing (I : Interval) (H : FiniteIntervalUnion)
    (hsub : I.carrier ⊆ H.carrier) : ∃ j, I.carrier ⊆ (H.component j).carrier := by
  let v := (I.lo + I.hi) / 2
  have hv : v ∈ I.carrier := by
    dsimp only [v]
    constructor <;> linarith [I.ordered]
  obtain ⟨j, hj⟩ := mem_iUnion.mp (hsub hv)
  let V := ⋃ k, ⋃ (_ : k ≠ j), (H.component k).carrier
  have hV : IsOpen V := isOpen_iUnion (fun _ => isOpen_iUnion (fun _ => isOpen_Ioo))
  have hd : Disjoint (H.component j).carrier V := by
    apply Set.disjoint_left.mpr
    intro x hx hxV
    obtain ⟨k, hk, hxk⟩ := mem_iUnion.mp hxV |>.imp fun _ h => mem_iUnion.mp h
    exact Set.disjoint_left.mp (H.disjoint hk.symm) hx hxk
  have hc : I.carrier ⊆ (H.component j).carrier ∪ V := by
    intro x hx
    obtain ⟨k, hk⟩ := mem_iUnion.mp (hsub hx)
    by_cases hkj : k = j
    · exact Or.inl (hkj ▸ hk)
    · exact Or.inr (mem_iUnion.mpr ⟨k, mem_iUnion.mpr ⟨hkj, hk⟩⟩)
  exact ⟨j, IsPreconnected.subset_left_of_subset_union isOpen_Ioo hV hd hc
    ⟨v, hv, hj⟩ isPreconnected_Ioo⟩



/-- The literal interval exit boundary is Borel in physical coordinates. -/
theorem measurableSet_nestedIntervalExit (H : Interval) (sMinus T : ℝ) :
    MeasurableSet (reconstructionExit H sMinus T) := by
  have hv : Measurable (fun p : Point => p.velocity 0) :=
    ((continuous_apply 0).comp continuous_velocity).measurable
  exact ((measurableSet_eq_fun continuous_time.measurable measurable_const).inter
    (measurableSet_Icc.preimage hv)).union
    ((measurableSet_lt measurable_const continuous_time.measurable).inter
      ((measurableSet_lt continuous_time.measurable measurable_const).inter
        ((measurableSet_eq_fun hv measurable_const).union
          (measurableSet_eq_fun hv measurable_const))))




/-- On the closure of a component, union interior membership is precisely component membership. -/
theorem FiniteIntervalUnion.mem_carrier_on_component_closure (H : FiniteIntervalUnion)
    (i : Fin H.count) {v : ℝ} (hv : v ∈ closure (H.component i).carrier) :
    v ∈ H.carrier ↔ v ∈ (H.component i).carrier := by
  constructor
  · intro hu
    obtain ⟨j, hj⟩ := mem_iUnion.mp hu
    by_cases hji : j = i
    · exact hji ▸ hj
    · exact False.elim (Set.disjoint_left.mp
        ((H.disjoint (Ne.symm hji)).closure_left (show IsOpen (H.component j).carrier
          from isOpen_Ioo)) hv hj)
  · intro hm
    exact H.component_subset i hm


/-- On a chosen closed component, the actual union exit is exactly the interval exit. -/
theorem FiniteIntervalUnion.exit_on_component_closure (H : FiniteIntervalUnion)
    (i : Fin H.count) (sMinus T : ℝ) (p : Point)
    (hv : p.velocity 0 ∈ Icc (H.component i).lo (H.component i).hi) :
    p ∈ finiteUnionExitSet H sMinus T ↔ p ∈ reconstructionExit (H.component i) sMinus T  := by
  have mem_frontier_on_component_closure {v : ℝ} (hv : v ∈ closure (H.component i).carrier) :
      v ∈ frontier H.carrier ↔ v ∈ frontier (H.component i).carrier := by
    rw [frontier, H.isOpen_carrier.interior_eq, frontier,
      (show IsOpen (H.component i).carrier from isOpen_Ioo).interior_eq]
    simp
    exact ⟨fun h => ⟨hv, fun hm => h.2 (H.component_subset i hm)⟩,
      fun h => ⟨closure_mono (H.component_subset i) hv,
        fun hm => h.2 ((H.mem_carrier_on_component_closure i hv).mp hm)⟩⟩
  have hcl : p.velocity 0 ∈ closure (H.component i).carrier := by
    change p.velocity 0 ∈ closure (Ioo (H.component i).lo (H.component i).hi)
    rwa [closure_Ioo (H.component i).ordered.ne]
  have hf := mem_frontier_on_component_closure hcl
  have hfaces : p.velocity 0 ∈ frontier (H.component i).carrier ↔
      p.velocity 0 = (H.component i).lo ∨ p.velocity 0 = (H.component i).hi := by
    change p.velocity 0 ∈ frontier (Ioo (H.component i).lo (H.component i).hi) ↔ _
    rw [frontier_Ioo (H.component i).ordered]
    simp
  constructor
  · rintro (hp | hp)
    · exact Or.inl ⟨hp.1, hv⟩
    · exact Or.inr ⟨hp.1, hp.2.1, hfaces.mp (hf.mp hp.2.2)⟩
  · rintro (hp | hp)
    · exact Or.inl ⟨hp.1, closure_mono (H.component_subset i) hcl⟩
    · exact Or.inr ⟨hp.1, hp.2.1, hf.mpr (hfaces.mpr hp.2.2)⟩



/-- The actual larger exit mixture restarted from the smaller internal boundary. -/
def nestedIntervalRestartExit
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (H1 H2 : Interval) (sMinus T : ℝ)
    (e : StripPole H1 (T : WithTop ℝ)) : Measure Point :=
  (nestedIntervalRestartPoles hH hLE hlam hLam A H1 H2 sMinus T e).bind
    (stripExit hH hLE hlam hLam A H2 T)

/-- The actual restarted exit mixture is finite. -/
instance nestedIntervalRestartExit_isFiniteMeasure
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (H1 H2 : Interval) (sMinus T : ℝ)
    (e : StripPole H1 (T : WithTop ℝ)) :
    IsFiniteMeasure (nestedIntervalRestartExit hH hLE hlam hLam A H1 H2 sMinus T e) := by
  constructor
  unfold nestedIntervalRestartExit
  rw [Measure.bind_apply MeasurableSet.univ
    (stripExit_measurable hH hLE hlam hLam A H2 T).aemeasurable]
  simp only [stripExit_mass_one, lintegral_const, one_mul]
  exact measure_lt_top _ _



/-- The actual internal exit of a single union pole, on the larger union pole carrier. -/
def finiteUnionPointRestartPoles
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (H1 H2 : FiniteIntervalUnion) (sMinus T : ℝ)
    (e : FiniteUnionPole H1 (T : WithTop ℝ)) : Measure (FiniteUnionPole H2 (T : WithTop ℝ)) :=
  ((finiteUnionExit hH hLE hlam hLam A H1 T e).restrict
    (finiteUnionInternalExit H1 H2 sMinus T)).comap Subtype.val

/-- Single-pole internal exits are finite. -/
instance finiteUnionPointRestartPoles_isFiniteMeasure
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (H1 H2 : FiniteIntervalUnion) (sMinus T : ℝ)
    (e : FiniteUnionPole H1 (T : WithTop ℝ)) :
    IsFiniteMeasure (finiteUnionPointRestartPoles hH hLE hlam hLam A H1 H2 sMinus T e) := by
  unfold finiteUnionPointRestartPoles
  infer_instance

/-- The actual point restart family is Borel, by restriction and subtype pullback. -/
theorem finiteUnionPointRestartPoles_measurable
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (H1 H2 : FiniteIntervalUnion) (sMinus T : ℝ) :
    Measurable (finiteUnionPointRestartPoles hH hLE hlam hLam A H1 H2 sMinus T) := by
  exact nested_measurable_family_comap _
    (nested_measurable_family_restrict _ (finiteUnionExit_measurable hH hLE hlam hLam A H1 T)
      _ (measurableSet_finiteUnionInternalExit H1 H2 sMinus T)) _
        (measurableSet_finiteUnionPole H2 T)

/-- The finite-source restart is exactly the actual measurable integral of point restarts. -/
theorem finiteUnionRestartPoleMeasure_disintegration
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (H1 H2 : FiniteIntervalUnion) (sMinus T : ℝ)
    (nu : Measure (FiniteUnionPole H1 (T : WithTop ℝ))) :
    finiteUnionRestartPoleMeasure hH hLE hlam hLam A H1 H2 sMinus T nu =
      nu.bind (finiteUnionPointRestartPoles hH hLE hlam hLam A H1 H2 sMinus T) := by
  unfold finiteUnionRestartPoleMeasure finiteUnionRestartMeasure finiteUnionExitMixture
  have hc := congrArg (fun μ : Measure Point => μ.comap
    (Subtype.val : FiniteUnionPole H2 (T : WithTop ℝ) → Point)) (nested_bind_restrict nu (finiteUnionExit hH hLE hlam hLam A H1 T) (finiteUnionExit_measurable hH hLE hlam hLam A H1 T) (finiteUnionInternalExit H1 H2 sMinus T) (measurableSet_finiteUnionInternalExit H1 H2 sMinus T))
  exact hc.trans (nested_comap_bind nu _
    (nested_measurable_family_restrict _ (finiteUnionExit_measurable hH hLE hlam hLam A H1 T)
      _ (measurableSet_finiteUnionInternalExit H1 H2 sMinus T)) _
        (measurableSet_finiteUnionPole H2 T))



/-- The certified component pole inclusion is measurable in the existing subtype carrier. -/
theorem measurable_componentPoleInclusion (H : FiniteIntervalUnion) (i : Fin H.count)
    (T : WithTop ℝ) : Measurable (componentPoleInclusion H i T) :=
  measurable_subtype_coe.subtype_mk




/-- The literal nested identities hold for every physical pole of a finite interval union. -/
theorem strip_nested_union_point
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
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
          (finiteUnionExit hH hLE hlam hLam A H2 T)   := by
  have component_contained (i : Fin H1.count) : ∃ j, (H1.component i).carrier ⊆ (H2.component j).carrier :=
    (H1.component i).exists_component_containing H2 ((H1.component_subset i).trans hsub)
  have nested_union_component_identity (i : Fin H1.count) (j : Fin H2.count) (hij : (H1.component i).carrier ⊆ (H2.component j).carrier) (sMinus : ℝ) (T : ℝ) (e : StripPole (H1.component i) (T : WithTop ℝ)) (he : sMinus < e.1.time) :
      let ep := componentPoleInclusion H1 i T e
    let eb := finiteUnionNestedPoleInclusion H1 H2 hsub T ep
    let τ := finiteUnionPointRestartPoles hH hLE hlam hLam A H1 H2 sMinus T ep
    finiteUnionGreen hH hLE hlam hLam A H2 T eb =
      finiteUnionGreen hH hLE hlam hLam A H1 T ep +
        τ.bind (finiteUnionGreen hH hLE hlam hLam A H2 T) ∧
    finiteUnionExit hH hLE hlam hLam A H2 T eb =
      (finiteUnionExit hH hLE hlam hLam A H1 T ep).restrict
        (finiteUnionExitSet H2 sMinus T) + τ.bind (finiteUnionExit hH hLE hlam hLam A H2 T) := by
    have nested_component_outer_restriction (hsub : (H1.component i).carrier ⊆ (H2.component j).carrier) :
        (stripExit hH hLE hlam hLam A (H1.component i) T e).restrict
        (finiteUnionExitSet H2 sMinus T) =
        (stripExit hH hLE hlam hLam A (H1.component i) T e).restrict
          (reconstructionExit (H2.component j) sMinus T) := by
      apply Measure.restrict_congr_set
      filter_upwards [nested_exit_ae_larger_slab hH hLE hlam hLam A
        (H1.component i) (H2.component j) hsub sMinus T e he.le] with p hp
      exact propext (H2.exit_on_component_closure j sMinus T p hp.2.2)
    have finiteUnionNestedPoleInclusion_component :
        finiteUnionNestedPoleInclusion H1 H2 hsub T (componentPoleInclusion H1 i T e) =
        componentPoleInclusion H2 j T
          (nestedPoleInclusion (H1.component i) (H2.component j) hij T e) := by
      apply Subtype.ext
      rfl
    have nested_restart_bind_component (hsub : (H1.component i).carrier ⊆ (H2.component j).carrier) (k : FiniteUnionPole H2 (T : WithTop ℝ) → Measure Point) (hk : Measurable k) (l : StripPole (H2.component j) (T : WithTop ℝ) → Measure Point) (hl : ∀ ep, k (componentPoleInclusion H2 j T ep) = l ep) :
        (finiteUnionPointRestartPoles hH hLE hlam hLam A H1 H2 sMinus T
        (componentPoleInclusion H1 i T e)).bind k =
        (nestedIntervalRestartPoles hH hLE hlam hLam A
          (H1.component i) (H2.component j) sMinus T e).bind l := by
      have finiteUnionPointRestartPoles_component :
          finiteUnionPointRestartPoles hH hLE hlam hLam A H1 H2 sMinus T
          (componentPoleInclusion H1 i T e) =
          (nestedIntervalRestartPoles hH hLE hlam hLam A
            (H1.component i) (H2.component j) sMinus T e).map (componentPoleInclusion H2 j T) := by
        have finiteUnionPointRestartPoles_map (e : FiniteUnionPole H1 (T : WithTop ℝ)) :
            (finiteUnionPointRestartPoles hH hLE hlam hLam A H1 H2 sMinus T e).map Subtype.val =
            (finiteUnionExit hH hLE hlam hLam A H1 T e).restrict
              (finiteUnionInternalExit H1 H2 sMinus T) := by
          unfold finiteUnionPointRestartPoles
          refine (map_comap_subtype_coe (measurableSet_finiteUnionPole H2 T) _).trans ?_
          apply Measure.restrict_eq_self_of_ae_mem
          filter_upwards [ae_restrict_mem
            (measurableSet_finiteUnionInternalExit H1 H2 sMinus T)] with p hp
          exact ⟨WithTop.coe_lt_coe.mpr hp.2.1, hp.2.2.2⟩
        have finiteUnionInternalExit_on_component_exit (p : Point) (hp : p ∈ reconstructionExit (H1.component i) sMinus T) :
            p ∈ finiteUnionInternalExit H1 H2 sMinus T ↔
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
              simpa using hs.2.2.1
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
          exact propext (finiteUnionInternalExit_on_component_exit p hp)
        exact (finiteUnionPointRestartPoles_map
          (componentPoleInclusion H1 i T e)).trans
            ((congrArg (fun μ : Measure Point => μ.restrict
              (finiteUnionInternalExit H1 H2 sMinus T)) hΩ).trans (hrestrict.trans hback.symm))
      have h := congrArg (fun μ => μ.bind k) finiteUnionPointRestartPoles_component
      exact h.trans ((nested_bind_map _ _ (measurable_componentPoleInclusion H2 j T) k hk).trans
        (Measure.bind_congr_right (Filter.Eventually.of_forall hl)))
    have nestedIntervalExit_identity (H1 : Interval) (H2 : Interval) (hsub : H1.carrier ⊆ H2.carrier) (sMinus : ℝ) (T : ℝ) (e : StripPole H1 (T : WithTop ℝ)) (he : sMinus < e.1.time) :
        stripExit hH hLE hlam hLam A H2 T (nestedPoleInclusion H1 H2 hsub T e) =
        (stripExit hH hLE hlam hLam A H1 T e).restrict (reconstructionExit H2 sMinus T) +
          nestedIntervalRestartExit hH hLE hlam hLam A H1 H2 sMinus T e := by
      have nestedIntervalExit_probe_identity (f : exitProbeSubmodule) :
          (∫ p, exitProbePhysical f p ∂stripExit hH hLE hlam hLam A H2 T
          (nestedPoleInclusion H1 H2 hsub T e)) =
          (∫ p, exitProbePhysical f p ∂(stripExit hH hLE hlam hLam A H1 T e).restrict
            (reconstructionExit H2 sMinus T)) +
          ∫ p, exitProbePhysical f p
            ∂nestedIntervalRestartExit hH hLE hlam hLam A H1 H2 sMinus T e := by
        have nestedIntervalExit_boundary_split :
            stripExit hH hLE hlam hLam A H1 T e =
            (stripExit hH hLE hlam hLam A H1 T e).restrict (reconstructionExit H2 sMinus T) +
            (stripExit hH hLE hlam hLam A H1 T e).restrict
              (nestedIntervalInternalExit H1 H2 sMinus T) := by
          have nestedIntervalExit_compl_iff_internal (p : Point) (hp : p ∈ reconstructionExit H1 sMinus T) :
              p ∉ reconstructionExit H2 sMinus T ↔ p ∈ nestedIntervalInternalExit H1 H2 sMinus T := by
            have hc := nested_strip_union_exit_subset_closed H1 H2 hsub sMinus T (Or.inr hp)
            constructor
            · intro hn
              rcases hp with hp | hp
              · exact False.elim (hn (Or.inl ⟨hp.1, hc.2⟩))
              · refine ⟨hp.1, hp.2.1, hp.2.2, ?_⟩
                have hl : p.velocity 0 ≠ H2.lo := fun hl => hn (Or.inr ⟨hp.1, hp.2.1, Or.inl hl⟩)
                have hh : p.velocity 0 ≠ H2.hi := fun hh => hn (Or.inr ⟨hp.1, hp.2.1, Or.inr hh⟩)
                exact ⟨lt_of_le_of_ne hc.2.1 hl.symm, lt_of_le_of_ne hc.2.2 hh⟩
            · intro hs hn
              rcases hn with hn | hn
              · exact (ne_of_lt hs.2.1) hn.1
              · rcases hn.2.2 with hv | hv
                · exact (ne_of_gt hs.2.2.2.1) hv
                · exact (ne_of_lt hs.2.2.2.2) hv
          let μ := stripExit hH hLE hlam hLam A H1 T e
          have hm : ∀ᵐ p ∂μ, p ∈ reconstructionExit H1 sMinus T := by
            rw [ae_iff]
            exact (strip_exit_probability hH hLE hlam hLam A H1 sMinus T e he.le).2.1
          have heq : (reconstructionExit H2 sMinus T)ᶜ =ᵐ[μ]
              nestedIntervalInternalExit H1 H2 sMinus T := by
            filter_upwards [hm] with p hp
            exact propext (nestedIntervalExit_compl_iff_internal p hp)
          have hs := μ.restrict_add_restrict_compl (measurableSet_nestedIntervalExit H2 sMinus T)
          rw [Measure.restrict_congr_set heq] at hs
          exact hs.symm
        obtain ⟨u, hc, hb, htrace, hrep, hid⟩ := exists_nested_exit_potential
          hH hLE hlam hLam A H1 H2 hsub sMinus T e he f
        let μ := stripExit hH hLE hlam hLam A H1 T e
        let τ := nestedIntervalRestartPoles hH hLE hlam hLam A H1 H2 sMinus T e
        have hi := nestedSlab_integrable H2 sMinus T μ u
          (nested_exit_ae_larger_slab hH hLE hlam hLam A H1 H2 hsub sMinus T e he.le) hc hb
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
          filter_upwards [nestedIntervalRestartPoles_ae_time_gt
            hH hLE hlam hLam A H1 H2 sMinus T e] with ep hep
          exact hrep ep hep.le
        exact hid.trans ((congrArg (fun ρ : Measure Point => ∫ p, u p ∂ρ) (nestedIntervalExit_boundary_split)).trans ((integral_add_measure (hi.restrict (s := reconstructionExit H2 sMinus T)) (hi.restrict (s := nestedIntervalInternalExit H1 H2 sMinus T))).trans (congrArg₂ (· + ·) houter
          (hmap.trans (hvalues.trans (nested_integral_bind τ (stripExit hH hLE hlam hLam A H2 T) (stripExit_measurable hH hLE hlam hLam A H2 T) (exitProbePhysical f) (nestedProbe_integrable A f (nestedIntervalRestartExit hH hLE hlam hLam A H1 H2 sMinus T e))).symm)))))
      apply nested_physical_measure_eq univ isOpen_univ
        (Filter.Eventually.of_forall (fun _ => mem_univ _))
        (Filter.Eventually.of_forall (fun _ => mem_univ _))
      intro f _ _
      rw [integral_add_measure (nestedProbe_integrable A f _)
        (nestedProbe_integrable A f _)]
      exact nestedIntervalExit_probe_identity f
    dsimp only
    let e2 := nestedPoleInclusion (H1.component i) (H2.component j) hij T e
    have hp := finiteUnionNestedPoleInclusion_component
    have hGb := (congrArg (finiteUnionGreen hH hLE hlam hLam A H2 T) hp).trans
      (finiteUnionGreen_component hH hLE hlam hLam A H2 j T e2)
    have hOb := (congrArg (finiteUnionExit hH hLE hlam hLam A H2 T) hp).trans
      (finiteUnionExit_component hH hLE hlam hLam A H2 j T e2)
    have hGτ := nested_restart_bind_component hij
      (finiteUnionGreen hH hLE hlam hLam A H2 T)
      (finiteUnionGreen_measurable hH hLE hlam hLam A H2 T)
      (stripGreen hH hLE hlam hLam A (H2.component j) T)
      (fun ep => finiteUnionGreen_component hH hLE hlam hLam A H2 j T ep)
    have hOτ := nested_restart_bind_component hij
      (finiteUnionExit hH hLE hlam hLam A H2 T)
      (finiteUnionExit_measurable hH hLE hlam hLam A H2 T)
      (stripExit hH hLE hlam hLam A (H2.component j) T)
      (fun ep => finiteUnionExit_component hH hLE hlam hLam A H2 j T ep)
    have houter := (congrArg (fun μ : Measure Point =>
      μ.restrict (finiteUnionExitSet H2 sMinus T)) (finiteUnionExit_component hH hLE hlam hLam A H1 i T e)).trans
        (nested_component_outer_restriction hij)
    constructor
    · exact hGb.trans ((nestedIntervalGreen_identity hH hLE hlam hLam A
        (H1.component i) (H2.component j) hij sMinus T e he).trans
          (congrArg₂ (· + ·) (finiteUnionGreen_component hH hLE hlam hLam A H1 i T e).symm hGτ.symm))
    · exact hOb.trans ((nestedIntervalExit_identity
        (H1.component i) (H2.component j) hij sMinus T e he).trans
          (congrArg₂ (· + ·) houter.symm hOτ.symm))
  let i := finiteUnionPoleIndex H1 T e
  let ep := finiteUnionComponentPole H1 T e
  obtain ⟨j, hij⟩ := component_contained i
  have hh := nested_union_component_identity i j hij
    sMinus T ep he
  have heq : componentPoleInclusion H1 i T ep = e := by apply Subtype.ext; rfl
  dsimp only at hh
  rw [heq] at hh
  exact hh

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous

