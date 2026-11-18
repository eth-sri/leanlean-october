module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.FiniteUnionDomainsMixtures
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.BoundedSourceLimitsInfinite
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.NestedStripRepresentation
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.GreenTestExtensionCanonical
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.NestedStripRestartPoles
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.NestedStripKernelIntegral

@[expose] public noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov
open scoped ENNReal

/-- A finite union's mass constant depends only on its interval lengths and ellipticity. -/
def finiteUnionGreenMassBound (lam : ℝ) (H : FiniteIntervalUnion) : ℝ≥0∞ :=
  ∑ i : Fin H.count, ENNReal.ofReal (((H.component i).hi - (H.component i).lo) ^ 2 /
    (2 * lam))

/-- The geometric finite-union mass constant is finite. -/
theorem finiteUnionGreenMassBound_ne_top (lam : ℝ) (H : FiniteIntervalUnion) :
    finiteUnionGreenMassBound lam H ≠ ⊤ := by
  unfold finiteUnionGreenMassBound
  exact ENNReal.sum_ne_top.mpr (fun _ _ => ENNReal.ofReal_ne_top)

/-- Every actual union Green pole has the same uniform finite mass bound. -/
theorem finiteUnionGreen_mass_le
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (H : FiniteIntervalUnion) (T : WithTop ℝ)
    (e : FiniteUnionPole H T) :
    finiteUnionGreen hH hLE hlam hLam A H T e univ ≤ finiteUnionGreenMassBound lam H := by
  let i := finiteUnionPoleIndex H T e
  let I := H.component i
  let ep := finiteUnionComponentPole H T e
  have hv := ep.2.2
  change I.lo < e.1.velocity 0 ∧ e.1.velocity 0 < I.hi at hv
  have hprod : (e.1.velocity 0 - I.lo) * (I.hi - e.1.velocity 0) ≤
      (I.hi - I.lo) ^ 2 := by
    have h1 : 0 ≤ e.1.velocity 0 - I.lo := by linarith
    have h2 : 0 ≤ I.hi - e.1.velocity 0 := by linarith
    nlinarith [sq_nonneg (e.1.velocity 0 - I.lo),
      sq_nonneg (I.hi - e.1.velocity 0), mul_nonneg h1 h2]
  apply (stripGreen_quadratic_mass hH hLE hlam hLam A I T ep).trans
  apply (show ENNReal.ofReal ((e.1.velocity 0 - I.lo) * (I.hi - e.1.velocity 0) /
    (2 * lam)) ≤ ENNReal.ofReal ((I.hi - I.lo) ^ 2 / (2 * lam)) from
    ENNReal.ofReal_le_ofReal
      ((div_le_div_iff_of_pos_right (by positivity : 0 < 2 * lam)).mpr hprod)).trans
  unfold finiteUnionGreenMassBound
  exact Finset.single_le_sum
    (f := fun j => ENNReal.ofReal
      (((H.component j).hi - (H.component j).lo) ^ 2 / (2 * lam)))
    (fun _ _ => zero_le) (Finset.mem_univ i)

/-- The actual Green mixture has mass bounded linearly by source mass. -/
theorem finiteUnionGreenMixture_mass_le
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (H : FiniteIntervalUnion) (T : WithTop ℝ)
    (nu : Measure (FiniteUnionPole H T)) :
    finiteUnionGreenMixture hH hLE hlam hLam A H T nu univ ≤
      finiteUnionGreenMassBound lam H * nu univ := by
  unfold finiteUnionGreenMixture
  rw [Measure.bind_apply MeasurableSet.univ
    (finiteUnionGreen_measurable hH hLE hlam hLam A H T).aemeasurable]
  calc
    _ ≤ ∫⁻ _x, finiteUnionGreenMassBound lam H ∂nu :=
      lintegral_mono (fun e => finiteUnionGreen_mass_le hH hLE hlam hLam A H T e)
    _ = _ := lintegral_const _

/-- A finite source has a finite actual Green mixture, including at infinite horizon. -/
instance finiteUnionGreenMixture_isFiniteMeasure
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (H : FiniteIntervalUnion) (T : WithTop ℝ)
    (nu : Measure (FiniteUnionPole H T)) [IsFiniteMeasure nu] :
    IsFiniteMeasure (finiteUnionGreenMixture hH hLE hlam hLam A H T nu) := by
  constructor
  exact (finiteUnionGreenMixture_mass_le hH hLE hlam hLam A H T nu).trans_lt
    (ENNReal.mul_lt_top (lt_top_iff_ne_top.mpr (finiteUnionGreenMassBound_ne_top lam H))
      (measure_lt_top nu univ))


/-- Internal exits for a pair of single intervals in physical coordinates. -/
def nestedIntervalInternalExit (H1 H2 : Interval) (sMinus T : ℝ) : Set Point :=
  {p | sMinus < p.time ∧ p.time < T ∧
    (p.velocity 0 = H1.lo ∨ p.velocity 0 = H1.hi) ∧ p.velocity 0 ∈ H2.carrier}

/-- The actual interval internal-exit set is Borel. -/
theorem measurableSet_nestedIntervalInternalExit (H1 H2 : Interval) (sMinus T : ℝ) :
    MeasurableSet (nestedIntervalInternalExit H1 H2 sMinus T) := by
  have hv : Measurable (fun p : Point => p.velocity 0) :=
    ((continuous_apply 0).comp continuous_velocity).measurable
  exact (measurableSet_lt measurable_const continuous_time.measurable).inter
    ((measurableSet_lt continuous_time.measurable measurable_const).inter
      (((measurableSet_eq_fun hv measurable_const).union
        (measurableSet_eq_fun hv measurable_const)).inter
        (isOpen_Ioo.measurableSet.preimage hv)))


/-- The larger Green source integral is the smaller integral plus its true internal restart.
The restart measure is the smaller exit measure restricted to the literal internal boundary. -/
theorem nestedSourcePotential_restart_identity
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (H1 H2 : Interval)
    (hsub : H1.carrier ⊆ H2.carrier) (sMinus T : ℝ)
    (e : StripPole H1 (T : WithTop ℝ)) (he : sMinus < e.1.time)
    (f : exitProbeSubmodule) (hfn : ∀ p, 0 ≤ exitProbePhysical f p)
    (hs : tsupport (exitProbePhysical f) ⊆ {p | p.time < T ∧ p.velocity 0 ∈ H2.carrier}) :
    (∫ p, exitProbePhysical f p ∂stripGreen hH hLE hlam hLam A H2 T
      (nestedPoleInclusion H1 H2 hsub T e)) =
      (∫ p, exitProbePhysical f p ∂stripGreen hH hLE hlam hLam A H1 T e) +
      ∫ p, nestedSourcePotential H2 (stripEvolution hH hLE hlam hLam A H2) T f p
        ∂(stripExit hH hLE hlam hLam A H1 T e).restrict
          (nestedIntervalInternalExit H1 H2 sMinus T)   := by
  have nestedSourcePotential_zero_outer (E : StripEvolution H2) (hE : IsStripEvolution A H2 E) (p : Point) (hp : p ∈ reconstructionExit H1 sMinus T) (hn : p ∉ nestedIntervalInternalExit H1 H2 sMinus T) :
      nestedSourcePotential H2 E T f p = 0 := by
    have hz := nestedSourcePotential_continuous_zero_exit hH hlam hLam A H2 E hE T f hfn hs
    rcases hp with hp | hp
    · exact hz.2.1 p hp.1
    · have hv : p.velocity 0 ∉ H2.carrier := fun hv => hn ⟨hp.1, hp.2.1, hp.2.2, hv⟩
      have hc := (nested_strip_union_exit_subset_closed H1 H2 hsub sMinus T
        (Or.inr (Or.inr hp))).2
      apply hz.2.2 p
      change ¬ (H2.lo < p.velocity 0 ∧ p.velocity 0 < H2.hi) at hv
      by_cases hl : p.velocity 0 = H2.lo
      · exact Or.inl hl
      · exact Or.inr (le_antisymm hc.2 (by
          by_contra hn
          exact hv ⟨lt_of_le_of_ne hc.1 (Ne.symm hl), lt_of_not_ge hn⟩))
  have nestedSourcePotential_small_identity :
      (∫ p, exitProbePhysical f p ∂stripGreen hH hLE hlam hLam A H2 T
      (nestedPoleInclusion H1 H2 hsub T e)) =
      (∫ p, exitProbePhysical f p ∂stripGreen hH hLE hlam hLam A H1 T e) +
      ∫ p, nestedSourcePotential H2 (stripEvolution hH hLE hlam hLam A H2) T f p
        ∂stripExit hH hLE hlam hLam A H1 T e := by
    let E := stripEvolution hH hLE hlam hLam A H2
    have hE := stripEvolution_spec hH hLE hlam hLam A H2
    let u := nestedSourcePotential H2 E T f
    obtain ⟨⟨C, -, hC⟩, hu, hop⟩ :=
      nestedSourcePotential_regular_source hH hlam hLam A H2 E hE T f hfn hs
    have hi : reconstructionStrip H1 sMinus T ⊆
        {p | p.time < T ∧ p.velocity 0 ∈ H2.carrier} :=
      fun _ hp => ⟨hp.2.1, hsub hp.2.2⟩
    obtain ⟨M, hM⟩ := exitProbePhysical_bounded_source A f
    have hb : ∃ M : ℝ, ∀ p ∈ reconstructionStrip H1 sMinus T,
        |u p| ≤ M ∧ |forwardScalarOperator A.a u p| ≤ M := by
      refine ⟨max C M, fun p hp => ⟨(hC p).trans (le_max_left _ _), ?_⟩⟩
      rw [hop p (hi hp).1 (hi hp).2, abs_neg]
      exact (hM p).1.trans (le_max_right _ _)
    have hsmall : Parabolic.IsKineticC112On u (reconstructionStrip H1 sMinus T) :=
      ⟨hu.1.mono hi, fun p hp => hu.2.1 p (hi hp),
        fun p hp => hu.2.2.1 p (hi hp), fun p hp => hu.2.2.2.1 p (hi hp),
        hu.2.2.2.2.1.mono hi, hu.2.2.2.2.2.1.mono hi,
        hu.2.2.2.2.2.2.1.mono hi, hu.2.2.2.2.2.2.2.mono hi⟩
    have hid := strip_identity_C112 hH hLE hlam hLam A H1 sMinus T
      (he.trans (WithTop.coe_lt_coe.mp e.2.1)) e he u hsmall
      (((nestedSourcePotential_continuous_zero_exit hH hlam hLam A H2 E hE T f hfn hs).1).mono (nested_strip_union_exit_subset_closed H1 H2 hsub sMinus T)) hb
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
      exact nestedSourcePotential_zero_outer _
        (stripEvolution_spec hH hLE hlam hLam A H2) p hp hm
  have hid := nestedSourcePotential_small_identity
  change _ = _ + ∫ p, u p ∂stripExit hH hLE hlam hLam A H1 T e at hid
  rw [integral_congr_ae heq,
    integral_indicator (measurableSet_nestedIntervalInternalExit H1 H2 sMinus T)] at hid
  exact hid


/-- The larger-interval restart measure is the subtype pullback of the actual restricted exit. -/
def nestedIntervalRestartPoles
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (H1 H2 : Interval) (sMinus T : ℝ)
    (e : StripPole H1 (T : WithTop ℝ)) : Measure (StripPole H2 (T : WithTop ℝ)) :=
  ((stripExit hH hLE hlam hLam A H1 T e).restrict
    (nestedIntervalInternalExit H1 H2 sMinus T)).comap Subtype.val

/-- The actual restart pole measure is finite. -/
instance nestedIntervalRestartPoles_isFiniteMeasure
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (H1 H2 : Interval) (sMinus T : ℝ)
    (e : StripPole H1 (T : WithTop ℝ)) :
    IsFiniteMeasure (nestedIntervalRestartPoles hH hLE hlam hLam A H1 H2 sMinus T e) := by
  unfold nestedIntervalRestartPoles
  infer_instance

/-- The finite pole predicate for an interval is a Borel set in physical coordinates. -/
theorem measurableSet_nestedIntervalPole (H : Interval) (T : ℝ) :
    MeasurableSet {p : Point | (p.time : WithTop ℝ) < T ∧ p.velocity 0 ∈ H.carrier} := by
  convert (isOpen_stripPast H T).measurableSet using 1
  ext p
  exact and_congr WithTop.coe_lt_coe Iff.rfl

/-- The restart poles recover precisely the actual smaller exit restricted to the internal face. -/
theorem nestedIntervalRestartPoles_map
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (H1 H2 : Interval) (sMinus T : ℝ)
    (e : StripPole H1 (T : WithTop ℝ)) :
    (nestedIntervalRestartPoles hH hLE hlam hLam A H1 H2 sMinus T e).map Subtype.val =
      (stripExit hH hLE hlam hLam A H1 T e).restrict
        (nestedIntervalInternalExit H1 H2 sMinus T) := by
  unfold nestedIntervalRestartPoles
  refine (map_comap_subtype_coe (measurableSet_nestedIntervalPole H2 T) _).trans ?_
  apply Measure.restrict_eq_self_of_ae_mem
  filter_upwards [ae_restrict_mem
    (measurableSet_nestedIntervalInternalExit H1 H2 sMinus T)] with p hp
  exact ⟨WithTop.coe_lt_coe.mpr hp.2.1, hp.2.2.2⟩

/-- Genuine restart poles retain the strict lower-time support of the internal face. -/
theorem nestedIntervalRestartPoles_ae_time_gt
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (H1 H2 : Interval) (sMinus T : ℝ)
    (e : StripPole H1 (T : WithTop ℝ)) :
    ∀ᵐ ep ∂nestedIntervalRestartPoles hH hLE hlam hLam A H1 H2 sMinus T e,
      sMinus < ep.1.time := by
  have ht : ∀ᵐ p ∂(stripExit hH hLE hlam hLam A H1 T e).restrict
      (nestedIntervalInternalExit H1 H2 sMinus T), sMinus < p.time := by
    filter_upwards [ae_restrict_mem
      (measurableSet_nestedIntervalInternalExit H1 H2 sMinus T)] with p hp
    exact hp.1
  rw [← nestedIntervalRestartPoles_map hH hLE hlam hLam A H1 H2 sMinus T e] at ht
  exact ((MeasurableEmbedding.subtype_coe (measurableSet_nestedIntervalPole H2 T)).ae_map_iff).mp ht

/-- The larger Green mixture of internal restart poles is the actual measurable measure bind. -/
def nestedIntervalRestartGreen
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (H1 H2 : Interval) (sMinus T : ℝ)
    (e : StripPole H1 (T : WithTop ℝ)) : Measure Point :=
  (nestedIntervalRestartPoles hH hLE hlam hLam A H1 H2 sMinus T e).bind
    (stripGreen hH hLE hlam hLam A H2 T)

/-- Uniform interval geometry makes the actual restart Green mixture finite. -/
instance nestedIntervalRestartGreen_isFiniteMeasure
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (H1 H2 : Interval) (sMinus T : ℝ)
    (e : StripPole H1 (T : WithTop ℝ)) :
    IsFiniteMeasure (nestedIntervalRestartGreen hH hLE hlam hLam A H1 H2 sMinus T e) := by
  let τ := nestedIntervalRestartPoles hH hLE hlam hLam A H1 H2 sMinus T e
  let C := finiteUnionGreenMassBound lam H2.toFiniteUnion
  have hb (ep : StripPole H2 (T : WithTop ℝ)) :
      stripGreen hH hLE hlam hLam A H2 T ep univ ≤ C := by
    let i : Fin H2.toFiniteUnion.count := ⟨0, by change 0 < 1; omega⟩
    have h := finiteUnionGreen_mass_le hH hLE hlam hLam A H2.toFiniteUnion T
      (componentPoleInclusion H2.toFiniteUnion i T ep)
    have hc := congrArg (fun ρ : Measure Point => ρ univ)
      (finiteUnionGreen_component hH hLE hlam hLam A H2.toFiniteUnion i T ep)
    exact hc ▸ h
  constructor
  change τ.bind (stripGreen hH hLE hlam hLam A H2 T) univ < ⊤
  rw [Measure.bind_apply MeasurableSet.univ]
  · apply (lintegral_mono hb).trans_lt
    rw [lintegral_const]
    exact ENNReal.mul_lt_top
      (lt_top_iff_ne_top.mpr (finiteUnionGreenMassBound_ne_top lam H2.toFiniteUnion))
      (measure_lt_top τ univ)
  · exact (Measure.measurable_measure.mpr (fun B hB =>
      stripGreen_measurable_apply hH hLE hlam hLam A H2 T B hB)).aemeasurable

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous

