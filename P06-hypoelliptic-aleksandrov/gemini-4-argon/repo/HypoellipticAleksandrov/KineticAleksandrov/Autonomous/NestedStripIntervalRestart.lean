module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.NestedStripSourceRestart
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.FiniteUnionDomainsMass
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.NestedStripKernelIntegral
import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.BoundedSourceLimitsInfinite
import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.FiniteUnionDomainsMixtures

/-! # The genuine internal restart measure on larger interval poles -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov
open scoped ENNReal

/- The larger-interval restart measure is the subtype pullback of the actual restricted exit. -/
def nestedIntervalRestartPoles
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam } (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (H1 H2 : Interval) (sMinus T : ℝ)
    (e : StripPole H1 (T : WithTop ℝ)) : Measure (StripPole H2 (T : WithTop ℝ)) :=
  ((stripExit hH hLE hlam hLam A H1 T e).restrict
    (nestedIntervalInternalExit H1 H2 sMinus T)).comap Subtype.val

/- The actual restart pole measure is finite. -/
instance nestedIntervalRestartPoles_isFiniteMeasure
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (H1 H2 : Interval) (sMinus T : ℝ)
    (e : StripPole H1 (T : WithTop ℝ)) :
    IsFiniteMeasure (nestedIntervalRestartPoles hH hLE hlam hLam A H1 H2 sMinus T e) := by
  unfold nestedIntervalRestartPoles
  infer_instance

/- The finite pole predicate for an interval is a Borel set in physical coordinates. -/
theorem measurableSet_nestedIntervalPole (H : Interval) (T : ℝ) :
    MeasurableSet {p : Point | (p.time : WithTop ℝ) < T ∧ p.velocity 0 ∈ H.carrier} := by
  convert (isOpen_stripPast H T).measurableSet using 1
  ext p
  exact and_congr WithTop.coe_lt_coe Iff.rfl

/- The restart poles recover precisely the actual smaller exit restricted to the internal face. -/
theorem nestedIntervalRestartPoles_map
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam } (hlam : 0 < lam) (hLam : lam ≤ Lam)
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

/- Genuine restart poles retain the strict lower-time support of the internal face. -/
def nestedIntervalRestartGreen
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam } (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (H1 H2 : Interval) (sMinus T : ℝ)
    (e : StripPole H1 (T : WithTop ℝ)) : Measure Point :=
  (nestedIntervalRestartPoles hH hLE hlam hLam A H1 H2 sMinus T e).bind
    (stripGreen hH hLE hlam hLam A H2 T)

/- Uniform interval geometry makes the actual restart Green mixture finite. -/
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
    have h : finiteUnionGreen hH hLE hlam hLam A H2.toFiniteUnion T (componentPoleInclusion H2.toFiniteUnion i T ep) univ ≤ finiteUnionGreenMassBound lam H2.toFiniteUnion := by
      let H := H2.toFiniteUnion
      let e := (componentPoleInclusion H2.toFiniteUnion i T ep)
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
      have hb := stripGreen_quadratic_mass hH hLE hlam hLam A I T ep
      apply hb.trans
      apply (show ENNReal.ofReal ((e.1.velocity 0 - I.lo) * (I.hi - e.1.velocity 0) /
        (2 * lam)) ≤ ENNReal.ofReal ((I.hi - I.lo) ^ 2 / (2 * lam)) from
        ENNReal.ofReal_le_ofReal
          ((div_le_div_iff_of_pos_right (by positivity : 0 < 2 * lam)).mpr hprod)).trans
      unfold finiteUnionGreenMassBound
      exact Finset.single_le_sum
        (f := fun j : Fin H.count => ENNReal.ofReal
          (((H.component j).hi - (H.component j).lo) ^ 2 / (2 * lam)))
        (fun _ _ => zero_le) (Finset.mem_univ i)
    have hc := congrArg (fun ρ : Measure Point => ρ univ)
      (finiteUnionGreen_component hH hLE hlam hLam A H2.toFiniteUnion i T ep)
    exact hc ▸ h
  constructor
  change τ.bind (stripGreen hH hLE hlam hLam A H2 T) univ < ⊤
  rw [Measure.bind_apply MeasurableSet.univ]
  · apply (lintegral_mono hb).trans_lt
    rw [lintegral_const]
    have _h_xinl_0 : finiteUnionGreenMassBound lam H2.toFiniteUnion ≠ ⊤ := by
      let H := H2.toFiniteUnion
      unfold finiteUnionGreenMassBound
      exact ENNReal.sum_ne_top.mpr (fun _ _ => ENNReal.ofReal_ne_top)
    exact ENNReal.mul_lt_top
      (lt_top_iff_ne_top.mpr _h_xinl_0)
      (measure_lt_top τ univ)
  · exact (Measure.measurable_measure.mpr (fun B hB =>
      stripGreen_measurable_apply hH hLE hlam hLam A H2 T B hB)).aemeasurable

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
