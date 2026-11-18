module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.GreenTestExtensionCutoffs
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Tactic
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.VisitMassQuadratic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.VisitMassGreenTest
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.VisitMassExitIntegrals
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.VisitMassCoefficientIntegral
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.CoreDominationWaiting
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.VisitMassOutgoing
import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.NestedStripKernelIntegral
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.CoreDominationIdentity
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.CoreDominationAllTimeKernel
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.InfiniteHorizonOrder
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.VisitMassCount
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.EnlargedVisits
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.EntranceStatement
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.InfiniteHorizonGreenSupport
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.VisitMassOuterBounds
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.StripTimeMarginal
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.VisitMassSummation
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.EntranceDensityReal

@[expose] public noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov HypoellipticAleksandrov.Parabolic ProbabilityTheory Filter
open scoped Topology Classical ENNReal

/-- A translated cutoff with inner radius three quarters of the interval length. -/
def visitTimeCutoff (a r : ℝ) (hr : 0 < r) (t : ℝ) : ℝ :=
  reconstructionPositionBump (3 * r ^ 2 / 4) (by positivity) (t - (a + r ^ 2 / 2))

/-- The time cutoff is smooth and lies between zero and one. -/
theorem visitTimeCutoff_properties (a r : ℝ) (hr : 0 < r) :
    ContDiff ℝ (⊤ : ℕ∞) (visitTimeCutoff a r hr) ∧
      (∀ t, 0 ≤ visitTimeCutoff a r hr t ∧ visitTimeCutoff a r hr t ≤ 1) :=
  ⟨(reconstructionPositionBump _ _).contDiff.comp (contDiff_id.sub contDiff_const),
    fun _ => ⟨(reconstructionPositionBump _ _).nonneg,
      (reconstructionPositionBump _ _).le_one⟩⟩

/-- It equals one on the whole closed interval, including a possible initial atom. -/
theorem visitTimeCutoff_eq_one (a r : ℝ) (hr : 0 < r) {t : ℝ}
    (ht : t ∈ Icc a (a + r ^ 2)) : visitTimeCutoff a r hr t = 1 := by
  apply (reconstructionPositionBump _ _).one_of_mem_closedBall
  rw [Metric.mem_closedBall, Real.dist_eq, sub_zero]
  change |t - (a + r ^ 2 / 2)| ≤ 3 * r ^ 2 / 4
  apply abs_le.mpr
  constructor <;> nlinarith [ht.1, ht.2, sq_nonneg r]


/-- A single constant controls the derivative of every rescaled time cutoff. -/
theorem visitTimeCutoff_deriv_bound : ∃ D : ℝ, 0 ≤ D ∧
    ∀ (a r : ℝ) (hr : 0 < r) (t : ℝ),
      |deriv (visitTimeCutoff a r hr) t| ≤ D / r ^ 2 := by
  obtain ⟨D, hD, hd⟩ := reconstructionUnitBump_properties.2.2.2
  refine ⟨4 * D / 3, by positivity, ?_⟩
  intro a r hr t
  have hs : ContDiff ℝ (⊤ : ℕ∞)
      (reconstructionPositionBump (3 * r ^ 2 / 4) (by positivity) : ℝ → ℝ) :=
    (reconstructionPositionBump _ _).contDiff
  have hc := (hs.differentiable (by norm_num) (t - (a + r ^ 2 / 2))).hasDerivAt.comp t
    ((hasDerivAt_id t).sub_const (a + r ^ 2 / 2))
  have he : deriv (visitTimeCutoff a r hr) t =
      deriv (reconstructionPositionBump (3 * r ^ 2 / 4) (by positivity))
        (t - (a + r ^ 2 / 2)) := by
    have hf : visitTimeCutoff a r hr = fun x =>
        reconstructionPositionBump (3 * r ^ 2 / 4) (by positivity)
          (x - (a + r ^ 2 / 2)) := rfl
    rw [hf]
    simpa [Function.comp_def] using hc.deriv
  rw [he]
  convert (reconstructionPositionBump_deriv_bound (3 * r ^ 2 / 4) (by positivity) D hd (t - (a + r ^ 2 / 2))) using 1
  field_simp

/-- The closed support has the same length-three bounding interval. -/
theorem visitTimeCutoff_tsupport (a r : ℝ) (hr : 0 < r) :
    tsupport (visitTimeCutoff a r hr) ⊆ Icc (a - r ^ 2) (a + 2 * r ^ 2)  := by
  have visitTimeCutoff_support :
      Function.support (visitTimeCutoff a r hr) ⊆ Ioo (a - r ^ 2) (a + 2 * r ^ 2) := by
    intro t ht
    have hb : t - (a + r ^ 2 / 2) ∈
        Function.support (reconstructionPositionBump (3 * r ^ 2 / 4) (by positivity)) := ht
    rw [ContDiffBump.support_eq, Metric.mem_ball, Real.dist_eq, sub_zero] at hb
    change |t - (a + r ^ 2 / 2)| < 2 * (3 * r ^ 2 / 4) at hb
    obtain ⟨hl, hu⟩ := abs_lt.mp hb
    constructor <;> linarith
  have h := closure_mono (visitTimeCutoff_support)
  have ho : a - r ^ 2 < a + 2 * r ^ 2 := by nlinarith [sq_pos_of_pos hr]
  rwa [closure_Ioo ho.ne] at h

/-- The cutoff derivative vanishes outside the same closed time window. -/
theorem visitTimeCutoff_deriv_tsupport (a r : ℝ) (hr : 0 < r) :
    tsupport (deriv (visitTimeCutoff a r hr)) ⊆ Icc (a - r ^ 2) (a + 2 * r ^ 2) :=
  tsupport_deriv_subset.trans (visitTimeCutoff_tsupport a r hr)


/-- The time-localized quadratic has exactly the source transport-diffusion operator. -/
theorem visitTimeQuadratic_operator (c : Clock) (eta : ℝ → ℝ)
    (heta : ContDiff ℝ (⊤ : ℕ∞) eta) (a : ℝ → ℝ → ℝ) (p : Point) :
    forwardScalarOperator a (fun q => eta q.time * visitQuadratic c (q.velocity 0)) p =
      deriv eta p.time * visitQuadratic c (p.velocity 0) -
        2 * a (p.position 0) (p.velocity 0) * eta p.time := by
  have htime : deriv (fun t => eta t * visitQuadratic c (p.velocity 0)) p.time =
      deriv eta p.time * visitQuadratic c (p.velocity 0) :=
    ((heta.differentiable (by norm_num) p.time).hasDerivAt.mul_const _).deriv
  have hquad (v : ℝ) : HasDerivAt (visitQuadratic c) (-2 * (v - c.vbar)) v := by
    have h := ((visitQuadratic_smooth c).differentiable (by norm_num) v).hasDerivAt
    rwa [visitQuadratic_deriv] at h
  have hsecond : deriv (deriv (fun v => eta p.time * visitQuadratic c v)) (p.velocity 0) =
      eta p.time * (-2) := by
    rw [(funext fun v => ((hquad v).const_mul (eta p.time)).deriv)]
    simpa using (((hasDerivAt_id (p.velocity 0)).sub_const c.vbar).const_mul (-2).const_mul (eta p.time)).deriv
  rw [forwardScalarOperator, kineticPositionGradient_scalar, kineticVelocityHessian_scalar]
  simp only [kineticTimeDerivative, htime, deriv_const, mul_zero, add_zero, hsecond]
  ring



/-- One universal cutoff constant bounds every actual localized quadratic operator. -/
theorem visitTimeQuadratic_uniform_operator_bound : ∃ D : ℝ, 0 ≤ D ∧
    ∀ (c : Clock) (b lam Lam : ℝ) (_hlam : 0 < lam) (A : SmoothAutonomous lam Lam)
      (p : Point), p.velocity 0 ∈ closure c.active →
      |forwardScalarOperator A.a
        (fun q => visitTimeCutoff b c.r c.positive q.time *
          visitQuadratic c (q.velocity 0)) p| ≤ 9 * D / 16 + 2 * Lam := by
  obtain ⟨D, hD, hd⟩ := visitTimeCutoff_deriv_bound
  refine ⟨D, hD, ?_⟩
  intro c b lam Lam hlam A p hp
  let eta := visitTimeCutoff b c.r c.positive
  have he := (visitTimeCutoff_properties b c.r c.positive).2 p.time
  have hf := visitQuadratic_nonneg c hp
  have ha := A.bounds (p.position 0) (p.velocity 0)
  have han := hlam.le.trans ha.1
  have hfirst : |deriv eta p.time * visitQuadratic c (p.velocity 0)| ≤ 9 * D / 16 := by
    rw [abs_mul, abs_of_nonneg hf]
    have hc : D / c.r ^ 2 * (9 * c.r ^ 2 / 16) = 9 * D / 16 := by
      field_simp [c.positive.ne']
    exact (mul_le_mul (hd b c.r c.positive p.time) (visitQuadratic_le c _) hf (by positivity : 0 ≤ D / c.r ^ 2)).trans_eq hc
  have hsecond : |2 * A.a (p.position 0) (p.velocity 0) * eta p.time| ≤ 2 * Lam := by
    rw [abs_of_nonneg (mul_nonneg (mul_nonneg (by norm_num) han) he.1)]
    exact (mul_le_mul_of_nonneg_left he.2 (mul_nonneg (by norm_num) han)).trans
      (by simpa using mul_le_mul_of_nonneg_left ha.2 (by norm_num : 0 ≤ (2 : ℝ)))
  rw [visitTimeQuadratic_operator c eta (visitTimeCutoff_properties b c.r c.positive).1]
  simpa using
    (abs_sub_le (deriv eta p.time * visitQuadratic c (p.velocity 0)) 0
      (2 * A.a (p.position 0) (p.velocity 0) * eta p.time)).trans
        (by simpa using add_le_add hfirst hsecond)


/-- Closed active velocity support makes the actual localized quadratic integrable. -/
theorem visitTimeQuadratic_integrable_of_active_support (c : Clock) (b : ℝ)
    (mu : Measure Point) [IsFiniteMeasure mu]
    (hmu : ∀ᵐ p ∂mu, p.velocity 0 ∈ closure c.active) :
    Integrable (fun p => visitTimeCutoff b c.r c.positive p.time *
      visitQuadratic c (p.velocity 0)) mu := by
  have hc : Continuous (fun p : Point => visitTimeCutoff b c.r c.positive p.time *
      visitQuadratic c (p.velocity 0)) :=
    ((visitTimeCutoff_properties b c.r c.positive).1.continuous.comp
    continuous_time).mul ((visitQuadratic_smooth c).continuous.comp
      ((continuous_apply 0).comp continuous_velocity))
  apply Integrable.mono' (integrable_const (9 * c.r ^ 2 / 16))
    hc.measurable.aestronglyMeasurable
  filter_upwards [hmu] with p hp
  change ‖visitTimeCutoff b c.r c.positive p.time * visitQuadratic c (p.velocity 0)‖ ≤ _
  have he := (visitTimeCutoff_properties b c.r c.positive).2 p.time
  have hf := visitQuadratic_nonneg c hp
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg he.1, abs_of_nonneg hf]
  have hm := mul_le_mul_of_nonneg_right he.2 hf
  simp at hm
  exact hm.trans (visitQuadratic_le c _)



/-- The actual active Green mixture has closed active velocity support. -/
theorem visitActiveGreenMixture_ae_closedActive
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (c : Clock) (J : Interval) (s T : ℝ)
    (mu : Measure Point) :
    ∀ᵐ q ∂(visitUnionGreenKernel hH hLE hlam hLam A (visitActiveUnion c J) s T ∘ₘ mu),
      q.velocity 0 ∈ closure c.active := by
  classical
  apply Measure.ae_comp_of_ae_ae
    (isClosed_closure.measurableSet.preimage
      ((continuous_apply 0).comp continuous_velocity).measurable)
  apply Filter.Eventually.of_forall
  intro p
  change ∀ᵐ q ∂(if hp : p ∈ visitPoleSet (visitActiveUnion c J) s T then
    finiteUnionGreen hH hLE hlam hLam A (visitActiveUnion c J) T
      (visitPoleInclusion _ s T ⟨p, hp⟩) else 0), q.velocity 0 ∈ closure c.active
  split
  · rename_i hp
    exact (visitUnionGreen_ae_velocity hH hLE hlam hLam A (visitActiveUnion c J) T
      (visitPoleInclusion _ s T ⟨p, hp⟩)).mono fun q hq =>
        subset_closure ((visitActiveUnion_carrier c J).le hq).1
  · simp

/-- The actual active exit mixture discharges the localized test's support condition. -/
theorem visitTimeQuadratic_integrable_activeExitMixture
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (c : Clock) (J : Interval) (s T b : ℝ)
    (mu : Measure Point) [IsFiniteMeasure mu] :
    Integrable (fun p => visitTimeCutoff b c.r c.positive p.time *
      visitQuadratic c (p.velocity 0))
      (visitUnionExitKernel hH hLE hlam hLam A (visitActiveUnion c J) s T ∘ₘ mu) :=
  visitTimeQuadratic_integrable_of_active_support c b _
    (visitActiveExitMixture_ae_velocity hH hLE hlam hLam A c J s T mu)

/-- The actual active Green mixture discharges the localized operator's support condition. -/
theorem visitTimeQuadratic_operator_integrable_activeGreenMixture
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (c : Clock) (J : Interval) (s T b : ℝ)
    (mu : Measure Point) [IsFiniteMeasure mu] :
    Integrable (fun p => forwardScalarOperator A.a
      (fun q => visitTimeCutoff b c.r c.positive q.time *
        visitQuadratic c (q.velocity 0)) p)
      (visitUnionGreenKernel hH hLE hlam hLam A (visitActiveUnion c J) s T ∘ₘ mu)  := by
  have visitTimeQuadratic_operator_integrable_of_active_support (mu : Measure Point) [IsFiniteMeasure mu] (hmu : ∀ᵐ p ∂mu, p.velocity 0 ∈ closure c.active) :
      Integrable (fun p => forwardScalarOperator A.a
      (fun q => visitTimeCutoff b c.r c.positive q.time *
        visitQuadratic c (q.velocity 0)) p) mu := by
    have visitTimeQuadratic_operator_continuous :
        Continuous (fun p => forwardScalarOperator A.a
        (fun q => visitTimeCutoff b c.r c.positive q.time *
          visitQuadratic c (q.velocity 0)) p) := by
      have he := (visitTimeCutoff_properties b c.r c.positive).1
      have hf : Continuous (fun p : Point => visitQuadratic c (p.velocity 0)) :=
        (visitQuadratic_smooth c).continuous.comp
        ((continuous_apply 0).comp continuous_velocity)
      have hh :=
        funext (visitTimeQuadratic_operator c (visitTimeCutoff b c.r c.positive) he A.a)
      rw [hh]
      exact (((he.continuous_deriv (by norm_num)).comp continuous_time).mul hf).sub
        ((continuous_const.mul (visitCoefficient_continuous A)).mul
          (he.continuous.comp continuous_time))
    obtain ⟨D, _hD, hd⟩ := visitTimeQuadratic_uniform_operator_bound
    apply Integrable.mono' (integrable_const (9 * D / 16 + 2 * Lam))
      (visitTimeQuadratic_operator_continuous).measurable.aestronglyMeasurable
    filter_upwards [hmu] with p hp
    change ‖forwardScalarOperator A.a
      (fun q => visitTimeCutoff b c.r c.positive q.time * visitQuadratic c (q.velocity 0)) p‖ ≤ _
    rw [Real.norm_eq_abs]
    exact hd c b lam Lam hlam A p hp
  exact visitTimeQuadratic_operator_integrable_of_active_support _
    (visitActiveGreenMixture_ae_closedActive hH hLE hlam hLam A c J s T mu)




/-- Every actual entrance satisfies the genuine integrated short-time quadratic identity. -/
theorem visitTimeQuadratic_entrance_green_identity
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (c : Clock) (J : Interval) (s T b : ℝ) (P : Point)
    (hP : s < P.time ∧ P.time < T ∧ P.velocity 0 ∈ J.carrier) (n : ℕ) :
    let mu := visitEntrancePiece hH hLE hlam hLam A c J s T P n
    let E := visitUnionExitKernel hH hLE hlam hLam A (visitActiveUnion c J) s T
    let G := visitUnionGreenKernel hH hLE hlam hLam A (visitActiveUnion c J) s T
    let f := fun q : Point => visitTimeCutoff b c.r c.positive q.time *
      visitQuadratic c (q.velocity 0)
    (∫ p, f p ∂mu) = (∫ p, f p ∂E ∘ₘ mu) -
      ∫ p, forwardScalarOperator A.a f p ∂G ∘ₘ mu  := by
  have visitTimeQuadratic_active_identity (e : FiniteUnionPole (visitActiveUnion c J) (T : WithTop ℝ)) :
      let f := fun q => visitTimeCutoff b c.r c.positive q.time *
      visitQuadratic c (q.velocity 0)
    f e.1 = (∫ p, f p ∂finiteUnionExit hH hLE hlam hLam A (visitActiveUnion c J) T e) -
      ∫ p, forwardScalarOperator A.a f p
        ∂finiteUnionGreen hH hLE hlam hLam A (visitActiveUnion c J) T e := by
    have visitTimeQuadratic_smooth (eta : ℝ → ℝ) (heta : ContDiff ℝ (⊤ : ℕ∞) eta) : ContDiff ℝ (⊤ : ℕ∞)
        ((fun q => eta q.time * visitQuadratic c (q.velocity 0)) ∘
          (KineticPoint.equivProd 1).symm) :=
      (heta.comp contDiff_fst).mul (capacity_velocity_smooth (visitQuadratic_smooth c))
    dsimp only
    apply visitUnion_identity_bounded_smooth hH hLE hlam hLam A (visitActiveUnion c J) T e
      (fun q => visitTimeCutoff b c.r c.positive q.time * visitQuadratic c (q.velocity 0))
    · exact visitTimeQuadratic_smooth _ (visitTimeCutoff_properties b c.r c.positive).1
    · obtain ⟨D, _hD, hd⟩ := visitTimeQuadratic_uniform_operator_bound
      refine ⟨max (9 * c.r ^ 2 / 16) (9 * D / 16 + 2 * Lam), ?_⟩
      intro p hp
      have hv :=
        subset_closure ((visitActiveUnion_carrier c J).le hp).1
      have he := (visitTimeCutoff_properties b c.r c.positive).2 p.time
      have hf := visitQuadratic_nonneg c hv
      constructor
      · rw [abs_mul, abs_of_nonneg he.1, abs_of_nonneg hf]
        have hm := mul_le_mul_of_nonneg_right he.2 hf
        simp at hm
        exact (hm.trans (visitQuadratic_le c _)).trans (le_max_left _ _)
      · exact (hd c b lam Lam hlam A p hv).trans (le_max_right _ _)
  classical
  dsimp only
  let mu := visitEntrancePiece hH hLE hlam hLam A c J s T P n
  let E := visitUnionExitKernel hH hLE hlam hLam A (visitActiveUnion c J) s T
  let G := visitUnionGreenKernel hH hLE hlam hLam A (visitActiveUnion c J) s T
  let f := fun q : Point => visitTimeCutoff b c.r c.positive q.time *
    visitQuadratic c (q.velocity 0)
  let g := fun p => forwardScalarOperator A.a f p
  have hE :=
    visitTimeQuadratic_integrable_activeExitMixture hH hLE hlam hLam A c J s T b mu
  have hG :=
    visitTimeQuadratic_operator_integrable_activeGreenMixture hH hLE hlam hLam A c J s T b mu
  have hiE : Integrable (fun p => ∫ q, f q ∂E p) mu := by
    rw [Measure.comp_eq_comp_const_apply] at hE
    simpa using hE.integral_comp
  have hiG : Integrable (fun p => ∫ q, g q ∂G p) mu := by
    rw [Measure.comp_eq_comp_const_apply] at hG
    simpa using hG.integral_comp
  have hp : f =ᵐ[mu] fun p => (∫ q, f q ∂E p) - ∫ q, g q ∂G p := by
    filter_upwards [visitEntrancePiece_ae_activePole hH hLE hlam hLam A c J s T P hP n]
      with p hp
    let ep := visitPoleInclusion (visitActiveUnion c J) s T ⟨p, hp⟩
    have he : E p = finiteUnionExit hH hLE hlam hLam A (visitActiveUnion c J) T ep := by
      change (if ht : p ∈ visitPoleSet (visitActiveUnion c J) s T then
        finiteUnionExit hH hLE hlam hLam A (visitActiveUnion c J) T
          (visitPoleInclusion _ s T ⟨p, ht⟩) else 0) = _
      rw [dite_eq_left hp]
    have hg : G p = finiteUnionGreen hH hLE hlam hLam A (visitActiveUnion c J) T ep := by
      change (if ht : p ∈ visitPoleSet (visitActiveUnion c J) s T then
        finiteUnionGreen hH hLE hlam hLam A (visitActiveUnion c J) T
          (visitPoleInclusion _ s T ⟨p, ht⟩) else 0) = _
      rw [dite_eq_left hp]
    have hh := visitTimeQuadratic_active_identity ep
    dsimp only at hh
    rw [← he, ← hg] at hh
    exact hh
  change (∫ p, f p ∂mu) = (∫ p, f p ∂E ∘ₘ mu) - ∫ p, g p ∂G ∘ₘ mu
  rw [integral_congr_ae hp, integral_sub hiE hiG]
  rw [nested_integral_bind mu E E.measurable f hE,
    nested_integral_bind mu G G.measurable g hG]


/-- The localized test counts every actual entrance in the closed interval of length r squared. -/
theorem visitTimeQuadratic_entrance_integral_lower
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (c : Clock) (J : Interval) (s T b : ℝ)
    (P : Point) (n : ℕ) :
    5 * c.r ^ 2 / 16 *
      (visitEntrancePiece hH hLE hlam hLam A c J s T P n
        {p | p.time ∈ Icc b (b + c.r ^ 2)}).toReal ≤
      ∫ p, visitTimeCutoff b c.r c.positive p.time * visitQuadratic c (p.velocity 0)
        ∂visitEntrancePiece hH hLE hlam hLam A c J s T P n  := by
  have visitTimeQuadratic_integrable_entrance :
      Integrable (fun p => visitTimeCutoff b c.r c.positive p.time *
      visitQuadratic c (p.velocity 0))
      (visitEntrancePiece hH hLE hlam hLam A c J s T P n) := by
    apply visitTimeQuadratic_integrable_of_active_support
    exact (visitGamma_ae_closedEntrance P c J s T _ _ n).mono
      (fun p hp => subset_closure (visitClosedEntrance_subset_active c hp))
  let W := {p : Point | p.time ∈ Icc b (b + c.r ^ 2)}
  have hW : MeasurableSet W := isClosed_Icc.measurableSet.preimage continuous_time.measurable
  have hi := integral_mono_ae ((integrable_const (5 * c.r ^ 2 / 16)).indicator hW)
    (visitTimeQuadratic_integrable_entrance) (by
      filter_upwards [visitGamma_ae_closedEntrance P c J s T _ _ n] with p hp
      by_cases ht : p ∈ W
      · rw [indicator_of_mem ht, visitTimeCutoff_eq_one b c.r c.positive ht, one_mul]
        exact visitQuadratic_entrance_lower c hp
      · rw [indicator_of_notMem ht]
        exact mul_nonneg ((visitTimeCutoff_properties b c.r c.positive).2 p.time).1
          ((by positivity : 0 ≤ 5 * c.r ^ 2 / 16).trans
            (visitQuadratic_entrance_lower c hp)))
  rw [integral_indicator hW, integral_const] at hi
  simpa only [smul_eq_mul, Measure.real, Measure.restrict_apply_univ, mul_comm] using hi

/-- The actual localized Green operator is controlled by occupation only in its short window. -/
theorem visitTimeQuadratic_activeGreen_integral_bound : ∃ D : ℝ, 0 ≤ D ∧
    ∀ (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
      (lam Lam : ℝ) (hlam : 0 < lam) (hLam : lam ≤ Lam) (A : SmoothAutonomous lam Lam)
      (c : Clock) (J : Interval) (s T b : ℝ) (mu : Measure Point)
      (_hmuFinite : IsFiniteMeasure mu),
      let G := visitUnionGreenKernel hH hLE hlam hLam A (visitActiveUnion c J) s T ∘ₘ mu;
      -(∫ p, forwardScalarOperator A.a
        (fun q => visitTimeCutoff b c.r c.positive q.time *
          visitQuadratic c (q.velocity 0)) p ∂G) ≤
        (9 * D / 16 + 2 * Lam) *
          (G {p | p.time ∈ Icc (b - c.r ^ 2) (b + 2 * c.r ^ 2)}).toReal  := by
  have visitTimeQuadratic_zero_off_window (c : Clock) (b : ℝ) (a : ℝ → ℝ → ℝ) (p : Point) (ht : p.time ∉ Icc (b - c.r ^ 2) (b + 2 * c.r ^ 2)) :
      visitTimeCutoff b c.r c.positive p.time * visitQuadratic c (p.velocity 0) = 0 ∧
      forwardScalarOperator a
        (fun q => visitTimeCutoff b c.r c.positive q.time *
          visitQuadratic c (q.velocity 0)) p = 0 := by
    have he : visitTimeCutoff b c.r c.positive p.time = 0 := by
      by_contra hn
      exact ht (visitTimeCutoff_tsupport b c.r c.positive (subset_closure hn))
    have hd : deriv (visitTimeCutoff b c.r c.positive) p.time = 0 := by
      by_contra hn
      exact ht (visitTimeCutoff_deriv_tsupport b c.r c.positive (subset_closure hn))
    constructor
    · rw [he, zero_mul]
    · rw [visitTimeQuadratic_operator c _
        (visitTimeCutoff_properties b c.r c.positive).1, he, hd]
      simp
  obtain ⟨D, hD, hd⟩ := visitTimeQuadratic_uniform_operator_bound
  refine ⟨D, hD, ?_⟩
  intro hH hLE lam Lam hlam hLam A c J s T b mu hmuFinite
  let := hmuFinite
  dsimp only
  let G := visitUnionGreenKernel hH hLE hlam hLam A (visitActiveUnion c J) s T ∘ₘ mu
  let f := fun p => forwardScalarOperator A.a
    (fun q => visitTimeCutoff b c.r c.positive q.time * visitQuadratic c (q.velocity 0)) p
  let W := {p : Point | p.time ∈ Icc (b - c.r ^ 2) (b + 2 * c.r ^ 2)}
  have hW : MeasurableSet W := isClosed_Icc.measurableSet.preimage continuous_time.measurable
  have hi := integral_mono_ae
    (visitTimeQuadratic_operator_integrable_activeGreenMixture
      hH hLE hlam hLam A c J s T b mu).neg
    ((integrable_const (9 * D / 16 + 2 * Lam)).indicator hW) (by
      filter_upwards [visitActiveGreenMixture_ae_closedActive hH hLE hlam hLam A c J s T mu]
        with p hp
      change -f p ≤ W.indicator (fun _ => 9 * D / 16 + 2 * Lam) p
      by_cases ht : p ∈ W
      · rw [indicator_of_mem ht]
        exact (neg_le_abs _).trans (hd c b lam Lam hlam A p hp)
      · have hz : f p = 0 := (visitTimeQuadratic_zero_off_window c b A.a p ht).2
        rw [indicator_of_notMem ht, hz]
        exact neg_zero.le)
  change (∫ p, -f p ∂G) ≤ ∫ p, W.indicator (fun _ => 9 * D / 16 + 2 * Lam) p ∂G at hi
  rw [integral_neg, integral_indicator hW, integral_const] at hi
  change -(∫ p, f p ∂G) ≤ (9 * D / 16 + 2 * Lam) * (G W).toReal
  simpa [Measure.real, Measure.restrict_apply_univ, mul_comm] using hi


/-- A forward-cylinder start has the literal strict physical pole support used by visits. -/
theorem visitCylinderStart_mem (Z0 : Point) (R : ℝ) (hR : 0 < R) (P : Point)
    (hP : P ∈ forwardCylinder Z0 R hR) :
    Z0.time < P.time ∧ P.time < Z0.time + R ^ 2 ∧
      P.velocity 0 ∈ (capacityCylinderInterval Z0 R hR).carrier :=
  ⟨hP.1, hP.2.1, (capacityCylinderPole Z0 P R hR hP).2.2⟩

/-- The actual cylinder counting measure is finite. -/
theorem visitStartsQ_isFiniteMeasure
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (c : Clock) (Z0 : Point) (R : ℝ) (hR : 0 < R)
    (P : Point) (hP : P ∈ forwardCylinder Z0 R hR) :
    IsFiniteMeasure (visitStartsQ hH hLE hlam hLam A c Z0 R hR P hP) :=
  visitCount_isFiniteMeasure hH hLE hlam hLam A c (capacityCylinderInterval Z0 R hR)
    Z0.time (Z0.time + R ^ 2) (by nlinarith [sq_pos_of_pos hR]) P
      (visitCylinderStart_mem Z0 R hR P hP)

/-- One ellipticity constant bounds every actual cylinder count by `C * (1 + R / r)`. -/
theorem exists_visitStartsQ_mass_constant {lam Lam : ℝ}
    (hlam : 0 < lam) (hLam : lam ≤ Lam) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
        (A : SmoothAutonomous lam Lam) (c : Clock) (Z0 : Point) (R : ℝ) (hR : 0 < R)
        (P : Point) (hP : P ∈ forwardCylinder Z0 R hR),
        visitStartsQ hH hLE hlam hLam A c Z0 R hR P hP univ ≤
          ENNReal.ofReal (C * (1 + R / c.r)) := by
  obtain ⟨C, hC, hc⟩ := exists_visitCount_mass_constant hlam hLam
  refine ⟨C, hC, ?_⟩
  intro hH hLE A c Z0 R hR P hP
  have hw : ((capacityCylinderInterval Z0 R hR).hi -
      (capacityCylinderInterval Z0 R hR).lo) / 2 = R := by
    dsimp only [capacityCylinderInterval]
    ring
  simpa only [hw, visitStartsQ] using (hc hH hLE A c (capacityCylinderInterval Z0 R hR) Z0.time (Z0.time + R ^ 2) (by nlinarith [sq_pos_of_pos hR]) P (visitCylinderStart_mem Z0 R hR P hP))


/-- The original cylinder strip Green is dominated on the core by the actual visit Green measure. -/
theorem core_green_le_visitGreen
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (c : Clock) (Z0 : Point) (R : ℝ) (hR : 0 < R)
    (P : Point) (hP : P ∈ forwardCylinder Z0 R hR) :
    (stripGreen hH hLE hlam hLam A (capacityCylinderInterval Z0 R hR)
      (Z0.time + R ^ 2) (capacityCylinderPole Z0 P R hR hP)).restrict
        {q | q.velocity 0 ∈ c.core} ≤
    (coreAllTimeGreenMeasure hH hLE hlam hLam A c
      (visitStartsQ hH hLE hlam hLam A c Z0 R hR P hP)).restrict
        {q | q.velocity 0 ∈ c.core}  := by
  have visitOuterGreen_core_domination (J : Interval) (s : ℝ) (T : ℝ) (hT : s < T) (hP : s < P.time ∧ P.time < T ∧ P.velocity 0 ∈ J.carrier) :
      (visitUnionGreenKernel hH hLE hlam hLam A J.toFiniteUnion s T P).restrict
      {q | q.velocity 0 ∈ c.core} ≤
    (coreAllTimeGreenMeasure hH hLE hlam hLam A c
      (Measure.sum (visitEntrancePiece hH hLE hlam hLam A c J s T P))).restrict
        {q | q.velocity 0 ∈ c.core} := by
    have visitActiveGreenMixture_le_allTime (mu : Measure Point) :
        visitUnionGreenKernel hH hLE hlam hLam A (visitActiveUnion c J) s T ∘ₘ mu ≤
        coreAllTimeGreenMeasure hH hLE hlam hLam A c mu := by
      have visitActiveGreenKernel_le_allTime (p : Point) :
          visitUnionGreenKernel hH hLE hlam hLam A (visitActiveUnion c J) s T p ≤
          coreAllTimeGreenKernel hH hLE hlam hLam A c p := by
        classical
        by_cases hp : p ∈ visitPoleSet (visitActiveUnion c J) s T
        · have hv : p.velocity 0 ∈ c.active :=
            ((visitActiveUnion_carrier c J).le hp.2.2).1
          let H := visitActiveUnion c J
          let e := visitPoleInclusion H s T ⟨p, hp⟩
          let i := finiteUnionPoleIndex H T e
          have hsub : (H.component i).carrier ⊆ (visitActiveInterval c).carrier := by
            intro v hv'
            exact ((visitActiveUnion_carrier c J).le (H.component_subset i hv')).1
          change (if ht : p ∈ visitPoleSet H s T then
            finiteUnionGreen hH hLE hlam hLam A H T (visitPoleInclusion H s T ⟨p, ht⟩) else 0) ≤
              (if ht : p.velocity 0 ∈ c.active then
                stripGreen hH hLE hlam hLam A (visitActiveInterval c) ⊤
                  (coreAllTimePole c ⟨p, ht⟩) else 0)
          rw [dite_eq_left hp, dite_eq_left hv]
          exact stripGreen_mono hH hLE hlam hLam A (H.component i) (visitActiveInterval c) hsub T ⊤ le_top (finiteUnionComponentPole H T e)
        · change (if ht : p ∈ visitPoleSet (visitActiveUnion c J) s T then _ else 0) ≤ _
          rw [dite_eq_right hp]
          intro B
          exact zero_le
      unfold coreAllTimeGreenMeasure
      apply Measure.le_iff.mpr
      intro B hB
      rw [Measure.bind_apply hB (Kernel.aemeasurable _),
        Measure.bind_apply hB (Kernel.aemeasurable _)]
      exact lintegral_mono (fun p => visitActiveGreenKernel_le_allTime p B)
    let C : Set Point := {q | q.velocity 0 ∈ c.core}
    have hC : MeasurableSet C :=
      isClosed_Icc.measurableSet.preimage ((continuous_apply 0).comp continuous_velocity).measurable
    rw [visitOuterGreen_core_identity hH hLE hlam hLam A c J s T hT P hP]
    unfold coreAllTimeGreenMeasure
    rw [Measure.bind_sum _ _ (Kernel.aemeasurable _), Measure.restrict_sum _ hC]
    apply Measure.le_iff.mpr
    intro B hB
    rw [Measure.sum_apply _ hB, Measure.sum_apply _ hB]
    apply ENNReal.tsum_le_tsum
    intro n
    exact Measure.restrict_mono_measure
      (visitActiveGreenMixture_le_allTime
        (visitEntrancePiece hH hLE hlam hLam A c J s T P n)) C B
  have hp := visitCylinderStart_mem Z0 R hR P hP
  have hd := visitOuterGreen_core_domination
    (capacityCylinderInterval Z0 R hR) Z0.time (Z0.time + R ^ 2)
    (by nlinarith [sq_pos_of_pos hR]) hp
  rw [visitOuterGreen_eq_strip hH hLE hlam hLam A _ _ _ P hp] at hd
  exact hd


/-- The two active all-time families use exactly the same canonical strip and physical poles. -/
theorem entrance_coreAllTimeGreen_eq
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (c : Clock) (nu : Measure Point) :
    coreAllTimeGreenMeasure hH hLE hlam hLam A c nu =
      enlargedActiveGreen hH hLE hlam hLam A c nu := by
  have hk : coreAllTimeGreenKernel hH hLE hlam hLam A c =
      enlargedActiveGreenKernel hH hLE hlam hLam A c := by
    apply Kernel.ext
    intro p
    change (if hp : p.velocity 0 ∈ c.active then
      stripGreen hH hLE hlam hLam A (visitActiveInterval c) ⊤ (coreAllTimePole c ⟨p, hp⟩)
      else 0) = (if hp : p.velocity 0 ∈ c.active then
      stripGreen hH hLE hlam hLam A c.activeInterval ⊤ (densityClockPole c p hp) else 0)
    split <;> rfl
  exact congrArg (fun K : Kernel Point Point => K ∘ₘ nu) hk

/-- The actual clipped cylinder entrance count retains closed-entrance velocity support. -/
theorem entrance_visitStartsQ_ae_closedEntrance
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (c : Clock) (Z0 : Point) (R : ℝ) (hR : 0 < R)
    (P : Point) (hP : P ∈ forwardCylinder Z0 R hR) :
    ∀ᵐ p ∂visitStartsQ hH hLE hlam hLam A c Z0 R hR P hP,
      p.velocity 0 ∈ closure c.entrance := by
  have hI : (visitEntranceInterval c).carrier = c.entrance := rfl
  have hS : MeasurableSet {p : Point | p.velocity 0 ∈ closure c.entrance} :=
    isClosed_closure.measurableSet.preimage
      ((continuous_apply 0).comp continuous_velocity).measurable
  change ∀ᵐ p ∂Measure.sum _, _
  apply Measure.ae_sum_iff.mpr
  intro n
  cases n with
  | zero =>
    unfold visitEntrancePiece visitGamma visitInitial
    split
    · rename_i hi
      apply (ae_dirac_iff hS).mpr
      simpa only [hI] using hi
    · filter_upwards [ae_restrict_mem (measurableSet_visitBoundary Z0.time
        (Z0.time + R ^ 2) (visitEntranceInterval c) (capacityCylinderInterval Z0 R hR))]
        with p hp
      have hv := frontier_subset_closure hp.2.2.1
      simpa only [hI] using hv
  | succ n =>
    unfold visitEntrancePiece visitGamma
    filter_upwards [ae_restrict_mem (measurableSet_visitBoundary Z0.time
      (Z0.time + R ^ 2) (visitEntranceInterval c) (capacityCylinderInterval Z0 R hR))]
      with p hp
    simpa only [hI] using (frontier_subset_closure hp.2.2.1)

/-- The actual cylinder Green measure lies inside its literal observation strip. -/
theorem entrance_cylinderGreen_ae_observation
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (Z0 : Point) (R : ℝ) (hR : 0 < R)
    (P : Point) (hP : P ∈ forwardCylinder Z0 R hR) :
    ∀ᵐ p ∂stripGreen hH hLE hlam hLam A (capacityCylinderInterval Z0 R hR)
      (Z0.time + R ^ 2) (capacityCylinderPole Z0 P R hR hP),
      p ∈ densityObservationStrip Z0 R hR := by
  let H := capacityCylinderInterval Z0 R hR
  let ep := capacityCylinderPole Z0 P R hR hP
  let K := (stripEvolution hH hLE hlam hLam A H).2
  filter_upwards [reconstruction_green_ae_time_gt H K (Z0.time + R ^ 2) ep,
    stripGreenOfKernel_ae_mem_stripPast H K (Z0.time + R ^ 2) ep] with p hp hq
  exact ⟨hP.1.trans hp, hq.1, hq.2⟩



/-- Removing the zero internal face bounds the localized exit integral by retained exit mass. -/
theorem visitTimeQuadratic_retainedExit_integral_le
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (c : Clock) (J : Interval) (s T b : ℝ)
    (P : Point) (n : ℕ) :
    let mu := visitEntrancePiece hH hLE hlam hLam A c J s T P n
    let E := visitUnionExitKernel hH hLE hlam hLam A (visitActiveUnion c J) s T
    let B := visitBoundary s T (visitActiveInterval c) J
    (∫ p, visitTimeCutoff b c.r c.positive p.time * visitQuadratic c (p.velocity 0)
      ∂E ∘ₘ mu) ≤ 9 * c.r ^ 2 / 16 * (((E ∘ₘ mu).restrict Bᶜ) univ).toReal   := by
  have visitTimeQuadratic_outgoing_integral_zero :
      (∫ p, visitTimeCutoff b c.r c.positive p.time * visitQuadratic c (p.velocity 0)
      ∂visitOutgoingPiece hH hLE hlam hLam A c J s T P n) = 0 := by
    have hz : (fun p => visitTimeCutoff b c.r c.positive p.time *
        visitQuadratic c (p.velocity 0)) =ᵐ[
          visitOutgoingPiece hH hLE hlam hLam A c J s T P n] 0 := by
      filter_upwards [visitQuadratic_ae_zero_outgoing hH hLE hlam hLam A c J s T P n] with p hp
      rw [hp, mul_zero]
      rfl
    rw [integral_congr_ae hz]
    exact integral_zero _ _
  have visitTimeQuadratic_le (p : Point) :
      visitTimeCutoff b c.r c.positive p.time * visitQuadratic c (p.velocity 0) ≤
      9 * c.r ^ 2 / 16 := by
    have he := (visitTimeCutoff_properties b c.r c.positive).2 p.time
    have hh := mul_le_mul_of_nonneg_right he.2 (by positivity : 0 ≤ 9 * c.r ^ 2 / 16)
    simp at hh
    exact (mul_le_mul_of_nonneg_left (visitQuadratic_le c (p.velocity 0)) he.1).trans hh
  dsimp only
  let mu := visitEntrancePiece hH hLE hlam hLam A c J s T P n
  let E := visitUnionExitKernel hH hLE hlam hLam A (visitActiveUnion c J) s T
  let B := visitBoundary s T (visitActiveInterval c) J
  let f := fun p : Point => visitTimeCutoff b c.r c.positive p.time *
    visitQuadratic c (p.velocity 0)
  have hiE : Integrable f (E ∘ₘ mu) :=
    visitTimeQuadratic_integrable_activeExitMixture hH hLE hlam hLam A c J s T b mu
  have hx : (∫ p, f p ∂(E ∘ₘ mu).restrict Bᶜ) ≤
      9 * c.r ^ 2 / 16 * (((E ∘ₘ mu).restrict Bᶜ) univ).toReal := by
    simpa [integral_const, Measure.real, mul_comm] using (integral_mono_ae (hiE.restrict (s := Bᶜ)) (integrable_const (9 * c.r ^ 2 / 16)) (Filter.Eventually.of_forall (visitTimeQuadratic_le)))
  have hz : (∫ p, f p ∂(E ∘ₘ mu).restrict B) = 0 :=
    visitTimeQuadratic_outgoing_integral_zero
  have hs := integral_add_compl (measurableSet_visitBoundary s T (visitActiveInterval c) J) hiE
  rw [hz, zero_add] at hs
  exact hs.symm.le.trans hx

/-- The true short-time count inequality holds for each actual entrance, with a universal cutoff. -/
theorem visitTimeQuadratic_entrance_mass_bound : ∃ D : ℝ, 0 ≤ D ∧
    ∀ (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
      (lam Lam : ℝ) (hlam : 0 < lam) (hLam : lam ≤ Lam) (A : SmoothAutonomous lam Lam)
      (c : Clock) (J : Interval) (s T b : ℝ) (P : Point)
      (_hP : s < P.time ∧ P.time < T ∧ P.velocity 0 ∈ J.carrier) (n : ℕ),
      let mu := visitEntrancePiece hH hLE hlam hLam A c J s T P n
      let E := visitUnionExitKernel hH hLE hlam hLam A (visitActiveUnion c J) s T
      let G := visitUnionGreenKernel hH hLE hlam hLam A (visitActiveUnion c J) s T
      let B := visitBoundary s T (visitActiveInterval c) J
      5 * c.r ^ 2 / 16 * (mu {p | p.time ∈ Icc b (b + c.r ^ 2)}).toReal ≤
        9 * c.r ^ 2 / 16 * (((E ∘ₘ mu).restrict Bᶜ) univ).toReal +
          (9 * D / 16 + 2 * Lam) *
            ((G ∘ₘ mu) {p | p.time ∈ Icc (b - c.r ^ 2) (b + 2 * c.r ^ 2)}).toReal := by
  obtain ⟨D, hD, hd⟩ := visitTimeQuadratic_activeGreen_integral_bound
  refine ⟨D, hD, ?_⟩
  intro hH hLE lam Lam hlam hLam A c J s T b P hP n
  dsimp only
  have hx := visitTimeQuadratic_retainedExit_integral_le hH hLE hlam hLam A c J s T b P n
  have hg := hd hH hLE lam Lam hlam hLam A c J s T b (visitEntrancePiece hH hLE hlam hLam A c J s T P n) inferInstance
  have hh := visitTimeQuadratic_entrance_green_identity hH hLE hlam hLam A c J s T b P hP n
  dsimp only at hx hg hh
  have hi := (visitTimeQuadratic_entrance_integral_lower
    hH hLE hlam hLam A c J s T b P n).trans hh.le
  rw [sub_eq_add_neg] at hi
  exact hi.trans (add_le_add hx hg)

/-- The actual short-time counting inequality sums over any finite number of visits. -/
theorem visitTimeQuadratic_partial_mass_bound : ∃ D : ℝ, 0 ≤ D ∧
    ∀ (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
      (lam Lam : ℝ) (hlam : 0 < lam) (hLam : lam ≤ Lam) (A : SmoothAutonomous lam Lam)
      (c : Clock) (J : Interval) (s T b : ℝ) (P : Point)
      (_hP : s < P.time ∧ P.time < T ∧ P.velocity 0 ∈ J.carrier) (N : ℕ),
      let mu := visitEntrancePiece hH hLE hlam hLam A c J s T P
      let E := visitUnionExitKernel hH hLE hlam hLam A (visitActiveUnion c J) s T
      let G := visitUnionGreenKernel hH hLE hlam hLam A (visitActiveUnion c J) s T
      let B := visitBoundary s T (visitActiveInterval c) J
      5 * c.r ^ 2 / 16 *
        (∑ n ∈ Finset.range N, (mu n {p | p.time ∈ Icc b (b + c.r ^ 2)}).toReal) ≤
        9 * c.r ^ 2 / 16 *
          (∑ n ∈ Finset.range N, (((E ∘ₘ mu n).restrict Bᶜ) univ).toReal) +
        (9 * D / 16 + 2 * Lam) *
          (∑ n ∈ Finset.range N,
            ((G ∘ₘ mu n) {p | p.time ∈ Icc (b - c.r ^ 2) (b + 2 * c.r ^ 2)}).toReal) := by
  obtain ⟨D, hD, hd⟩ := visitTimeQuadratic_entrance_mass_bound
  refine ⟨D, hD, ?_⟩
  intro hH hLE lam Lam hlam hLam A c J s T b P hP N
  have h := Finset.sum_le_sum (s := Finset.range N)
    (fun n _ => hd hH hLE lam Lam hlam hLam A c J s T b P hP n)
  dsimp only at h ⊢
  simpa only [Finset.mul_sum, Finset.sum_add_distrib] using h


/-- Active occupation in the cutoff window has total partial mass at most its time length. -/
theorem visitActiveGreen_partial_time_mass_le
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (c : Clock) (J : Interval) (s T b : ℝ) (hT : s < T)
    (P : Point) (hP : s < P.time ∧ P.time < T ∧ P.velocity 0 ∈ J.carrier) (N : ℕ) :
    ∑ n ∈ Finset.range N,
      ((visitUnionGreenKernel hH hLE hlam hLam A (visitActiveUnion c J) s T ∘ₘ
        visitEntrancePiece hH hLE hlam hLam A c J s T P n)
          {p | p.time ∈ Icc (b - c.r ^ 2) (b + 2 * c.r ^ 2)}).toReal ≤ 3 * c.r ^ 2 := by
  let W : Set Point := {p | p.time ∈ Icc (b - c.r ^ 2) (b + 2 * c.r ^ 2)}
  have hW : MeasurableSet W := isClosed_Icc.measurableSet.preimage continuous_time.measurable
  have hm := visitActiveGreen_partial_le hH hLE hlam hLam A c J s T hT P hP N W
  rw [visitOuterGreen_eq_strip hH hLE hlam hLam A J s T P hP] at hm
  have ht := stripGreen_timeMarginal hH hLE hlam hLam A J T
    ⟨P, WithTop.coe_lt_coe.mpr hP.2.1, hP.2.2⟩
    (Icc (b - c.r ^ 2) (b + 2 * c.r ^ 2)) isClosed_Icc.measurableSet
  rw [Real.volume_Icc] at ht
  have hw : b + 2 * c.r ^ 2 - (b - c.r ^ 2) = 3 * c.r ^ 2 := by ring
  rw [hw] at ht
  have hh := ENNReal.toReal_mono ENNReal.ofReal_ne_top (hm.trans ht)
  rw [ENNReal.toReal_ofReal (by positivity), visit_partial_real_mass _ N W hW] at hh
  exact hh




/-- The literal source half-open short-time window satisfies the same uniform count bound. -/
theorem visit_short_time_mass {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
        (A : SmoothAutonomous lam Lam) (c : Clock) (Z0 : Point) (R : ℝ) (hR : 0 < R)
        (P : Point) (hP : P ∈ forwardCylinder Z0 R hR) (b : ℝ),
        visitStartsQ hH hLE hlam hLam A c Z0 R hR P hP
          {p | p.time ∈ Ioc b (b + c.r ^ 2)} ≤ ENNReal.ofReal C  := by
  have visit_short_time_mass_closed :
      ∃ C : ℝ, 0 < C ∧
      ∀ (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
        (A : SmoothAutonomous lam Lam) (c : Clock) (Z0 : Point) (R : ℝ) (hR : 0 < R)
        (P : Point) (hP : P ∈ forwardCylinder Z0 R hR) (b : ℝ),
        visitStartsQ hH hLE hlam hLam A c Z0 R hR P hP
          {p | p.time ∈ Icc b (b + c.r ^ 2)} ≤ ENNReal.ofReal C := by
    have exists_visitTime_mass_constant :
        ∃ C : ℝ, 0 < C ∧
        ∀ (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
          (A : SmoothAutonomous lam Lam) (c : Clock) (J : Interval) (s T b : ℝ) (_hT : s < T)
          (P : Point) (_hP : s < P.time ∧ P.time < T ∧ P.velocity 0 ∈ J.carrier),
          Measure.sum (visitEntrancePiece hH hLE hlam hLam A c J s T P)
            {p | p.time ∈ Icc b (b + c.r ^ 2)} ≤ ENNReal.ofReal C := by
      have exists_visitTime_partial_constant :
          ∃ C : ℝ, 0 < C ∧
          ∀ (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
            (A : SmoothAutonomous lam Lam) (c : Clock) (J : Interval) (s T b : ℝ) (_hT : s < T)
            (P : Point) (_hP : s < P.time ∧ P.time < T ∧ P.velocity 0 ∈ J.carrier) (N : ℕ),
            (∑ n ∈ Finset.range N,
              (visitEntrancePiece hH hLE hlam hLam A c J s T P n
                {p | p.time ∈ Icc b (b + c.r ^ 2)}).toReal) ≤ C := by
        obtain ⟨D, hD, hd⟩ := visitTimeQuadratic_partial_mass_bound
        let M := 9 * D / 16 + 2 * Lam
        have hM : 0 ≤ M := by dsimp only [M]; linarith
        refine ⟨9 / 5 + 48 * M / 5, by positivity, ?_⟩
        intro hH hLE A c J s T b hT P hP N
        have h := hd hH hLE lam Lam hlam hLam A c J s T b P hP N
        have he := visitRetainedExit_partial_real_mass_le_one hH hLE hlam hLam A c J s T hT P hP N
        have hg := visitActiveGreen_partial_time_mass_le hH hLE hlam hLam A c J s T b hT P hP N
        dsimp only at h he hg
        have hh := h.trans (add_le_add
          (mul_le_mul_of_nonneg_left he (by positivity)) (mul_le_mul_of_nonneg_left hg hM))
        have hr : 0 < c.r ^ 2 := pow_pos c.positive _
        change 5 * c.r ^ 2 / 16 * _ ≤ 9 * c.r ^ 2 / 16 * 1 + M * (3 * c.r ^ 2) at hh
        nlinarith only [hh, hr]
      obtain ⟨C, hC, hc⟩ := exists_visitTime_partial_constant
      refine ⟨C, hC, ?_⟩
      intro hH hLE A c J s T b hT P hP
      let W : Set Point := {p | p.time ∈ Icc b (b + c.r ^ 2)}
      have hW : MeasurableSet W := isClosed_Icc.measurableSet.preimage continuous_time.measurable
      rw [Measure.sum_apply _ hW]
      apply ENNReal.tsum_le_of_sum_range_le
      intro N
      rw [← Measure.finsetSum_apply]
      apply (ENNReal.le_ofReal_iff_toReal_le (measure_ne_top _ W) hC.le).mpr
      rw [visit_partial_real_mass _ N W hW]
      exact hc hH hLE A c J s T b hT P hP N
    obtain ⟨C, hC, hc⟩ := exists_visitTime_mass_constant
    refine ⟨C, hC, ?_⟩
    intro hH hLE A c Z0 R hR P hP b
    exact hc hH hLE A c (capacityCylinderInterval Z0 R hR) Z0.time (Z0.time + R ^ 2) b
      (by nlinarith [sq_pos_of_pos hR]) P (visitCylinderStart_mem Z0 R hR P hP)
  obtain ⟨C, hC, hc⟩ := visit_short_time_mass_closed
  refine ⟨C, hC, ?_⟩
  intro hH hLE A c Z0 R hR P hP b
  have hs : {p : Point | p.time ∈ Ioc b (b + c.r ^ 2)} ⊆
      {p | p.time ∈ Icc b (b + c.r ^ 2)} := fun _ hp => ⟨hp.1.le, hp.2⟩
  exact (measure_mono hs).trans (hc hH hLE A c Z0 R hR P hP b)


/-- The source core Green density has the exact radius and entrance-count scaling. -/
theorem entrance_density
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (q : ℝ) (hq : 1 < q ∧ q < 3 / 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ (A : SmoothAutonomous lam Lam) (c : Clock)
      (Z0 : Point) (R : ℝ) (hR : 0 < R) (P : Point)
      (hP : P ∈ forwardCylinder Z0 R hR)
      (_hcore : (c.core ∩ (capacityCylinderInterval Z0 R hR).carrier).Nonempty),
      enlargedDensityBound
        ((stripGreen hH hLE hlam hLam A (capacityCylinderInterval Z0 R hR)
          (Z0.time + R ^ 2) (capacityCylinderPole Z0 P R hR hP)).restrict
            {p | p.velocity 0 ∈ c.core}) (densityObservationStrip Z0 R hR) q
        (C * c.r ^ (6 / q - 4) * (1 + R / c.r) ^ (1 / q)) := by
  obtain ⟨B, hB, hb⟩ := exists_visitStartsQ_mass_constant hlam hLam
  obtain ⟨M, hM, hm⟩ := visit_short_time_mass hlam hLam
  obtain ⟨C, hC, hc⟩ := entrance_density_from_counts hH hLE hlam hLam q hq B M hB hM
  refine ⟨C, hC, ?_⟩
  intro A c Z0 R hR P hP _hcore
  have : SigmaFinite (volume : Measure Point) := density_volume_sigmaFinite
  let nu := visitStartsQ hH hLE hlam hLam A c Z0 R hR P hP
  have : IsFiniteMeasure nu := visitStartsQ_isFiniteMeasure hH hLE hlam hLam A c Z0 R hR P hP
  have hnu : ∀ᵐ e ∂nu, e.velocity 0 ∈ c.active :=
    (entrance_visitStartsQ_ae_closedEntrance hH hLE hlam hLam A c Z0 R hR P hP).mono
      (fun _ h => visitClosedEntrance_subset_active c h)
  have hshort (k : ℤ) : nu (entranceTimeBin c.r k) ≤ ENNReal.ofReal M := by
    simpa [entranceTimeBin, add_mul] using
      hm hH hLE A c Z0 R hR P hP ((k : ℝ) * c.r ^ 2)
  obtain ⟨G, hGm, hG0, hGd, hGp, hGn⟩ := hc A c nu (1 + R / c.r)
    (by positivity [c.positive]) hnu (hb hH hLE A c Z0 R hR P hP) hshort
  let Q := {p : Point | p.velocity 0 ∈ c.core}
  let mu := (stripGreen hH hLE hlam hLam A (capacityCylinderInterval Z0 R hR)
    (Z0.time + R ^ 2) (capacityCylinderPole Z0 P R hR hP)).restrict Q
  have hmajor : mu ≤ enlargedActiveGreen hH hLE hlam hLam A c nu :=
    ((core_green_le_visitGreen hH hLE hlam hLam A c Z0 R hR P hP).trans_eq (congrArg (fun rho => rho.restrict Q) (entrance_coreAllTimeGreen_eq hH hLE hlam hLam A c nu))).trans
      Measure.restrict_le_self
  have : IsFiniteMeasure (enlargedActiveGreen hH hLE hlam hLam A c nu) :=
    enlargedActiveGreen_isFiniteMeasure hH hLE hlam hLam A c nu
  have : IsFiniteMeasure mu := isFiniteMeasure_of_le _ hmajor
  have hle : mu ≤ volume.withDensity (fun p => ENNReal.ofReal (G p)) :=
    hmajor.trans_eq hGd
  obtain ⟨g, hgm, hg0, hgd, hgp, hgn⟩ :=
    density_of_le_withDensity volume mu G hGm hG0 (ENNReal.ofReal q) hGp hle
  let D := densityObservationStrip Z0 R hR
  have hD : MeasurableSet D :=
    (continuous_time.measurable measurableSet_Ioi).inter
      ((continuous_time.measurable measurableSet_Iio).inter
        (isOpen_Ioo.measurableSet.preimage
          ((continuous_apply 0).comp continuous_velocity).measurable))
  have hmu : ∀ᵐ p ∂mu, p ∈ D :=
    ae_restrict_of_ae (entrance_cylinderGreen_ae_observation hH hLE hlam hLam A Z0 R hR P hP)
  have hden : mu = (volume.restrict D).withDensity (fun p => ENNReal.ofReal (g p)) :=
    (Measure.restrict_eq_self_of_ae_mem hmu).symm.trans ((congrArg (fun rho : Measure Point => rho.restrict D) hgd).trans
      (restrict_withDensity hD (fun p => ENNReal.ofReal (g p))))
  refine ⟨g, ⟨hgm, hg0, hden⟩, hgp.restrict D, ?_⟩
  exact (ENNReal.toReal_mono hGp.ne_top ((eLpNorm_restrict_le g (ENNReal.ofReal q) volume D).trans hgn)).trans hGn

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous

