module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.GreenTestExtensionCutoffs
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.EnlargedVisitsCells
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Tactic
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.VisitMassOutgoing
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.BoxConcentrationSetting
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.ClockGeometry
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.EnlargedVisitMassTerminal
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.VisitMassCoefficientIntegral
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.InfiniteHorizonGreenSupport
import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.VisitRecursionUnconditionalInitial
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.EnlargedRecursionHorizonLimit
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.CoreDominationAllTimeKernel
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.PositionCellsSlab
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.EnlargedRecursionOccupation
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.PositionCellCountBounds
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.PositionCellCount

@[expose] public noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov HypoellipticAleksandrov.Parabolic ProbabilityTheory
open scoped Classical ENNReal

/-- A translated cutoff with inner radius three quarters of the cell width. -/
def positionStartCutoff (Y r : ℝ) (hr : 0 < r) (X : ℝ) : ℝ :=
  reconstructionPositionBump (3 * r ^ 3 / 4) (by positivity) (X - Y)

/-- The position cutoff is smooth and lies between zero and one. -/
theorem positionStartCutoff_properties (Y r : ℝ) (hr : 0 < r) :
    ContDiff ℝ (⊤ : ℕ∞) (positionStartCutoff Y r hr) ∧
      (∀ X, 0 ≤ positionStartCutoff Y r hr X ∧ positionStartCutoff Y r hr X ≤ 1) :=
  ⟨(reconstructionPositionBump _ _).contDiff.comp (contDiff_id.sub contDiff_const),
    fun _ => ⟨(reconstructionPositionBump _ _).nonneg,
      (reconstructionPositionBump _ _).le_one⟩⟩

/-- It equals one within half a cell width of its centre. -/
theorem positionStartCutoff_eq_one (Y r : ℝ) (hr : 0 < r) {X : ℝ}
    (ht : |X - Y| ≤ r ^ 3 / 2) : positionStartCutoff Y r hr X = 1 := by
  apply (reconstructionPositionBump _ _).one_of_mem_closedBall
  rw [Metric.mem_closedBall, Real.dist_eq, sub_zero]
  change |X - Y| ≤ 3 * r ^ 3 / 4
  apply abs_le.mpr
  constructor <;> linarith [pow_pos hr 3, (abs_le.mp ht).1, (abs_le.mp ht).2]


/-- A single constant controls the derivative of every rescaled position cutoff. -/
theorem positionStartCutoff_deriv_bound : ∃ D : ℝ, 0 ≤ D ∧
    ∀ (Y r : ℝ) (hr : 0 < r) (X : ℝ),
      |deriv (positionStartCutoff Y r hr) X| ≤ D / r ^ 3 := by
  obtain ⟨D, hD, hd⟩ := reconstructionUnitBump_properties.2.2.2
  refine ⟨4 * D / 3, by positivity, ?_⟩
  intro Y r hr X
  have hs : ContDiff ℝ (⊤ : ℕ∞)
      (reconstructionPositionBump (3 * r ^ 3 / 4) (by positivity) : ℝ → ℝ) :=
    (reconstructionPositionBump _ _).contDiff
  have hc := (hs.differentiable (by norm_num) (X - Y)).hasDerivAt.comp X
    ((hasDerivAt_id X).sub_const Y)
  have he : deriv (positionStartCutoff Y r hr) X =
      deriv (reconstructionPositionBump (3 * r ^ 3 / 4) (by positivity))
        (X - Y) := by
    have hf : positionStartCutoff Y r hr = fun x =>
        reconstructionPositionBump (3 * r ^ 3 / 4) (by positivity)
          (x - Y) := rfl
    rw [hf]
    simpa [Function.comp_def] using hc.deriv
  rw [he]
  convert (reconstructionPositionBump_deriv_bound (3 * r ^ 3 / 4) (by positivity) D hd (X - Y)) using 1
  field_simp


/-- The closed support stays within the same length-three position interval. -/
theorem positionStartCutoff_tsupport (Y r : ℝ) (hr : 0 < r) :
    tsupport (positionStartCutoff Y r hr) ⊆
      Icc (Y - 3 * r ^ 3 / 2) (Y + 3 * r ^ 3 / 2)  := by
  have positionStartCutoff_support :
      Function.support (positionStartCutoff Y r hr) ⊆
      Ioo (Y - 3 * r ^ 3 / 2) (Y + 3 * r ^ 3 / 2) := by
    intro X ht
    have hb : X - Y ∈
        Function.support (reconstructionPositionBump (3 * r ^ 3 / 4) (by positivity)) := ht
    rw [ContDiffBump.support_eq, Metric.mem_ball, Real.dist_eq, sub_zero] at hb
    change |X - Y| < 2 * (3 * r ^ 3 / 4) at hb
    obtain ⟨hl, hu⟩ := abs_lt.mp hb
    constructor <;> linarith
  have h := closure_mono (positionStartCutoff_support)
  rw [closure_Ioo (by linarith [pow_pos hr 3])] at h
  exact h


/-- The position-localized quadratic has exactly the source transport-diffusion operator. -/
theorem positionStartQuadratic_operator (c : Clock) (eta : ℝ → ℝ)
    (heta : ContDiff ℝ (⊤ : ℕ∞) eta) (a : ℝ → ℝ → ℝ) (p : Point) :
    forwardScalarOperator a (fun q => eta (q.position 0) * visitQuadratic c (q.velocity 0)) p =
      p.velocity 0 * deriv eta (p.position 0) * visitQuadratic c (p.velocity 0) -
        2 * a (p.position 0) (p.velocity 0) * eta (p.position 0) := by
  have hposition : deriv (fun X => eta X * visitQuadratic c (p.velocity 0))
      (p.position 0) = deriv eta (p.position 0) * visitQuadratic c (p.velocity 0) :=
    ((heta.differentiable (by norm_num) (p.position 0)).hasDerivAt.mul_const _).deriv
  have hquad (v : ℝ) : HasDerivAt (visitQuadratic c) (-2 * (v - c.vbar)) v := by
    have h := ((visitQuadratic_smooth c).differentiable (by norm_num) v).hasDerivAt
    rwa [visitQuadratic_deriv] at h
  have hsecond : deriv (deriv (fun v => eta (p.position 0) * visitQuadratic c v)) (p.velocity 0) =
      eta (p.position 0) * (-2) := by
    rw [(funext fun v => ((hquad v).const_mul (eta (p.position 0))).deriv)]
    simpa using (((hasDerivAt_id (p.velocity 0)).sub_const c.vbar).const_mul (-2).const_mul (eta (p.position 0))).deriv
  rw [forwardScalarOperator, kineticPositionGradient_scalar, kineticVelocityHessian_scalar]
  simp only [kineticTimeDerivative, deriv_const, hposition, zero_add, hsecond]
  ring



/-- The source localized quadratic has a uniform generator bound on the active interval. -/
theorem positionStartQuadratic_operator_bound {lam Lam : ℝ}
    (hlam : 0 < lam) (hLam : lam ≤ Lam) :
    ∃ C : ℝ, 0 < C ∧ ∀ (A : SmoothAutonomous lam Lam) (c : Clock) (Y : ℝ) (p : Point),
      |c.vbar| = 2 * c.r → p.velocity 0 ∈ c.active →
      |forwardScalarOperator A.a
        (fun q => positionStartCutoff Y c.r c.positive (q.position 0) *
          visitQuadratic c (q.velocity 0)) p| ≤
        C * (box 4 c.r Y).indicator (fun _ => (1 : ℝ)) (p.position 0, p.velocity 0) := by
  obtain ⟨D, hD, hd⟩ := positionStartCutoff_deriv_bound
  refine ⟨2 * Lam + 27 * D / 16, by linarith, ?_⟩
  intro A c Y p hc hv
  have hr := c.positive
  let chi := positionStartCutoff Y c.r c.positive
  have h01 := (positionStartCutoff_properties Y c.r c.positive).2 (p.position 0)
  have hq0 := visitQuadratic_nonneg c (subset_closure hv)
  have hva : |p.velocity 0| ≤ 3 * c.r := by
    have hh := (c.active_abs_bounds hv).2
    rw [hc] at hh
    linarith only [hh]
  have ha0 : 0 ≤ A.a (p.position 0) (p.velocity 0) :=
    hlam.le.trans (A.bounds _ _).1
  rw [positionStartQuadratic_operator c chi ((positionStartCutoff_properties Y c.r c.positive).1)]
  by_cases hp : (p.position 0, p.velocity 0) ∈ box 4 c.r Y
  · rw [indicator_of_mem hp, mul_one]
    apply (abs_sub _ _).trans
    rw [abs_mul, abs_mul, abs_of_nonneg hq0, abs_mul, abs_mul,
      abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2), abs_of_nonneg ha0,
      abs_of_nonneg h01.1]
    have hfirst : |p.velocity 0| * |deriv chi (p.position 0)| *
        visitQuadratic c (p.velocity 0) ≤
        (3 * c.r) * (D / c.r ^ 3) * (9 * c.r ^ 2 / 16) := by
      apply mul_le_mul (mul_le_mul hva (hd Y c.r c.positive (p.position 0))
        (abs_nonneg _) (by positivity)) (visitQuadratic_le c (p.velocity 0)) hq0 (by positivity)
    have hsecond : 2 * A.a (p.position 0) (p.velocity 0) * chi (p.position 0) ≤
        2 * Lam := by
      have h := mul_le_mul_of_nonneg_left h01.2 (by positivity :
        0 ≤ 2 * A.a (p.position 0) (p.velocity 0))
      simp at h
      exact h.trans (mul_le_mul_of_nonneg_left ((A.bounds (p.position 0) (p.velocity 0)).2) (by norm_num))
    have he : (3 * c.r) * (D / c.r ^ 3) * (9 * c.r ^ 2 / 16) = 27 * D / 16 := by
      field_simp [c.positive.ne']
      ring
    rw [he] at hfirst
    linarith only [hfirst, hsecond]
  · rw [indicator_of_notMem hp, mul_zero]
    have hnot : p.position 0 ∉ tsupport chi := by
      intro hx
      have hh := positionStartCutoff_tsupport Y c.r c.positive hx
      apply hp
      change |p.position 0 - Y| ≤ 4 * c.r ^ 3 ∧ |p.velocity 0| ≤ 4 * c.r
      constructor
      · apply abs_le.mpr
        constructor <;> linarith [hh.1, hh.2, pow_pos c.positive 3]
      · linarith [c.positive]
    rw [image_eq_zero_of_notMem_tsupport hnot, deriv_of_notMem_tsupport hnot]
    simp


/-- Closed active support bounds the localized test by the exact quadratic maximum. -/
theorem positionStartQuadratic_integrable (c : Clock) (Y : ℝ)
    (mu : Measure Point) [IsFiniteMeasure mu]
    (hmu : ∀ᵐ p ∂mu, p.velocity 0 ∈ closure c.active) :
    Integrable (fun p => positionStartCutoff Y c.r c.positive (p.position 0) *
      visitQuadratic c (p.velocity 0)) mu := by
  have hc := ((positionStartCutoff_properties Y c.r c.positive).1.continuous.comp ((continuous_apply (0 : Fin 1)).comp continuous_position)).mul
    ((visitQuadratic_smooth c).continuous.comp ((continuous_apply (0 : Fin 1)).comp continuous_velocity))
  apply Integrable.mono' (integrable_const (9 * c.r ^ 2 / 16))
    hc.measurable.aestronglyMeasurable
  filter_upwards [hmu] with p hp
  change ‖positionStartCutoff Y c.r c.positive (p.position 0) *
    visitQuadratic c (p.velocity 0)‖ ≤ 9 * c.r ^ 2 / 16
  rw [Real.norm_eq_abs, abs_mul,
    abs_of_nonneg ((positionStartCutoff_properties Y c.r c.positive).2 _).1,
    abs_of_nonneg (visitQuadratic_nonneg c hp)]
  exact (mul_le_mul_of_nonneg_right
    ((positionStartCutoff_properties Y c.r c.positive).2 _).2
    (visitQuadratic_nonneg c hp)).trans (by
      simpa using visitQuadratic_le c (p.velocity 0))


/-- Finite active occupation makes the exact position-localized operator integrable. -/
theorem positionStartQuadratic_operator_integrable {lam Lam : ℝ}
    (hlam : 0 < lam) (hLam : lam ≤ Lam) (A : SmoothAutonomous lam Lam)
    (c : Clock) (Y : ℝ) (hc : |c.vbar| = 2 * c.r)
    (mu : Measure Point) [IsFiniteMeasure mu]
    (hmu : ∀ᵐ p ∂mu, p.velocity 0 ∈ c.active) :
    Integrable (fun p => forwardScalarOperator A.a
      (fun q => positionStartCutoff Y c.r c.positive (q.position 0) *
        visitQuadratic c (q.velocity 0)) p) mu  := by
  have positionStartQuadratic_operator_continuous :
      Continuous (fun p => forwardScalarOperator A.a
      (fun q => positionStartCutoff Y c.r c.positive (q.position 0) *
        visitQuadratic c (q.velocity 0)) p) := by
    have he := (positionStartCutoff_properties Y c.r c.positive).1
    have hx := (continuous_apply (0 : Fin 1)).comp continuous_position
    have hv := (continuous_apply (0 : Fin 1)).comp continuous_velocity
    have hh := funext (positionStartQuadratic_operator c (positionStartCutoff Y c.r c.positive) he A.a)
    rw [hh]
    exact ((hv.mul ((he.continuous_deriv (by norm_num)).comp hx)).mul
      ((visitQuadratic_smooth c).continuous.comp hv)).sub
        ((continuous_const.mul (visitCoefficient_continuous A)).mul (he.continuous.comp hx))
  obtain ⟨C, hC, hb⟩ := positionStartQuadratic_operator_bound hlam hLam
  apply Integrable.mono' (integrable_const C)
    (positionStartQuadratic_operator_continuous).measurable.aestronglyMeasurable
  filter_upwards [hmu] with p hp
  rw [Real.norm_eq_abs]
  apply (hb A c Y p hc hp).trans
  by_cases hbox : (p.position 0, p.velocity 0) ∈ box 4 c.r Y
  · rw [indicator_of_mem hbox, mul_one]
  · rw [indicator_of_notMem hbox, mul_zero]
    exact hC.le


/-- The concrete terminal family, including its zero-duration atom, is measurable. -/
theorem positionStartTerminalFamily_measurable
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (c : Clock) (J : Interval) (b : ℝ) :
    Measurable (enlargedActiveTerminalFamily hH hLE hlam hLam A c J b) := by
  let E := enlargedVisitExitKernel hH hLE hlam hLam A (visitActiveUnion c J) b
  have hS : MeasurableSet {q : Point | q.time = b} :=
    (isClosed_eq continuous_time continuous_const).measurableSet
  have hm : Measurable (fun p => (E p).restrict {q | q.time = b}) :=
    Measure.measurable_of_measurable_coe _ fun B hB => by
      simp_rw [Measure.restrict_apply hB]
      exact E.measurable_coe (hB.inter hS)
  exact Measure.measurable_dirac.ite
    (hS.inter ((visitActiveUnion c J).isOpen_carrier.measurableSet.preimage
      ((continuous_apply 0).comp continuous_velocity).measurable)) hm


/-- Before a finite observation time, the concrete terminal family obeys the Green identity. -/
theorem positionStartQuadratic_terminal_identity
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (c : Clock) (J : Interval) (Y b : ℝ)
    (hc : |c.vbar| = 2 * c.r) (hJ : closure c.active ⊆ J.carrier)
    (p : Point) (hv : p.velocity 0 ∈ c.active) (ht : p.time < b) :
    let f := fun q : Point => positionStartCutoff Y c.r c.positive (q.position 0) *
      visitQuadratic c (q.velocity 0)
    f p = (∫ q, f q ∂enlargedActiveTerminalFamily hH hLE hlam hLam A c J b p) -
      ∫ q, forwardScalarOperator A.a f q
        ∂enlargedVisitGreenKernel hH hLE hlam hLam A (visitActiveUnion c J) b p   := by
  have positionStartQuadratic_exit_integral_eq_terminal (T : ℝ) (mu : Measure Point) (ht : ∀ᵐ p ∂mu, p.time < T) :
      (∫ q, positionStartCutoff Y c.r c.positive (q.position 0) *
      visitQuadratic c (q.velocity 0)
      ∂(enlargedVisitExitKernel hH hLE hlam hLam A (visitActiveUnion c J) T ∘ₘ mu)) =
    ∫ q, positionStartCutoff Y c.r c.positive (q.position 0) *
      visitQuadratic c (q.velocity 0)
      ∂mu.bind (enlargedActiveTerminalFamily hH hLE hlam hLam A c J T) := by
    rw [enlargedActiveTerminal_bind_eq_restrict hH hLE hlam hLam A c J T mu ht]
    symm
    rw [← integral_indicator (isClosed_eq continuous_time continuous_const).measurableSet]
    apply integral_congr_ae
    filter_upwards [enlargedActiveExit_ae_quadratic_zero_or_terminal
      hH hLE hlam hLam A c J T hJ mu] with q hq
    rcases hq with hq | hq
    · simp [Set.indicator, hq]
    · by_cases htq : q.time = T
      · simp [Set.indicator, htq]
      · simp [Set.indicator, htq, hq]
  have positionStartQuadratic_active_identity (T : ℝ) (e : FiniteUnionPole (visitActiveUnion c J) (T : WithTop ℝ)) :
      let f := fun q => positionStartCutoff Y c.r c.positive (q.position 0) *
      visitQuadratic c (q.velocity 0)
    f e.1 = (∫ p, f p ∂finiteUnionExit hH hLE hlam hLam A (visitActiveUnion c J) T e) -
      ∫ p, forwardScalarOperator A.a f p
        ∂finiteUnionGreen hH hLE hlam hLam A (visitActiveUnion c J) T e := by
    have positionStartQuadratic_smooth (eta : ℝ → ℝ) (heta : ContDiff ℝ (⊤ : ℕ∞) eta) : ContDiff ℝ (⊤ : ℕ∞)
        ((fun q : Point => eta (q.position 0) * visitQuadratic c (q.velocity 0)) ∘
          (KineticPoint.equivProd 1).symm) :=
      (heta.comp ((contDiff_apply ℝ ℝ 0).comp contDiff_snd.fst)).mul
          ((visitQuadratic_smooth c).comp
            ((contDiff_apply ℝ ℝ 0).comp contDiff_snd.snd))
    dsimp only
    apply visitUnion_identity_bounded_smooth hH hLE hlam hLam A (visitActiveUnion c J) T e
      (fun q => positionStartCutoff Y c.r c.positive (q.position 0) *
        visitQuadratic c (q.velocity 0))
    · exact positionStartQuadratic_smooth _
        (positionStartCutoff_properties Y c.r c.positive).1
    · obtain ⟨C, hC, hb⟩ := positionStartQuadratic_operator_bound hlam hLam
      refine ⟨max (9 * c.r ^ 2 / 16) C, ?_⟩
      intro p hp
      have hv := ((visitActiveUnion_carrier c J).le hp).1
      have hchi := (positionStartCutoff_properties Y c.r c.positive).2 (p.position 0)
      have hquad := visitQuadratic_nonneg c (subset_closure hv)
      constructor
      · rw [abs_mul, abs_of_nonneg hchi.1, abs_of_nonneg hquad]
        exact ((mul_le_mul_of_nonneg_right hchi.2 hquad).trans
          (by simpa using visitQuadratic_le c (p.velocity 0))).trans
            (le_max_left _ _)
      · apply (hb A c Y p hc hv).trans
        by_cases hbox : (p.position 0, p.velocity 0) ∈ box 4 c.r Y
        · rw [indicator_of_mem hbox, mul_one]
          exact le_max_right _ _
        · rw [indicator_of_notMem hbox, mul_zero]
          exact hC.le.trans (le_max_right _ _)
  dsimp only
  have hp : p ∈ enlargedVisitPoleSet (visitActiveUnion c J) b := by
    refine ⟨ht, ?_⟩
    rw [visitActiveUnion_carrier]
    exact ⟨hv, hJ (subset_closure hv)⟩
  let e := enlargedVisitPole (visitActiveUnion c J) b ⟨p, hp⟩
  have hi := positionStartQuadratic_active_identity b e
  have hE : enlargedVisitExitKernel hH hLE hlam hLam A (visitActiveUnion c J) b p =
      finiteUnionExit hH hLE hlam hLam A (visitActiveUnion c J) b e := by
    change (if h : p ∈ enlargedVisitPoleSet (visitActiveUnion c J) b then _ else 0) = _
    rw [dite_eq_left hp]
  have hG : enlargedVisitGreenKernel hH hLE hlam hLam A (visitActiveUnion c J) b p =
      finiteUnionGreen hH hLE hlam hLam A (visitActiveUnion c J) b e := by
    change (if h : p ∈ enlargedVisitPoleSet (visitActiveUnion c J) b then _ else 0) = _
    rw [dite_eq_left hp]
  have he := positionStartQuadratic_exit_integral_eq_terminal b (Measure.dirac p)
      ((ae_dirac_iff (isOpen_lt continuous_time continuous_const).measurableSet).mpr ht)
  rw [visitKernel_comp_dirac,
    Measure.dirac_bind (positionStartTerminalFamily_measurable
      hH hLE hlam hLam A c J b)] at he
  rw [hE] at he
  dsimp only at hi
  rw [← hG, he] at hi
  exact hi

/-- Clipping the genuine all-time active occupation at `b` gives its finite Green kernel. -/
theorem positionStartGreen_eq_restrict
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (c : Clock) (J : Interval) (b : ℝ)
    (hJ : closure c.active ⊆ J.carrier) (p : Point)
    (hv : p.velocity 0 ∈ c.active) (ht : p.time < b) :
    enlargedVisitGreenKernel hH hLE hlam hLam A (visitActiveUnion c J) b p =
      (stripGreen hH hLE hlam hLam A c.activeInterval ⊤
        (densityClockPole c p hv)).restrict {q | q.time < b} := by
  rw [enlarged_activeUnion_eq c J hJ]
  have hp : p ∈ enlargedVisitPoleSet c.activeInterval.toFiniteUnion b := by
    refine ⟨ht, ?_⟩
    rw [Interval.toFiniteUnion_carrier]
    exact (densityClockPole c p hv).2.2
  change (if h : p ∈ enlargedVisitPoleSet c.activeInterval.toFiniteUnion b then _
    else 0) = _
  rw [dite_eq_left hp]
  exact stripGreen_finite_restrict_infinite hH hLE hlam hLam A c.activeInterval
    (densityClockPole c p hv) b ht


/-- The all-time active occupation has no atom on a fixed time slice. -/
theorem positionStartGreen_ae_time_ne
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (c : Clock) (p : Point)
    (hv : p.velocity 0 ∈ c.active) (b : ℝ) :
    ∀ᵐ q ∂stripGreen hH hLE hlam hLam A c.activeInterval ⊤
      (densityClockPole c p hv), q.time ≠ b := by
  rw [ae_iff]
  simpa using enlarged_stripGreen_time_slice_zero
    hH hLE hlam hLam A c.activeInterval (densityClockPole c p hv) b



/-- The existing terminal family as a measurable kernel, including zero-duration starts. -/
def positionStartTerminalKernel
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (c : Clock) (J : Interval) (b : ℝ) :
    Kernel Point Point :=
  ⟨enlargedActiveTerminalFamily hH hLE hlam hLam A c J b,
    positionStartTerminalFamily_measurable hH hLE hlam hLam A c J b⟩

/-- Every actual active terminal family has mass at most one. -/
theorem positionStartTerminalKernel_mass_le_one
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (c : Clock) (J : Interval) (b : ℝ) (p : Point) :
    positionStartTerminalKernel hH hLE hlam hLam A c J b p univ ≤ 1 := by
  change (enlargedActiveTerminalFamily hH hLE hlam hLam A c J b p) univ ≤ 1
  unfold enlargedActiveTerminalFamily
  split
  · simp
  · apply (Measure.restrict_le_self univ).trans
    change (if h : p ∈ enlargedVisitPoleSet (visitActiveUnion c J) b then _
      else (0 : Measure Point)) univ ≤ 1
    split
    · simp
    · exact zero_le

/-- The terminal kernel is uniformly finite without a domination hypothesis. -/
instance positionStartTerminalKernel_isFiniteKernel
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (c : Clock) (J : Interval) (b : ℝ) :
    IsFiniteKernel (positionStartTerminalKernel hH hLE hlam hLam A c J b) :=
  ⟨1, ENNReal.one_lt_top,
    positionStartTerminalKernel_mass_le_one hH hLE hlam hLam A c J b⟩

/-- Terminal mixtures retain the closed active velocity support. -/
theorem positionStartTerminalMixture_ae_closedActive
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (c : Clock) (J : Interval) (b : ℝ)
    (mu : Measure Point) :
    ∀ᵐ q ∂(positionStartTerminalKernel hH hLE hlam hLam A c J b ∘ₘ mu),
      q.velocity 0 ∈ closure c.active := by
  apply Measure.ae_comp_of_ae_ae
    (isClosed_closure.measurableSet.preimage
      ((continuous_apply 0).comp continuous_velocity).measurable)
  apply Filter.Eventually.of_forall
  intro p
  change ∀ᵐ q ∂enlargedActiveTerminalFamily hH hLE hlam hLam A c J b p,
    q.velocity 0 ∈ closure c.active
  unfold enlargedActiveTerminalFamily
  split
  · rename_i hp
    apply (ae_dirac_iff (isClosed_closure.measurableSet.preimage
      ((continuous_apply 0).comp continuous_velocity).measurable)).mpr
    exact subset_closure ((visitActiveUnion_carrier c J).le hp.2).1
  · have hs := enlargedActiveExitMixture_ae_velocity
      hH hLE hlam hLam A c J b (Measure.dirac p)
    rw [visitKernel_comp_dirac] at hs
    exact hs.filter_mono (ae_mono Measure.restrict_le_self)

/-- Finite all-time active mixtures retain open active support. -/
theorem positionStartAllTimeMixture_ae_active
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (c : Clock) (mu : Measure Point) :
    ∀ᵐ q ∂(coreAllTimeGreenKernel hH hLE hlam hLam A c ∘ₘ mu),
      q.velocity 0 ∈ c.active := by
  apply Measure.ae_comp_of_ae_ae
    (isOpen_Ioo.measurableSet.preimage
      ((continuous_apply 0).comp continuous_velocity).measurable)
  apply Filter.Eventually.of_forall
  intro p
  change ∀ᵐ q ∂(if hp : p.velocity 0 ∈ c.active then
    stripGreen hH hLE hlam hLam A (visitActiveInterval c) ⊤
      (coreAllTimePole c ⟨p, hp⟩) else 0), q.velocity 0 ∈ c.active
  split
  · exact (stripGreen_infinite_ae_future_carrier hH hLE hlam hLam A
      (visitActiveInterval c) _).mono fun _ hq => hq.2
  · simp


/-- Finite active starting measures satisfy the exact position-resolved slab identity. -/
theorem positionStartQuadratic_integrated_slab_identity
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (c : Clock) (J : Interval) (Y a b : ℝ)
    (hc : |c.vbar| = 2 * c.r) (hJ : closure c.active ⊆ J.carrier)
    (mu : Measure Point) [IsFiniteMeasure mu]
    (hmu : ∀ᵐ p ∂mu, p.velocity 0 ∈ c.active) (hab : a ≤ b) :
    let f := fun q : Point => positionStartCutoff Y c.r c.positive (q.position 0) *
      visitQuadratic c (q.velocity 0)
    (∫ p in {q : Point | a < q.time ∧ q.time ≤ b}, f p ∂mu) =
      (∫ q, f q ∂(positionStartTerminalKernel hH hLE hlam hLam A c J b ∘ₘ mu)) -
      (∫ q, f q ∂(positionStartTerminalKernel hH hLE hlam hLam A c J a ∘ₘ mu)) -
      ∫ q in {q : Point | a < q.time ∧ q.time ≤ b}, forwardScalarOperator A.a f q
        ∂(coreAllTimeGreenKernel hH hLE hlam hLam A c ∘ₘ mu)  := by
  have positionStartQuadratic_slab_identity (p : Point) (hv : p.velocity 0 ∈ c.active) :
      let f := fun q : Point => positionStartCutoff Y c.r c.positive (q.position 0) *
      visitQuadratic c (q.velocity 0)
    ({q : Point | a < q.time ∧ q.time ≤ b}.indicator f) p =
      (∫ q, f q ∂enlargedActiveTerminalFamily hH hLE hlam hLam A c J b p) -
      (∫ q, f q ∂enlargedActiveTerminalFamily hH hLE hlam hLam A c J a p) -
      ∫ q in {q : Point | a < q.time ∧ q.time ≤ b}, forwardScalarOperator A.a f q
        ∂stripGreen hH hLE hlam hLam A c.activeInterval ⊤ (densityClockPole c p hv) := by
    have positionStartQuadratic_cumulative_identity (b : ℝ) :
        let f := fun q : Point => positionStartCutoff Y c.r c.positive (q.position 0) *
        visitQuadratic c (q.velocity 0)
      ({q : Point | q.time ≤ b}.indicator f) p =
        (∫ q, f q ∂enlargedActiveTerminalFamily hH hLE hlam hLam A c J b p) -
        ∫ q in {q : Point | q.time ≤ b}, forwardScalarOperator A.a f q
          ∂stripGreen hH hLE hlam hLam A c.activeInterval ⊤ (densityClockPole c p hv) := by
      dsimp only
      let G := stripGreen hH hLE hlam hLam A c.activeInterval ⊤ (densityClockPole c p hv)
      have hvJ : p.velocity 0 ∈ (visitActiveUnion c J).carrier := by
        rw [visitActiveUnion_carrier]
        exact ⟨hv, hJ (subset_closure hv)⟩
      by_cases ht : p.time < b
      · rw [indicator_of_mem (show p ∈ {q : Point | q.time ≤ b} from ht.le)]
        have hi := positionStartQuadratic_terminal_identity
          hH hLE hlam hLam A c J Y b hc hJ p hv ht
        dsimp only at hi
        rw [positionStartGreen_eq_restrict hH hLE hlam hLam A c J b hJ p hv ht] at hi
        have hs : {q : Point | q.time < b} =ᵐ[G] {q | q.time ≤ b} := by
          filter_upwards [positionStartGreen_ae_time_ne hH hLE hlam hLam A c p hv b] with q hq
          exact propext (lt_iff_le_and_ne.trans (and_iff_left hq))
        rw [Measure.restrict_congr_set hs] at hi
        exact hi
      · have hbp : b ≤ p.time := le_of_not_gt ht
        have hz : G.restrict {q : Point | q.time ≤ b} = 0 := by
          apply Measure.restrict_eq_zero.mpr
          have hn :=
            (stripGreen_infinite_ae_future_carrier hH hLE hlam hLam A c.activeInterval
              (densityClockPole c p hv)).mono fun q hq => not_le_of_gt (hbp.trans_lt hq.1)
          rw [ae_iff] at hn
          simpa using hn
        change _ = _ - ∫ q, _ ∂G.restrict {q : Point | q.time ≤ b}
        rw [hz, integral_zero_measure, sub_zero]
        by_cases he : p.time = b
        · rw [indicator_of_mem (show p ∈ {q : Point | q.time ≤ b} from he.le)]
          unfold enlargedActiveTerminalFamily
          rw [ite_eq_left ⟨he, hvJ⟩, integral_dirac]
        · rw [indicator_of_notMem (show p ∉ {q : Point | q.time ≤ b} from
            fun h => he (le_antisymm h hbp))]
          have hp : p ∉ enlargedVisitPoleSet (visitActiveUnion c J) b := fun h => ht h.1
          have hE : enlargedVisitExitKernel hH hLE hlam hLam A (visitActiveUnion c J) b p =
              0 := by
            change (if h : p ∈ enlargedVisitPoleSet (visitActiveUnion c J) b then _ else
              0) = 0
            rw [dite_eq_right hp]
          unfold enlargedActiveTerminalFamily
          rw [ite_eq_right (fun h => he h.1), hE, Measure.restrict_zero, integral_zero_measure]
    dsimp only
    let f := fun q : Point => positionStartCutoff Y c.r c.positive (q.position 0) *
      visitQuadratic c (q.velocity 0)
    let G := stripGreen hH hLE hlam hLam A c.activeInterval ⊤ (densityClockPole c p hv)
    have hid := positionStartQuadratic_cumulative_identity b
    have hia := positionStartQuadratic_cumulative_identity a
    change ({q : Point | q.time ≤ b}.indicator f) p = _ at hid
    change ({q : Point | q.time ≤ a}.indicator f) p = _ at hia
    have hd : {q : Point | a < q.time ∧ q.time ≤ b} =
        {q : Point | q.time ≤ b} \ {q : Point | q.time ≤ a} := by
      ext q
      simp
      exact and_comm
    have hi : (∫ q in {q : Point | a < q.time ∧ q.time ≤ b},
        forwardScalarOperator A.a f q ∂G) =
        (∫ q in {q : Point | q.time ≤ b}, forwardScalarOperator A.a f q ∂G) -
        ∫ q in {q : Point | q.time ≤ a}, forwardScalarOperator A.a f q ∂G := by
      rw [hd]
      exact setIntegral_sdiff₀
        (isClosed_le continuous_time continuous_const).measurableSet.nullMeasurableSet
        (positionStartQuadratic_operator_integrable hlam hLam A c Y hc G ((stripGreen_infinite_ae_future_carrier hH hLE hlam hLam A c.activeInterval (densityClockPole c p hv)).mono fun _ hq => hq.2)).integrableOn (fun _ hq => hq.trans hab)
    rw [hi]
    have he : ({q : Point | a < q.time ∧ q.time ≤ b}.indicator f) p =
        ({q : Point | q.time ≤ b}.indicator f) p -
        ({q : Point | q.time ≤ a}.indicator f) p := by
      by_cases hpa : p.time ≤ a
      · rw [indicator_of_notMem (show p ∉ {q : Point | a < q.time ∧ q.time ≤ b} from
          fun h => (not_lt_of_ge hpa) h.1),
          indicator_of_mem (show p ∈ {q : Point | q.time ≤ b} from hpa.trans hab),
          indicator_of_mem (show p ∈ {q : Point | q.time ≤ a} from hpa), sub_self]
      · rw [indicator_of_notMem (show p ∉ {q : Point | q.time ≤ a} from hpa), sub_zero]
        by_cases hpb : p.time ≤ b
        · rw [indicator_of_mem (show p ∈ {q : Point | a < q.time ∧ q.time ≤ b} from
            ⟨lt_of_not_ge hpa, hpb⟩),
            indicator_of_mem (show p ∈ {q : Point | q.time ≤ b} from hpb)]
        · rw [indicator_of_notMem (show p ∉ {q : Point | a < q.time ∧ q.time ≤ b} from
            fun h => hpb h.2),
            indicator_of_notMem (show p ∉ {q : Point | q.time ≤ b} from hpb)]
    rw [he, hid, hia]
    ring
  dsimp only
  let f := fun q : Point => positionStartCutoff Y c.r c.positive (q.position 0) *
    visitQuadratic c (q.velocity 0)
  let g := fun q : Point => forwardScalarOperator A.a f q
  let S := {q : Point | a < q.time ∧ q.time ≤ b}
  let B := positionStartTerminalKernel hH hLE hlam hLam A c J b
  let D := positionStartTerminalKernel hH hLE hlam hLam A c J a
  let G := coreAllTimeGreenKernel hH hLE hlam hLam A c
  have hS : MeasurableSet S :=
    (isOpen_lt continuous_const continuous_time).measurableSet.inter
      (isClosed_le continuous_time continuous_const).measurableSet
  have hB :=
    positionStartQuadratic_integrable c Y _
      (positionStartTerminalMixture_ae_closedActive hH hLE hlam hLam A c J b mu)
  have hD :=
    positionStartQuadratic_integrable c Y _
      (positionStartTerminalMixture_ae_closedActive hH hLE hlam hLam A c J a mu)
  have hGs := (positionStartQuadratic_operator_integrable hlam hLam A c Y hc _ (positionStartAllTimeMixture_ae_active hH hLE hlam hLam A c mu)).indicator hS
  have hiB : Integrable (fun p => ∫ q, f q ∂B p) mu := by
    rw [Measure.comp_eq_comp_const_apply] at hB
    simpa using hB.integral_comp
  have hiD : Integrable (fun p => ∫ q, f q ∂D p) mu := by
    rw [Measure.comp_eq_comp_const_apply] at hD
    simpa using hD.integral_comp
  have hiG : Integrable (fun p => ∫ q, S.indicator g q ∂G p) mu := by
    rw [Measure.comp_eq_comp_const_apply] at hGs
    simpa using hGs.integral_comp
  have hp : S.indicator f =ᵐ[mu] fun p =>
      (∫ q, f q ∂B p) - (∫ q, f q ∂D p) - ∫ q, S.indicator g q ∂G p := by
    filter_upwards [hmu] with p hv
    have hi := positionStartQuadratic_slab_identity p hv
    dsimp only at hi
    have he : G p = stripGreen hH hLE hlam hLam A c.activeInterval ⊤
        (densityClockPole c p hv) := by
      change (if h : p.velocity 0 ∈ c.active then _ else 0) = _
      rw [dite_eq_left hv]
      rfl
    rw [integral_indicator hS, he]
    exact hi
  change (∫ p in S, f p ∂mu) =
    (∫ q, f q ∂B ∘ₘ mu) - (∫ q, f q ∂D ∘ₘ mu) - ∫ q in S, g q ∂G ∘ₘ mu
  rw [← integral_indicator hS, integral_congr_ae hp]
  have he : (∫ p, (∫ q, f q ∂B p) - (∫ q, f q ∂D p) -
      (∫ q, S.indicator g q ∂G p) ∂mu) =
      (∫ p, (∫ q, f q ∂B p) - (∫ q, f q ∂D p) ∂mu) -
        ∫ p, ∫ q, S.indicator g q ∂G p ∂mu := integral_sub (hiB.sub hiD) hiG
  have hd : (∫ p, (∫ q, f q ∂B p) - (∫ q, f q ∂D p) ∂mu) =
      (∫ p, ∫ q, f q ∂B p ∂mu) - ∫ p, ∫ q, f q ∂D p ∂mu := integral_sub hiB hiD
  rw [he, hd,
    ← nested_integral_bind mu B B.measurable f hB,
    ← nested_integral_bind mu D D.measurable f hD,
    ← nested_integral_bind mu G G.measurable (S.indicator g) hGs,
    integral_indicator hS]


/-- The quadratic weight gives a uniform constant after its exact radius cancellation. -/
theorem positionStart_slab_arithmetic (r C n F I : ℝ) (hr : 0 < r) (hC : 0 ≤ C)
    (hF : 0 ≤ F) (hI : 0 ≤ I)
    (h : 5 * r ^ 2 / 16 * n ≤ 9 * r ^ 2 / 16 * F + C * I) :
    n ≤ (9 / 5 + 16 * C / 5) * (F + r ^ (-2 : ℤ) * I) := by
  have hw : 0 < 5 * r ^ 2 / 16 := by positivity
  have he : 5 * r ^ 2 / 16 * (9 / 5 * F + (16 * C / 5) * r ^ (-2 : ℤ) * I) =
      9 * r ^ 2 / 16 * F + C * I := by
    rw [zpow_neg, zpow_ofNat]
    field_simp [hr.ne']
  have hn : n ≤ 9 / 5 * F + (16 * C / 5) * r ^ (-2 : ℤ) * I :=
    le_of_mul_le_mul_left (h.trans_eq he.symm) hw
  have hpos : 0 ≤ r ^ (-2 : ℤ) * I := mul_nonneg (zpow_nonneg hr.le _) hI
  calc
    n ≤ 9 / 5 * F + (16 * C / 5) * r ^ (-2 : ℤ) * I := hn
    _ ≤ (9 / 5 + 16 * C / 5) * F +
        (9 / 5 + 16 * C / 5) * (r ^ (-2 : ℤ) * I) := by
      rw [mul_assoc]
      exact add_le_add
        (mul_le_mul_of_nonneg_right (by linarith only [hC]) hF)
        (mul_le_mul_of_nonneg_right (by linarith) hpos)
    _ = _ := by ring


/-- The localized start integral dominates the literal cell count with weight `5*r²/16`. -/
theorem positionStartQuadratic_slab_lower (mu : Measure Point) [IsFiniteMeasure mu]
    (c : Clock) (s x a b : ℝ) (k : ℤ)
    (hmu : ∀ᵐ p ∂mu, p.velocity 0 ∈ closure c.entrance) :
    5 * c.r ^ 2 / 16 * enlargedPositionSlabMass mu c s x a b k ≤
      ∫ p in {q : Point | s + a < q.time ∧ q.time ≤ s + b},
        positionStartCutoff (x + ((k : ℝ) + 1 / 2) * c.r ^ 3) c.r c.positive
          (p.position 0) * visitQuadratic c (p.velocity 0) ∂mu  := by
  have positionStartQuadratic_start_lower (p : Point) (hx : p.position 0 ∈ enlargedPositionCell c.r x k) (hv : p.velocity 0 ∈ closure c.entrance) :
      5 * c.r ^ 2 / 16 ≤
      positionStartCutoff (x + ((k : ℝ) + 1 / 2) * c.r ^ 3) c.r c.positive
        (p.position 0) * visitQuadratic c (p.velocity 0) := by
    have positionStartCutoff_eq_one_on_cell (r : ℝ) (hr : 0 < r) {X : ℝ} (hX : X ∈ enlargedPositionCell r x k) :
        positionStartCutoff (x + ((k : ℝ) + 1 / 2) * r ^ 3) r hr X = 1 := by
      apply positionStartCutoff_eq_one
      change x + (k : ℝ) * r ^ 3 ≤ X ∧ X < x + ((k : ℝ) + 1) * r ^ 3 at hX
      rw [abs_le]
      constructor <;> linarith only [hX.1, hX.2]
    rw [positionStartCutoff_eq_one_on_cell c.r c.positive hx, one_mul]
    exact visitQuadratic_entrance_lower c hv
  let Y := x + ((k : ℝ) + 1 / 2) * c.r ^ 3
  let f := fun p : Point => positionStartCutoff Y c.r c.positive (p.position 0) *
    visitQuadratic c (p.velocity 0)
  let S := {q : Point | s + a < q.time ∧ q.time ≤ s + b}
  let B := {p : Point | s + a < p.time ∧ p.time ≤ s + b ∧
    p.position 0 ∈ enlargedPositionCell c.r x k ∧
      p.velocity 0 ∈ closure c.entrance}
  have hS : MeasurableSet S :=
    (isOpen_lt continuous_const continuous_time).measurableSet.inter
      (isClosed_le continuous_time continuous_const).measurableSet
  have hB : MeasurableSet B :=
    (isOpen_lt continuous_const continuous_time).measurableSet.inter
      ((isClosed_le continuous_time continuous_const).measurableSet.inter
        (((measurableSet_enlargedPositionCell c.r x k).preimage
          ((continuous_apply 0).comp continuous_position).measurable).inter
            (isClosed_closure.measurableSet.preimage
              ((continuous_apply 0).comp continuous_velocity).measurable)))
  have hf : Integrable f mu := positionStartQuadratic_integrable c Y mu
    (hmu.mono fun _ hp => subset_closure (enlarged_closedEntrance_subset_active c hp))
  have hm : (∫ p, B.indicator (fun _ => 5 * c.r ^ 2 / 16) p ∂mu) ≤
      ∫ p, S.indicator f p ∂mu := by
    apply integral_mono_ae ((integrable_const _).indicator hB) (hf.indicator hS)
    filter_upwards [hmu] with p hv
    by_cases hp : p ∈ B
    · rw [indicator_of_mem hp, indicator_of_mem (show p ∈ S from ⟨hp.1, hp.2.1⟩)]
      exact positionStartQuadratic_start_lower p hp.2.2.1 hp.2.2.2
    · rw [indicator_of_notMem hp]
      by_cases hs : p ∈ S
      · rw [indicator_of_mem hs]
        exact mul_nonneg ((positionStartCutoff_properties Y c.r c.positive).2 _).1
          (visitQuadratic_nonneg c
            (subset_closure (enlarged_closedEntrance_subset_active c hv)))
      · rw [indicator_of_notMem hs]
  rw [integral_indicator hB, integral_const, integral_indicator hS] at hm
  change 5 * c.r ^ 2 / 16 * (mu B).toReal ≤ ∫ p in S, f p ∂mu
  simpa [mul_comm, Measure.real, Measure.restrict_apply MeasurableSet.univ, univ_inter] using hm


/-- The localized test is nonnegative and bounded by its quadratic maximum on the source box. -/
theorem positionStartQuadratic_box_bound (c : Clock) (Y : ℝ) (p : Point)
    (hc : |c.vbar| = 2 * c.r) (hv : p.velocity 0 ∈ closure c.active) :
    0 ≤ positionStartCutoff Y c.r c.positive (p.position 0) *
      visitQuadratic c (p.velocity 0) ∧
    positionStartCutoff Y c.r c.positive (p.position 0) *
      visitQuadratic c (p.velocity 0) ≤
      9 * c.r ^ 2 / 16 * (box 4 c.r Y).indicator (fun _ => (1 : ℝ))
        (p.position 0, p.velocity 0) := by
  have hchi := (positionStartCutoff_properties Y c.r c.positive).2 (p.position 0)
  have hq := visitQuadratic_nonneg c hv
  refine ⟨mul_nonneg hchi.1 hq, ?_⟩
  by_cases hb : (p.position 0, p.velocity 0) ∈ box 4 c.r Y
  · rw [indicator_of_mem hb, mul_one]
    exact (mul_le_mul_of_nonneg_right hchi.2 hq).trans (by
      simpa using visitQuadratic_le c (p.velocity 0))
  · rw [indicator_of_notMem hb, mul_zero]
    have ho : c.vbar - 3 * c.r / 4 < c.vbar + 3 * c.r / 4 := by
      linarith [c.positive]
    have hvel := hv
    rw [Clock.active, closure_Ioo ho.ne] at hvel
    have hupper := le_abs_self c.vbar
    have hlower := neg_abs_le c.vbar
    rw [hc] at hupper hlower
    have hva : |p.velocity 0| ≤ 4 * c.r := by
      rw [abs_le]
      constructor <;> linarith [hvel.1, hvel.2, c.positive]
    have hnot : p.position 0 ∉ tsupport (positionStartCutoff Y c.r c.positive) := by
      intro hp
      have hs := positionStartCutoff_tsupport Y c.r c.positive hp
      apply hb
      change |p.position 0 - Y| ≤ 4 * c.r ^ 3 ∧ |p.velocity 0| ≤ 4 * c.r
      refine ⟨?_, hva⟩
      rw [abs_le]
      constructor <;> linarith [hs.1, hs.2, pow_pos c.positive 3]
    rw [image_eq_zero_of_notMem_tsupport hnot, zero_mul]

/-- A finite terminal mixture has a nonnegative localized value. -/
theorem positionStartQuadratic_terminal_integral_nonneg
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (c : Clock) (J : Interval) (Y b : ℝ)
    (mu : Measure Point) :
    0 ≤ ∫ q, positionStartCutoff Y c.r c.positive (q.position 0) *
      visitQuadratic c (q.velocity 0)
      ∂(positionStartTerminalKernel hH hLE hlam hLam A c J b ∘ₘ mu) := by
  apply integral_nonneg_of_ae
  exact (positionStartTerminalMixture_ae_closedActive hH hLE hlam hLam A c J b mu).mono
    fun q hq => mul_nonneg ((positionStartCutoff_properties Y c.r c.positive).2 _).1
      (visitQuadratic_nonneg c hq)


/-- Pull the literal phase-space source box back to physical spacetime. -/
def positionStartBox (c : Clock) (Y : ℝ) : Set Point :=
  {q | (q.position 0, q.velocity 0) ∈ box 4 c.r Y}

/-- The physical source box is measurable. -/
theorem measurableSet_positionStartBox (c : Clock) (Y : ℝ) :
    MeasurableSet (positionStartBox c Y) :=
  (box_measurable 4 c.r Y).preimage
    (((continuous_apply 0).comp continuous_position).measurable.prodMk
      ((continuous_apply 0).comp continuous_velocity).measurable)



/-- Domination of every initial partial sum dominates the complete positive measure sum. -/
theorem positionStart_sum_le_of_partial_le {X : Type*} [MeasurableSpace X]
    (mu : ℕ → Measure X) (nu : Measure X)
    (h : ∀ N : ℕ, (∑ n ∈ Finset.range N, mu n) ≤ nu) : Measure.sum mu ≤ nu := by
  apply Measure.le_iff.mpr
  intro B hB
  rw [Measure.sum_apply _ hB]
  apply ENNReal.tsum_le_of_sum_range_le
  intro N
  simpa only [Measure.finsetSum_apply, hB] using h N B


/-- Restricting actual starting mixtures preserves the finite-horizon slab identity. -/
theorem positionStartGreenMixture_slab_eq_finite
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (c : Clock) (J : Interval) (a b U : ℝ)
    (hJ : closure c.active ⊆ J.carrier) (mu : Measure Point)
    (hmu : ∀ᵐ p ∂mu, p.velocity 0 ∈ c.active ∧ p.time < U) (hb : b ≤ U) :
    (coreAllTimeGreenKernel hH hLE hlam hLam A c ∘ₘ mu).restrict
      {q : Point | a < q.time ∧ q.time ≤ b} =
    (enlargedVisitGreenKernel hH hLE hlam hLam A (visitActiveUnion c J) U ∘ₘ mu).restrict
      {q : Point | a < q.time ∧ q.time ≤ b}  := by
  have positionStartGreen_slab_eq_finite (p : Point) (hv : p.velocity 0 ∈ c.active) (hp : p.time < U) :
      (coreAllTimeGreenKernel hH hLE hlam hLam A c p).restrict
      {q : Point | a < q.time ∧ q.time ≤ b} =
    (enlargedVisitGreenKernel hH hLE hlam hLam A (visitActiveUnion c J) U p).restrict
      {q : Point | a < q.time ∧ q.time ≤ b} := by
    have he : coreAllTimeGreenKernel hH hLE hlam hLam A c p =
        stripGreen hH hLE hlam hLam A c.activeInterval ⊤ (densityClockPole c p hv) := by
      change (if h : p.velocity 0 ∈ c.active then _ else 0) = _
      rw [dite_eq_left hv]
      rfl
    rw [he, positionStartGreen_eq_restrict hH hLE hlam hLam A c J U hJ p hv hp]
    have hS : MeasurableSet {q : Point | a < q.time ∧ q.time ≤ b} :=
      (isOpen_lt continuous_const continuous_time).measurableSet.inter
        (isClosed_le continuous_time continuous_const).measurableSet
    rw [Measure.restrict_restrict hS]
    apply Measure.restrict_congr_set
    filter_upwards [positionStartGreen_ae_time_ne hH hLE hlam hLam A c p hv U] with q hq
    apply propext
    constructor
    · intro h
      exact ⟨h, lt_of_le_of_ne (h.2.trans hb) hq⟩
    · exact fun h => h.1
  let S := {q : Point | a < q.time ∧ q.time ≤ b}
  have hS : MeasurableSet S :=
    (isOpen_lt continuous_const continuous_time).measurableSet.inter
      (isClosed_le continuous_time continuous_const).measurableSet
  ext B hB
  rw [Measure.restrict_apply hB, Measure.restrict_apply hB,
    Measure.bind_apply (hB.inter hS) (Kernel.aemeasurable _),
    Measure.bind_apply (hB.inter hS) (Kernel.aemeasurable _)]
  apply lintegral_congr_ae
  filter_upwards [hmu] with p hp
  simpa only [Measure.restrict_apply hB] using (congrArg (fun rho : Measure Point => rho B) (positionStartGreen_slab_eq_finite p hp.1 hp.2))

/-- All actual active occupations are dominated by full-space occupation. -/
theorem positionStart_all_occupation_le_fullspace
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (c : Clock) (J : Interval) (T : ℝ) (P : Point)
    (hT : 0 < T) (hv : P.velocity 0 ∈ J.carrier) :
    enlargedVisitGreenKernel hH hLE hlam hLam A (visitActiveUnion c J) (P.time + T) ∘ₘ
      enlargedVisitStarts hH hLE hlam hLam A c J P.time (P.time + T) P ≤
        enlargedFullSpaceOccupation hH hLE hlam hLam A P T := by
  change (Measure.sum (enlargedVisitEntrance hH hLE hlam hLam A c J P.time (P.time + T) P)).bind
    (enlargedVisitGreenKernel hH hLE hlam hLam A (visitActiveUnion c J) (P.time + T)) ≤ _
  rw [Measure.bind_sum _ _ (Kernel.aemeasurable _)]
  apply positionStart_sum_le_of_partial_le
  exact enlarged_active_occupation_le_fullspace hH hLE hlam hLam A c J T hT P hv


/-- Full-space terminal mass in the physical source box is its elapsed box probability. -/
theorem positionStartFullSpaceTerminal_box
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (c : Clock) (P : Point) (Y b : ℝ) :
    enlargedFullSpaceTerminal hH hLE hlam hLam A P (P.time + b) (positionStartBox c Y) =
      kernelXV (fullSpaceEvolution hH hLE hlam hLam A) (Real.toNNReal b)
        (P.position 0, P.velocity 0) (box 4 c.r Y) := by
  unfold enlargedFullSpaceTerminal
  rw [Measure.map_apply (enlargedTerminalPoint_measurable _)
    (measurableSet_positionStartBox c Y), add_sub_cancel_left]
  rfl

/-- The full-space occupation mass in a physical slab is the source iterated box action. -/
theorem positionStartFullSpaceOccupation_box_slab
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (c : Clock) (P : Point) (Y a b T : ℝ)
    (ha : 0 ≤ a) (hb : b ≤ T) :
    enlargedFullSpaceOccupation hH hLE hlam hLam A P T
      ({q : Point | P.time + a < q.time ∧ q.time ≤ P.time + b} ∩ positionStartBox c Y) =
      ∫⁻ t in Ioc a b, kernelXV (fullSpaceEvolution hH hLE hlam hLam A) (Real.toNNReal t)
        (P.position 0, P.velocity 0) (box 4 c.r Y) := by
  let S := {q : Point | P.time + a < q.time ∧ q.time ≤ P.time + b}
  let W := positionStartBox c Y
  have hS : MeasurableSet S :=
    (isOpen_lt continuous_const continuous_time).measurableSet.inter
      (isClosed_le continuous_time continuous_const).measurableSet
  have hW := measurableSet_positionStartBox c Y
  let F : Point → ℝ≥0∞ := (S ∩ W).indicator 1
  have hF : Measurable F := measurable_one.indicator (hS.inter hW)
  rw [← lintegral_indicator_one (hS.inter hW)]
  change (∫⁻ p, F p ∂enlargedFullSpaceOccupation hH hLE hlam hLam A P T) = _
  rw [enlargedFullSpaceOccupation_lintegral hH hLE hlam hLam A P T F hF]
  have he (t : ℝ) : (∫⁻ z, F (enlargedTerminalPoint (P.time + t) z)
      ∂kernelXV (fullSpaceEvolution hH hLE hlam hLam A) (Real.toNNReal t)
        (P.position 0, P.velocity 0)) =
      (Ioc a b).indicator (fun u => kernelXV (fullSpaceEvolution hH hLE hlam hLam A)
        (Real.toNNReal u) (P.position 0, P.velocity 0) (box 4 c.r Y)) t := by
    by_cases ht : t ∈ Ioc a b
    · rw [indicator_of_mem ht, ← lintegral_indicator_one (box_measurable 4 c.r Y)]
      apply lintegral_congr
      intro z
      have heq : enlargedTerminalPoint (P.time + t) z ∈ S ∩ W ↔ z ∈ box 4 c.r Y := by
        change ((P.time + a < P.time + t ∧ P.time + t ≤ P.time + b) ∧
          z ∈ box 4 c.r Y) ↔ z ∈ box 4 c.r Y
        have hs : P.time + a < P.time + t ∧ P.time + t ≤ P.time + b := by
          constructor <;> linarith only [ht.1, ht.2]
        exact and_iff_right hs
      simp only [F, Set.indicator, heq, Pi.one_apply]
    · rw [indicator_of_notMem ht]
      have hz : (fun z : Z => F (enlargedTerminalPoint (P.time + t) z)) =
          fun _ => 0 := by
        funext z
        have hn : enlargedTerminalPoint (P.time + t) z ∉ S ∩ W := by
          intro hz
          apply ht
          have hs : P.time + a < P.time + t ∧ P.time + t ≤ P.time + b := hz.1
          constructor <;> linarith only [hs.1, hs.2]
        exact indicator_of_notMem hn _
      rw [hz, lintegral_zero]
  simp_rw [he]
  rw [lintegral_indicator measurableSet_Ioc,
    Measure.restrict_restrict measurableSet_Ioc]
  have hs : Ioc a b ∩ Ioc 0 T = Ioc a b :=
    inter_eq_left.mpr (fun _ ht => ⟨ha.trans_lt ht.1, ht.2.trans hb⟩)
  rw [hs]

/-- The extended slab box action equals the ofReal of the actual integrable real action. -/
theorem positionStartBox_slab_ofReal_integral (E : FullSpaceEvolution) (z : Z)
    (r Y a b : ℝ) :
    ENNReal.ofReal (∫ t in Ioc a b, (kernelXV E (Real.toNNReal t) z (box 4 r Y)).toReal) =
      ∫⁻ t in Ioc a b, kernelXV E (Real.toNNReal t) z (box 4 r Y) := by
  rw [ofReal_integral_eq_lintegral_ofReal
    (position_box_probability_integrable E z 4 r Y a b)
    (Filter.Eventually.of_forall fun _ => ENNReal.toReal_nonneg)]
  apply lintegral_congr
  intro t
  exact ENNReal.ofReal_toReal ((measure_mono (subset_univ _)).trans_lt
    ((kernelXV_mass_le_one E (Real.toNNReal t) z).trans_lt ENNReal.one_lt_top)).ne


/-- The exact source `hStart` estimate, relative only to the existing terminal domination input. -/
theorem positionStartSlabBound_holds
    (hTerminal : ∀ (hH : HormanderHypoellipticityStatement)
      (hLE : LiebermanEllipsoidDirichletStatement)
      (lam Lam : ℝ) (hlam : 0 < lam) (hLam : lam ≤ Lam)
      (A : SmoothAutonomous lam Lam) (c : Clock) (J : Interval) (T : ℝ) (P : Point),
      |c.vbar| = 2 * c.r → 0 < T → closure c.active ⊆ J.carrier →
      P.velocity 0 ∈ closure c.entrance →
      ∀ (N : ℕ) (b : ℝ), P.time ≤ b → b ≤ P.time + T →
        enlargedActiveTerminal hH hLE hlam hLam A c J P.time (P.time + T) P N b ≤
          enlargedFullSpaceTerminal hH hLE hlam hLam A P b) :
    ∀ (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
      (lam Lam : ℝ) (hlam : 0 < lam) (hLam : lam ≤ Lam),
      ∃ A0 Cs : ℝ, 0 < A0 ∧ 0 < Cs ∧
      ∀ (A : SmoothAutonomous lam Lam) (c : Clock) (J : Interval) (T : ℝ) (P : Point),
      |c.vbar| = 2 * c.r → closure c.active ⊆ J.carrier → 0 < T →
      P.velocity 0 ∈ closure c.entrance → ∀ (a b : ℝ) (k : ℤ),
      0 ≤ a → a < b → b - a ≤ c.r ^ 2 → b ≤ T →
      enlargedPositionSlabMass (visitsFromZero hH hLE hlam hLam A c J T P)
        c P.time 0 a b k ≤ Cs *
          ((kernelXV (fullSpaceEvolution hH hLE hlam hLam A) (Real.toNNReal b)
            (P.position 0, P.velocity 0)
              (box A0 c.r (((k : ℝ) + 1 / 2) * c.r ^ 3))).toReal +
           c.r ^ (-2 : ℤ) * ∫ t in Ioc a b,
             (kernelXV (fullSpaceEvolution hH hLE hlam hLam A) (Real.toNNReal t)
               (P.position 0, P.velocity 0)
                 (box A0 c.r (((k : ℝ) + 1 / 2) * c.r ^ 3))).toReal)  := by
  intro hH hLE lam Lam hlam hLam
  have positionStartQuadratic_slab_mass_bound :
      ∃ C : ℝ, 0 < C ∧
    ∀ (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
      (A : SmoothAutonomous lam Lam) (c : Clock) (J : Interval) (s x a b : ℝ) (k : ℤ)
      (mu : Measure Point) [IsFiniteMeasure mu],
      |c.vbar| = 2 * c.r → closure c.active ⊆ J.carrier → a ≤ b →
      (∀ᵐ p ∂mu, p.velocity 0 ∈ closure c.entrance) →
      let Y := x + ((k : ℝ) + 1 / 2) * c.r ^ 3
      5 * c.r ^ 2 / 16 * enlargedPositionSlabMass mu c s x a b k ≤
        9 * c.r ^ 2 / 16 *
          ((positionStartTerminalKernel hH hLE hlam hLam A c J (s + b) ∘ₘ mu)
            (positionStartBox c Y)).toReal +
        C * ((coreAllTimeGreenKernel hH hLE hlam hLam A c ∘ₘ mu)
          ({q : Point | s + a < q.time ∧ q.time ≤ s + b} ∩ positionStartBox c Y)).toReal := by
    obtain ⟨C, hC, hbound⟩ := positionStartQuadratic_operator_bound hlam hLam
    refine ⟨C, hC, ?_⟩
    intro hH hLE A c J s x a b k mu _ hc hJ hab hmu
    dsimp only
    let Y := x + ((k : ℝ) + 1 / 2) * c.r ^ 3
    let f := fun q : Point => positionStartCutoff Y c.r c.positive (q.position 0) *
      visitQuadratic c (q.velocity 0)
    let g := fun q : Point => forwardScalarOperator A.a f q
    let S := {q : Point | s + a < q.time ∧ q.time ≤ s + b}
    let W := positionStartBox c Y
    let B := positionStartTerminalKernel hH hLE hlam hLam A c J (s + b) ∘ₘ mu
    let D := positionStartTerminalKernel hH hLE hlam hLam A c J (s + a) ∘ₘ mu
    let G := coreAllTimeGreenKernel hH hLE hlam hLam A c ∘ₘ mu
    have hS : MeasurableSet S :=
      (isOpen_lt continuous_const continuous_time).measurableSet.inter
        (isClosed_le continuous_time continuous_const).measurableSet
    have hW : MeasurableSet W := measurableSet_positionStartBox c Y
    have hfB : Integrable f B := positionStartQuadratic_integrable c Y B
      (positionStartTerminalMixture_ae_closedActive hH hLE hlam hLam A c J (s + b) mu)
    have hgG : Integrable g G := positionStartQuadratic_operator_integrable
      hlam hLam A c Y hc G (positionStartAllTimeMixture_ae_active hH hLE hlam hLam A c mu)
    have hterm : (∫ q, f q ∂B) ≤ 9 * c.r ^ 2 / 16 * (B W).toReal := by
      have hh : (∫ q, f q ∂B) ≤ ∫ q, W.indicator (fun _ => 9 * c.r ^ 2 / 16) q ∂B := by
        apply integral_mono_ae hfB ((integrable_const _).indicator hW)
        filter_upwards [positionStartTerminalMixture_ae_closedActive
          hH hLE hlam hLam A c J (s + b) mu] with q hq
        have h := (positionStartQuadratic_box_bound c Y q hc hq).2
        change f q ≤ W.indicator (fun _ => 9 * c.r ^ 2 / 16) q
        by_cases hw : q ∈ W
        · rw [indicator_of_mem hw]
          simpa [indicator_of_mem
            (show (q.position 0, q.velocity 0) ∈ box 4 c.r Y from hw)] using h
        · rw [indicator_of_notMem hw]
          simpa [indicator_of_notMem
            (show (q.position 0, q.velocity 0) ∉ box 4 c.r Y from hw)] using h
      rw [integral_indicator hW, integral_const] at hh
      simpa [Measure.real, Measure.restrict_apply MeasurableSet.univ, univ_inter, mul_comm] using hh
    have hop : -(∫ q in S, g q ∂G) ≤ C * (G (S ∩ W)).toReal := by
      have hh : (∫ q in S, -g q ∂G) ≤ ∫ q in S, W.indicator (fun _ => C) q ∂G := by
        apply integral_mono_ae hgG.neg.restrict (((integrable_const C).indicator hW).restrict)
        have ha : ∀ᵐ q ∂G.restrict S, q.velocity 0 ∈ c.active :=
          (positionStartAllTimeMixture_ae_active hH hLE hlam hLam A c mu).filter_mono
            (ae_mono Measure.restrict_le_self)
        filter_upwards [ha] with q hq
        change -g q ≤ W.indicator (fun _ => C) q
        have hb := (neg_le_abs (g q)).trans (hbound A c Y q hc hq)
        by_cases hw : q ∈ W
        · rw [indicator_of_mem hw]
          simpa [indicator_of_mem
            (show (q.position 0, q.velocity 0) ∈ box 4 c.r Y from hw)] using hb
        · rw [indicator_of_notMem hw]
          simpa [indicator_of_notMem
            (show (q.position 0, q.velocity 0) ∉ box 4 c.r Y from hw)] using hb
      rw [integral_neg, integral_indicator hW, integral_const] at hh
      simpa [Measure.real, Measure.restrict_apply MeasurableSet.univ, univ_inter, Measure.restrict_apply hW, inter_comm, mul_comm] using hh
    have hi := positionStartQuadratic_integrated_slab_identity
      hH hLE hlam hLam A c J Y (s + a) (s + b) hc hJ mu (hmu.mono fun _ hp => enlarged_closedEntrance_subset_active c hp) (by linarith only [hab])
    have hlo := positionStartQuadratic_slab_lower mu c s x a b k hmu
    have hn := positionStartQuadratic_terminal_integral_nonneg
      hH hLE hlam hLam A c J Y (s + a) mu
    change (∫ q in S, f q ∂mu) = (∫ q, f q ∂B) - (∫ q, f q ∂D) -
      ∫ q in S, g q ∂G at hi
    change 5 * c.r ^ 2 / 16 * enlargedPositionSlabMass mu c s x a b k ≤
      (∫ q in S, f q ∂mu) at hlo
    change 0 ≤ ∫ q, f q ∂D at hn
    change 5 * c.r ^ 2 / 16 * enlargedPositionSlabMass mu c s x a b k ≤
      9 * c.r ^ 2 / 16 * (B W).toReal + C * (G (S ∩ W)).toReal
    linarith only [hlo, hi, hn, hterm, hop]
  obtain ⟨C, hC, hbound⟩ := positionStartQuadratic_slab_mass_bound
  refine ⟨4, 9 / 5 + 16 * C / 5, by norm_num, by positivity, ?_⟩
  intro A c J T P hc hJ hT hv a b k ha hab _hlen hb
  let mu := visitsFromZero hH hLE hlam hLam A c J T P
  have : IsFiniteMeasure mu :=
    visitsFromZero_isFiniteMeasure hH hLE hlam hLam A c J T P hc hJ hT hv
  let Y := ((k : ℝ) + 1 / 2) * c.r ^ 3
  let S := {q : Point | P.time + a < q.time ∧ q.time ≤ P.time + b}
  let W := positionStartBox c Y
  let B := positionStartTerminalKernel hH hLE hlam hLam A c J (P.time + b) ∘ₘ mu
  let G := coreAllTimeGreenKernel hH hLE hlam hLam A c ∘ₘ mu
  let E := fullSpaceEvolution hH hLE hlam hLam A
  let F := (kernelXV E (Real.toNNReal b) (P.position 0, P.velocity 0) (box 4 c.r Y)).toReal
  let I := ∫ t in Ioc a b,
    (kernelXV E (Real.toNNReal t) (P.position 0, P.velocity 0) (box 4 c.r Y)).toReal
  have hI : 0 ≤ I := setIntegral_nonneg measurableSet_Ioc fun _ _ => ENNReal.toReal_nonneg
  have hs := enlargedVisitStarts_ae_support hH hLE hlam hLam A c J P.time (P.time + T)
    P le_rfl (by linarith only [hT])
  have hmu : ∀ᵐ p ∂mu, p.velocity 0 ∈ closure c.entrance := hs.mono fun _ hp => hp.2.2
  have hB : B ≤ enlargedFullSpaceTerminal hH hLE hlam hLam A P (P.time + b) := by
    change (Measure.sum
      (enlargedVisitEntrance hH hLE hlam hLam A c J P.time (P.time + T) P)).bind
        (positionStartTerminalKernel hH hLE hlam hLam A c J (P.time + b)) ≤ _
    rw [Measure.bind_sum _ _ (Kernel.aemeasurable _)]
    apply positionStart_sum_le_of_partial_le
    intro N
    exact hTerminal hH hLE lam Lam hlam hLam A c J T P hc hT hJ hv N (P.time + b)
      (by linarith only [ha, hab]) (by linarith only [hb])
  have hBF : (B W).toReal ≤ F := by
    have hm := (hB W).trans_eq
      (positionStartFullSpaceTerminal_box hH hLE hlam hLam A c P Y b)
    exact ENNReal.toReal_mono
      ((measure_mono (subset_univ _)).trans_lt
        ((kernelXV_mass_le_one E (Real.toNNReal b) (P.position 0, P.velocity 0)).trans_lt
          ENNReal.one_lt_top)).ne hm
  have hW := measurableSet_positionStartBox c Y
  have he := positionStartGreenMixture_slab_eq_finite hH hLE hlam hLam A c J
    (P.time + a) (P.time + b) (P.time + T) hJ mu
      (hs.mono fun _ hp => ⟨enlarged_closedEntrance_subset_active c hp.2.2, hp.2.1⟩)
        (by linarith only [hb])
  have hGE : G (S ∩ W) ≤ ENNReal.ofReal I := by
    have hh := congrArg (fun rho : Measure Point => rho W) he
    rw [Measure.restrict_apply hW, Measure.restrict_apply hW, inter_comm W] at hh
    change G (S ∩ W) = _ at hh
    rw [hh]
    apply (positionStart_all_occupation_le_fullspace hH hLE hlam hLam A c J T P hT
      (hJ (subset_closure (enlarged_closedEntrance_subset_active c hv))) (S ∩ W)).trans_eq
    exact (positionStartFullSpaceOccupation_box_slab
      hH hLE hlam hLam A c P Y a b T ha hb).trans
        (positionStartBox_slab_ofReal_integral E (P.position 0, P.velocity 0) c.r Y a b).symm
  have hGI := ENNReal.toReal_mono ENNReal.ofReal_ne_top hGE
  rw [ENNReal.toReal_ofReal hI] at hGI
  have hn := hbound hH hLE A c J P.time 0 a b k mu hc hJ hab.le hmu
  simp only [zero_add] at hn
  have hfinal := hn.trans (add_le_add
    (mul_le_mul_of_nonneg_left hBF (by positivity))
    (mul_le_mul_of_nonneg_left hGI hC.le))
  exact positionStart_slab_arithmetic c.r C _ F I c.positive hC.le
    ENNReal.toReal_nonneg hI hfinal

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous

