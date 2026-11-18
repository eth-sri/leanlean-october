module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.EnlargedVisitMassQuadratic
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.IntegratedVelocity
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.BoxConcentrationAveraging
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.TimeBinCountReturnBridge
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.ClockGeometry
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.ReturnGeometryKernel
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.InfiniteHorizonGreen
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.InfiniteHorizonGreenSupport
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.EnlargedRecursionOccupation
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.CoreDominationFiniteBounds
import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.EnlargedVisitMassCapacity
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.EnlargedRecursionTerminalDomination
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.VisitMassSummation
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.PositionVisitsStatement
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.EnlargedVisitMassSupport
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.EnlargedVisitMassCanonical

@[expose] public noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory ProbabilityTheory HypoellipticAleksandrov
open scoped Classical ENNReal

/-- The guard for the zero-duration branch of the actual terminal family is measurable. -/
theorem entranceSlabTerminal_guard_measurable (c : Clock) (J : Interval) (b : ℝ) :
    MeasurableSet {p : Point | p.time = b ∧
      p.velocity 0 ∈ (visitActiveUnion c J).carrier} :=
  (isClosed_eq continuous_time continuous_const).measurableSet.inter
    ((visitActiveUnion c J).isOpen_carrier.measurableSet.preimage
      ((continuous_apply 0).comp continuous_velocity).measurable)

/-- The existing terminal family, packaged as a measurable finite kernel. -/
def entranceSlabTerminalKernel
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (c : Clock) (J : Interval) (b : ℝ) :
    Kernel Point Point :=
  Kernel.piecewise (entranceSlabTerminal_guard_measurable c J b) Kernel.id
    ((enlargedVisitExitKernel hH hLE hlam hLam A (visitActiveUnion c J) b).restrict
      (show MeasurableSet {p : Point | p.time = b} from
        (isClosed_eq continuous_time continuous_const).measurableSet))

/-- The finite kernel is exactly the canonical terminal family at every pole. -/
theorem entranceSlabTerminalKernel_apply
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (c : Clock) (J : Interval) (b : ℝ) (p : Point) :
    entranceSlabTerminalKernel hH hLE hlam hLam A c J b p =
      enlargedActiveTerminalFamily hH hLE hlam hLam A c J b p := rfl

/-- Each actual terminal family has a uniform finite mass bound. -/
instance entranceSlabTerminalKernel_isFiniteKernel
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (c : Clock) (J : Interval) (b : ℝ) :
    IsFiniteKernel (entranceSlabTerminalKernel hH hLE hlam hLam A c J b) := by
  unfold entranceSlabTerminalKernel
  infer_instance


/-- A mixture of actual terminal families is finite for any finite starting measure. -/
instance entranceSlabTerminal_bind_isFiniteMeasure
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (c : Clock) (J : Interval) (b : ℝ)
    (mu : Measure Point) [IsFiniteMeasure mu] :
    IsFiniteMeasure (mu.bind (enlargedActiveTerminalFamily hH hLE hlam hLam A c J b)) :=
  inferInstanceAs (IsFiniteMeasure
    (entranceSlabTerminalKernel hH hLE hlam hLam A c J b ∘ₘ mu))







/-- A lower time bound makes the clipped active occupation of any finite start measure finite. -/
theorem entranceSlabGreen_isFiniteMeasure
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (c : Clock) (J : Interval) (a b : ℝ)
    (mu : Measure Point) [IsFiniteMeasure mu] (ha : ∀ᵐ p ∂mu, a ≤ p.time) :
    IsFiniteMeasure
      (enlargedVisitGreenKernel hH hLE hlam hLam A (visitActiveUnion c J) b ∘ₘ mu) := by
  rw [enlargedVisitGreen_comp_eq_clipped hH hLE hlam hLam A (visitActiveUnion c J) a b mu ha]
  infer_instance



/-- Finite canonical slab counts satisfy the source quadratic estimate without a past-mass term. -/
theorem entranceSlabQuadratic_partial_mass_bound
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (c : Clock) (J : Interval) (s T : ℝ)
    (P : Point) (hs : s ≤ P.time) (hT : P.time < T)
    (hJ : closure c.active ⊆ J.carrier) (a b : ℝ) (N : ℕ) :
    let mu := fun n => (enlargedVisitEntrance hH hLE hlam hLam A c J s T P n).restrict
      {p | p.time ∈ Ioc a b}
    5 * c.r ^ 2 / 16 * (∑ n ∈ Finset.range N, (mu n univ).toReal) ≤
      9 * c.r ^ 2 / 16 * (∑ n ∈ Finset.range N,
        ((mu n).bind (enlargedActiveTerminalFamily hH hLE hlam hLam A c J b)
          {q | q.velocity 0 ∈ c.active}).toReal) +
      2 * Lam * (∑ n ∈ Finset.range N,
        ((enlargedVisitGreenKernel hH hLE hlam hLam A (visitActiveUnion c J) b ∘ₘ mu n)
          univ).toReal)   := by
  have entranceSlabTerminal_quadratic_integrable (mu : Measure Point) [IsFiniteMeasure mu] :
      Integrable (fun q => visitQuadratic c (q.velocity 0))
      (mu.bind (enlargedActiveTerminalFamily hH hLE hlam hLam A c J b)) := by
    have entranceSlabTerminal_ae_velocity :
        ∀ᵐ q ∂mu.bind (enlargedActiveTerminalFamily hH hLE hlam hLam A c J b),
        q.velocity 0 ∈ closure c.active := by
      change ∀ᵐ q ∂(entranceSlabTerminalKernel hH hLE hlam hLam A c J b ∘ₘ mu), _
      apply Measure.ae_comp_of_ae_ae
        (isClosed_closure.measurableSet.preimage
          ((continuous_apply 0).comp continuous_velocity).measurable)
      apply Filter.Eventually.of_forall
      intro p
      rw [entranceSlabTerminalKernel_apply]
      unfold enlargedActiveTerminalFamily
      split
      · rename_i hp
        apply (ae_dirac_iff (isClosed_closure.measurableSet.preimage
          ((continuous_apply 0).comp continuous_velocity).measurable)).mpr
        exact subset_closure (((visitActiveUnion_carrier c J).le hp.2).1)
      · have hz := enlargedActiveExitMixture_ae_velocity hH hLE hlam hLam A c J b
          (Measure.dirac p)
        rw [Measure.dirac_bind
          (enlargedVisitExitKernel hH hLE hlam hLam A (visitActiveUnion c J) b).measurable p]
          at hz
        exact hz.filter_mono (ae_mono Measure.restrict_le_self)
    apply Integrable.mono' (integrable_const (9 * c.r ^ 2 / 16))
      (((visitQuadratic_smooth c).continuous.comp
        ((continuous_apply 0).comp continuous_velocity)).measurable.aestronglyMeasurable)
    filter_upwards [entranceSlabTerminal_ae_velocity] with q hq
    change ‖visitQuadratic c (q.velocity 0)‖ ≤ 9 * c.r ^ 2 / 16
    rw [Real.norm_eq_abs, abs_of_nonneg (visitQuadratic_nonneg c hq)]
    exact visitQuadratic_le c _
  have entranceSlabQuadratic_mass_bound (mu : Measure Point) [IsFiniteMeasure mu] (hmu : ∀ᵐ p ∂mu, a ≤ p.time ∧ p.time ≤ b ∧ p.velocity 0 ∈ closure c.entrance) :
      5 * c.r ^ 2 / 16 * (mu univ).toReal ≤
      9 * c.r ^ 2 / 16 *
        (mu.bind (enlargedActiveTerminalFamily hH hLE hlam hLam A c J b)
          {q | q.velocity 0 ∈ c.active}).toReal +
      2 * Lam *
        ((enlargedVisitGreenKernel hH hLE hlam hLam A (visitActiveUnion c J) b ∘ₘ mu)
          univ).toReal := by
    have entranceSlabQuadratic_integrated_identity [IsFiniteMeasure mu] (hmu : ∀ᵐ p ∂mu, a ≤ p.time ∧ p.time ≤ b ∧
        p.velocity 0 ∈ (visitActiveUnion c J).carrier) :
        (∫ p, visitQuadratic c (p.velocity 0) ∂mu) =
        (∫ q, visitQuadratic c (q.velocity 0)
          ∂mu.bind (enlargedActiveTerminalFamily hH hLE hlam hLam A c J b)) +
        ∫ q, 2 * A.a (q.position 0) (q.velocity 0)
          ∂(enlargedVisitGreenKernel hH hLE hlam hLam A (visitActiveUnion c J) b ∘ₘ mu) := by
      have entranceSlabQuadratic_closed_point_identity (p : Point) (ht : p.time ≤ b) (hv : p.velocity 0 ∈ (visitActiveUnion c J).carrier) :
          visitQuadratic c (p.velocity 0) =
          (∫ q, visitQuadratic c (q.velocity 0)
            ∂enlargedActiveTerminalFamily hH hLE hlam hLam A c J b p) +
          ∫ q, 2 * A.a (q.position 0) (q.velocity 0)
            ∂enlargedVisitGreenKernel hH hLE hlam hLam A (visitActiveUnion c J) b p := by
        have entranceSlabQuadratic_point_identity (ht : p.time < b) :
            visitQuadratic c (p.velocity 0) =
            (∫ q, visitQuadratic c (q.velocity 0)
              ∂enlargedActiveTerminalFamily hH hLE hlam hLam A c J b p) +
            ∫ q, 2 * A.a (q.position 0) (q.velocity 0)
              ∂enlargedVisitGreenKernel hH hLE hlam hLam A (visitActiveUnion c J) b p := by
          classical
          have hp : p ∈ enlargedVisitPoleSet (visitActiveUnion c J) b := ⟨ht, hv⟩
          let ep := enlargedVisitPole (visitActiveUnion c J) b ⟨p, hp⟩
          have hi := visitQuadratic_active_identity hH hLE hlam hLam A c J b ep
          have he : enlargedVisitExitKernel hH hLE hlam hLam A (visitActiveUnion c J) b p =
              finiteUnionExit hH hLE hlam hLam A (visitActiveUnion c J) b ep := by
            change (if h : p ∈ enlargedVisitPoleSet (visitActiveUnion c J) b then
              finiteUnionExit hH hLE hlam hLam A (visitActiveUnion c J) b
                (enlargedVisitPole _ b ⟨p, h⟩) else 0) = _
            rw [dite_eq_left hp]
          have hg : enlargedVisitGreenKernel hH hLE hlam hLam A (visitActiveUnion c J) b p =
              finiteUnionGreen hH hLE hlam hLam A (visitActiveUnion c J) b ep := by
            change (if h : p ∈ enlargedVisitPoleSet (visitActiveUnion c J) b then
              finiteUnionGreen hH hLE hlam hLam A (visitActiveUnion c J) b
                (enlargedVisitPole _ b ⟨p, h⟩) else 0) = _
            rw [dite_eq_left hp]
          let E := enlargedVisitExitKernel hH hLE hlam hLam A (visitActiveUnion c J) b
          have hz := enlargedActiveExit_ae_quadratic_zero_or_terminal
            hH hLE hlam hLam A c J b hJ (Measure.dirac p)
          rw [Measure.dirac_bind E.measurable p] at hz
          have heq : (∫ q, visitQuadratic c (q.velocity 0) ∂E p) =
              ∫ q, visitQuadratic c (q.velocity 0)
                ∂enlargedActiveTerminalFamily hH hLE hlam hLam A c J b p := by
            unfold enlargedActiveTerminalFamily
            rw [ite_eq_right (fun h => (ne_of_lt ht) h.1)]
            rw [← integral_indicator
              (isClosed_eq continuous_time continuous_const).measurableSet]
            apply integral_congr_ae
            filter_upwards [hz] with q hq
            rcases hq with hq | hq
            · simp [Set.indicator, hq]
            · by_cases hqb : q.time = b
              · simp [Set.indicator, hqb]
              · simp [Set.indicator, hqb, hq]
          rw [← he, ← hg] at hi
          rw [heq] at hi
          have hn : (fun q : Point => -2 * A.a (q.position 0) (q.velocity 0)) =
              -(fun q => 2 * A.a (q.position 0) (q.velocity 0)) := by
            funext q
            simp
          rw [hn, integral_neg', sub_neg_eq_add] at hi
          exact hi
        have entranceSlabQuadratic_terminal_at_start (ht : p.time = b) :
            (∫ q, visitQuadratic c (q.velocity 0)
            ∂enlargedActiveTerminalFamily hH hLE hlam hLam A c J b p) =
              visitQuadratic c (p.velocity 0) := by
          unfold enlargedActiveTerminalFamily
          rw [ite_eq_left ⟨ht, hv⟩, integral_dirac]
        classical
        rcases lt_or_eq_of_le ht with hlt | heq
        · exact entranceSlabQuadratic_point_identity hlt
        · have hg : enlargedVisitGreenKernel hH hLE hlam hLam A (visitActiveUnion c J) b p =
              0 := by
            change (if h : p ∈ enlargedVisitPoleSet (visitActiveUnion c J) b then
              finiteUnionGreen hH hLE hlam hLam A (visitActiveUnion c J) b
                (enlargedVisitPole _ b ⟨p, h⟩) else 0) = 0
            exact dite_eq_right (fun h => (ne_of_lt h.1) heq)
          rw [hg, integral_zero_measure, add_zero,
            entranceSlabQuadratic_terminal_at_start heq]
      let K := entranceSlabTerminalKernel hH hLE hlam hLam A c J b
      let G := enlargedVisitGreenKernel hH hLE hlam hLam A (visitActiveUnion c J) b
      let f := fun p : Point => visitQuadratic c (p.velocity 0)
      let g := fun p : Point => 2 * A.a (p.position 0) (p.velocity 0)
      have : IsFiniteMeasure (G ∘ₘ mu) := entranceSlabGreen_isFiniteMeasure
        hH hLE hlam hLam A c J a b mu (hmu.mono fun _ hp => hp.1)
      have hK : Integrable f (K ∘ₘ mu) :=
        entranceSlabTerminal_quadratic_integrable mu
      have hG : Integrable g (G ∘ₘ mu) := visitCoefficient_integrable hlam A _
      have hiK : Integrable (fun p => ∫ q, f q ∂K p) mu := by
        rw [Measure.comp_eq_comp_const_apply] at hK
        simpa using hK.integral_comp
      have hiG : Integrable (fun p => ∫ q, g q ∂G p) mu := by
        rw [Measure.comp_eq_comp_const_apply] at hG
        simpa using hG.integral_comp
      have hp : f =ᵐ[mu] fun p => (∫ q, f q ∂K p) + ∫ q, g q ∂G p := by
        filter_upwards [hmu] with p hp
        exact entranceSlabQuadratic_closed_point_identity p hp.2.1 hp.2.2
      change (∫ p, f p ∂mu) = (∫ q, f q ∂K ∘ₘ mu) + ∫ q, g q ∂G ∘ₘ mu
      rw [integral_congr_ae hp, integral_add hiK hiG]
      rw [nested_integral_bind mu K K.measurable f hK,
        nested_integral_bind mu G G.measurable g hG]
    have entranceSlabQuadratic_integral_le_active (mu : Measure Point) [IsFiniteMeasure mu] (hi : Integrable (fun q => visitQuadratic c (q.velocity 0)) mu) :
        (∫ q, visitQuadratic c (q.velocity 0) ∂mu) ≤
        9 * c.r ^ 2 / 16 * (mu {q | q.velocity 0 ∈ c.active}).toReal := by
      have entranceSlabQuadratic_nonpos (v : ℝ) (hv : v ∉ c.active) :
          visitQuadratic c v ≤ 0 := by
        have hr := c.positive
        change ¬(c.vbar - 3 * c.r / 4 < v ∧ v < c.vbar + 3 * c.r / 4) at hv
        rw [visitQuadratic]
        by_cases hl : c.vbar - 3 * c.r / 4 < v
        · have hu : c.vbar + 3 * c.r / 4 ≤ v := le_of_not_gt (fun h => hv ⟨hl, h⟩)
          exact mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hl.le) (sub_nonpos.mpr hu)
        · have hl' : v ≤ c.vbar - 3 * c.r / 4 := le_of_not_gt hl
          exact mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hl') (by linarith)
      let B : Set Point := {q | q.velocity 0 ∈ c.active}
      have hB : MeasurableSet B := isOpen_Ioo.measurableSet.preimage
        ((continuous_apply 0).comp continuous_velocity).measurable
      have hm := integral_mono_ae hi ((integrable_const (9 * c.r ^ 2 / 16)).indicator hB)
        (Filter.Eventually.of_forall fun q => by
          by_cases hq : q ∈ B
          · rw [indicator_of_mem hq]
            exact visitQuadratic_le c _
          · rw [indicator_of_notMem hq]
            exact entranceSlabQuadratic_nonpos _ hq)
      rw [integral_indicator hB] at hm
      simpa [integral_const, Measure.real, Measure.restrict_apply MeasurableSet.univ, univ_inter, mul_comm] using hm
    have entranceSlabQuadratic_mass_lower [IsFiniteMeasure mu] (hmu : ∀ᵐ p ∂mu, p.velocity 0 ∈ closure c.entrance) :
        5 * c.r ^ 2 / 16 * (mu univ).toReal ≤
        ∫ p, visitQuadratic c (p.velocity 0) ∂mu := by
      have entranceSlabQuadratic_integrable :
          Integrable (fun p => visitQuadratic c (p.velocity 0)) mu := by
        apply Integrable.mono' (integrable_const (9 * c.r ^ 2 / 16))
          (((visitQuadratic_smooth c).continuous.comp
            ((continuous_apply 0).comp continuous_velocity)).measurable.aestronglyMeasurable)
        filter_upwards [hmu] with p hp
        change ‖visitQuadratic c (p.velocity 0)‖ ≤ 9 * c.r ^ 2 / 16
        rw [Real.norm_eq_abs, abs_of_nonneg
          ((by positivity : 0 ≤ 5 * c.r ^ 2 / 16).trans
            (visitQuadratic_entrance_lower c hp))]
        exact visitQuadratic_le c _
      have h := integral_mono_ae (integrable_const (5 * c.r ^ 2 / 16))
        (entranceSlabQuadratic_integrable)
        (hmu.mono fun _ hp => visitQuadratic_entrance_lower c hp)
      simpa [integral_const, Measure.real, mul_comm] using h
    have : IsFiniteMeasure
        (enlargedVisitGreenKernel hH hLE hlam hLam A (visitActiveUnion c J) b ∘ₘ mu) :=
      entranceSlabGreen_isFiniteMeasure hH hLE hlam hLam A c J a b mu
        (hmu.mono fun _ hp => hp.1)
    have hi := entranceSlabQuadratic_integrated_identity
      (hmu.mono fun _ hp => ⟨hp.1, hp.2.1, by
        rw [visitActiveUnion_carrier]
        have hv := enlarged_closedEntrance_subset_active c hp.2.2
        exact ⟨hv, hJ (subset_closure hv)⟩⟩)
    have hm := entranceSlabQuadratic_mass_lower (hmu.mono fun _ hp => hp.2.2)
    rw [hi] at hm
    have ht' := entranceSlabQuadratic_integral_le_active
      (mu.bind (enlargedActiveTerminalFamily hH hLE hlam hLam A c J b))
      (entranceSlabTerminal_quadratic_integrable mu)
    exact hm.trans (add_le_add ht' (visitCoefficient_integral_le hlam A _))
  dsimp only
  let mu := fun n => (enlargedVisitEntrance hH hLE hlam hLam A c J s T P n).restrict
    {p | p.time ∈ Ioc a b}
  have hm (n : ℕ) : ∀ᵐ p ∂mu n,
      a ≤ p.time ∧ p.time ≤ b ∧ p.velocity 0 ∈ closure c.entrance := by
    have hv : ∀ᵐ p ∂mu n, p.velocity 0 ∈ closure c.entrance :=
      ((enlargedVisitEntrance_ae_support
      hH hLE hlam hLam A c J s T P hs hT n).mono fun _ hp => hp.2.2).filter_mono
        (ae_mono Measure.restrict_le_self)
    have ht : ∀ᵐ p ∂mu n, p.time ∈ Ioc a b :=
      ae_restrict_mem (measurableSet_Ioc.preimage continuous_time.measurable)
    filter_upwards [ht, hv] with p hp hvel
    exact ⟨hp.1.le, hp.2, hvel⟩
  simpa only [Finset.mul_sum, Finset.sum_add_distrib] using (Finset.sum_le_sum (s := Finset.range N) (fun n _ => entranceSlabQuadratic_mass_bound (mu n) (hm n)))


/-- The later window has length `t`; its occupation is bounded by occupation through `3t`. -/
theorem velocity_return_time_average {lam Lam : ℝ} (A : SmoothAutonomous lam Lam)
    (E : FullSpaceEvolution) (hE : IsFullSpaceEvolution A E) (z : Z) (r t C : ℝ)
    (ht : 0 < t) (hC : 0 ≤ C)
    (hcomp : ∀ s ∈ Ioc (2 * t) (3 * t),
      velocityBandAction E r t z ≤ C * velocityBandAction E r s z) :
    t * velocityBandAction E r t z ≤
      C * ∫ s in Ioc 0 (3 * t), velocityBandAction E r s z := by
  have hi : IntegrableOn (fun s => velocityBandAction E r s z) (Ioc 0 (3 * t)) :=
    velocityBandAction_integrable A E hE r (3 * t) z
  have hs : Ioc (2 * t) (3 * t) ⊆ Ioc 0 (3 * t) :=
    fun s hs => ⟨by linarith [hs.1], hs.2⟩
  have hmono := setIntegral_mono_on
    (integrableOn_const (C := (fun s => velocityBandAction E r s z) t) (by simp : volume (Ioc (2 * t) (3 * t)) ≠ ⊤))
    ((hi.mono_set hs).const_mul C) measurableSet_Ioc hcomp
  have hvol : volume.real (Ioc (2 * t) (3 * t)) = t := by
    rw [measureReal_def, Real.volume_Ioc, ENNReal.toReal_ofReal (by linarith)]
    ring
  rw [setIntegral_const, hvol, smul_eq_mul, integral_const_mul] at hmono
  have hnonneg : ∀ s, 0 ≤ velocityBandAction E r s z := fun s => by
    rw [velocityBandAction_eq_probability A E hE]
    exact ENNReal.toReal_nonneg
  exact hmono.trans (mul_le_mul_of_nonneg_left
    (setIntegral_mono_set hi (Filter.Eventually.of_forall hnonneg)
      (Filter.Eventually.of_forall hs)) hC)


/-- The source's active velocity indicator, as actual bounded Borel scalar data. -/
def activeVelocityDatum (c : Clock) : BoundedBorel Z := by
  let B : Set Z := {w | w.2 ∈ c.active}
  have hB : MeasurableSet B := isOpen_Ioo.measurableSet.preimage measurable_snd
  exact ⟨B.indicator (fun _ => 1), measurable_const.indicator hB,
    ⟨1, zero_le_one, fun w => by
      by_cases hw : w ∈ B
      · simp only [indicator_of_mem hw, abs_one, le_refl]
      · simp only [indicator_of_notMem hw, abs_zero, zero_le_one]⟩⟩


/-- The source active indicator action is the real mass of the same active velocity set. -/
theorem activeVelocityDatum_action_eq
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (c : Clock) (t : ℝ) (ht : 0 ≤ t) (z : Z) :
    S hH hLE hlam hLam A t (activeVelocityDatum c) z =
      (kernelXV (fullSpaceEvolution hH hLE hlam hLam A) (Real.toNNReal t) z
        {w | w.2 ∈ c.active}).toReal  := by
  have return_Kphysical_eq_kernelXV (z : Z) :
      Kphysical hH hLE hlam hLam A t z =
      kernelXV (fullSpaceEvolution hH hLE hlam hLam A) (Real.toNNReal t) z := by
    unfold Kphysical kernelXV wholeQuery
    rw [dite_eq_left ht]
    simp only [Real.coe_toNNReal t ht]
    rfl
  rw [S_eq_integral hH hLE hlam hLam A t ht]
  change (∫ w, ({w : Z | w.2 ∈ c.active}).indicator (fun _ => 1) w
    ∂Kphysical hH hLE hlam hLam A t z) = _
  have hB : MeasurableSet {w : Z | w.2 ∈ c.active} :=
    isOpen_Ioo.measurableSet.preimage measurable_snd
  rw [integral_indicator hB]
  simp [integral_const, Measure.real, Measure.restrict_apply MeasurableSet.univ, univ_inter, return_Kphysical_eq_kernelXV]



/-- Full-space terminal measures are finite in physical spacetime. -/
instance entranceSlab_fullSpaceTerminal_isFiniteMeasure
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (P : Point) (b : ℝ) :
    IsFiniteMeasure (enlargedFullSpaceTerminal hH hLE hlam hLam A P b) := by
  exact ⟨(enlargedFullSpaceTerminal_mass_le_one hH hLE hlam hLam A P b).trans_lt
    ENNReal.one_lt_top⟩

/-- Full-space occupation on a finite observation window is a finite physical measure. -/
instance entranceSlab_fullSpaceOccupation_isFiniteMeasure
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (P : Point) (T : ℝ) :
    IsFiniteMeasure (enlargedFullSpaceOccupation hH hLE hlam hLam A P T) := by
  unfold enlargedFullSpaceOccupation
  infer_instance



/-- The real physical slab mass is exactly the source active-velocity action integral. -/
theorem entranceSlab_fullSpaceOccupation_active_real
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (c : Clock) (P : Point) (T a b : ℝ)
    (ha : 0 ≤ a) (hbT : b ≤ T) :
    (enlargedFullSpaceOccupation hH hLE hlam hLam A P T
      {q | q.time ∈ Ioc (P.time + a) (P.time + b) ∧ q.velocity 0 ∈ c.active}).toReal =
      ∫ t in Ioc a b,
        S hH hLE hlam hLam A t (activeVelocityDatum c) (P.position 0, P.velocity 0)  := by
  have entranceSlab_fullSpaceOccupation_active :
      enlargedFullSpaceOccupation hH hLE hlam hLam A P T
      {q | q.time ∈ Ioc (P.time + a) (P.time + b) ∧ q.velocity 0 ∈ c.active} =
      ∫⁻ t in Ioc a b,
        kernelXV (fullSpaceEvolution hH hLE hlam hLam A) (Real.toNNReal t)
          (P.position 0, P.velocity 0) {z | z.2 ∈ c.active} := by
    let B : Set Point :=
      {q | q.time ∈ Ioc (P.time + a) (P.time + b) ∧ q.velocity 0 ∈ c.active}
    let V : Set Z := {z | z.2 ∈ c.active}
    have hB : MeasurableSet B :=
      (measurableSet_Ioc.preimage continuous_time.measurable).inter
        (isOpen_Ioo.measurableSet.preimage
          ((continuous_apply 0).comp continuous_velocity).measurable)
    have hV : MeasurableSet V := isOpen_Ioo.measurableSet.preimage measurable_snd
    let K := fun t : ℝ => kernelXV (fullSpaceEvolution hH hLE hlam hLam A)
      (Real.toNNReal t) (P.position 0, P.velocity 0)
    have hi (t : ℝ) : (∫⁻ z, B.indicator 1
        (enlargedTerminalPoint (P.time + t) z) ∂K t) =
        (Ioc a b).indicator (fun t => K t V) t := by
      have ht : P.time + t ∈ Ioc (P.time + a) (P.time + b) ↔ t ∈ Ioc a b := by
        simp
      by_cases h : t ∈ Ioc a b
      · have htime := ht.mpr h
        rw [indicator_of_mem h]
        have he : (fun z => B.indicator (1 : Point → ℝ≥0∞)
            (enlargedTerminalPoint (P.time + t) z)) = V.indicator 1 := by
          funext z
          have hm : enlargedTerminalPoint (P.time + t) z ∈ B ↔ z ∈ V := by
            change (P.time + t ∈ Ioc (P.time + a) (P.time + b) ∧ z.2 ∈ c.active) ↔
              z.2 ∈ c.active
            exact and_iff_right htime
          by_cases hz : z ∈ V
          · rw [indicator_of_mem (hm.mpr hz), indicator_of_mem hz]
            rfl
          · rw [indicator_of_notMem (mt hm.mp hz), indicator_of_notMem hz]
        rw [he, lintegral_indicator_one hV]
      · have htime := mt ht.mp h
        rw [indicator_of_notMem h]
        have he : (fun z => B.indicator (1 : Point → ℝ≥0∞)
            (enlargedTerminalPoint (P.time + t) z)) = 0 := by
          funext z
          have hm : enlargedTerminalPoint (P.time + t) z ∉ B := by
            intro hp
            exact htime hp.1
          rw [indicator_of_notMem hm]
          rfl
        rw [he, lintegral_zero_fun]
    change enlargedFullSpaceOccupation hH hLE hlam hLam A P T B =
      ∫⁻ t in Ioc a b, K t V
    calc
      _ = ∫⁻ q, B.indicator 1 q
          ∂enlargedFullSpaceOccupation hH hLE hlam hLam A P T :=
        (lintegral_indicator_one hB).symm
      _ = ∫⁻ t in Ioc 0 T, ∫⁻ z, B.indicator 1
          (enlargedTerminalPoint (P.time + t) z) ∂K t :=
        enlargedFullSpaceOccupation_lintegral hH hLE hlam hLam A P T
          (B.indicator 1) (measurable_const.indicator hB)
      _ = ∫⁻ t in Ioc 0 T, (Ioc a b).indicator (fun t => K t V) t :=
        lintegral_congr hi
      _ = _ := by
        rw [lintegral_indicator measurableSet_Ioc,
          Measure.restrict_restrict measurableSet_Ioc,
          inter_eq_left.mpr (show Ioc a b ⊆ Ioc 0 T from
            fun _ ht => ⟨ha.trans_lt ht.1, ht.2.trans hbT⟩)]
  let E := fullSpaceEvolution hH hLE hlam hLam A
  let z : Z := (P.position 0, P.velocity 0)
  let B : Set Z := {w | w.2 ∈ c.active}
  let f := fun t : ℝ => kernelXV E (Real.toNNReal t) z B
  have hf : Measurable f :=
    (physicalElapsedKernel E z).measurable_coe (isOpen_Ioo.measurableSet.preimage measurable_snd)
  have hfinite (t : ℝ) : f t < ⊤ :=
    ((measure_mono (subset_univ B)).trans (kernelXV_mass_le_one E (Real.toNNReal t) z)).trans_lt
      ENNReal.one_lt_top
  have hi : (∫ t in Ioc a b, (f t).toReal) = (∫⁻ t in Ioc a b, f t).toReal :=
    integral_toReal hf.aemeasurable (Filter.Eventually.of_forall hfinite)
  have hS : (∫ t in Ioc a b,
      S hH hLE hlam hLam A t (activeVelocityDatum c) z) = ∫ t in Ioc a b, (f t).toReal := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact activeVelocityDatum_action_eq hH hLE hlam hLam A c t (ha.trans ht.1.le) z
  exact (congrArg ENNReal.toReal (entranceSlab_fullSpaceOccupation_active)).trans (hi.symm.trans hS.symm)


/-- The real finite occupation sum is bounded by the literal source active-band integral. -/
theorem entranceSlab_partial_occupation_mass_le
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (c : Clock) (J : Interval) (T a b : ℝ)
    (hT : 0 < T) (ha : 0 ≤ a) (hbT : b ≤ T) (hJ : closure c.active ⊆ J.carrier)
    (P : Point) (hv : P.velocity 0 ∈ J.carrier) (N : ℕ) :
    (∑ n ∈ Finset.range N,
      ((enlargedVisitGreenKernel hH hLE hlam hLam A (visitActiveUnion c J) (P.time + b) ∘ₘ
        (enlargedVisitEntrance hH hLE hlam hLam A c J P.time (P.time + T) P n).restrict
          {p | p.time ∈ Ioc (P.time + a) (P.time + b)}) univ).toReal) ≤
      ∫ t in Ioc a b,
        S hH hLE hlam hLam A t (activeVelocityDatum c) (P.position 0, P.velocity 0)  := by
  have entranceSlab_partial_occupation_le_fullspace :
      (∑ n ∈ Finset.range N,
      enlargedVisitGreenKernel hH hLE hlam hLam A (visitActiveUnion c J) (P.time + b) ∘ₘ
        (enlargedVisitEntrance hH hLE hlam hLam A c J P.time (P.time + T) P n).restrict
          {p | p.time ∈ Ioc (P.time + a) (P.time + b)}) ≤
      (enlargedFullSpaceOccupation hH hLE hlam hLam A P T).restrict
        {q | q.time ∈ Ioc (P.time + a) (P.time + b) ∧ q.velocity 0 ∈ c.active} := by
    have entranceSlab_greenMixture_le_restrict (a : ℝ) (b : ℝ) (T : ℝ) (hBT : b ≤ T) (mu : Measure Point) :
        enlargedVisitGreenKernel hH hLE hlam hLam A (visitActiveUnion c J) b ∘ₘ
        mu.restrict {p | p.time ∈ Ioc a b} ≤
        (enlargedVisitGreenKernel hH hLE hlam hLam A (visitActiveUnion c J) T ∘ₘ mu).restrict
          {q | q.time ∈ Ioc a b ∧ q.velocity 0 ∈ c.active} := by
      have entranceSlab_greenMixture_ae_support :
          ∀ᵐ q ∂(enlargedVisitGreenKernel hH hLE hlam hLam A (visitActiveUnion c J) b ∘ₘ
          mu.restrict {p | p.time ∈ Ioc a b}),
          q.time ∈ Ioc a b ∧ q.velocity 0 ∈ c.active := by
        have entranceSlab_greenKernel_ae_support (p : Point) :
            ∀ᵐ q ∂enlargedVisitGreenKernel hH hLE hlam hLam A (visitActiveUnion c J) b p,
            p.time < q.time ∧ q.time < b ∧ q.velocity 0 ∈ c.active := by
          classical
          rw [enlarged_activeUnion_eq c J hJ]
          change ∀ᵐ q ∂(if hp : p ∈ enlargedVisitPoleSet c.activeInterval.toFiniteUnion b then
            finiteUnionGreen hH hLE hlam hLam A c.activeInterval.toFiniteUnion b
              (enlargedVisitPole _ b ⟨p, hp⟩) else 0), _
          split
          · rename_i hp
            have hv : p.velocity 0 ∈ c.activeInterval.carrier := by
              simpa only [Interval.toFiniteUnion_carrier] using hp.2
            let e : StripPole c.activeInterval ⊤ := ⟨p, WithTop.coe_lt_top _, hv⟩
            change ∀ᵐ q ∂stripGreen hH hLE hlam hLam A c.activeInterval b
              (stripPoleFinite c.activeInterval e b hp.1), _
            rw [stripGreen_finite_restrict_infinite hH hLE hlam hLam A c.activeInterval e b hp.1]
            have ht : ∀ᵐ q ∂(stripGreen hH hLE hlam hLam A c.activeInterval ⊤ e).restrict
                {q | q.time < b}, q.time < b :=
              ae_restrict_mem (isOpen_lt continuous_time continuous_const).measurableSet
            filter_upwards [(stripGreen_infinite_ae_future_carrier hH hLE hlam hLam A c.activeInterval e).filter_mono (ae_mono (Measure.restrict_le_self (s := {q | q.time < b}))), ht] with q hq hqt
            exact ⟨hq.1, hqt, hq.2⟩
          · simp only [ae_zero, Filter.eventually_bot]
        apply Measure.ae_comp_of_ae_ae
          ((measurableSet_Ioc.preimage continuous_time.measurable).inter
            (isOpen_Ioo.measurableSet.preimage
              ((continuous_apply 0).comp continuous_velocity).measurable))
        filter_upwards [ae_restrict_mem
          (measurableSet_Ioc.preimage continuous_time.measurable)] with p hp
        exact (entranceSlab_greenKernel_ae_support p).mono
          fun q hq => ⟨⟨hp.1.trans hq.1, hq.2.1.le⟩, hq.2.2⟩
      have entranceSlab_greenMixture_le (H : FiniteIntervalUnion) (D : Set Point) :
          enlargedVisitGreenKernel hH hLE hlam hLam A H b ∘ₘ mu.restrict D ≤
          enlargedVisitGreenKernel hH hLE hlam hLam A H T ∘ₘ mu := by
        have entranceSlab_greenKernel_horizon_le (p : Point) :
            enlargedVisitGreenKernel hH hLE hlam hLam A H b p ≤
            (enlargedVisitGreenKernel hH hLE hlam hLam A H T p).restrict {q | q.time < b} := by
          have entranceSlab_unionGreen_horizon_restrict (hb : p.time < b) (hv : p.velocity 0 ∈ H.carrier) :
              finiteUnionGreen hH hLE hlam hLam A H b (enlargedVisitPole H b ⟨p, hb, hv⟩) =
              (finiteUnionGreen hH hLE hlam hLam A H T
                (enlargedVisitPole H T ⟨p, hb.trans_le hBT, hv⟩)).restrict {q | q.time < b} := by
            let ep := enlargedVisitPole H T ⟨p, hb.trans_le hBT, hv⟩
            let i := finiteUnionPoleIndex H T ep
            let e := stripPoleInfinite (H.component i) T (finiteUnionComponentPole H T ep)
            have he : enlargedVisitPole H b ⟨p, hb, hv⟩ =
                componentPoleInclusion H i b (stripPoleFinite (H.component i) e b hb) :=
              Subtype.ext rfl
            rw [he, finiteUnionGreen_component]
            change stripGreen hH hLE hlam hLam A (H.component i) b
                (stripPoleFinite (H.component i) e b hb) =
              (stripGreen hH hLE hlam hLam A (H.component i) T
                (stripPoleFinite (H.component i) e T (hb.trans_le hBT))).restrict {q | q.time < b}
            rw [stripGreen_finite_restrict_infinite hH hLE hlam hLam A (H.component i) e b hb,
              stripGreen_finite_restrict_infinite hH hLE hlam hLam A (H.component i) e T
                (hb.trans_le hBT),
              Measure.restrict_restrict (isOpen_lt continuous_time continuous_const).measurableSet,
              inter_eq_left.mpr (show {q : Point | q.time < b} ⊆ {q | q.time < T} from
                fun _ hq => hq.trans_le hBT)]
          classical
          by_cases hp : p ∈ enlargedVisitPoleSet H b
          · have hpT : p ∈ enlargedVisitPoleSet H T := ⟨hp.1.trans_le hBT, hp.2⟩
            change (if h : p ∈ enlargedVisitPoleSet H b then
              finiteUnionGreen hH hLE hlam hLam A H b (enlargedVisitPole H b ⟨p, h⟩) else 0) ≤
              (if h : p ∈ enlargedVisitPoleSet H T then
                finiteUnionGreen hH hLE hlam hLam A H T (enlargedVisitPole H T ⟨p, h⟩)
                  else 0).restrict {q | q.time < b}
            rw [dite_eq_left hp, dite_eq_left hpT]
            exact (entranceSlab_unionGreen_horizon_restrict hp.1 hp.2).le
          · have hz : enlargedVisitGreenKernel hH hLE hlam hLam A H b p = 0 := by
              change (if h : p ∈ enlargedVisitPoleSet H b then
                finiteUnionGreen hH hLE hlam hLam A H b (enlargedVisitPole H b ⟨p, h⟩)
                  else 0) = 0
              exact dite_eq_right hp
            rw [hz]
            exact Measure.zero_le _
        apply Measure.le_iff.mpr
        intro B hB
        rw [Measure.bind_apply hB (enlargedVisitGreenKernel hH hLE hlam hLam A H b).aemeasurable, Measure.bind_apply hB (enlargedVisitGreenKernel hH hLE hlam hLam A H T).aemeasurable]
        apply lintegral_mono' Measure.restrict_le_self
        intro p
        exact ((entranceSlab_greenKernel_horizon_le p).trans
          Measure.restrict_le_self) B
      have hle := Measure.restrict_mono (subset_refl
        {q : Point | q.time ∈ Ioc a b ∧ q.velocity 0 ∈ c.active})
          (entranceSlab_greenMixture_le (visitActiveUnion c J) {p | p.time ∈ Ioc a b})
      have heq : (enlargedVisitGreenKernel hH hLE hlam hLam A (visitActiveUnion c J) b ∘ₘ
          mu.restrict {p | p.time ∈ Ioc a b}).restrict
            {q | q.time ∈ Ioc a b ∧ q.velocity 0 ∈ c.active} =
          enlargedVisitGreenKernel hH hLE hlam hLam A (visitActiveUnion c J) b ∘ₘ
            mu.restrict {p | p.time ∈ Ioc a b} :=
        Measure.restrict_eq_self_of_ae_mem
          (entranceSlab_greenMixture_ae_support)
      exact heq.symm.le.trans hle
    let S : Set Point :=
      {q | q.time ∈ Ioc (P.time + a) (P.time + b) ∧ q.velocity 0 ∈ c.active}
    let gm := enlargedActivePiece hH hLE hlam hLam A c J P.time (P.time + T) P
    have he : ∀ N : ℕ, (∑ n ∈ Finset.range N, (gm n).restrict S) =
        (∑ n ∈ Finset.range N, gm n).restrict S := by
      intro N
      induction N with
      | zero => simp [Finset.range_zero, Measure.restrict_zero]
      | succ N ih => rw [Finset.sum_range_succ, Finset.sum_range_succ,
          Measure.restrict_add, ih]
    exact (Finset.sum_le_sum (s := Finset.range N) (fun n _ => entranceSlab_greenMixture_le_restrict (P.time + a) (P.time + b) (P.time + T) (by linarith only [hbT]) (enlargedVisitEntrance hH hLE hlam hLam A c J P.time (P.time + T) P n))).trans ((he N).le.trans (Measure.restrict_mono (subset_refl S)
      (enlarged_active_occupation_le_fullspace hH hLE hlam hLam A c J T hT P hv N)))
  let gm := fun n => enlargedVisitGreenKernel hH hLE hlam hLam A (visitActiveUnion c J)
    (P.time + b) ∘ₘ
      (enlargedVisitEntrance hH hLE hlam hLam A c J P.time (P.time + T) P n).restrict
        {p | p.time ∈ Ioc (P.time + a) (P.time + b)}
  have : ∀ n, IsFiniteMeasure (gm n) := fun n =>
    entranceSlabGreen_isFiniteMeasure hH hLE hlam hLam A c J (P.time + a) (P.time + b) _
      ((ae_restrict_mem (measurableSet_Ioc.preimage continuous_time.measurable)).mono
        fun _ hp => hp.1.le)
  have hr := ENNReal.toReal_mono (measure_ne_top _ univ) (entranceSlab_partial_occupation_le_fullspace univ)
  rw [Measure.restrict_apply MeasurableSet.univ, univ_inter,
    entranceSlab_fullSpaceOccupation_active_real hH hLE hlam hLam A c P T a b ha hbT] at hr
  rw [visit_partial_real_mass gm N univ MeasurableSet.univ] at hr
  exact hr


/-- The slab constant depends only on the upper ellipticity bound. -/
def entranceSlabConstant (Lam : ℝ) : ℝ := 9 / 5 + 32 * Lam / 5

/-- The source slab constant is strictly positive for positive ellipticity. -/
theorem entranceSlabConstant_pos {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam) :
    0 < entranceSlabConstant Lam := by
  have hL := hlam.trans_le hLam
  unfold entranceSlabConstant
  positivity

/-- Dividing the source quadratic inequality gives its radius-normalized slab estimate. -/
theorem entranceSlab_mass_arithmetic {r Lam M p g : ℝ}
    (hr : 0 < r) (hLam : 0 ≤ Lam) (hp : 0 ≤ p) (hg : 0 ≤ g)
    (hM : 5 * r ^ 2 / 16 * M ≤ 9 * r ^ 2 / 16 * p + 2 * Lam * g) :
    M ≤ entranceSlabConstant Lam * (p + r ^ (-2 : ℤ) * g) := by
  have hinv : r ^ (-2 : ℤ) = 1 / r ^ 2 := by
    norm_num only [zpow_neg, zpow_ofNat, one_div]
  rw [hinv]
  have hd : M ≤ (9 * r ^ 2 / 16 * p + 2 * Lam * g) / (5 * r ^ 2 / 16) :=
    (le_div_iff₀ (by positivity : 0 < 5 * r ^ 2 / 16)).mpr
      (by simpa only [mul_comm] using hM)
  have he : (9 * r ^ 2 / 16 * p + 2 * Lam * g) / (5 * r ^ 2 / 16) =
      9 / 5 * p + (32 * Lam / 5) * (1 / r ^ 2 * g) := by
    field_simp
    ring
  rw [he] at hd
  have hC1 : (9 / 5 : ℝ) ≤ entranceSlabConstant Lam := by
    unfold entranceSlabConstant
    exact le_add_of_nonneg_right (by positivity)
  have hC2 : 32 * Lam / 5 ≤ entranceSlabConstant Lam := by
    unfold entranceSlabConstant
    exact le_add_of_nonneg_left (by norm_num)
  exact hd.trans (by
    rw [mul_add]
    exact add_le_add (mul_le_mul_of_nonneg_right hC1 hp)
      (mul_le_mul_of_nonneg_right hC2 (by positivity)))



/-- The source square-root decay is bounded by its value at the bin's left endpoint. -/
theorem timeBinCount_decay_le (c : Clock) (j : ℕ) (t : ℝ)
    (ht : (j : ℝ) * c.r ^ 2 ≤ t) :
    (1 + t / c.r ^ 2) ^ (-1 / 2 : ℝ) ≤ (1 + (j : ℝ)) ^ (-1 / 2 : ℝ)  := by
  have timeBinCount_scaled_time_le :
      1 + (j : ℝ) ≤ 1 + t / c.r ^ 2 := by
    linarith only [((le_div_iff₀ (sq_pos_of_pos c.positive)).mpr ht)]
  exact Real.rpow_le_rpow_of_nonpos (by positivity) (timeBinCount_scaled_time_le)
    (by norm_num)


/-- A uniform probability bound on a bin gives radius-squared times that bound in occupation. -/
theorem timeBinCount_integral_le {r a b D : ℝ} {f : ℝ → ℝ}
    (hab : a ≤ b) (hlen : b - a ≤ r ^ 2) (hD : 0 ≤ D)
    (hi : IntegrableOn f (Ioc a b)) (hb : ∀ t ∈ Ioc a b, f t ≤ D) :
    (∫ t in Ioc a b, f t) ≤ r ^ 2 * D := by
  have hm := setIntegral_mono_on hi
    (integrableOn_const (C := D) (by simp : volume (Ioc a b) ≠ ⊤)) measurableSet_Ioc hb
  have hv : volume.real (Ioc a b) = b - a := by
    rw [measureReal_def, Real.volume_Ioc, ENNReal.toReal_ofReal (sub_nonneg.mpr hab)]
  rw [setIntegral_const, hv, smul_eq_mul] at hm
  exact hm.trans (mul_le_mul_of_nonneg_right hlen hD)


/-- A slab of length at most one bin inherits the source square-root decay. -/
theorem timeBinCount_slab_le
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (C : ℝ) (hC : 0 < C)
    (hDecay : ∀ (A : SmoothAutonomous lam Lam) (c : Clock) (P : Point),
      |c.vbar| = 2 * c.r → P.velocity 0 ∈ closure c.entrance →
      ∀ (j : ℕ) (t : ℝ), (j : ℝ) * c.r ^ 2 ≤ t →
      S hH hLE hlam hLam A t (activeVelocityDatum c) (P.position 0, P.velocity 0) ≤
        C * (1 + (j : ℝ)) ^ (-1 / 2 : ℝ))
    (A : SmoothAutonomous lam Lam) (c : Clock) (J : Interval) (T : ℝ) (P : Point)
    (hbar : |c.vbar| = 2 * c.r) (hJ : closure c.active ⊆ J.carrier) (hT : 0 < T)
    (hvel : P.velocity 0 ∈ closure c.entrance) (j : ℕ) (a b : ℝ)
    (hja : (j : ℝ) * c.r ^ 2 ≤ a) (hab : a ≤ b) (hbT : b ≤ T)
    (hlen : b - a ≤ c.r ^ 2) :
    (visitsFromZero hH hLE hlam hLam A c J T P
      {p | p.time ∈ Ioc (P.time + a) (P.time + b)}).toReal ≤
      (2 * entranceSlabConstant Lam * C) * (1 + (j : ℝ)) ^ (-1 / 2 : ℝ)     := by
  have entranceSlab_activeAction_integrableOn (z : Z) (ha : 0 ≤ a) :
      IntegrableOn (fun t => S hH hLE hlam hLam A t (activeVelocityDatum c) z) (Ioc a b) := by
    let E := fullSpaceEvolution hH hLE hlam hLam A
    let B : Set Z := {w | w.2 ∈ c.active}
    have hm : Measurable (fun t : ℝ => kernelXV E (Real.toNNReal t) z B) :=
      (physicalElapsedKernel E z).measurable_coe (isOpen_Ioo.measurableSet.preimage measurable_snd)
    have hi : IntegrableOn (fun t => (kernelXV E (Real.toNNReal t) z B).toReal)
        (Ioc a b) := by
      apply Integrable.mono' (integrable_const 1) hm.ennreal_toReal.aestronglyMeasurable
      exact Filter.Eventually.of_forall fun t => by
        rw [Real.norm_of_nonneg ENNReal.toReal_nonneg]
        simpa only [ENNReal.toReal_one] using ENNReal.toReal_mono ENNReal.one_ne_top
          ((measure_mono (subset_univ B)).trans (kernelXV_mass_le_one E (Real.toNNReal t) z))
    apply hi.congr
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact (activeVelocityDatum_action_eq hH hLE hlam hLam A c t (ha.trans ht.1.le) z).symm
  have entranceSlab_fullSpaceTerminal_active :
      enlargedFullSpaceTerminal hH hLE hlam hLam A P (P.time + b)
      {q | q.velocity 0 ∈ c.active} =
      kernelXV (fullSpaceEvolution hH hLE hlam hLam A) (Real.toNNReal b)
        (P.position 0, P.velocity 0) {z | z.2 ∈ c.active} := by
    have hB : MeasurableSet {q : Point | q.velocity 0 ∈ c.active} :=
      isOpen_Ioo.measurableSet.preimage
        ((continuous_apply 0).comp continuous_velocity).measurable
    have he := Measure.map_apply
      (μ := kernelXV (fullSpaceEvolution hH hLE hlam hLam A)
        (Real.toNNReal (P.time + b - P.time)) (P.position 0, P.velocity 0))
      (enlargedTerminalPoint_measurable (P.time + b)) hB
    have ht : P.time + b - P.time = b := by ring
    rw [ht] at he
    unfold enlargedFullSpaceTerminal
    rw [ht]
    exact he
  have entranceSlabTerminal_restrict_bind_le (b : ℝ) (mu : Measure Point) (D : Set Point) :
      (mu.restrict D).bind (enlargedActiveTerminalFamily hH hLE hlam hLam A c J b) ≤
      mu.bind (enlargedActiveTerminalFamily hH hLE hlam hLam A c J b) := by
    have entranceSlabTerminalFamily_measurable : Measurable (enlargedActiveTerminalFamily hH hLE hlam hLam A c J b) :=
      (entranceSlabTerminalKernel hH hLE hlam hLam A c J b).measurable
    apply Measure.le_iff.mpr
    intro B hB
    rw [Measure.bind_apply hB
      (entranceSlabTerminalFamily_measurable).aemeasurable,
      Measure.bind_apply hB
        (entranceSlabTerminalFamily_measurable).aemeasurable]
    exact lintegral_mono' Measure.restrict_le_self le_rfl
  have entranceSlab_mass_le (ha : 0 ≤ a) (hv : P.velocity 0 ∈ J.carrier) :
      visitsFromZero hH hLE hlam hLam A c J T P
      {p | p.time ∈ Ioc (P.time + a) (P.time + b)} ≤
      ENNReal.ofReal (entranceSlabConstant Lam *
        (S hH hLE hlam hLam A b (activeVelocityDatum c) (P.position 0, P.velocity 0) +
          c.r ^ (-2 : ℤ) * ∫ t in Ioc a b,
            S hH hLE hlam hLam A t (activeVelocityDatum c) (P.position 0, P.velocity 0))) := by
    have entranceSlab_partial_terminal_mass_le (hb : 0 ≤ b) (N : ℕ) :
        (∑ n ∈ Finset.range N,
        (((enlargedVisitEntrance hH hLE hlam hLam A c J P.time (P.time + T) P n).restrict
          {p | p.time ∈ Ioc (P.time + a) (P.time + b)}).bind
            (enlargedActiveTerminalFamily hH hLE hlam hLam A c J (P.time + b))
              {q | q.velocity 0 ∈ c.active}).toReal) ≤
        S hH hLE hlam hLam A b (activeVelocityDatum c) (P.position 0, P.velocity 0) := by
      let gamma := enlargedVisitEntrance hH hLE hlam hLam A c J P.time (P.time + T) P
      let F := enlargedActiveTerminalFamily hH hLE hlam hLam A c J (P.time + b)
      let D : Set Point := {p | p.time ∈ Ioc (P.time + a) (P.time + b)}
      let B : Set Point := {q | q.velocity 0 ∈ c.active}
      let tm := fun n => ((gamma n).restrict D).bind F
      have hB : MeasurableSet B := isOpen_Ioo.measurableSet.preimage
        ((continuous_apply 0).comp continuous_velocity).measurable
      have hm : (∑ n ∈ Finset.range N, tm n) ≤
          enlargedFullSpaceTerminal hH hLE hlam hLam A P (P.time + b) := by
        calc
          _ ≤ ∑ n ∈ Finset.range N, (gamma n).bind F :=
            Finset.sum_le_sum fun n _ => entranceSlabTerminal_restrict_bind_le (P.time + b) (gamma n) D
          _ ≤ _ := enlarged_active_terminal_le_fullspace hH hLE hlam hLam A c J
            P.time (P.time + T) P le_rfl (by linarith) hJ N (P.time + b)
              (by linarith) (by linarith)
      have hr := ENNReal.toReal_mono
        (measure_ne_top (enlargedFullSpaceTerminal hH hLE hlam hLam A P (P.time + b)) B)
        (hm B)
      rw [visit_partial_real_mass tm N B hB] at hr
      have he := entranceSlab_fullSpaceTerminal_active
      rw [he] at hr
      exact hr.trans_eq (activeVelocityDatum_action_eq hH hLE hlam hLam A c b hb
        (P.position 0, P.velocity 0)).symm
    let gamma := enlargedVisitEntrance hH hLE hlam hLam A c J P.time (P.time + T) P
    let D : Set Point := {p | p.time ∈ Ioc (P.time + a) (P.time + b)}
    let mu := fun n => (gamma n).restrict D
    let f := fun t => S hH hLE hlam hLam A t (activeVelocityDatum c)
      (P.position 0, P.velocity 0)
    have hp : 0 ≤ f b := by
      dsimp only [f]
      rw [activeVelocityDatum_action_eq hH hLE hlam hLam A c b (ha.trans hab)]
      exact ENNReal.toReal_nonneg
    have hg : 0 ≤ ∫ t in Ioc a b, f t := by
      rw [← entranceSlab_fullSpaceOccupation_active_real hH hLE hlam hLam A c P T a b ha hbT]
      exact ENNReal.toReal_nonneg
    have hbound (N : ℕ) : (∑ n ∈ Finset.range N, mu n) univ ≤
        ENNReal.ofReal (entranceSlabConstant Lam *
          (f b + c.r ^ (-2 : ℤ) * ∫ t in Ioc a b, f t)) := by
      have ht := entranceSlab_partial_terminal_mass_le (ha.trans hab) N
      have hL : 0 ≤ Lam := (hlam.trans_le hLam).le
      have hq' : 5 * c.r ^ 2 / 16 * (∑ n ∈ Finset.range N, (mu n univ).toReal) ≤
          9 * c.r ^ 2 / 16 * f b + 2 * Lam * ∫ t in Ioc a b, f t :=
        (entranceSlabQuadratic_partial_mass_bound hH hLE hlam hLam A c J P.time (P.time + T) P le_rfl (by linarith) hJ (P.time + a) (P.time + b) N).trans (add_le_add (mul_le_mul_of_nonneg_left ht (by positivity))
          (mul_le_mul_of_nonneg_left (entranceSlab_partial_occupation_mass_le hH hLE hlam hLam A c J T a b hT ha hbT hJ P hv N) (by positivity)))
      have hr := entranceSlab_mass_arithmetic c.positive hL hp hg hq'
      rw [← visit_partial_real_mass mu N univ MeasurableSet.univ] at hr
      exact (ENNReal.le_ofReal_iff_toReal_le (measure_ne_top _ univ) (by
        exact mul_nonneg (entranceSlabConstant_pos hlam hLam).le
          (add_nonneg hp (mul_nonneg (by positivity) hg)))).mpr hr
    have hm := visit_sum_mass_le_of_partial_mass_le mu _ hbound
    have hD : MeasurableSet D := measurableSet_Ioc.preimage continuous_time.measurable
    have he : Measure.sum mu = (Measure.sum gamma).restrict D :=
      (Measure.restrict_sum gamma hD).symm
    rw [he, Measure.restrict_apply MeasurableSet.univ, univ_inter] at hm
    exact hm
  let d := C * (1 + (j : ℝ)) ^ (-1 / 2 : ℝ)
  let f := fun t => S hH hLE hlam hLam A t (activeVelocityDatum c)
    (P.position 0, P.velocity 0)
  have hd : 0 ≤ d := by dsimp only [d]; positivity
  have ha : 0 ≤ a := (by positivity : 0 ≤ (j : ℝ) * c.r ^ 2).trans hja
  have hp : f b ≤ d := hDecay A c P hbar hvel j b (hja.trans hab)
  have hg : (∫ t in Ioc a b, f t) ≤ c.r ^ 2 * d :=
    timeBinCount_integral_le hab hlen hd
      (entranceSlab_activeAction_integrableOn
        (P.position 0, P.velocity 0) ha)
      (fun t ht => hDecay A c P hbar hvel j t (hja.trans ht.1.le))
  have hn : c.r ^ (-2 : ℤ) * c.r ^ 2 = 1 := by
    norm_num only [zpow_neg, zpow_ofNat]
    exact inv_mul_cancel₀ (ne_of_gt (sq_pos_of_pos c.positive))
  have hb : entranceSlabConstant Lam *
      (f b + c.r ^ (-2 : ℤ) * ∫ t in Ioc a b, f t) ≤
        (2 * entranceSlabConstant Lam * C) * (1 + (j : ℝ)) ^ (-1 / 2 : ℝ) := by
    calc
      _ ≤ entranceSlabConstant Lam * (d + c.r ^ (-2 : ℤ) * (c.r ^ 2 * d)) :=
        mul_le_mul_of_nonneg_left
          (add_le_add hp (mul_le_mul_of_nonneg_left hg (by positivity)))
          (entranceSlabConstant_pos hlam hLam).le
      _ = _ := by rw [← mul_assoc, hn]; dsimp only [d]; ring
  have hv : P.velocity 0 ∈ J.carrier := hJ
    (subset_closure (enlarged_closedEntrance_subset_active c hvel))
  have hm' := (entranceSlab_mass_le ha hv).trans (ENNReal.ofReal_le_ofReal hb)
  have hr := ENNReal.toReal_mono ENNReal.ofReal_ne_top hm'
  have hCs := entranceSlabConstant_pos hlam hLam
  rw [ENNReal.toReal_ofReal (by positivity)] at hr
  exact hr



/-- Starting in the closed entrance interval contributes exactly one atom at its own time. -/
theorem timeBinCount_initial_slice
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (c : Clock) (J : Interval) (T : ℝ) (P : Point)
    (hv : P.velocity 0 ∈ closure c.entrance) :
    visitsFromZero hH hLE hlam hLam A c J T P {p | p.time = P.time} = 1  := by
  have timeBinCount_later_initial_slice_zero (s : ℝ) (T : ℝ) (n : ℕ) :
      enlargedVisitEntrance hH hLE hlam hLam A c J s T P (n + 1) {p | p.time = s} = 0 := by
    have hS : MeasurableSet {p : Point | p.time = s} :=
      (isClosed_eq continuous_time continuous_const).measurableSet
    change (_ : Measure Point).restrict (visitBoundary s T (visitEntranceInterval c) J)
      {p | p.time = s} = 0
    rw [Measure.restrict_apply hS]
    have he : {p : Point | p.time = s} ∩ visitBoundary s T (visitEntranceInterval c) J =
        ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro p hp
      exact (ne_of_lt hp.2.1) hp.1.symm
    rw [he, measure_empty]
  have hS : MeasurableSet {p : Point | p.time = P.time} :=
    (isClosed_eq continuous_time continuous_const).measurableSet
  let gm := enlargedVisitEntrance hH hLE hlam hLam A c J P.time (P.time + T) P
  change Measure.sum gm {p | p.time = P.time} = 1
  rw [Measure.sum_apply _ hS]
  have hz : ∀ n : ℕ, n ≠ 0 → gm n {p | p.time = P.time} = 0 := by
    intro n hn
    cases n with
    | zero => exact (hn rfl).elim
    | succ n =>
      exact timeBinCount_later_initial_slice_zero P.time (P.time + T) n
  rw [tsum_eq_single 0 hz]
  have he : gm 0 = Measure.dirac P := by
    change visitInitial P (visitEntranceInterval c)
      (visitBoundary P.time (P.time + T) (visitEntranceInterval c) J)
      (enlargedVisitExitKernel hH hLE hlam hLam A (visitWaitingUnion c J) (P.time + T)) = _
    unfold visitInitial
    exact ite_eq_left hv
  rw [he, Measure.dirac_apply_of_mem (show P ∈ {p : Point | p.time = P.time} from rfl)]

/-- A later bin entirely beyond the observation horizon contains no starts. -/
theorem timeBinCount_mass_eq_zero_of_horizon_le
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (c : Clock) (J : Interval) (T : ℝ) (P : Point)
    (hT : 0 < T) (j : ℕ) (hj : j ≠ 0) (hTJ : T ≤ (j : ℝ) * c.r ^ 2) :
    enlargedTimeVisitMass (visitsFromZero hH hLE hlam hLam A c J T P) c P.time j = 0 := by
  have hs := enlargedVisitStarts_ae_support hH hLE hlam hLam A c J P.time (P.time + T)
    P le_rfl (by linarith only [hT])
  have hz : visitsFromZero hH hLE hlam hLam A c J T P
      {p | p.time ∈ enlargedTimeBin c.r P.time j ∧
        p.velocity 0 ∈ closure c.entrance} = 0 := by
    apply measure_eq_zero_iff_ae_notMem.mpr
    filter_upwards [hs] with p hp
    intro hcell
    have ht := hcell.1
    rw [enlargedTimeBin, ite_eq_right hj] at ht
    have hlate : P.time + T < p.time := lt_of_le_of_lt
      (by linarith only [hTJ]) ht.1
    exact (not_lt_of_ge hlate.le) hp.2.1
  exact congrArg ENNReal.toReal hz

/-- Later bins are bounded by the literal slab truncated at the supported horizon. -/
theorem timeBinCount_mass_le_truncated_slab (nu : Measure Point) [IsFiniteMeasure nu]
    (c : Clock) (s T : ℝ) (j : ℕ) (hj : j ≠ 0)
    (hnu : ∀ᵐ p ∂nu, p.time < s + T) :
    enlargedTimeVisitMass nu c s j ≤
      (nu {p | p.time ∈ Ioc (s + (j : ℝ) * c.r ^ 2)
        (s + min (((j : ℝ) + 1) * c.r ^ 2) T)}).toReal := by
  apply ENNReal.toReal_mono (measure_ne_top nu _)
  apply measure_mono_ae
  filter_upwards [hnu] with p hp
  intro hcell
  have ht := hcell.1
  rw [enlargedTimeBin, ite_eq_right hj] at ht
  exact ⟨ht.1, by
    rw [add_min]
    exact le_min ht.2 hp.le⟩

/-- Bin zero charges its initial atom and its positive-time slab separately. -/
theorem timeBinCount_initial_mass_le_atom_add_slab
    (nu : Measure Point) [IsFiniteMeasure nu] (c : Clock) (s T : ℝ)
    (hnu : ∀ᵐ p ∂nu, p.time < s + T) :
    enlargedTimeVisitMass nu c s 0 ≤ (nu {p | p.time = s}).toReal +
      (nu {p | p.time ∈ Ioc s (s + min (c.r ^ 2) T)}).toReal := by
  let A : Set Point := {p | p.time = s}
  let B : Set Point := {p | p.time ∈ Ioc s (s + min (c.r ^ 2) T)}
  have hm : nu {p | p.time ∈ enlargedTimeBin c.r s 0 ∧
      p.velocity 0 ∈ closure c.entrance} ≤ nu A + nu B := by
    apply (measure_mono_ae ?_).trans (measure_union_le A B)
    filter_upwards [hnu] with p hp
    intro hcell
    have ht := hcell.1
    rw [enlargedTimeBin, ite_eq_left rfl] at ht
    rcases eq_or_lt_of_le ht.1 with he | hlt
    · exact Or.inl he.symm
    · right
      refine ⟨hlt, ?_⟩
      rw [add_min]
      exact le_min ht.2 hp.le
  have hr := ENNReal.toReal_mono
    (ENNReal.add_ne_top.mpr ⟨measure_ne_top nu A, measure_ne_top nu B⟩) hm
  rw [ENNReal.toReal_add (measure_ne_top nu A) (measure_ne_top nu B)] at hr
  exact hr


/-- The actual canonical visits satisfy the exact uniform time-bin count from the source. -/
theorem timeBinCount_holds_of_return_time
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (hReturn : ∃ C : ℝ, 0 < C ∧ ∀ (A : SmoothAutonomous lam Lam) (F : BoundedBorel Z),
      (∀ z, 0 ≤ F z) → ∀ t s X v : ℝ,
      0 < t → 2 * t ≤ s → s ≤ 3 * t → |v| ≤ Real.sqrt t →
      S hH hLE hlam hLam A t F (X, v) ≤ C * S hH hLE hlam hLam A s F (X, v)) :
    ∃ Ct : ℝ, 0 < Ct ∧ ∀ (A : SmoothAutonomous lam Lam) (c : Clock) (J : Interval)
      (T : ℝ) (P : Point), |c.vbar| = 2 * c.r → closure c.active ⊆ J.carrier → 0 < T →
      P.velocity 0 ∈ closure c.entrance → ∀ j : ℕ,
      enlargedTimeVisitMass (visitsFromZero hH hLE hlam hLam A c J T P) c P.time j ≤
        Ct * (1 + (j : ℝ)) ^ (-1 / 2 : ℝ)   := by
  have velocity_return_action_of_return_time (hReturn : ∃ C : ℝ, 0 < C ∧ ∀ (A : SmoothAutonomous lam Lam) (F : BoundedBorel Z),
      (∀ z, 0 ≤ F z) → ∀ t s X v : ℝ,
      0 < t → 2 * t ≤ s → s ≤ 3 * t → |v| ≤ Real.sqrt t →
      S hH hLE hlam hLam A t F (X, v) ≤ C * S hH hLE hlam hLam A s F (X, v)) :
      ∃ C : ℝ, 0 < C ∧ ∀ (A : SmoothAutonomous lam Lam) (c : Clock) (z : Z) (t : ℝ),
      |c.vbar| = 2 * c.r → |z.2| ≤ 3 * c.r → 0 ≤ t →
      S hH hLE hlam hLam A t (activeVelocityDatum c) z ≤
        C * (1 + t / c.r ^ 2) ^ (-(1 : ℝ) / 2) := by
    have velocity_band_return_of_return_time (hReturn : ∃ C : ℝ, 0 < C ∧ ∀ (A : SmoothAutonomous lam Lam) (F : BoundedBorel Z),
        (∀ z, 0 ≤ F z) → ∀ t s X v : ℝ,
        0 < t → 2 * t ≤ s → s ≤ 3 * t → |v| ≤ Real.sqrt t →
        S hH hLE hlam hLam A t F (X, v) ≤ C * S hH hLE hlam hLam A s F (X, v)) :
        ∃ C : ℝ, 0 < C ∧ ∀ (A : SmoothAutonomous lam Lam) (r : ℝ) (z : Z) (t : NNReal),
        0 < r → |z.2| ≤ 3 * r →
        (kernelXV (fullSpaceEvolution hH hLE hlam hLam A) t z
          {w | |w.2| ≤ 3 * r}).toReal ≤ C * (1 + (t : ℝ) / r ^ 2) ^ (-(1 : ℝ) / 2) := by
      obtain ⟨CR, hCR, hreturn⟩ := return_time_ambient_of_scalar hH hLE hlam hLam hReturn
      obtain ⟨B, hB, hocc⟩ := velocity_occupation_and_moment hH hLE hlam hLam
      let K := CR * B * Real.sqrt 3
      have hK : 0 < K := by dsimp only [K]; positivity
      let C := 10 ^ ((1 : ℝ) / 2) + K * 2 ^ ((1 : ℝ) / 2)
      have hC : 0 < C := by dsimp only [C]; positivity
      refine ⟨C, hC, ?_⟩
      intro A r z t hr hz
      let E := fullSpaceEvolution hH hLE hlam hLam A
      have hE := fullSpaceEvolution_spec hH hLE hlam hLam A
      let f := fun s => velocityBandAction E r s z
      let x := (t : ℝ) / r ^ 2
      have hx : 0 ≤ x := div_nonneg t.property (sq_nonneg r)
      have hx1 : 0 < 1 + x := by linarith
      have hdecay : 0 ≤ (1 + x) ^ (-(1 : ℝ) / 2) := Real.rpow_nonneg hx1.le _
      have hf : f t = (kernelXV E t z {w | |w.2| ≤ 3 * r}).toReal := by
        dsimp only [f]
        rw [velocityBandAction_eq_probability A E hE,
          velocityBandProbability_eq_kernelXV, Real.toNNReal_coe]
      by_cases hlarge : 9 * r ^ 2 ≤ (t : ℝ)
      · have ht : 0 < (t : ℝ) := lt_of_lt_of_le (by positivity) hlarge
        have hv : |z.2| ≤ Real.sqrt (t : ℝ) := hz.trans
          (Real.le_sqrt_of_sq_le (by nlinarith))
        have hfcomp (s : ℝ) (hs : s ∈ Ioc (2 * (t : ℝ)) (3 * (t : ℝ))) :
            f t ≤ CR * f s := by
          have hs0 : 0 ≤ s := by linarith [hs.1]
          have hh := hreturn A (velocityBandDatum r) (fun p => by
            change 0 ≤ ({w : EvolutionAmbientState 1 | |w.2 0| ≤ 3 * r}).indicator
              (fun _ => 1) p
            exact indicator_nonneg (fun _ _ => zero_le_one) _)
            t (Real.toNNReal s) z ht
            (by simpa only [Real.coe_toNNReal s hs0] using hs.1.le)
            (by simpa only [Real.coe_toNNReal s hs0] using hs.2) hv
          change fullSpaceAction E (velocityBandDatum r)
              ⟨t, fun _ => z.1, fun _ => z.2⟩ ≤
            CR * fullSpaceAction E (velocityBandDatum r)
              ⟨Real.toNNReal s, fun _ => z.1, fun _ => z.2⟩ at hh
          rw [← fullSpacePhysicalSemigroup_eq_action A E hE t (velocityBandDatum r)
              (fun _ => z.1, fun _ => z.2),
            ← fullSpacePhysicalSemigroup_eq_action A E hE (Real.toNNReal s)
              (velocityBandDatum r) (fun _ => z.1, fun _ => z.2)] at hh
          simpa only [f, velocityBandAction, Real.toNNReal_coe] using hh
        have hav := velocity_return_time_average A E hE z r t CR ht hCR.le hfcomp
        have hoc := (hocc A r (3 * (t : ℝ)) z hr (by positivity)).1
        have hprod := hav.trans (mul_le_mul_of_nonneg_left hoc hCR.le)
        rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 3)] at hprod
        have hraw : f t ≤ K * (r * Real.sqrt (t : ℝ) / (t : ℝ)) := by
          have hdiv : f t ≤ (CR * (B * r * (Real.sqrt 3 * Real.sqrt (t : ℝ)))) /
              (t : ℝ) := (le_div_iff₀ ht).mpr (by simpa only [mul_comm] using hprod)
          convert hdiv using 1
          dsimp only [K]
          ring
        have hscale : r * Real.sqrt (t : ℝ) / (t : ℝ) = x ^ (-(1 : ℝ) / 2) := by
          have hh := box_decay_scaling (alpha := 1) hr ht
          norm_num only [gamma, Real.rpow_one, one_div, show (2 : ℝ) - 1 = 1 by norm_num] at hh
          simpa only [Real.sqrt_eq_rpow, x, neg_div] using hh
        rw [hscale] at hraw
        have hxlarge : 1 ≤ x := by
          dsimp only [x]
          apply (le_div_iff₀ (by positivity : 0 < r ^ 2)).mpr
          nlinarith
        have hfinal := hraw.trans (mul_le_mul_of_nonneg_left
          (box_decay_large_comparison (g := 1) hxlarge (by norm_num)) hK.le)
        have hKC : K * (2 : ℝ) ^ ((1 : ℝ) / 2) ≤ C := by
          dsimp only [C]
          exact le_add_of_nonneg_left (by positivity)
        have hbound : K * ((2 : ℝ) ^ ((1 : ℝ) / 2) *
            (1 + x) ^ (-(1 : ℝ) / 2)) ≤ C * (1 + x) ^ (-(1 : ℝ) / 2) := by
          rw [← mul_assoc]
          exact mul_le_mul_of_nonneg_right hKC hdecay
        rw [hf] at hfinal
        exact hfinal.trans hbound
      · have hxsmall : 1 + x ≤ 10 := by
          dsimp only [x]
          have hh := (div_lt_iff₀ (by positivity : 0 < r ^ 2)).mpr (lt_of_not_ge hlarge)
          linarith
        have hp := Real.rpow_le_rpow_of_nonpos hx1 hxsmall (by norm_num : -(1 : ℝ) / 2 ≤ 0)
        have hm := mul_le_mul_of_nonneg_left hp
          (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 10) ((1 : ℝ) / 2))
        have hone : (10 : ℝ) ^ ((1 : ℝ) / 2) * 10 ^ (-(1 : ℝ) / 2) = 1 := by
          rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 10)]
          norm_num
        rw [hone] at hm
        have hmass : (kernelXV E t z {w | |w.2| ≤ 3 * r}).toReal ≤ 1 := by
          exact (ENNReal.toReal_mono ENNReal.one_ne_top
            ((measure_mono (subset_univ _)).trans (kernelXV_mass_le_one E t z))).trans_eq
              ENNReal.toReal_one
        have hsmallC : (10 : ℝ) ^ ((1 : ℝ) / 2) ≤ C := by
          dsimp only [C]
          exact le_add_of_nonneg_right (by positivity)
        exact (hmass.trans hm).trans (mul_le_mul_of_nonneg_right hsmallC hdecay)
    obtain ⟨C, hC, h⟩ := velocity_band_return_of_return_time hReturn
    refine ⟨C, hC, ?_⟩
    intro A c z t hc hz ht
    rw [activeVelocityDatum_action_eq hH hLE hlam hLam A c t ht z]
    have hsub : {w : Z | w.2 ∈ c.active} ⊆ {w | |w.2| ≤ 3 * c.r} := by
      intro w hw
      have hh := (c.active_abs_bounds hw).2
      rw [hc] at hh
      change |w.2| ≤ 3 * c.r
      linarith only [hh]
    have hmass := (measure_mono (subset_univ {w : Z | |w.2| ≤ 3 * c.r})).trans
      (kernelXV_mass_le_one (fullSpaceEvolution hH hLE hlam hLam A) (Real.toNNReal t) z)
    apply (ENNReal.toReal_mono (hmass.trans_lt ENNReal.one_lt_top).ne
      (measure_mono hsub)).trans
    simpa only [Real.coe_toNNReal t ht] using h A c.r z (Real.toNNReal t) c.positive hz
  have timeBinCount_velocity_decay_of_return_time (hReturn : ∃ C : ℝ, 0 < C ∧ ∀ (A : SmoothAutonomous lam Lam) (F : BoundedBorel Z),
      (∀ z, 0 ≤ F z) → ∀ t s X v : ℝ,
      0 < t → 2 * t ≤ s → s ≤ 3 * t → |v| ≤ Real.sqrt t →
      S hH hLE hlam hLam A t F (X, v) ≤ C * S hH hLE hlam hLam A s F (X, v)) :
      ∃ C : ℝ, 0 < C ∧ ∀ (A : SmoothAutonomous lam Lam) (c : Clock) (P : Point),
      |c.vbar| = 2 * c.r → P.velocity 0 ∈ closure c.entrance →
      ∀ (j : ℕ) (t : ℝ), (j : ℝ) * c.r ^ 2 ≤ t →
      S hH hLE hlam hLam A t (activeVelocityDatum c) (P.position 0, P.velocity 0) ≤
        C * (1 + (j : ℝ)) ^ (-1 / 2 : ℝ) := by
    obtain ⟨C, hC, h⟩ := velocity_return_action_of_return_time hReturn
    refine ⟨C, hC, ?_⟩
    intro A c P hbar hv j t ht
    have hb := (c.active_abs_bounds (enlarged_closedEntrance_subset_active c hv)).2
    rw [hbar] at hb
    have hp : |P.velocity 0| ≤ 3 * c.r := by linarith only [hb, c.positive]
    have ht0 : 0 ≤ t := (mul_nonneg (Nat.cast_nonneg j) (sq_nonneg c.r)).trans ht
    exact (h A c (P.position 0, P.velocity 0) t hbar hp ht0).trans
      (mul_le_mul_of_nonneg_left (timeBinCount_decay_le c j t ht) hC.le)
  obtain ⟨C, hC, hDecay⟩ := timeBinCount_velocity_decay_of_return_time hReturn
  let D := 2 * entranceSlabConstant Lam * C
  have hD : 0 < D := by
    dsimp only [D]
    exact mul_pos (mul_pos (by norm_num) (entranceSlabConstant_pos hlam hLam)) hC
  refine ⟨1 + D, by positivity, ?_⟩
  intro A c J T P hbar hJ hT hvel j
  let nu := visitsFromZero hH hLE hlam hLam A c J T P
  have : IsFiniteMeasure nu := enlargedVisitStarts_isFiniteMeasure
    hH hLE hlam hLam A c J (1 + T) T P (by linarith) hT
      (by nlinarith [sq_nonneg T]) hbar hJ hvel
  have hnu : ∀ᵐ p ∂nu, p.time < P.time + T :=
    (enlargedVisitStarts_ae_support hH hLE hlam hLam A c J P.time (P.time + T)
      P le_rfl (by linarith)).mono fun _ hp => hp.2.1
  have hslab (a b : ℝ) (hja : (j : ℝ) * c.r ^ 2 ≤ a) (hab : a ≤ b)
      (hbT : b ≤ T) (hlen : b - a ≤ c.r ^ 2) :
      (nu {p | p.time ∈ Ioc (P.time + a) (P.time + b)}).toReal ≤
        D * (1 + (j : ℝ)) ^ (-1 / 2 : ℝ) :=
    timeBinCount_slab_le hH hLE hlam hLam C hC hDecay A c J T P
      hbar hJ hT hvel j a b hja hab hbT hlen
  by_cases hj : j = 0
  · subst j
    have hb : 0 < min (c.r ^ 2) T := lt_min (sq_pos_of_pos c.positive) hT
    have hs := hslab 0 (min (c.r ^ 2) T) (by simp) hb.le (min_le_right _ _)
      (by linarith [min_le_left (c.r ^ 2) T])
    have hm := timeBinCount_initial_mass_le_atom_add_slab nu c P.time T hnu
    have he := timeBinCount_initial_slice hH hLE hlam hLam A c J T P hvel
    have hs' : (nu {p | p.time ∈ Ioc P.time (P.time + min (c.r ^ 2) T)}).toReal ≤ D := by
      simpa [Nat.cast_zero, Real.one_rpow] using hs
    have he' : (nu {p | p.time = P.time}).toReal = 1 := by
      exact congrArg ENNReal.toReal he
    simpa [Nat.cast_zero, Real.one_rpow] using
      hm.trans (by rw [he']; linarith only [hs'])
  · by_cases hlate : T ≤ (j : ℝ) * c.r ^ 2
    · rw [timeBinCount_mass_eq_zero_of_horizon_le hH hLE hlam hLam A c J T P hT j hj hlate]
      positivity
    · have haT : (j : ℝ) * c.r ^ 2 < T := lt_of_not_ge hlate
      let a := (j : ℝ) * c.r ^ 2
      let b := min (((j : ℝ) + 1) * c.r ^ 2) T
      have hab : a ≤ b := le_min (by
        dsimp only [a]
        nlinarith [sq_pos_of_pos c.positive]) haT.le
      have hs := hslab a b le_rfl hab (min_le_right _ _)
        (by dsimp only [a, b]; nlinarith [min_le_left (((j : ℝ) + 1) * c.r ^ 2) T])
      have hm := timeBinCount_mass_le_truncated_slab nu c P.time T j hj hnu
      exact (hm.trans hs).trans (mul_le_mul_of_nonneg_right (by linarith)
        (by positivity))

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous

