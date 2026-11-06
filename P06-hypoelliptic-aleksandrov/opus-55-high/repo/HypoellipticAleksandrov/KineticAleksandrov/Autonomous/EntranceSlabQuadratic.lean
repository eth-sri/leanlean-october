module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.EnlargedVisitMassQuadratic

/-! # Quadratic identities for visits restricted to a time slab

The terminal family retains starts at its observation time. This endpoint is
needed for the right-closed time bins in the source entrance-slab estimate.
-/

@[expose] public section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov

variable (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement) {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam) (A : SmoothAutonomous lam Lam) (c : Clock) (mu : Measure Point)

/-- Entrance-supported finite measures have an integrable source quadratic. -/
theorem entranceSlabQuadratic_integrable 
    [IsFiniteMeasure mu] (hmu : ∀ᵐ p ∂mu, p.velocity 0 ∈ closure c.entrance) :
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

/-- The lower quadratic bound survives restriction to any measurable time slab. -/
theorem entranceSlabQuadratic_mass_lower 
    [IsFiniteMeasure mu] (hmu : ∀ᵐ p ∂mu, p.velocity 0 ∈ closure c.entrance) :
    5 * c.r ^ 2 / 16 * (mu univ).toReal ≤
      ∫ p, visitQuadratic c (p.velocity 0) ∂mu := by
  have h := integral_mono_ae (integrable_const _)
    (entranceSlabQuadratic_integrable c mu hmu)
    (hmu.mono fun _ hp => visitQuadratic_entrance_lower c hp)
  simpa only [integral_const, smul_eq_mul, Measure.real, mul_comm] using h

/-- A visit starting at the right endpoint contributes its actual initial quadratic value. -/
theorem entranceSlabQuadratic_terminal_at_start
     (J : Interval) (b : ℝ) (p : Point)
    (ht : p.time = b) (hv : p.velocity 0 ∈ (visitActiveUnion c J).carrier) :
    (∫ q, visitQuadratic c (q.velocity 0)
      ∂enlargedActiveTerminalFamily hH hLE hlam hLam A c J b p) =
        visitQuadratic c (p.velocity 0) := by
  unfold enlargedActiveTerminalFamily
  simp_all

/-- Before its right endpoint the slab identity is the actual active Green identity. -/
theorem entranceSlabQuadratic_point_identity
     (J : Interval) (b : ℝ)
    (hJ : closure c.active ⊆ J.carrier) (p : Point)
    (ht : p.time < b) (hv : p.velocity 0 ∈ (visitActiveUnion c J).carrier) :
    visitQuadratic c (p.velocity 0) =
      (∫ q, visitQuadratic c (q.velocity 0)
        ∂enlargedActiveTerminalFamily hH hLE hlam hLam A c J b p) +
      ∫ q, 2 * A.a (q.position 0) (q.velocity 0)
        ∂enlargedVisitGreenKernel hH hLE hlam hLam A (visitActiveUnion c J) b p := by
  classical
  have hp : p ∈ enlargedVisitPoleSet _ b := ⟨ht, hv⟩
  let ep := enlargedVisitPole _ b ⟨p, hp⟩
  have hi := visitQuadratic_active_identity hH hLE hlam hLam A c J b ep
  have he : enlargedVisitExitKernel hH hLE hlam hLam A (visitActiveUnion c J) b p =
      finiteUnionExit hH hLE hlam hLam A _ b ep := by
    change (if h : p ∈ enlargedVisitPoleSet _ b then
      finiteUnionExit hH hLE hlam hLam A _ b
        _ else 0) = _
    grind
  have hg : enlargedVisitGreenKernel hH hLE hlam hLam A (visitActiveUnion c J) b p =
      finiteUnionGreen hH hLE hlam hLam A _ b ep := by
    change (if h : p ∈ enlargedVisitPoleSet _ b then
      finiteUnionGreen hH hLE hlam hLam A _ b
        _ else 0) = _
    grind
  let E := enlargedVisitExitKernel hH hLE hlam hLam A (visitActiveUnion c J) b
  have hz := enlargedActiveExit_ae_quadratic_zero_or_terminal
    hH hLE hlam hLam A c J b hJ (Measure.dirac p)
  rw [Measure.dirac_bind E.measurable] at hz
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
    · simp_all
    · by_cases hqb : q.time = b
      · simp_all
      simp_all
  rw [← he, ← hg, heq] at hi
  have hn : (fun q : Point => -2 * A.a (q.position 0) (q.velocity 0)) =
      -(fun q => 2 * A.a (q.position 0) (q.velocity 0)) := by
    aesop
  rw [hn, integral_neg', sub_neg_eq_add] at hi
  exact hi

/-- The point identity includes visits starting exactly at the slab's right endpoint. -/
theorem entranceSlabQuadratic_closed_point_identity
     (J : Interval) (b : ℝ)
    (hJ : closure c.active ⊆ J.carrier) (p : Point)
    (ht : p.time ≤ b) (hv : p.velocity 0 ∈ (visitActiveUnion c J).carrier) :
    visitQuadratic c (p.velocity 0) =
      (∫ q, visitQuadratic c (q.velocity 0)
        ∂enlargedActiveTerminalFamily hH hLE hlam hLam A c J b p) +
      ∫ q, 2 * A.a (q.position 0) (q.velocity 0)
        ∂enlargedVisitGreenKernel hH hLE hlam hLam A (visitActiveUnion c J) b p := by
  classical
  rcases lt_or_eq_of_le ht with hlt | heq
  · exact entranceSlabQuadratic_point_identity hH hLE hlam hLam A c J b hJ p hlt hv
  · have hg : enlargedVisitGreenKernel hH hLE hlam hLam A (visitActiveUnion c J) b p =
        0 := dite_eq_right (fun h => (ne_of_lt h.1) heq)
    rw [hg, integral_zero_measure, add_zero,
      entranceSlabQuadratic_terminal_at_start hH hLE hlam hLam A c J b p heq hv]

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
