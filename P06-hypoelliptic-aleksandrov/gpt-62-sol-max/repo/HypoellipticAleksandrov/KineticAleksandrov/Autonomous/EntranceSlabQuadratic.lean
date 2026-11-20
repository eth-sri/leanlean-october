module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.EnlargedVisitMassQuadratic

/-! # Quadratic identities for visits restricted to a time slab

The terminal family retains starts at its observation time. This endpoint is
needed for the right-closed time bins in the source entrance-slab estimate.
-/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov

section
variable {lam Lam : ℝ} (A : SmoothAutonomous lam Lam) (c : Clock) (J : Interval) (b : ℝ)

/-- A visit starting at the right endpoint contributes its actual initial quadratic value. -/
theorem entranceSlabQuadratic_terminal_at_start (p : Point)
    (ht : p.time = b) (hv : p.velocity 0 ∈ (visitActiveUnion c J).carrier) :
    (∫ q, visitQuadratic c (q.velocity 0)
      ∂enlargedActiveTerminalFamily A c J b p) =
        visitQuadratic c (p.velocity 0) := by
  unfold enlargedActiveTerminalFamily
  rw [ite_eq_left ⟨ht, hv⟩, integral_dirac]

/-- Before its right endpoint the slab identity is the actual active Green identity. -/
theorem entranceSlabQuadratic_point_identity
    (hJ : closure c.active ⊆ J.carrier) (p : Point)
    (ht : p.time < b) (hv : p.velocity 0 ∈ (visitActiveUnion c J).carrier) :
    visitQuadratic c (p.velocity 0) =
      (∫ q, visitQuadratic c (q.velocity 0)
        ∂enlargedActiveTerminalFamily A c J b p) +
      ∫ q, 2 * A.a (q.position 0) (q.velocity 0)
        ∂enlargedVisitGreenKernel A (visitActiveUnion c J) b p := by
  let E := enlargedVisitExitKernel A (visitActiveUnion c J) b
  have hz := enlargedActiveExit_ae_quadratic_zero_or_terminal A c J b hJ (Measure.dirac p)
  rw [Measure.dirac_bind E.measurable p] at hz
  have heq : (∫ q, visitQuadratic c (q.velocity 0) ∂E p) =
      ∫ q, visitQuadratic c (q.velocity 0) ∂enlargedActiveTerminalFamily A c J b p := by
    rw [enlargedActiveTerminalFamily, if_neg (fun h => ht.ne h.1), ← integral_indicator
      (isClosed_eq continuous_time continuous_const).measurableSet]
    refine integral_congr_ae ?_
    filter_upwards [hz] with q hq
    rcases hq with hq | hq <;> simp [Set.indicator, hq]
  rw [← heq]
  exact enlargedQuadratic_pole_identity A c J b ⟨ht, hv⟩

end

/-- The point identity includes visits starting exactly at the slab's right endpoint. -/
theorem entranceSlabQuadratic_closed_point_identity
    
    {lam Lam : ℝ} 
    (A : SmoothAutonomous lam Lam) (c : Clock) (J : Interval) (b : ℝ)
    (hJ : closure c.active ⊆ J.carrier) (p : Point)
    (ht : p.time ≤ b) (hv : p.velocity 0 ∈ (visitActiveUnion c J).carrier) :
    visitQuadratic c (p.velocity 0) =
      (∫ q, visitQuadratic c (q.velocity 0)
        ∂enlargedActiveTerminalFamily A c J b p) +
      ∫ q, 2 * A.a (q.position 0) (q.velocity 0)
        ∂enlargedVisitGreenKernel A (visitActiveUnion c J) b p := by
  rcases lt_or_eq_of_le ht with hlt | heq
  · exact entranceSlabQuadratic_point_identity A c J b hJ p hlt hv
  · have hn : p ∉ enlargedVisitPoleSet (visitActiveUnion c J) b := fun h => h.1.ne heq
    rw [enlargedVisitGreenKernel, visitExtendKernel_apply_notMem hn,
      integral_zero_measure, add_zero, entranceSlabQuadratic_terminal_at_start A c J b p heq hv]

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
