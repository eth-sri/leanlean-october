module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.NestedStripRestart

/-! # The internal-exit measure on the existing larger-strip pole carrier -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov

/-- The finite-horizon pole predicate is Borel in physical coordinates. -/
theorem measurableSet_finiteUnionPole (H : FiniteIntervalUnion) (T : ℝ) :
    MeasurableSet {p : Point | (p.time : WithTop ℝ) < T ∧ p.velocity 0 ∈ H.carrier} := by
  have ht : {p : Point | (p.time : WithTop ℝ) < T} = {p | p.time < T} := by
    ext p
    exact WithTop.coe_lt_coe
  rw [show {p : Point | (p.time : WithTop ℝ) < T ∧ p.velocity 0 ∈ H.carrier} =
    {p | (p.time : WithTop ℝ) < T} ∩ {p | p.velocity 0 ∈ H.carrier} from rfl, ht]
  exact (measurableSet_lt continuous_time.measurable measurable_const).inter
    (H.isOpen_carrier.measurableSet.preimage
      ((continuous_apply 0).comp continuous_velocity).measurable)
section
variable (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement) {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam) (A : SmoothAutonomous lam Lam) (H1 H2 : FiniteIntervalUnion) (sMinus T : ℝ) (nu : Measure (FiniteUnionPole H1 (T : WithTop ℝ)))

/-- The restart measure on valid larger-strip poles is the actual subtype pullback. -/
def finiteUnionRestartPoleMeasure
     :
    Measure (FiniteUnionPole H2 (T : WithTop ℝ)) :=
  (finiteUnionRestartMeasure hH hLE hlam hLam A H1 H2 sMinus T nu).comap Subtype.val

/-- Subtype pullback preserves finiteness of the internal-exit measure. -/
instance finiteUnionRestartPoleMeasure_isFiniteMeasure
     [IsFiniteMeasure nu] :
    IsFiniteMeasure (finiteUnionRestartPoleMeasure hH hLE hlam hLam A H1 H2 sMinus T nu) := by
  unfold finiteUnionRestartPoleMeasure
  infer_instance
end

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
