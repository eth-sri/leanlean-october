module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.FiniteUnionDomainsMixtures

@[expose] public noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov

/-- Include a smaller-union pole into the larger union at the identical physical point. -/
def finiteUnionNestedPoleInclusion (H1 H2 : FiniteIntervalUnion)
    (hsub : H1.carrier ⊆ H2.carrier) (T : WithTop ℝ)
    (e : FiniteUnionPole H1 T) : FiniteUnionPole H2 T :=
  ⟨e.1, e.2.1, hsub e.2.2⟩

/-- The pole inclusion is Borel; it does not alter time, position or velocity. -/
theorem measurable_finiteUnionNestedPoleInclusion (H1 H2 : FiniteIntervalUnion)
    (hsub : H1.carrier ⊆ H2.carrier) (T : WithTop ℝ) :
    Measurable (finiteUnionNestedPoleInclusion H1 H2 hsub T) :=
  measurable_subtype_coe.subtype_mk

/-- The internal restart measure is precisely the actual smaller exit restricted to Sigma. -/
def finiteUnionRestartMeasure
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (H1 H2 : FiniteIntervalUnion) (sMinus T : ℝ)
    (nu : Measure (FiniteUnionPole H1 (T : WithTop ℝ))) : Measure Point :=
  (finiteUnionExitMixture hH hLE hlam hLam A H1 T nu).restrict
    (finiteUnionInternalExit H1 H2 sMinus T)

/-- Internal restart measures of finite sources are finite. -/
instance finiteUnionRestartMeasure_isFiniteMeasure
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (H1 H2 : FiniteIntervalUnion) (sMinus T : ℝ)
    (nu : Measure (FiniteUnionPole H1 (T : WithTop ℝ))) [IsFiniteMeasure nu] :
    IsFiniteMeasure (finiteUnionRestartMeasure hH hLE hlam hLam A H1 H2 sMinus T nu) := by
  unfold finiteUnionRestartMeasure
  infer_instance

/-- Every restart occurs strictly after the common lower time and inside the larger velocity set. -/
theorem finiteUnionRestartMeasure_ae_valid
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (H1 H2 : FiniteIntervalUnion) (sMinus T : ℝ)
    (nu : Measure (FiniteUnionPole H1 (T : WithTop ℝ))) :
    ∀ᵐ p ∂finiteUnionRestartMeasure hH hLE hlam hLam A H1 H2 sMinus T nu,
      sMinus < p.time ∧ p.time < T ∧ p.velocity 0 ∈ H2.carrier := by
  unfold finiteUnionRestartMeasure
  filter_upwards [ae_restrict_mem
    (measurableSet_finiteUnionInternalExit H1 H2 sMinus T)] with p hp
  exact ⟨hp.1, hp.2.1, hp.2.2.2⟩


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

/-- The restart measure on valid larger-strip poles is the actual subtype pullback. -/
def finiteUnionRestartPoleMeasure
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (H1 H2 : FiniteIntervalUnion) (sMinus T : ℝ)
    (nu : Measure (FiniteUnionPole H1 (T : WithTop ℝ))) :
    Measure (FiniteUnionPole H2 (T : WithTop ℝ)) :=
  (finiteUnionRestartMeasure hH hLE hlam hLam A H1 H2 sMinus T nu).comap Subtype.val

/-- Subtype pullback preserves finiteness of the internal-exit measure. -/
instance finiteUnionRestartPoleMeasure_isFiniteMeasure
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (H1 H2 : FiniteIntervalUnion) (sMinus T : ℝ)
    (nu : Measure (FiniteUnionPole H1 (T : WithTop ℝ))) [IsFiniteMeasure nu] :
    IsFiniteMeasure (finiteUnionRestartPoleMeasure hH hLE hlam hLam A H1 H2 sMinus T nu) := by
  unfold finiteUnionRestartPoleMeasure
  infer_instance

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous

