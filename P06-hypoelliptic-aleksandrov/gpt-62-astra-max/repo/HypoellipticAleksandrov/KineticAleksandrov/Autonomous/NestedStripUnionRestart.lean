module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.NestedStripRestartPoles
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.NestedStripKernelIntegral

/-! # Measurable point restart poles and exact source disintegration -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov

/-- The actual internal exit of a single union pole, on the larger union pole carrier. -/
def finiteUnionPointRestartPoles
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (H1 H2 : FiniteIntervalUnion) (sMinus T : ℝ)
    (e : FiniteUnionPole H1 (T : WithTop ℝ)) : Measure (FiniteUnionPole H2 (T : WithTop ℝ)) :=
  ((finiteUnionExit hlam hLam A H1 T e).restrict
    (finiteUnionInternalExit H1 H2 sMinus T)).comap Subtype.val

/-- Single-pole internal exits are finite. -/
instance finiteUnionPointRestartPoles_isFiniteMeasure
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (H1 H2 : FiniteIntervalUnion) (sMinus T : ℝ)
    (e : FiniteUnionPole H1 (T : WithTop ℝ)) :
    IsFiniteMeasure (finiteUnionPointRestartPoles hlam hLam A H1 H2 sMinus T e) := by
  unfold finiteUnionPointRestartPoles
  infer_instance

variable {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam) (A : SmoothAutonomous lam Lam)
    (H1 H2 : FiniteIntervalUnion) (sMinus T : ℝ)

/-- The actual point restart family is Borel, by restriction and subtype pullback. -/
theorem finiteUnionPointRestartPoles_measurable :
    Measurable (finiteUnionPointRestartPoles hlam hLam A H1 H2 sMinus T) := nested_measurable_family_comap _
    (nested_measurable_family_restrict _ (finiteUnionExit_measurable hlam hLam A H1 T)
      _ (measurableSet_finiteUnionInternalExit H1 H2 sMinus T)) _
        (measurableSet_finiteUnionPole H2 T)

/-- The finite-source restart is exactly the actual measurable integral of point restarts. -/
theorem finiteUnionRestartPoleMeasure_disintegration
    (nu : Measure (FiniteUnionPole H1 (T : WithTop ℝ))) :
    finiteUnionRestartPoleMeasure hlam hLam A H1 H2 sMinus T nu =
      nu.bind (finiteUnionPointRestartPoles hlam hLam A H1 H2 sMinus T) := by
  unfold finiteUnionRestartPoleMeasure finiteUnionRestartMeasure finiteUnionExitMixture
  have hr := nested_bind_restrict nu (finiteUnionExit hlam hLam A H1 T)
    (finiteUnionExit_measurable hlam hLam A H1 T)
    (finiteUnionInternalExit H1 H2 sMinus T)
    (measurableSet_finiteUnionInternalExit H1 H2 sMinus T)
  exact (congrArg (fun μ : Measure Point => μ.comap (Subtype.val : FiniteUnionPole H2 (T : WithTop ℝ) → Point)) hr).trans (nested_comap_bind nu _
    (nested_measurable_family_restrict _ (finiteUnionExit_measurable hlam hLam A H1 T)
      _ (measurableSet_finiteUnionInternalExit H1 H2 sMinus T)) _
        (measurableSet_finiteUnionPole H2 T))

/-- Returning point restart poles to physical coordinates recovers the literal restricted exit. -/
theorem finiteUnionPointRestartPoles_map
    (e : FiniteUnionPole H1 (T : WithTop ℝ)) :
    (finiteUnionPointRestartPoles hlam hLam A H1 H2 sMinus T e).map Subtype.val =
      (finiteUnionExit hlam hLam A H1 T e).restrict
        (finiteUnionInternalExit H1 H2 sMinus T) := by
  unfold finiteUnionPointRestartPoles
  refine (map_comap_subtype_coe (measurableSet_finiteUnionPole H2 T) _).trans ?_
  apply Measure.restrict_eq_self_of_ae_mem
  filter_upwards [ae_restrict_mem
    (measurableSet_finiteUnionInternalExit H1 H2 sMinus T)] with p hp
  exact ⟨WithTop.coe_lt_coe.mpr hp.2.1, hp.2.2.2⟩

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
