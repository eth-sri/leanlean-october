module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.ExitFunctional
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.ExitMeasureRiesz

/-! # The uniquely characterized Riesz exit measure of the actual strip evolution -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov
open scoped CompactlySupported ENNReal

/-- The closed exit carrier inherits local compactness from kinetic spacetime. -/
instance stripClosedExit_locallyCompactSpace (H : Interval) (T : ℝ) :
    LocallyCompactSpace (stripClosedExit H T) := by
  let  :=
    (KineticPoint.homeomorphProd 1).isClosedEmbedding.locallyCompactSpace
  exact (isClosed_stripClosedExit H T).locallyCompactSpace

/-- The closed exit carrier has a countable topological basis. -/
instance stripClosedExit_secondCountableTopology (H : Interval) (T : ℝ) :
    SecondCountableTopology (stripClosedExit H T) := by
  let  := (KineticPoint.homeomorphProd 1).secondCountableTopology
  infer_instance

variable (hH : HormanderHypoellipticityStatement) {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam) (A : SmoothAutonomous lam Lam) (H : Interval) (E : StripEvolution H) (hE : IsStripEvolution A H E) (T : ℝ) (e : StripPole H (T : WithTop ℝ))

/-- There is exactly one subprobability measure with the full boundary-functional action. -/
theorem existsUnique_strip_exit
     :
    ∃! μ : Measure (stripClosedExit H T), μ univ ≤ 1 ∧
      ∀ f : C_c(stripClosedExit H T, ℝ), ∫ p, f p ∂μ =
        stripBoundaryFunctional hH hlam hLam A H E hE T e f :=
  existsUnique_boundaryFunctional_measure _
    (stripBoundaryFunctional_spec hH hlam hLam A H E hE T e).1

/-- The exit measure is chosen only from the proved unique full compact-test characterization. -/
def stripExitMeasureOnBoundary
     :
    Measure (stripClosedExit H T) :=
  (existsUnique_strip_exit hH hlam hLam A H E hE T e).exists.choose

/-- Full characterization of the unique exit measure on its closed boundary carrier. -/
theorem stripExitMeasureOnBoundary_spec
     :
    stripExitMeasureOnBoundary hH hlam hLam A H E hE T e univ ≤ 1 ∧
      ∀ f : C_c(stripClosedExit H T, ℝ),
        ∫ p, f p ∂stripExitMeasureOnBoundary hH hlam hLam A H E hE T e =
          stripBoundaryFunctional hH hlam hLam A H E hE T e f :=
  (existsUnique_strip_exit hH hlam hLam A H E hE T e).exists.choose_spec

/-- Each uniquely characterized exit measure is finite. -/
instance stripExitMeasureOnBoundary_isFiniteMeasure
    (hH : HormanderHypoellipticityStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (H : Interval) (E : StripEvolution H)
    (hE : IsStripEvolution A H E) (T : ℝ) (e : StripPole H (T : WithTop ℝ)) :
    IsFiniteMeasure (stripExitMeasureOnBoundary hH hlam hLam A H E hE T e) :=
  ⟨lt_of_le_of_lt (stripExitMeasureOnBoundary_spec hH hlam hLam A H E hE T e).1 (by simp)⟩

/-- The physical exit measure is the image of that unique boundary measure. -/
def stripExitOfRealization
    (hH : HormanderHypoellipticityStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (H : Interval) (E : StripEvolution H)
    (hE : IsStripEvolution A H E) (T : ℝ) (e : StripPole H (T : WithTop ℝ)) : Measure Point :=
  (stripExitMeasureOnBoundary hH hlam hLam A H E hE T e).map Subtype.val

/-- The physical exit measure is finite. -/
instance stripExitOfRealization_isFiniteMeasure
    (hH : HormanderHypoellipticityStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (H : Interval) (E : StripEvolution H)
    (hE : IsStripEvolution A H E) (T : ℝ) (e : StripPole H (T : WithTop ℝ)) :
    IsFiniteMeasure (stripExitOfRealization hH hlam hLam A H E hE T e) := by
  unfold stripExitOfRealization
  infer_instance

variable (hH : HormanderHypoellipticityStatement) {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam) (A : SmoothAutonomous lam Lam) (H : Interval) (E : StripEvolution H) (hE : IsStripEvolution A H E) (T : ℝ) (e : StripPole H (T : WithTop ℝ))

/-- The physical exit measure has mass at most one. -/
theorem stripExitOfRealization_mass_le_one
     :
    stripExitOfRealization hH hlam hLam A H E hE T e univ ≤ 1 := by
  unfold stripExitOfRealization
  rw [Measure.map_apply measurable_subtype_coe MeasurableSet.univ,
    preimage_univ]
  exact (stripExitMeasureOnBoundary_spec hH hlam hLam A H E hE T e).1

/-- The physical measure is supported on the full closed terminal/lateral exit carrier. -/
theorem stripExitOfRealization_compl_closedExit
     :
    stripExitOfRealization hH hlam hLam A H E hE T e (stripClosedExit H T)ᶜ = 0 := by
  unfold stripExitOfRealization
  rw [Measure.map_apply measurable_subtype_coe
    (isClosed_stripClosedExit H T).measurableSet.compl]
  simp_all

/-- Actual homogeneous probe values are exactly the physical exit integrals. -/
theorem stripExitOfRealization_probe_integral

    (f : exitProbeSubmodule) :
    ∫ p, exitProbePhysical f p ∂stripExitOfRealization hH hlam hLam A H E hE T e =
      exitProbeValue A H E T e f := by
  unfold stripExitOfRealization
  rw [integral_map measurable_subtype_coe.aemeasurable
    (exitProbePhysical_continuous_compact f).1.measurable.aestronglyMeasurable]
  change (∫ p, exitProbeCcLinear H T f p
    ∂stripExitMeasureOnBoundary hH hlam hLam A H E hE T e) = _
  rw [(stripExitMeasureOnBoundary_spec hH hlam hLam A H E hE T e).2,
    (stripBoundaryFunctional_spec hH hlam hLam A H E hE T e).2]
  rfl

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
