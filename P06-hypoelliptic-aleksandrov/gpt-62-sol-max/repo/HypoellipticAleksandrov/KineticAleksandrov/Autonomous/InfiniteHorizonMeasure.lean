module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.InfiniteHorizonFunctional
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.ExitMeasureRiesz

/-! # Unique infinite-horizon Riesz exit measure with its full compact-test characterization -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov
open SectionTwo TheoremA Evolution
open scoped CompactlySupported

section
variable {lam Lam : ℝ} (A : SmoothAutonomous lam Lam) (H : Interval) (e : StripPole H ⊤)
include lam Lam A e

/-- There is exactly one subprobability measure with the full boundary-functional action. -/
theorem existsUnique_infinite_exit :
    ∃! μ : Measure (stripInfiniteFace H), μ univ ≤ 1 ∧
      ∀ f : C_c(stripInfiniteFace H, ℝ), ∫ p, f p ∂μ =
        infiniteBoundaryFunctional A H e f :=
  existsUnique_boundaryFunctional_measure (infiniteBoundaryFunctional A H e)
    (infiniteBoundaryFunctional_spec A H e).1

/-- The exit measure is chosen only from the proved unique full compact-test characterization. -/
def infiniteExitMeasureOnFace :
    Measure (stripInfiniteFace H) :=
  (existsUnique_infinite_exit A H e).exists.choose

/-- Full characterization of the unique exit measure on its closed boundary carrier. -/
theorem infiniteExitMeasureOnFace_spec :
    infiniteExitMeasureOnFace A H e univ ≤ 1 ∧
      ∀ f : C_c(stripInfiniteFace H, ℝ),
        ∫ p, f p ∂infiniteExitMeasureOnFace A H e =
          infiniteBoundaryFunctional A H e f :=
  (existsUnique_infinite_exit A H e).exists.choose_spec

end

/-- Each uniquely characterized exit measure is finite. -/
instance infiniteExitMeasureOnFace_isFiniteMeasure
    
    {lam Lam : ℝ} 
    (A : SmoothAutonomous lam Lam) (H : Interval) (e : StripPole H ⊤) :
    IsFiniteMeasure (infiniteExitMeasureOnFace A H e) :=
  ⟨lt_of_le_of_lt (infiniteExitMeasureOnFace_spec A H e).1 (by simp)⟩

/-- The physical exit measure is the image of that unique boundary measure. -/
def stripInfiniteExit
    
    {lam Lam : ℝ} 
    (A : SmoothAutonomous lam Lam) (H : Interval) (e : StripPole H ⊤) : Measure Point :=
  (infiniteExitMeasureOnFace A H e).map Subtype.val

/-- The physical exit measure is finite. -/
instance stripInfiniteExit_isFiniteMeasure
    
    {lam Lam : ℝ} 
    (A : SmoothAutonomous lam Lam) (H : Interval) (e : StripPole H ⊤) :
    IsFiniteMeasure (stripInfiniteExit A H e) := by
  unfold stripInfiniteExit
  infer_instance

section
variable {lam Lam : ℝ} (A : SmoothAutonomous lam Lam) (H : Interval) (e : StripPole H ⊤)

/-- The physical exit measure has mass at most one. -/
theorem stripInfiniteExit_mass_le_one :
    stripInfiniteExit A H e univ ≤ 1 := by
  unfold stripInfiniteExit
  rw [Measure.map_apply measurable_subtype_coe MeasurableSet.univ,
    preimage_univ]
  exact (infiniteExitMeasureOnFace_spec A H e).1

/-- Actual homogeneous probe values are exactly the physical exit integrals. -/
theorem stripInfiniteExit_probe_integral
    (f : exitProbeSubmodule) :
    ∫ p, exitProbePhysical f p ∂stripInfiniteExit A H e =
      infiniteExitProbeValue A H e f := by
  unfold stripInfiniteExit
  rw [integral_map measurable_subtype_coe.aemeasurable
    (exitProbePhysical_continuous_compact f).1.measurable.aestronglyMeasurable]
  change (∫ p, infiniteExitProbeCcLinear H f p
    ∂infiniteExitMeasureOnFace A H e) = _
  rw [(infiniteExitMeasureOnFace_spec A H e).2,
    (infiniteBoundaryFunctional_spec A H e).2]
  rfl

end

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
