module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.StripGreenCharacterization

/-! # Physical-time marginals of the killed strip Green measure

The constant is exactly one and the statement covers every measurable time set and both
finite and infinite horizons. No source-time lower endpoint enters the construction.
-/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov
open HypoellipticAleksandrov.KineticAleksandrov.SectionTwo
open scoped ENNReal

variable {lam Lam : ℝ} (R : ℝ≥0∞) (hlam : 0 < lam) (s : ℝ) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (H : Interval)
    (K : MovingFiberKernel (intervalDomain H) (fun _ => 0)) (T : WithTop ℝ) (e : StripPole H T)
    (J : Set ℝ) (hJ : MeasurableSet J)
include hJ

/-- Restricting elapsed times can only decrease the Lebesgue mass of an absolute-time set. -/
theorem elapsedVolume_absoluteTime_le :
    elapsedVolume R {τ | s + τ.1 ∈ J} ≤ volume J := by
  rw [elapsedVolume_apply R _
    (show MeasurableSet {τ : ElapsedTime R | s + τ.1 ∈ J} from (measurable_const.add measurable_subtype_coe) hJ)]
  calc
    _ ≤ volume ((fun t : ℝ => s + t) ⁻¹' J) := by
      apply measure_mono
      grind
    _ = volume J := by
      simp

/-- The literal killed kernel has physical-time marginal at most Lebesgue measure. -/
theorem stripGreenOfKernel_timeMarginal :
    stripGreenOfKernel H K T e {p | p.time ∈ J} ≤ volume J := by
  rw [stripGreenOfKernel, Measure.map_apply (measurable_elapsedPhysicalPoint _ _)
    (show MeasurableSet {p : Point | p.time ∈ J} from
      hJ.preimage continuous_time.measurable)]
  calc
    _ ≤ (Measure.dirac (stripPoleState H T e)) univ *
        elapsedVolume (stripHorizon T e.1.time) {τ | e.1.time + τ.1 ∈ J} :=
      greenMeasure_timeMarginal_le K e.1.time _ _ _
        (greenMeasure_spec K _ _ _ _) _ ((measurable_const.add measurable_subtype_coe) hJ)
    _ = elapsedVolume (stripHorizon T e.1.time) {τ | e.1.time + τ.1 ∈ J} := by
      simp
    _ ≤ volume J := elapsedVolume_absoluteTime_le _ _ J hJ

/-- The canonical autonomous strip Green measure has the exact constant-one time bound. -/
theorem stripGreen_timeMarginal :
    stripGreen hlam hLam A H T e {p | p.time ∈ J} ≤ volume J :=
  stripGreenOfKernel_timeMarginal H _ T e J hJ

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
