module

public import Mathlib.Analysis.SpecialFunctions.Complex.CircleMap
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-! Standard sets, measure and parameter for disk and Fourier calculations. The
interval measure here is ordinary Lebesgue measure, not normalized Haar measure. -/

public section

namespace PolyaNeumann

scoped notation "unitDisk" => Metric.ball (0 : ℂ) 1
scoped notation "closedDisk" => Metric.closedBall (0 : ℂ) 1
scoped notation "diskSphere" => Metric.sphere (0 : ℂ) 1
scoped notation "unitCirclePt" => circleMap 0 1
scoped notation "anglePeriod" => (2 * Real.pi)
scoped notation "angleInterval" => Set.Icc (0 : ℝ) anglePeriod
scoped notation "angleIco" => Set.Ico (0 : ℝ) anglePeriod
scoped notation "angleIoc" => Set.Ioc (0 : ℝ) anglePeriod
scoped notation "angleInterior" => Set.Ioo (0 : ℝ) anglePeriod
scoped notation "angleMeasure" => MeasureTheory.volume.restrict angleIoc
scoped notation "ParamCircle" => AddCircle anglePeriod

public instance anglePeriodPos : Fact (0 < anglePeriod) := ⟨Real.two_pi_pos⟩

end PolyaNeumann
