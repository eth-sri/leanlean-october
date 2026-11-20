module

public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.AngularDisintegrationReweight
public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.AngularDisintegrationFactorization
import Mathlib.Tactic

/-! # Factorization of the actual homogeneous measure after degree reweighting -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov
open MeasureTheory Set

variable (β : ℝ) (μ : Measure BellmanPuncturedPlane) (hμ : IsFiniteMeasureOnCompacts μ)
include hμ

/-- The actual reweighted log-coordinate measure remains finite on compact sets. -/
theorem bellmanLogAngularMeasure_finiteOnCompacts :
    IsFiniteMeasureOnCompacts (bellmanLogAngularMeasure β μ) := by
  let :=
    bellmanAngularPullback_finiteOnCompacts μ hμ
  have hw : Continuous (fun w : BellmanPositiveTime × ℝ => w.1.val ^ (β - 4)) := by
    apply Continuous.rpow_const
    · fun_prop
    · grind
  let : IsFiniteMeasureOnCompacts
      ((bellmanAngularPullback μ).withDensity (bellmanRadialDegreeWeight β)) :=
    bellman_withDensity_finiteOnCompacts (bellmanAngularPullback μ) _ hw
  apply bellman_map_homeomorph_finiteOnCompacts

/-- Homogeneity alone produces a literal angular measure after passing to log radius. -/
theorem bellmanLogAngularMeasure_factorization
    (hd : HasBellmanDensityDegree β μ) :
    bellmanLogAngularMeasure β μ =
      (volume : Measure ℝ).prod (bellmanUnitSection (bellmanLogAngularMeasure β μ)) := by
  let :=
    bellmanLogAngularMeasure_finiteOnCompacts β μ hμ
  exact bellman_translation_factorization _ hd.logAngularMeasure_invariant

end HypoellipticAleksandrov.KineticAleksandrov
