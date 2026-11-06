module

public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.AngularDisintegrationReweight
public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.AngularDisintegrationFactorization
import Mathlib.Tactic
import HypoellipticAleksandrov.KineticAleksandrov.Bellman.AngularCoordinates
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.Topology.Maps.Basic

/-! # Factorization of the actual homogeneous measure after degree reweighting -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov
open MeasureTheory Set
open Topology

/- The actual reweighted log-coordinate measure remains finite on compact sets. -/
theorem bellmanLogAngularMeasure_finiteOnCompacts (β : ℝ)
    (μ ) (hμ : IsFiniteMeasureOnCompacts μ) :
    IsFiniteMeasureOnCompacts (bellmanLogAngularMeasure β μ) := by
  let : IsFiniteMeasureOnCompacts (bellmanAngularPullback μ) := by
    let : IsFiniteMeasureOnCompacts μ := hμ
    exact IsFiniteMeasureOnCompacts.comap' μ continuous_bellmanAngularPoint
      isOpenEmbedding_bellmanAngularPoint.measurableEmbedding
  have hw : Continuous (fun w : BellmanPositiveTime × ℝ => w.1.val ^ (β - 4)) := by
    apply Continuous.rpow_const
    · fun_prop
    · intro w
      exact Or.inl w.1.property.ne'
  let : IsFiniteMeasureOnCompacts
      ((bellmanAngularPullback μ).withDensity (bellmanRadialDegreeWeight β)) :=
    bellman_withDensity_finiteOnCompacts (bellmanAngularPullback μ) _ hw
  exact bellman_map_homeomorph_finiteOnCompacts bellmanLogAngularHomeomorph _

/- Homogeneity alone produces a literal angular measure after passing to log radius. -/
end HypoellipticAleksandrov.KineticAleksandrov
