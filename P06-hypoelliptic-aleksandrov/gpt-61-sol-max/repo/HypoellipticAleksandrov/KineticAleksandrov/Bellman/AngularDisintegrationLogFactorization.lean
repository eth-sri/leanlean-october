module

public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.AngularDisintegrationReweight
public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.AngularDisintegrationFactorization
import Mathlib.Tactic

/-! # Factorization of the actual homogeneous measure after degree reweighting -/

 public section

namespace HypoellipticAleksandrov.KineticAleksandrov
open MeasureTheory

variable (β : ℝ) (μ : Measure BellmanPuncturedPlane)

/-- The actual reweighted log-coordinate measure remains finite on compact sets. -/
theorem bellmanLogAngularMeasure_finiteOnCompacts  (hμ : IsFiniteMeasureOnCompacts μ) :
    IsFiniteMeasureOnCompacts (bellmanLogAngularMeasure β μ) := by
  let  :=
    bellmanAngularPullback_finiteOnCompacts μ hμ

  let : IsFiniteMeasureOnCompacts
      ((bellmanAngularPullback μ).withDensity (bellmanRadialDegreeWeight β)) :=
    bellman_withDensity_finiteOnCompacts _ _ (by
        apply Continuous.rpow_const
        · fun_prop
        · intro w
          exact Or.inl w.1.property.ne')
  exact bellman_map_homeomorph_finiteOnCompacts bellmanLogAngularHomeomorph _

/-- Homogeneity alone produces a literal angular measure after passing to log radius. -/
theorem bellmanLogAngularMeasure_factorization  (hμ : IsFiniteMeasureOnCompacts μ)
    (hd : HasBellmanDensityDegree β μ) :
    bellmanLogAngularMeasure β μ =
      (volume : Measure ℝ).prod (bellmanUnitSection (bellmanLogAngularMeasure β μ)) := by
  let  :=
    bellmanLogAngularMeasure_finiteOnCompacts β μ hμ
  exact bellman_translation_factorization _ hd.logAngularMeasure_invariant

end HypoellipticAleksandrov.KineticAleksandrov
