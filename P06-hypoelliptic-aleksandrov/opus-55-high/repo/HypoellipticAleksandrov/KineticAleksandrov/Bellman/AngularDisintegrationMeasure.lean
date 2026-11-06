module

public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.AngularDisintegrationLogFactorization
public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.AngularDisintegrationRadialHaar
import Mathlib.Tactic

/-! # The actual angular measure obtained from the homogeneous Radon measure -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov
open MeasureTheory Set

/-- The normalized unit-log-radius section of the actual reweighted homogeneous measure. -/
def bellmanAngularMeasure (β : ℝ) (μ : Measure BellmanPuncturedPlane) : Measure ℝ :=
  bellmanRadialHaarFactor⁻¹ • bellmanUnitSection (bellmanLogAngularMeasure β μ)

variable (β : ℝ) (μ : Measure BellmanPuncturedPlane)

/-- The actual angular measure is finite on compact angular sets. -/
theorem bellmanAngularMeasure_finiteOnCompacts  (hμ : IsFiniteMeasureOnCompacts μ) :
    IsFiniteMeasureOnCompacts (bellmanAngularMeasure β μ) := by
  let  :=
    bellmanLogAngularMeasure_finiteOnCompacts β μ hμ
  let : IsFiniteMeasureOnCompacts (bellmanUnitSection (bellmanLogAngularMeasure β μ)) :=
    bellmanUnitSection_finiteOnCompacts _
  exact IsFiniteMeasureOnCompacts.smul _ ENNReal.coe_ne_top

/-- The actual angular measure is inner regular. -/
theorem bellmanAngularMeasure_innerRegular  (hμ : IsFiniteMeasureOnCompacts μ) :
    Measure.InnerRegular (bellmanAngularMeasure β μ) := by
  let  :=
    bellmanAngularMeasure_finiteOnCompacts β μ hμ
  infer_instance

/-- The weighted log-coordinate factorization uses the actual radial reference measure. -/
theorem bellmanLogAngularMeasure_factorization_radial  (hμ : IsFiniteMeasureOnCompacts μ)
    (hd : HasBellmanDensityDegree β μ) :
    bellmanLogAngularMeasure β μ =
      bellmanLogRadialHaar.prod (bellmanAngularMeasure β μ) := by
  let  :=
    bellmanLogAngularMeasure_finiteOnCompacts β μ hμ
  let : IsFiniteMeasureOnCompacts (bellmanUnitSection (bellmanLogAngularMeasure β μ)) :=
    bellmanUnitSection_finiteOnCompacts _
  rw [bellmanLogRadialHaar_eq_smul_volume, bellmanAngularMeasure,
    Measure.prod_smul_left, Measure.prod_smul_right, smul_smul,
    mul_inv_cancel₀ bellmanRadialHaarFactor_ne_zero, one_smul]
  exact bellmanLogAngularMeasure_factorization β μ hμ hd

/-- The actual coordinate measure after degree removal factors as ds/s times its angular
measure. -/
theorem bellmanAngularPullback_reweighted_factorization  (hμ : IsFiniteMeasureOnCompacts μ)
    (hd : HasBellmanDensityDegree β μ) :
    (bellmanAngularPullback μ).withDensity (bellmanRadialDegreeWeight β) =
      bellmanRadialHaar.prod (bellmanAngularMeasure β μ) := by
  let  :=
    bellmanAngularMeasure_finiteOnCompacts β μ hμ
  apply bellmanLogAngularHomeomorph.measurableEmbedding.map_injective
  change bellmanLogAngularMeasure β μ =
    Measure.map (Prod.map bellmanLogRadiusHomeomorph id)
      _
  rw [← Measure.map_prod_map _ _ bellmanLogRadiusHomeomorph.measurable measurable_id,
    Measure.map_id]
  exact bellmanLogAngularMeasure_factorization_radial β μ hμ hd

end HypoellipticAleksandrov.KineticAleksandrov
