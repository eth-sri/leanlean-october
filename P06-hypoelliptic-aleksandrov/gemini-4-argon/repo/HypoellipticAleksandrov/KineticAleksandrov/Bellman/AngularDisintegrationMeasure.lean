module

public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.AngularDisintegrationLogFactorization
public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.AngularDisintegrationRadialHaar
import Mathlib.Tactic
import HypoellipticAleksandrov.KineticAleksandrov.Bellman.AngularCoordinates
import HypoellipticAleksandrov.KineticAleksandrov.Bellman.AngularDisintegrationFactorization
import HypoellipticAleksandrov.KineticAleksandrov.Bellman.AngularDisintegrationReweight
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.Topology.Maps.Basic

/-! # The actual angular measure obtained from the homogeneous Radon measure -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov
open MeasureTheory Set
open Topology

/- The normalized unit-log-radius section of the actual reweighted homogeneous measure. -/
def bellmanAngularMeasure (β : ℝ) (μ : Measure BellmanPuncturedPlane) : Measure ℝ :=
  bellmanRadialHaarFactor⁻¹ • bellmanUnitSection (bellmanLogAngularMeasure β μ)

/- The actual angular measure is finite on compact angular sets. -/
theorem bellmanAngularMeasure_finiteOnCompacts (β : ℝ)
    (μ ) (hμ : IsFiniteMeasureOnCompacts μ) :
    IsFiniteMeasureOnCompacts (bellmanAngularMeasure β μ) := by
  let : IsFiniteMeasureOnCompacts (bellmanLogAngularMeasure β μ) :=
    bellmanLogAngularMeasure_finiteOnCompacts β μ hμ
  let : IsFiniteMeasureOnCompacts (bellmanUnitSection (bellmanLogAngularMeasure β μ)) :=
    bellmanUnitSection_finiteOnCompacts _
  unfold bellmanAngularMeasure
  exact IsFiniteMeasureOnCompacts.smul _ ENNReal.coe_ne_top

/- The actual angular measure is inner regular. -/
theorem bellmanAngularMeasure_innerRegular (β : ℝ)
    (μ ) (hμ : IsFiniteMeasureOnCompacts μ) :
    Measure.InnerRegular (bellmanAngularMeasure β μ) := by
  let : IsFiniteMeasureOnCompacts (bellmanAngularMeasure β μ) :=
    bellmanAngularMeasure_finiteOnCompacts β μ hμ
  infer_instance

/- The weighted log-coordinate factorization uses the actual radial reference measure. -/
theorem bellmanLogAngularMeasure_factorization_radial (β : ℝ)
    (μ ) (hμ : IsFiniteMeasureOnCompacts μ)
    (hd : HasBellmanDensityDegree β μ) :
    bellmanLogAngularMeasure β μ =
      bellmanLogRadialHaar.prod (bellmanAngularMeasure β μ) := by
  let : IsFiniteMeasureOnCompacts (bellmanLogAngularMeasure β μ) :=
    bellmanLogAngularMeasure_finiteOnCompacts β μ hμ
  let : IsFiniteMeasureOnCompacts (bellmanUnitSection (bellmanLogAngularMeasure β μ)) :=
    bellmanUnitSection_finiteOnCompacts _
  rw [bellmanLogRadialHaar_eq_smul_volume, bellmanAngularMeasure,
    Measure.prod_smul_left, Measure.prod_smul_right, smul_smul,
    mul_inv_cancel₀ bellmanRadialHaarFactor_ne_zero, one_smul]
  let : IsFiniteMeasureOnCompacts (bellmanLogAngularMeasure β μ) :=
    bellmanLogAngularMeasure_finiteOnCompacts β μ hμ
  exact bellman_translation_factorization _ hd.logAngularMeasure_invariant

/- The actual coordinate measure after degree removal factors as ds/s times its angular
measure. -/
end HypoellipticAleksandrov.KineticAleksandrov
