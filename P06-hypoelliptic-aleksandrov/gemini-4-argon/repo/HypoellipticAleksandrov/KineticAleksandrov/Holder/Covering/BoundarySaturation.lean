module

public import HypoellipticAleksandrov.KineticAleksandrov.Holder.Covering.BoundarySaturationDensity
public import HypoellipticAleksandrov.KineticAleksandrov.Holder.Covering.BoundarySaturationContinuity
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic
import HypoellipticAleksandrov.KineticAleksandrov.Holder.Covering.BoundarySaturationGeometry
import HypoellipticAleksandrov.KineticAleksandrov.Holder.Covering.Differentiation
import HypoellipticAleksandrov.KineticAleksandrov.Holder.Covering.NullFacesBoundary
import HypoellipticAleksandrov.KineticAleksandrov.Holder.Covering.DifferentiationDefect
import HypoellipticAleksandrov.KineticAleksandrov.Holder.Covering.DifferentiationGeometry
import HypoellipticAleksandrov.KineticAleksandrov.Holder.Covering.DifferentiationRegular
import HypoellipticAleksandrov.KineticAleksandrov.Holder.Covering.Inflation
import HypoellipticAleksandrov.KineticAleksandrov.Holder.Covering.InflationVolume
import HypoellipticAleksandrov.KineticAleksandrov.Holder.Covering.Maximal
import Mathlib.MeasureTheory.Group.Prod
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.MeasureTheory.Integral.Indicator

/-! # Critical cylinders before the prescribed radius cutoff -/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Holder.Covering

open Set MeasureTheory
open scoped Topology
open Filter

/- Intersection volume minus the near-full threshold along the admissible path. -/
def saturationGap {d } (E : Set (KineticPoint d)) (eta : ℝ)
    (X : KineticPoint d) (r : ℝ) : ℝ :=
  (volume (E ∩ backwardCylinder (saturationCenter X r) r)).toReal-
    (1-eta)*(volume (backwardCylinder (saturationCenter X r) r)).toReal

/- The threshold gap is continuous at every positive radius. -/
end HypoellipticAleksandrov.KineticAleksandrov.Holder.Covering
