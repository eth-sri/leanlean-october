module

public import HypoellipticAleksandrov.KineticAleksandrov.Holder.Covering.DifferentiationGeometry
public import HypoellipticAleksandrov.KineticAleksandrov.Holder.Covering.InflationVolume
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.MeasureTheory.Group.Prod
import Mathlib.Topology.MetricSpace.ProperSpace

/-! # Regularity and finite-volume neighborhoods for kinetic Lebesgue measure -/

@[expose] public section

namespace HypoellipticAleksandrov.KineticAleksandrov.Holder.Covering

open Set MeasureTheory

variable (d : ℕ)

/-- The transported product metric is proper; this statement concerns topology only. -/
theorem properSpace_kineticPoint  : ProperSpace (KineticPoint d) := by
  refine ⟨fun P R => ?_⟩
  have h := (isCompact_closedBall ((KineticPoint.isometryEquivProd d) P) R).image
    (KineticPoint.isometryEquivProd d).symm.continuous
  simp_all

/-- Literal kinetic Lebesgue volume is locally finite. -/
theorem locallyFinite_kinetic_volume  :
    IsLocallyFiniteMeasure (volume : Measure (KineticPoint d)) := by
  refine ⟨fun P => ?_⟩
  refine ⟨centeredCylinder P 1,
    (isOpen_cylinder _ 1).mem_nhds (self_mem_centeredCylinder P zero_lt_one),
    ?_⟩
  exact lt_top_iff_ne_top.mpr (volume_cylinder_pos_ne_top _ zero_lt_one).2

/-- Kinetic Lebesgue volume is outer regular by its defining coordinate homeomorphism. -/
theorem outerRegular_kinetic_volume  :
    Measure.OuterRegular (volume : Measure (KineticPoint d)) := by
  change Measure.OuterRegular
    (Measure.map (KineticPoint.homeomorphProd d).symm
      volume)
  let : Measure.Regular (volume : Measure (ℝ × (PDE.Vec d × PDE.Vec d))) :=
    Measure.Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure volume
  exact Measure.OuterRegular.map _ volume

/-- Every bounded kinetic set has finite volume. -/
theorem volume_bounded_ne_top {d : ℕ} {E : Set (KineticPoint d)}
    (hE : Bornology.IsBounded E) : volume E ≠ ⊤ := by
  let  := properSpace_kineticPoint d
  let  :=
    locallyFinite_kinetic_volume d
  exact hE.measure_lt_top.ne

end HypoellipticAleksandrov.KineticAleksandrov.Holder.Covering
