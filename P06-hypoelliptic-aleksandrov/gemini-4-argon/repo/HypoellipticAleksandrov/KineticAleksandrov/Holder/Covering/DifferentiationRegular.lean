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

/- The transported product metric is proper; this statement concerns topology only. -/
theorem volume_bounded_ne_top {d } {E : Set (KineticPoint d)}
    (hE : Bornology.IsBounded E) : volume E ≠ ⊤ := by
  let : ProperSpace (KineticPoint d) := by
      refine ⟨fun P R => ?_⟩
      have h := (isCompact_closedBall ((KineticPoint.isometryEquivProd d) P) R).image
        (KineticPoint.isometryEquivProd d).symm.continuous
      rw [(KineticPoint.isometryEquivProd d).symm.image_closedBall,
        (KineticPoint.isometryEquivProd d).symm_apply_apply] at h
      exact h

    /- Literal kinetic Lebesgue volume is locally finite. -/
  let : IsLocallyFiniteMeasure (volume : Measure (KineticPoint d)) := by
      refine ⟨fun P => ?_⟩
      refine ⟨centeredCylinder P 1,
        (isOpen_cylinder (centeredTop P 1) 1).mem_nhds (self_mem_centeredCylinder P zero_lt_one),
        ?_⟩
      exact lt_top_iff_ne_top.mpr (volume_cylinder_pos_ne_top (centeredTop P 1) zero_lt_one).2

    /- Kinetic Lebesgue volume is outer regular by its defining coordinate homeomorphism. -/
  exact hE.measure_lt_top.ne

end HypoellipticAleksandrov.KineticAleksandrov.Holder.Covering
