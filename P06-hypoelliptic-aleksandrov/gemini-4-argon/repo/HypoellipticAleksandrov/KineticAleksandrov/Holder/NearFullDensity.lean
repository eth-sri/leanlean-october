module

public import HypoellipticAleksandrov.KineticAleksandrov.Holder.NearFullCutoffAffine
public import HypoellipticAleksandrov.KineticAleksandrov.Holder.AffineGeometryTopology
import HypoellipticAleksandrov.KineticAleksandrov.Maximum.BorelSource
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.Tactic

/-! # Finite cylinder volume and the density defect in the near-full argument -/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Holder

open Set MeasureTheory

/- Every compact set in physical kinetic coordinates has finite native volume. -/
theorem kinetic_volume_compact_lt_top {d } {K : Set (KineticPoint d)}
    (hK : IsCompact K) : volume K < ⊤ := by
  let e := KineticPoint.homeomorphProd d
  have hc := hK.image e.continuous
  have heq := (KineticPoint.measurePreserving_equivProd d).measure_preimage
    hc.measurableSet.nullMeasurableSet
  have hpre : (KineticPoint.equivProd d) ⁻¹' (e '' K) = K := by
    ext P
    exact (KineticPoint.equivProd d).injective.mem_set_image
  rw [hpre] at heq
  rw [heq]
  exact hc.measure_lt_top

/- Positive-radius backward cylinders have finite native volume. -/
theorem volume_backwardCylinder_lt_top {d } (P₀ : KineticPoint d)
    {R : ℝ} (hR : 0 < R) : volume (backwardCylinder P₀ R) < ⊤ :=
  (measure_mono subset_closure).trans_lt
    (kinetic_volume_compact_lt_top (isCompact_closure_backwardCylinder P₀ R hR))

/- The density hypothesis bounds the volume of the strict sublevel set. -/
end HypoellipticAleksandrov.KineticAleksandrov.Holder
