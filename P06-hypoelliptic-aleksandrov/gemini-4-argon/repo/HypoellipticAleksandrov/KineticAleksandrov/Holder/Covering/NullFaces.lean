module

public import HypoellipticAleksandrov.KineticAleksandrov.Geometry
public import HypoellipticAleksandrov.Geometry.KineticPointMeasure
import Mathlib.MeasureTheory.Measure.Prod

/-! # Null time faces of kinetic cylinders and stacks

The proof uses the existing product Lebesgue measure in the literal coordinate order.
-/

@[expose] public section

namespace HypoellipticAleksandrov.KineticAleksandrov.Holder.Covering

open Set MeasureTheory

/-- A complete kinetic time slice has zero Lebesgue measure. -/
theorem volume_time_face {d } (t : ℝ) :
    volume {P : KineticPoint d | P.time = t} = 0 := by
  have hset : {P : KineticPoint d | P.time = t} =
      (KineticPoint.equivProd d) ⁻¹'
        ({t} ×ˢ (univ : Set (PDE.Vec d × PDE.Vec d))) := by
    ext P
    simp only [mem_ofPred_eq, mem_preimage, mem_prod, mem_singleton_iff, mem_univ,
      and_true]
    rfl
  rw [hset, (KineticPoint.measurePreserving_equivProd d).measure_preimage
    ((measurableSet_singleton t).prod MeasurableSet.univ).nullMeasurableSet]
  change (volume : Measure ℝ).prod volume ({t} ×ˢ univ) = 0
  rw [Measure.prod_prod]
  simp only [measure_singleton, zero_mul]

end HypoellipticAleksandrov.KineticAleksandrov.Holder.Covering
