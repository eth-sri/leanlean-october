module

public import HypoellipticAleksandrov.Geometry.KineticPoint
public import Mathlib.MeasureTheory.Measure.Map
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Dynamics.Ergodic.MeasurePreserving
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Measure.Prod

/-!
# Lebesgue measure on kinetic points

The coordinate equivalence identifies kinetic volume with product Lebesgue
measure in the literal order (t,x,v), without any normalization factor.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov

open MeasureTheory

/-- Borel measurable sets for the coordinate product topology on kinetic points. -/
@[expose] instance KineticPoint.instMeasurableSpace (d : ℕ) :
    MeasurableSpace (KineticPoint d) := borel (KineticPoint d)

/-- The measurable structure on kinetic points is the Borel structure. -/
@[expose] instance KineticPoint.instBorelSpace (d : ℕ) : BorelSpace (KineticPoint d) :=
  ⟨rfl⟩

/-- Product Lebesgue measure transported to kinetic points in the order (t,x,v). -/
@[expose] instance KineticPoint.instMeasureSpace (d : ℕ) : MeasureSpace (KineticPoint d) where
  volume := Measure.map (KineticPoint.equivProd d).symm
    (volume : Measure (ℝ × (PDE.Vec d × PDE.Vec d)))

variable (d : ℕ)

/-- The kinetic coordinate equivalence is Borel measurable. -/
theorem KineticPoint.measurable_equivProd  :
    Measurable (KineticPoint.equivProd d) :=
  (KineticPoint.homeomorphProd d).continuous.measurable

/-- The inverse coordinate equivalence is Borel measurable. -/
theorem KineticPoint.measurable_equivProd_symm  :
    Measurable (KineticPoint.equivProd d).symm :=
  (KineticPoint.homeomorphProd d).symm.continuous.measurable

/-- Kinetic volume is exactly product Lebesgue volume in coordinate space. -/
theorem KineticPoint.measurePreserving_equivProd  :
    MeasurePreserving (KineticPoint.equivProd d) volume volume := by
  refine ⟨KineticPoint.measurable_equivProd d, ?_⟩
  change Measure.map (KineticPoint.equivProd d)
    (Measure.map _ volume) = volume
  rw [Measure.map_map (KineticPoint.measurable_equivProd d)
    (KineticPoint.measurable_equivProd_symm d)]
  simp

end HypoellipticAleksandrov
