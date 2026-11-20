module

public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Topology.MetricSpace.Isometry

/-! # The coordinate model shared by the public statements and the estimates -/

@[expose] public section
noncomputable section
open MeasureTheory
namespace KineticAleksandrovChallenge

/-- The native coordinate model of `ℝᵈ`. -/
abbrev Vec (d : ℕ) := Fin d → ℝ

/-! ## Kinetic points -/

/-- A point of kinetic spacetime. -/
structure KineticPoint (d : ℕ) where
  /-- Time coordinate. -/
  time : ℝ
  /-- Position coordinate. -/
  position : Vec d
  /-- Velocity coordinate. -/
  velocity : Vec d

/-- The coordinate equivalence with `ℝ × (ℝᵈ × ℝᵈ)`. -/
def KineticPoint.equivProd (d : ℕ) : KineticPoint d ≃ ℝ × (Vec d × Vec d) where
  toFun z := (z.time, (z.position, z.velocity))
  invFun z := ⟨z.1, z.2.1, z.2.2⟩
  left_inv z := by cases z; rfl
  right_inv z := by rcases z with ⟨t, x, v⟩; rfl

/-- The product metric transported along the coordinate equivalence; it supplies the product
topology only, never the kinetic or Euclidean geometry. -/
instance (d : ℕ) : MetricSpace (KineticPoint d) :=
  MetricSpace.induced (KineticPoint.equivProd d) (KineticPoint.equivProd d).injective
    inferInstance

/-- Borel sets for the product topology. -/
instance KineticPoint.instMeasurableSpace (d : ℕ) : MeasurableSpace (KineticPoint d) :=
  borel (KineticPoint d)

/-- Lebesgue measure: the product measure in the order `(t, x, v)`, transported. -/
instance KineticPoint.instMeasureSpace (d : ℕ) : MeasureSpace (KineticPoint d) where
  volume := Measure.map (KineticPoint.equivProd d).symm
    (volume : Measure (ℝ × (Vec d × Vec d)))

end KineticAleksandrovChallenge
