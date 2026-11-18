module

public import PDEFoundation.Geometry.ConvexDomain
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import PDEFoundation.Ambient.Basic

@[expose] public noncomputable section

namespace PDE
open MeasureTheory Set

/-- The open axis box `∏ i, (a i, b i)` in the native `Vec d` ambient
space. -/
def axisBox {d : ℕ} (a b : Vec d) : Set (Vec d) :=
  Set.pi Set.univ fun i => Set.Ioo (a i) (b i)

theorem isOpen_axisBox {d : ℕ} (a b : Vec d) :
    IsOpen (axisBox a b) := by
  exact isOpen_set_pi Set.finite_univ fun _ _ => isOpen_Ioo

theorem isBoundedDomain_axisBox {d : ℕ} (a b : Vec d) :
    IsBoundedDomain (axisBox a b) := by
  exact Bornology.IsBounded.isBoundedDomain <|
    Bornology.IsBounded.pi fun _ => Metric.isBounded_Ioo _ _




/-- The sole-coordinate measurable equivalence from native `Vec 1` to
scalars. -/
def vecOneEquivReal : Vec 1 ≃ᵐ ℝ :=
  MeasurableEquiv.funUnique (Fin 1) ℝ

/-- The scalar coordinate of a native one-coordinate vector. -/
def vecOneCoordinate (x : Vec 1) : ℝ := x 0

/-- The native one-coordinate lift of a scalar. -/
def scalarToVecOne (t : ℝ) : Vec 1 := fun _ => t

/-- The native one-coordinate realization of a scalar open interval. -/
def oneDimensionalAxisBox (a b : ℝ) : Set (Vec 1) :=
  axisBox (fun _ => a) (fun _ => b)



@[simp] theorem vecOneCoordinate_scalarToVecOne (t : ℝ) :
    vecOneCoordinate (scalarToVecOne t) = t :=
  rfl


/-- The native coordinate equivalence preserves the project's volume measure
exactly. -/
theorem volumePreserving_vecOneEquivReal :
    MeasurePreserving vecOneEquivReal
      (volume : Measure (Vec 1)) (volume : Measure ℝ) := by
  simpa using!
    (volume_preserving_funUnique (Fin 1) ℝ)

/-- Membership in a native one-coordinate interval is precisely membership
of the scalar coordinate in the corresponding open interval. -/
@[simp] theorem mem_oneDimensionalAxisBox_iff {a b : ℝ} {x : Vec 1} :
    x ∈ oneDimensionalAxisBox a b ↔ vecOneCoordinate x ∈ Ioo a b := by
  constructor
  · intro hx
    exact hx 0 (Set.mem_univ 0)
  · intro hx i _
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    exact hx


end PDE

