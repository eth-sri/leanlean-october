module

public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import PDEFoundation.Ambient.Basic
public import PDEFoundation.Geometry.AxisBox

/-!
# Native one-coordinate transport

This module identifies the project's native `Vec 1` carrier with scalar
Lebesgue measure.  The identification is the measurable equivalence supplied
by Mathlib for functions from a unique index type, so it preserves volume
exactly rather than merely up to an unspecified normalization.
-/

@[expose] public section

namespace PDE

open MeasureTheory Set

noncomputable section

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

variable (t : ℝ) (x : Vec 1)

@[simp] theorem vecOneEquivReal_apply  :
    vecOneEquivReal x = vecOneCoordinate x := by
  aesop

@[simp] theorem vecOneEquivReal_symm_apply  :
    vecOneEquivReal.symm t = scalarToVecOne t := by
  aesop

@[simp] theorem vecOneCoordinate_scalarToVecOne  :
    vecOneCoordinate (scalarToVecOne t) = t :=
  rfl

@[simp] theorem scalarToVecOne_vecOneCoordinate  :
    scalarToVecOne (vecOneCoordinate x) = x := by
  funext i
  have hi : i = 0 := Subsingleton.elim _ _
  aesop

/-- The native coordinate equivalence preserves the project's volume measure
exactly. -/
theorem volumePreserving_vecOneEquivReal :
    MeasurePreserving vecOneEquivReal
      (volume : Measure (Vec 1)) (volume : Measure ℝ) := by
  simpa only [vecOneEquivReal] using!
    (volume_preserving_funUnique _ ℝ)

/-- Membership in a native one-coordinate interval is precisely membership
of the scalar coordinate in the corresponding open interval. -/
@[simp] theorem mem_oneDimensionalAxisBox_iff {a b : ℝ} {x : Vec 1} :
    x ∈ oneDimensionalAxisBox a b ↔ vecOneCoordinate x ∈ Ioo a b := by
  constructor
  · intro hx
    exact hx 0 (Set.mem_univ 0)
  · intro hx i _
    have hi : i = 0 := Subsingleton.elim _ _
    aesop

end

end PDE
