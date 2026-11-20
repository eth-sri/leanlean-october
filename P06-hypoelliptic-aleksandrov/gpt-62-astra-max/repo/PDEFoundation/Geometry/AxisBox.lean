module

public import PDEFoundation.Geometry.AxisCube

/-!
# Axis-aligned boxes

This file extracts the open coordinate-box geometry already used by the
application repositories into the shared native-vector foundation. An
`axisBox a b` is the product `∏ i, (a i, b i)`. Axis cubes remain the
equal-side special case.
-/

@[expose] public section

namespace PDE

/-- The open axis box `∏ i, (a i, b i)` in the native `Vec d` ambient
space. -/
def axisBox {d : ℕ} (a b : Vec d) : Set (Vec d) :=
  Set.pi Set.univ fun i => Set.Ioo (a i) (b i)

theorem isOpen_axisBox {d : ℕ} (a b : Vec d) :
    IsOpen (axisBox a b) := by
  dsimp [axisBox]
  exact isOpen_set_pi Set.finite_univ fun _ _ => isOpen_Ioo

theorem isBoundedDomain_axisBox {d : ℕ} (a b : Vec d) :
    IsBoundedDomain (axisBox a b) := by
  dsimp [axisBox]
  exact Bornology.IsBounded.isBoundedDomain <|
    Bornology.IsBounded.pi fun _ => Metric.isBounded_Ioo _ _

end PDE
