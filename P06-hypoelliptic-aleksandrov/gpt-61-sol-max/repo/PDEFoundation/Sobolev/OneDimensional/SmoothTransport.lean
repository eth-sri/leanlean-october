module

public import PDEFoundation.Ambient.Basis
public import PDEFoundation.Measure.OneDimensionalCoordinate

/-!
# Smooth transport between `Vec 1` and scalars

The smooth-test-function bridge for one-dimensional weak derivatives is an
exact change of variables on the native carrier.  It uses the continuous
linear `piUnique` equivalence, while measure transport remains in
`OneDimensionalCoordinate`.
-/

@[expose] public section

namespace PDE



noncomputable section

/-- The continuous linear scalar-to-native-one-coordinate equivalence. -/
def scalarToVecOneContinuousLinearEquiv : ℝ ≃L[ℝ] Vec 1 :=
  (ContinuousLinearEquiv.piUnique ℝ (fun _ : Fin 1 => ℝ)).symm

@[simp] theorem scalarToVecOneContinuousLinearEquiv_apply (t : ℝ) :
    scalarToVecOneContinuousLinearEquiv t = scalarToVecOne t := by
  rfl

@[simp] theorem scalarToVecOneContinuousLinearEquiv_one :
    scalarToVecOneContinuousLinearEquiv (1 ) = basisVec (0 : Fin 1) := by
  rw [scalarToVecOneContinuousLinearEquiv_apply]
  funext i
  have hi : i = 0 := Subsingleton.elim _ _
  subst i
  rfl

variable (φ : Vec 1 → ℝ)





end

end PDE
