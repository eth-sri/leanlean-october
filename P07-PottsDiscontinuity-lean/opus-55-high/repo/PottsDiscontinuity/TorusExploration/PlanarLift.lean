module

public import PottsDiscontinuity.CorrLength.RotatedLattice
public import PottsDiscontinuity.Torus.DiamondGraph

/-! Unrolling a horizontally exact cylinder into the rotated square lattice. -/

@[expose] public section

namespace PottsDiscontinuity.TorusExploration
open Torus CorrLength
variable {N M : ℕ}

/-- Integer coordinates of the lift associated with an integer seam potential. -/
def potentialLiftCoordinates (F : FaceVertex N M true → ℤ) (v : FaceVertex N M true) : ℤ × ℤ :=
  ((v.val.1.val : ℤ)+(N : ℤ)*F v,v.val.2.val)

section
variable (hN : Even N) (F : FaceVertex N M true → ℤ)
include hN
theorem potentialLiftCoordinates_even (v : FaceVertex N M true) :
    Even ((potentialLiftCoordinates F v).1+(potentialLiftCoordinates F v).2) := by
  have hv : Even (v.val.1.val+v.val.2.val) := by
    grind [checker]
  have hv' : Even ((v.val.1.val : ℤ)+(v.val.2.val : ℤ)) := by grind
  have hN' : Even (N : ℤ) := by simp_all
  convert hv'.add (hN'.mul_right (F v)) using 1; grind [potentialLiftCoordinates]

/-- An actual rotated-lattice vertex, with unchanged cylinder height. -/
def potentialLift (v : FaceVertex N M true) : RotatedVertex :=
  ⟨potentialLiftCoordinates F v,potentialLiftCoordinates_even hN F v⟩

/-- Distinct cylinder vertices remain distinct after unrolling. -/
theorem potentialLift_injective  :
    Function.Injective (potentialLift hN F) := by
  intro u v huv
  have hx := congrArg (fun w : RotatedVertex => w.val.1 % (N : ℤ)) huv
  have hy := congrArg (fun w : RotatedVertex => w.val.2) huv
  have hmod (w : FaceVertex N M true) :
      (potentialLift hN F w).val.1 % (N : ℤ) = w.val.1.val := by
    change ((w.val.1.val : ℤ)+(N : ℤ)*F w) % (N : ℤ) = _
    simp
    exact Int.emod_eq_of_lt (by omega) (by omega)
  rw [hmod,hmod] at hx
  apply Subtype.ext
  apply Prod.ext
  · omega
  · change (u.val.2.val : ℤ) = (v.val.2.val : ℤ) at hy
    omega
end

end PottsDiscontinuity.TorusExploration
