module
public import Mathlib

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

lemma potentialLiftCoordinates_even (hN : Even N)
    (F : FaceVertex N M true → ℤ) (v : FaceVertex N M true) :
    Even ((potentialLiftCoordinates F v).1+(potentialLiftCoordinates F v).2) := by
  
  have hv' : Even ( v.val.1.val +(v.val.2.val : ℤ)) := by exact_mod_cast  by
                                                                                grind [checker] 
  have hN' : Even (N : ℤ) := by exact_mod_cast hN
  convert hv'.add (hN'.mul_right (F v)) using 1; dsimp [potentialLiftCoordinates]; ring

/-- An actual rotated-lattice vertex, with unchanged cylinder height. -/
def potentialLift (hN : Even N) (F : FaceVertex N M true → ℤ)
    (v : FaceVertex N M true) : RotatedVertex :=
  ⟨potentialLiftCoordinates F v,potentialLiftCoordinates_even hN F v⟩

/-- Distinct cylinder vertices remain distinct after unrolling. -/
theorem potentialLift_injective (hN : Even N) (F : FaceVertex N M true → ℤ) :
    Function.Injective (potentialLift hN F) := by
  intro u v huv
  have hx := congrArg (fun w  => w.val.1 % (N : ℤ)) huv
  
  have hmod (w : FaceVertex N M true) :
      (potentialLift hN F w).val.1 %  N  = w.val.1.val := by
    change ( w.val.1.val + N *F w) %  N  = _
    rw [Int.add_emod,Int.mul_emod]
    simp only [Int.emod_self,zero_mul,Int.zero_emod,add_zero,Int.emod_emod]
    exact Int.emod_eq_of_lt (by omega) (by exact_mod_cast w.val.1.isLt)
  rw [hmod,hmod] at hx
  apply Subtype.ext
  apply Prod.ext
  · apply Fin.ext
    exact_mod_cast hx
  · grind +locals

end PottsDiscontinuity.TorusExploration
