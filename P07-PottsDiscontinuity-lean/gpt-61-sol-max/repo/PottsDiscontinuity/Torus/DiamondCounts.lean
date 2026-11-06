module
public import Mathlib

public import PottsDiscontinuity.Torus.DiamondGraph

/-!
# Sizes of the actual diamond-torus vertex and indexed edge carriers
-/

@[expose] public section

open PottsDiscontinuity.SixVertex

namespace PottsDiscontinuity.Torus

variable {N M : ℕ}

/-- One horizontal translation exchanges the two face colours. -/
def faceFlipEquiv (hN : Even N) (c : Bool) : FaceVertex N M c ≃ FaceVertex N M  !c  where
  toFun v := ⟨(nxt v.val.1, v.val.2), by rw [checker_nxt_x hN, v.property]⟩
  invFun v := ⟨(prv v.val.1, v.val.2), by rw [checker_prv_x hN, v.property, Bool.not_not]⟩
  left_inv v := by
    grind
  right_inv v := by
    grind

/-- Each of the primal and dual graphs has exactly NM/2 face vertices. -/
theorem card_faceVertex (hN : Even N) (c : Bool) :
    Fintype.card (FaceVertex N M c) = N * M / 2 := by
  
  have heq : Fintype.card (FaceVertex N M true) = Fintype.card (FaceVertex N M false) :=
    Fintype.card_congr (faceFlipEquiv hN true)
  have hc : Fintype.card (FaceVertex N M false) =
      N * M - Fintype.card (FaceVertex N M true) := by
    
    simpa only [Bool.not_eq_true, Fintype.card_prod, Fintype.card_fin] using  Fintype.card_subtype_compl  fun v  => checker v = true  
  
  
  cases c
  · omega
  · exact  by omega 

end PottsDiscontinuity.Torus
