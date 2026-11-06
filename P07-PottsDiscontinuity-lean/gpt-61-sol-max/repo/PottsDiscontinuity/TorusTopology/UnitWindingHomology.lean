module
public import Mathlib

public import PottsDiscontinuity.TorusTopology.UnitWindingStructure
public import Mathlib.LinearAlgebra.Dimension.FreeAndStrongRankCondition

/-! The complete homological form of U=1: the two essential loops have opposite
classes (a,1) and (-a,-1), with no restriction on the integer a. -/

@[expose] public section


namespace PottsDiscontinuity.TorusTopology
open Torus TorusLoops

variable {N M : ℕ}

section

variable (hN : Even N) (hM : Even M)
include hN hM

/-- The displacement vectors of any two smoothed torus loops are collinear. -/
theorem loop_displacement_determinant_zero 
    (hNp : 0 < N) (hMp : 0 < M) (A : RCConfig N M)
    (q r : Loop hN hM (rcSmoothing A)) :
    loopDisplacementX hN hM A q * loopDisplacementY hN hM A r -
      loopDisplacementX hN hM A r * loopDisplacementY hN hM A q = 0 := by
  
  
  obtain ⟨v,hv⟩ := (finrank_le_one_iff (K := ℚ)).mp
    (finrank_loopIncidenceCycleSpace_le_one hN hM hNp hMp A)
  obtain ⟨a,ha⟩ := hv  ⟨loopDisplacementX hN hM A,loopDisplacementX_mem_incidenceCycleSpace hN hM A⟩ 
  obtain ⟨b,hb⟩ := hv  ⟨loopDisplacementY hN hM A,loopDisplacementY_mem_incidenceCycleSpace hN hM A⟩ 
  have hX (t) : loopDisplacementX hN hM A t = a * v.val t :=
    (congrFun (congrArg Subtype.val ha) t).symm
  have hY (t) : loopDisplacementY hN hM A t = b * v.val t :=
    (congrFun (congrArg Subtype.val hb) t).symm
  rw [hX,hX,hY,hY]
  ring

section

variable (i : Fin N) (j : Fin M) (A : RCConfig N M)
include i j A

/-- Exact integer parallelism, for both signed seam coordinates. -/
theorem loop_winding_determinant_zero 
    
    (q r : Loop hN hM (rcSmoothing A)) :
    loopSum (checkerArrows N M) (rcSmoothing A)
      (checkerArrows_compatible hN hM _) (horizontalCross i) q *
      loopVertical (checkerArrows N M) (rcSmoothing A)
        (checkerArrows_compatible hN hM _) j r -
    loopSum (checkerArrows N M) (rcSmoothing A)
      (checkerArrows_compatible hN hM _) (horizontalCross i) r *
      loopVertical (checkerArrows N M) (rcSmoothing A)
        (checkerArrows_compatible hN hM _) j q = 0 := by
  have he := loop_displacement_determinant_zero hN hM (Fin.pos i) (Fin.pos j) A q r
  have hX (t) : loopDisplacementX hN hM A t =  N  *
       loopSum (checkerArrows N M) (rcSmoothing A)
        (checkerArrows_compatible hN hM _) (horizontalCross i) t  := by
    unfold loopDisplacementX
    rw [loop_horizontal_displacement _ _ _ i]
    push_cast
    rfl
  have hY (t) : loopDisplacementY hN hM A t =  M  *
       loopVertical (checkerArrows N M) (rcSmoothing A)
        (checkerArrows_compatible hN hM _) j t  := by
    unfold loopDisplacementY
    rw [loop_vertical_displacement _ _ _ j]
    push_cast
    rfl
  rw [hX,hX,hY,hY] at he
  
  
  have hc : ∀ a b c d ,  N*a *(M*b)- N*c *(M*d) =
      (N : ℚ)*M*(a*b-c*d) := by intros; ring
  rw [hc] at he
  
  exact_mod_cast  (mul_eq_zero.mp he).resolve_left (mul_ne_zero (by exact_mod_cast (Fin.pos i).ne') (by exact_mod_cast (Fin.pos j).ne')) 

/-- U=1 permits an arbitrary common integer horizontal slope. This is the
strongest homological replacement for the erroneous horizontal-zero clause. -/
theorem U_one_horizontal_multiple_vertical
     
    (hU : rcVerticalWinding hN hM j A = 1) :
    ∃ a : ℤ, ∀ q : Loop hN hM (rcSmoothing A),
      loopSum (checkerArrows N M) (rcSmoothing A)
        (checkerArrows_compatible hN hM _) (horizontalCross i) q =
      a * loopVertical (checkerArrows N M) (rcSmoothing A)
        (checkerArrows_compatible hN hM _) j q := by
  obtain ⟨q,r,_,_,hq,_⟩ := U_one_vertical_loop_structure hN hM j A hU
  refine ⟨loopSum _ _ (checkerArrows_compatible hN hM _) (horizontalCross i) q,?_⟩
  intro t
  have he := loop_winding_determinant_zero hN hM i j A t q
  grind

end

end

end PottsDiscontinuity.TorusTopology
