module

public import PottsDiscontinuity.TorusTopology.UnitWindingStructure
public import Mathlib.LinearAlgebra.Dimension.FreeAndStrongRankCondition

/-! The complete homological form of U=1: the two essential loops have opposite
classes (a,1) and (-a,-1), with no restriction on the integer a. -/

@[expose] public section

open PottsDiscontinuity.SixVertex
namespace PottsDiscontinuity.TorusTopology
open Torus TorusLoops
open scoped Classical
variable {N M : ℕ}

variable (hN : Even N) (hM : Even M) (i : Fin N) (j : Fin M) (hNp : 0 < N) (hMp : 0 < M)
    (A : RCConfig N M) (q r : Loop hN hM (rcSmoothing A))

include hNp hMp in
/-- The displacement vectors of any two smoothed torus loops are collinear. -/
theorem loop_displacement_determinant_zero :
    loopDisplacementX q * loopDisplacementY r -
      loopDisplacementX r * loopDisplacementY q = 0 := by
  let X : LinearMap.ker (loopIncidenceBoundary hN hM A) :=
    ⟨loopDisplacementX (hN := hN) (hM := hM) (A := A),loopDisplacementX_mem_incidenceCycleSpace hN hM A⟩
  let Y : LinearMap.ker (loopIncidenceBoundary hN hM A) :=
    ⟨loopDisplacementY (hN := hN) (hM := hM) (A := A),loopDisplacementY_mem_incidenceCycleSpace hN hM A⟩
  obtain ⟨v,hv⟩ := (finrank_le_one_iff (K := ℚ)).mp
    (finrank_loopIncidenceCycleSpace_le_one hN hM hNp hMp A)
  obtain ⟨a,ha⟩ := hv X
  obtain ⟨b,hb⟩ := hv Y
  have hX (t) : loopDisplacementX t = a * v.val t :=
    (congrFun (congrArg Subtype.val ha) t).symm
  have hY (t) : loopDisplacementY t = b * v.val t :=
    (congrFun (congrArg Subtype.val hb) t).symm
  rw [hX,hX,hY,hY]
  ring

/-- Exact integer parallelism, for both signed seam coordinates. -/
theorem loop_winding_determinant_zero :
    loopSum (horizontalCross i) q *
      loopVertical (ω := (checkerArrows N M)) (s := (rcSmoothing A))
        (h := (checkerArrows_compatible hN hM _)) j r -
    loopSum (ω := (checkerArrows N M)) (s := (rcSmoothing A))
      (h := (checkerArrows_compatible hN hM _)) (horizontalCross i) r *
      loopVertical (ω := (checkerArrows N M)) (s := (rcSmoothing A))
        (h := (checkerArrows_compatible hN hM _)) j q = 0 := by
  have he := loop_displacement_determinant_zero hN hM (Fin.pos i) (Fin.pos j) A q r
  have hX (t) : loopDisplacementX (hN := hN) (hM := hM) (A := A) t = (N : ℚ) *
      (loopSum (ω := (checkerArrows N M)) (s := (rcSmoothing A))
        (h := (checkerArrows_compatible hN hM _)) (horizontalCross i) t : ℚ) := by
    unfold loopDisplacementX
    rw [loop_horizontal_displacement (ω := _) (s := _) _ i]
    push_cast
    rfl
  have hY (t) : loopDisplacementY (hN := hN) (hM := hM) (A := A) t = (M : ℚ) *
      (loopVertical (ω := (checkerArrows N M)) (s := (rcSmoothing A))
        (h := (checkerArrows_compatible hN hM _)) j t : ℚ) := by
    unfold loopDisplacementY
    rw [loop_vertical_displacement (ω := _) (s := _) _ j]
    push_cast
    rfl
  rw [hX,hX,hY,hY] at he
  have hN0 : (N : ℚ) ≠ 0 := by exact_mod_cast (Fin.pos i).ne'
  have hM0 : (M : ℚ) ≠ 0 := by exact_mod_cast (Fin.pos j).ne'
  have hc : ∀ a b c d : ℚ, (N*a)*(M*b)-(N*c)*(M*d) =
      (N : ℚ)*M*(a*b-c*d) := by intros; ring
  rw [hc] at he
  have hz := (mul_eq_zero.mp he).resolve_left (mul_ne_zero hN0 hM0)
  exact_mod_cast hz

/-- U=1 permits an arbitrary common integer horizontal slope. This is the
strongest homological replacement for the erroneous horizontal-zero clause. -/
theorem U_one_horizontal_multiple_vertical
    (hU : rcVerticalWinding hN hM j A = 1) :
    ∃ a : ℤ, ∀ q : Loop hN hM (rcSmoothing A),
      loopSum (horizontalCross i) q =
      a * loopVertical j q := by
  obtain ⟨q,r,_,_,hq,_⟩ := U_one_vertical_loop_structure hN hM j A hU
  refine ⟨loopSum (horizontalCross i) q,?_⟩
  intro t
  have he := loop_winding_determinant_zero hN hM i j A t q
  grind

end PottsDiscontinuity.TorusTopology
