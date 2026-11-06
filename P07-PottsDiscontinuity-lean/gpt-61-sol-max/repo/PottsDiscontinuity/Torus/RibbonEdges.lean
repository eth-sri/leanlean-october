module
public import Mathlib

public import PottsDiscontinuity.Torus.RibbonBoundary

/-!
# Indexed ribbon ends and diamond endpoints

Each medial midpoint carries two canonical outgoing slots. These are the two
ends of its primal ribbon, even when the period identifies their face labels.
-/

@[expose] public section

open PottsDiscontinuity.SixVertex

namespace PottsDiscontinuity.Torus

variable {N M : ℕ}

/-- The two primal ribbon ends at an indexed diamond edge. -/
def ribbonEnd (v : Fin N × Fin M) (b : Bool) : Dart N M :=
  (v, if checker v then  if b then .west else .east 
    else  if b then .south else .north )

section

variable (hN : Even N) (hM : Even M) (v : Fin N × Fin M)
include hN hM

theorem dartOut_checker_at  (p : Port) :
    dartOut (checkerArrows N M) (v, p) =
      match p with
      | .west | .east => checker v
      | .south | .north => !checker v := by
  
  cases p <;> simp only [dartOut, localOut, checkerArrows, ArrowConfig.left,
    ArrowConfig.right, ArrowConfig.below, ArrowConfig.above,
    checker_prv_x hN, checker_prv_y hM, Bool.not_not]

theorem ribbonEnd_out  (b : Bool) :
    dartOut (checkerArrows N M) (ribbonEnd v b) = true := by
  grind [ribbonEnd, dartOut_checker_at]

end

/-- Which of the two ends a slot occupies. -/
def ribbonEndSide : Port → Bool
  | .west | .south => true
  | .east | .north => false

@[simp] theorem ribbonEnd_side (v : Fin N × Fin M) (b : Bool) :
    ribbonEndSide (ribbonEnd v b).2 = b := by
  grind +locals

theorem ribbonEnd_recover (hN : Even N) (hM : Even M)
    (d : DirectedDart (checkerArrows N M)) :
    ribbonEnd d.val.1 (ribbonEndSide d.val.2) = d.val := by
  grind [ribbonEnd, ribbonEndSide, dartOut_checker_at]

/-- The two-end parametrization retains the full indexed edge set. -/
def ribbonEndEquiv (hN : Even N) (hM : Even M) :
    (Fin N × Fin M) × Bool ≃ DirectedDart (checkerArrows N M) where
  toFun x := ⟨ribbonEnd x.1 x.2, ribbonEnd_out hN hM x.1 x.2⟩
  invFun d := (d.val.1, ribbonEndSide d.val.2)
  left_inv x := by
    aesop
  right_inv d := Subtype.ext (ribbonEnd_recover hN hM d)



@[simp] theorem ribbonEndEquiv_val (hN : Even N) (hM : Even M)
    (v : Fin N × Fin M) (b : Bool) :
    (ribbonEndEquiv hN hM (v, b)).val = ribbonEnd v b := rfl

/-- The face incident to each ribbon end is the corresponding diamond endpoint. -/
theorem leftFace_ribbonEnd (v : Fin N × Fin M) (b : Bool) :
    leftFace (ribbonEnd v b) = faceEndpointRaw true v b := by
  grind [ribbonEnd, leftFace, faceEndpointRaw]

/-- An open indexed ribbon exchanges its two ends; a closed ribbon fixes them. -/
theorem ribbonSwitch_ribbonEnd (A : RCConfig N M) (v : Fin N × Fin M) (b : Bool) :
    ribbonSwitch A (ribbonEnd v b) = ribbonEnd v (Bool.xor (A v) b) := by
  grind [ribbonSwitch, strandReverse, rcSmoothing, ribbonEnd, pairedPort]

theorem ribbonEdgePairing_end (hN : Even N) (hM : Even M)
    (A : RCConfig N M) (v : Fin N × Fin M) (b : Bool) :
    ribbonEdgePairing hN hM A (ribbonEndEquiv hN hM (v, b)) =
      ribbonEndEquiv hN hM (v, Bool.xor (A v) b) := Subtype.ext (ribbonSwitch_ribbonEnd A v b)

end PottsDiscontinuity.Torus
