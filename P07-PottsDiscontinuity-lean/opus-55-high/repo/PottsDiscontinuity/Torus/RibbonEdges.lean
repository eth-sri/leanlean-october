module

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
  (v, if checker v then (if b then .west else .east)
    else (if b then .south else .north))

section
variable (hN : Even N) (hM : Even M) (v : Fin N × Fin M)
include hN hM
theorem dartOut_checker_at (p : Port) :
    dartOut (checkerArrows N M) (v, p) =
      match p with
      | .west | .east => checker v
      | .south | .north => !checker v := by
  cases p <;> simp only [dartOut, localOut, checkerArrows, ArrowConfig.left,
    ArrowConfig.right, ArrowConfig.below, ArrowConfig.above,
    checker_prv_x hN, checker_prv_y hM, Bool.not_not]

theorem ribbonEnd_out (b : Bool) :
    dartOut (checkerArrows N M) (ribbonEnd v b) = true := by
  grind [ribbonEnd, checker, dartOut_checker_at]
end

/-- Which of the two ends a slot occupies. -/
def ribbonEndSide : Port → Bool
  | .west | .south => true
  | .east | .north => false

@[simp] theorem ribbonEnd_side (v : Fin N × Fin M) (b : Bool) :
    ribbonEndSide (ribbonEnd v b).2 = b := by
  cases hc : checker v <;> cases b <;> simp [ribbonEnd, hc, ribbonEndSide]

section
variable (hN : Even N) (hM : Even M)
include hN hM
theorem ribbonEnd_recover (d : DirectedDart (checkerArrows N M)) :
    ribbonEnd d.val.1 (ribbonEndSide d.val.2) = d.val := by
  grind [dartOut_checker_at, checker, ribbonEnd, ribbonEndSide]

/-- The two-end parametrization retains the full indexed edge set. -/
def ribbonEndEquiv  :
    (Fin N × Fin M) × Bool ≃ DirectedDart (checkerArrows N M) where
  toFun x := ⟨ribbonEnd x.1 x.2, ribbonEnd_out hN hM x.1 x.2⟩
  invFun d := (d.val.1, ribbonEndSide d.val.2)
  left_inv x := by
    aesop
  right_inv d := Subtype.ext (ribbonEnd_recover hN hM d)

@[simp] theorem ribbonEndEquiv_val (v : Fin N × Fin M) (b : Bool) :
    (ribbonEndEquiv hN hM (v, b)).val = ribbonEnd v b := rfl
end

/-- The face incident to each ribbon end is the corresponding diamond endpoint. -/
theorem leftFace_ribbonEnd (v : Fin N × Fin M) (b : Bool) :
    leftFace (ribbonEnd v b) = faceEndpointRaw true v b := by
  grind [checker, ribbonEnd, leftFace, faceEndpointRaw]

/-- An open indexed ribbon exchanges its two ends; a closed ribbon fixes them. -/
theorem ribbonSwitch_ribbonEnd (A : RCConfig N M) (v : Fin N × Fin M) (b : Bool) :
    ribbonSwitch A (ribbonEnd v b) = ribbonEnd v (Bool.xor (A v) b) := by
  grind [checker, ribbonSwitch, strandReverse, rcSmoothing, ribbonEnd, pairedPort]

theorem ribbonEdgePairing_end (hN : Even N) (hM : Even M)
    (A : RCConfig N M) (v : Fin N × Fin M) (b : Bool) :
    ribbonEdgePairing hN hM A (ribbonEndEquiv hN hM (v, b)) =
      ribbonEndEquiv hN hM (v, Bool.xor (A v) b) := by
  apply Subtype.ext
  simp [ribbonSwitch_ribbonEnd]

end PottsDiscontinuity.Torus
