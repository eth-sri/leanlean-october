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

section
variable (hN : Even N) (hM : Even M) (v : Fin N × Fin M) (b : Bool)
include v

include b in
/-- The two primal ribbon ends at an indexed diamond edge. -/
def ribbonEnd : Dart N M :=
  (v, if checker v then (if b then .west else .east)
    else (if b then .south else .north))

include hN hM in
theorem dartOut_checker_at (p : Port) :
    dartOut (checkerArrows N M) (v, p) =
      match p with
      | .west | .east => checker v
      | .south | .north => !checker v := by
  rcases v with ⟨i, j⟩
  cases p <;> simp only [dartOut, localOut, checkerArrows, ArrowConfig.left,
    ArrowConfig.right, ArrowConfig.below, ArrowConfig.above,
    checker_prv_x hN, checker_prv_y hM, Bool.not_not]

include hN hM in
theorem ribbonEnd_out :
    dartOut (checkerArrows N M) (ribbonEnd v b) = true := by
  unfold ribbonEnd
  cases hc : checker v <;> cases b <;>
    simp only [hc, Bool.false_eq_true, ite_false, ite_true, dartOut_checker_at hN hM,
      Bool.not_false]

end

/-- Which of the two ends a slot occupies. -/
def ribbonEndSide : Port → Bool
  | .west | .south => true
  | .east | .north => false

variable (hN : Even N) (hM : Even M) (A : RCConfig N M) (v : Fin N × Fin M) (b : Bool)

@[simp] theorem ribbonEnd_side :
    ribbonEndSide (ribbonEnd v b).2 = b := by
  cases hc : checker v <;> cases b <;> simp [ribbonEnd, hc, ribbonEndSide]

include hN hM in
theorem ribbonEnd_recover
    (d : DirectedDart (checkerArrows N M)) :
    ribbonEnd d.val.1 (ribbonEndSide d.val.2) = d.val := by
  rcases d with ⟨⟨v, p⟩, hd⟩
  rw [dartOut_checker_at hN hM] at hd
  cases p <;> cases hc : checker v <;>
    simp_all only [Bool.not_true, Bool.not_false, Bool.false_eq_true, ribbonEnd,
      ribbonEndSide, ite_false, ite_true]

include hN hM in
/-- The two-end parametrization retains the full indexed edge set. -/
def ribbonEndEquiv :
    (Fin N × Fin M) × Bool ≃ DirectedDart (checkerArrows N M) where
  toFun x := ⟨ribbonEnd x.1 x.2, ribbonEnd_out hN hM x.1 x.2⟩
  invFun d := (d.val.1, ribbonEndSide d.val.2)
  left_inv x := by
    apply Prod.ext
    · rfl
    · exact ribbonEnd_side x.1 x.2
  right_inv d := Subtype.ext (ribbonEnd_recover hN hM d)

@[simp] theorem ribbonEndEquiv_val :
    (ribbonEndEquiv hN hM (v, b)).val = ribbonEnd v b := rfl

/-- The face incident to each ribbon end is the corresponding diamond endpoint. -/
theorem leftFace_ribbonEnd :
    leftFace (ribbonEnd v b) = faceEndpointRaw true v b := by
  cases hc : checker v <;> cases b <;>
    simp only [ribbonEnd, hc, Bool.false_eq_true, ite_false, ite_true,
      leftFace, faceEndpointRaw]

/-- An open indexed ribbon exchanges its two ends; a closed ribbon fixes them. -/
theorem ribbonSwitch_ribbonEnd :
    ribbonSwitch A (ribbonEnd v b) = ribbonEnd v (Bool.xor (A v) b) := by
  cases hc : checker v <;> cases ha : A v <;> cases b <;>
    simp only [ribbonSwitch, strandReverse, rcSmoothing, ribbonEnd, hc, ha,
      Bool.false_eq_true, ite_false, ite_true, Bool.xor_false, Bool.xor_true,
      Bool.not_false, Bool.not_true, pairedPort]

theorem ribbonEdgePairing_end :
    ribbonEdgePairing hN hM A (ribbonEndEquiv hN hM (v, b)) =
      ribbonEndEquiv hN hM (v, Bool.xor (A v) b) := by
  apply Subtype.ext
  exact ribbonSwitch_ribbonEnd A v b

end PottsDiscontinuity.Torus
