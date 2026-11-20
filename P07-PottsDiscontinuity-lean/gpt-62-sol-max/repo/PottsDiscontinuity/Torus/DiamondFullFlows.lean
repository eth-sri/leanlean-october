module

public import PottsDiscontinuity.Torus.RibbonHalfFlow
public import PottsDiscontinuity.Torus.RibbonFullBoundary

/-!
# Explicit horizontal and vertical full-torus flows

The all-one indexed flow and the checker-sign indexed flow are conserved. Their
corner tables normalize the two displacement coordinates.
-/

@[expose] public section

open Finset PottsDiscontinuity.SixVertex

namespace PottsDiscontinuity.Torus

variable {N M : ℕ}

theorem sum_port (t : Port → ℚ) :
    ∑ p : Port, t p = t .west + t .east + t .south + t .north := by
  have hu : (univ : Finset Port) = {.west, .east, .south, .north} := by decide
  rw [hu]
  simp [add_assoc]

/-- The fully open edge subtype is explicitly the full indexed edge carrier. -/
def fullDiamondEdgeEquiv (N M : ℕ) : OpenDiamondEdge (openRCConfig N M) ≃ Fin N × Fin M where
  toFun e := e.val
  invFun v := ⟨v, rfl⟩
  left_inv _ := rfl
  right_inv _ := rfl



theorem ribbonHalfFlow_raw (hN : Even N) (hM : Even M) (A : RCConfig N M)
    (f : OpenDiamondEdge A → ℚ) (d : DirectedDart (checkerArrows N M)) :
    ribbonHalfFlow hN hM A f d =
      if ribbonEndSide d.val.2 then -extendDiamondChain A f d.val.1
        else extendDiamondChain A f d.val.1 := rfl

theorem diamondCycleSpace_mem_iff_corners (hN : Even N) (hM : Even M)
    (A : RCConfig N M) (f : OpenDiamondEdge A → ℚ) :
    f ∈ diamondCycleSpace hN hM A ↔
      ∀ v : FaceVertex N M true,
        (∑ p : Port, ribbonHalfFlow hN hM A f (ribbonCornerEquiv hN hM (v, p))) = 0 := by
  simp only [sum_ribbonHalfFlow_corners_eq_neg_boundary, neg_eq_zero]
  change diamondBoundary hN hM A f = 0 ↔ _
  exact funext_iff

/-- The indexed flow pointing downward on every oriented primal edge. -/
def verticalDiamondFlow (N M : ℕ) : OpenDiamondEdge (openRCConfig N M) → ℚ := fun _ => 1

/-- The checker-sign indexed flow, with pure horizontal total displacement. -/
def horizontalDiamondFlow (N M : ℕ) : OpenDiamondEdge (openRCConfig N M) → ℚ :=
  fun e => if checker e.val then 1 else -1

def verticalCornerFlow : Port → ℚ
  | .west | .south => -1
  | .east | .north => 1

def horizontalCornerFlow : Port → ℚ
  | .west | .north => -1
  | .east | .south => 1

theorem verticalDiamondFlow_corner (hN : Even N) (hM : Even M)
    (v : FaceVertex N M true) (p : Port) :
    ribbonHalfFlow hN hM (openRCConfig N M) (verticalDiamondFlow N M)
      (ribbonCornerEquiv hN hM (v, p)) = verticalCornerFlow p := by
  cases p <;> simp only [ribbonHalfFlow_raw, ribbonCornerEquiv_val, faceCorner,
    ribbonEndSide, extendDiamondChain, openRCConfig, verticalDiamondFlow,
    Bool.false_eq_true, ite_false, ite_true, verticalCornerFlow]
  all_goals rfl

theorem horizontalDiamondFlow_corner (hN : Even N) (hM : Even M)
    (v : FaceVertex N M true) (p : Port) :
    ribbonHalfFlow hN hM (openRCConfig N M) (horizontalDiamondFlow N M)
      (ribbonCornerEquiv hN hM (v, p)) = horizontalCornerFlow p := by
  rcases v with ⟨⟨i, j⟩, hv⟩
  cases p <;> simp only [ribbonHalfFlow_raw, ribbonCornerEquiv_val, faceCorner,
    ribbonEndSide, extendDiamondChain, openRCConfig, dite_true, horizontalDiamondFlow,
    checker_nxt_x hN, checker_nxt_y hM, hv, Bool.not_true, Bool.not_false,
    Bool.false_eq_true, ite_false, ite_true, horizontalCornerFlow, neg_neg]

theorem verticalDiamondFlow_mem (hN : Even N) (hM : Even M) :
    verticalDiamondFlow N M ∈ diamondCycleSpace hN hM (openRCConfig N M) := by
  rw [diamondCycleSpace_mem_iff_corners]
  intro v
  simp only [verticalDiamondFlow_corner, sum_port, verticalCornerFlow]
  norm_num

theorem horizontalDiamondFlow_mem (hN : Even N) (hM : Even M) :
    horizontalDiamondFlow N M ∈ diamondCycleSpace hN hM (openRCConfig N M) := by
  rw [diamondCycleSpace_mem_iff_corners]
  intro v
  simp only [horizontalDiamondFlow_corner, sum_port, horizontalCornerFlow]
  norm_num

def verticalDiamondCycle (hN : Even N) (hM : Even M) :
    diamondCycleSpace hN hM (openRCConfig N M) :=
  ⟨verticalDiamondFlow N M, verticalDiamondFlow_mem hN hM⟩

def horizontalDiamondCycle (hN : Even N) (hM : Even M) :
    diamondCycleSpace hN hM (openRCConfig N M) :=
  ⟨horizontalDiamondFlow N M, horizontalDiamondFlow_mem hN hM⟩

end PottsDiscontinuity.Torus
