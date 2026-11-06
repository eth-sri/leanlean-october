module
public import Mathlib

public import PottsDiscontinuity.Torus.RibbonCornerPrimitive
public import PottsDiscontinuity.Torus.RibbonFullBoundary

/-!
# Explicit horizontal and vertical full-torus flows

The all-one indexed flow and the checker-sign indexed flow are conserved. Their
corner tables will identify intersection coordinates with lifted displacement.
-/

@[expose] public section



namespace PottsDiscontinuity.Torus

variable {N M : ℕ}

section

variable (hN : Even N) (hM : Even M) (A : RCConfig N M) (f : OpenDiamondEdge A → ℚ)
include hN hM f

theorem ribbonHalfFlow_raw  (d : DirectedDart (checkerArrows N M)) :
    ribbonHalfFlow hN hM A f d =
      if ribbonEndSide d.val.2 then -extendDiamondChain A f d.val.1
        else extendDiamondChain A f d.val.1 := rfl

theorem sum_ribbonHalfFlow_corners_eq_neg_boundary  (v : FaceVertex N M true) :
     ∑ p : Port, ribbonHalfFlow hN hM A f (ribbonCornerEquiv hN hM (v, p))  =
      -diamondBoundary hN hM A f v := by
  
  have he := sum_ribbonHalfFlow_pairing hN hM A f  fun w => if v = w then 1 else 0 
  rw [← (ribbonCornerEquiv hN hM).sum_comp, Fintype.sum_prod_type] at he
  have hx : ∀ w p,
      ribbonFace hN hM (ribbonCornerEquiv hN hM (w, p)) = w :=
    by
      solve_by_elim [_root_.Subtype.ext, _root_.PottsDiscontinuity.Torus.leftFace_faceCorner]
  simpa only [hx, ite_mul, one_mul, zero_mul, Finset.sum_ite_irrel,
    Finset.sum_const_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true] using he

theorem diamondCycleSpace_mem_iff_corners  :
    f ∈ diamondCycleSpace hN hM A ↔
      ∀ v : FaceVertex N M true,
         ∑ p : Port, ribbonHalfFlow hN hM A f (ribbonCornerEquiv hN hM (v, p))  = 0 := by
  constructor
  · intro hf v
    exact sum_ribbonHalfFlow_corners hN hM A ⟨f, hf⟩ v
  · intro h
    
    funext v
    have he := sum_ribbonHalfFlow_corners_eq_neg_boundary hN hM A f v
    rw [h v] at he
    simp only [Pi.zero_apply]
    linarith

end

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

section

variable (hN : Even N) (hM : Even M)


theorem verticalDiamondFlow_corner 
    (v : FaceVertex N M true) (p : Port) :
    ribbonHalfFlow hN hM (openRCConfig N M) (verticalDiamondFlow N M)
      (ribbonCornerEquiv hN hM (v, p)) = verticalCornerFlow p := by
  cases p <;> simp only [ribbonHalfFlow_raw]
  all_goals rfl

theorem horizontalDiamondFlow_corner 
    (v : FaceVertex N M true) (p : Port) :
    ribbonHalfFlow hN hM (openRCConfig N M) (horizontalDiamondFlow N M)
      (ribbonCornerEquiv hN hM (v, p)) = horizontalCornerFlow p := by
  rcases v with ⟨⟨i, j⟩, hv⟩
  cases p <;> simp only [ribbonHalfFlow_raw, ribbonCornerEquiv_val, faceCorner,
    ribbonEndSide, extendDiamondChain, openRCConfig, dite_true, horizontalDiamondFlow,
    checker_nxt_x hN, checker_nxt_y hM, hv, Bool.not_true, Bool.not_false,
    Bool.false_eq_true, ite_false, ite_true, horizontalCornerFlow, neg_neg]

theorem verticalDiamondFlow_mem  :
    verticalDiamondFlow N M ∈ diamondCycleSpace hN hM (openRCConfig N M) := by
  rw [diamondCycleSpace_mem_iff_corners]
  
  simp only [verticalDiamondFlow_corner, sum_port, verticalCornerFlow]
  norm_num

theorem horizontalDiamondFlow_mem  :
    horizontalDiamondFlow N M ∈ diamondCycleSpace hN hM (openRCConfig N M) := by
  rw [diamondCycleSpace_mem_iff_corners]
  
  simp only [horizontalDiamondFlow_corner, sum_port, horizontalCornerFlow]
  norm_num

end

def verticalDiamondCycle (hN : Even N) (hM : Even M) :
    diamondCycleSpace hN hM (openRCConfig N M) :=
  ⟨verticalDiamondFlow N M, verticalDiamondFlow_mem hN hM⟩

def horizontalDiamondCycle (hN : Even N) (hM : Even M) :
    diamondCycleSpace hN hM (openRCConfig N M) :=
  ⟨horizontalDiamondFlow N M, horizontalDiamondFlow_mem hN hM⟩

end PottsDiscontinuity.Torus
