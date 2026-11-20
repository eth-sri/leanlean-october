module

public import PottsDiscontinuity.Torus.RibbonChainComplex

/-!
# Conserved flows on ribbon ends

Extend an open-edge chain by zero on the closed indexed edges and assign opposite
outward flows to its two ends. Vertex conservation becomes a zero sum at the four
corners of each primal face.
-/

@[expose] public section

open Finset PottsDiscontinuity.SixVertex

namespace PottsDiscontinuity.Torus

variable {N M : ℕ}

section

variable
  (A : RCConfig N M) (f : OpenDiamondEdge A → ℚ)
    (v : Fin N × Fin M)

/-- Extension of an indexed open-edge chain by zero on precisely the closed edges. -/
def extendDiamondChain : ℚ := if h : A v = true then f ⟨v, h⟩ else 0

@[simp] theorem extendDiamondChain_open (hv : A v = true) : extendDiamondChain A f v = f ⟨v, hv⟩ := by
  simp [extendDiamondChain, hv]

@[simp] theorem extendDiamondChain_closed (hv : A v = false) : extendDiamondChain A f v = 0 := by
  simp [extendDiamondChain, hv]

end

section

variable (hN : Even N) (hM : Even M) (A : RCConfig N M)

/-- Outward half-edge flow at a canonical ribbon corner. -/
def ribbonHalfFlow
    (f : OpenDiamondEdge A → ℚ) (d : DirectedDart (checkerArrows N M)) : ℚ :=
  let x := (ribbonEndEquiv hN hM).symm d
  if x.2 then -extendDiamondChain A f x.1 else extendDiamondChain A f x.1

@[simp] theorem ribbonHalfFlow_end
    (f : OpenDiamondEdge A → ℚ) (v : Fin N × Fin M) (b : Bool) :
    ribbonHalfFlow hN hM A f (ribbonEndEquiv hN hM (v, b)) =
      if b then -extendDiamondChain A f v else extendDiamondChain A f v := by
  simp [ribbonHalfFlow]

theorem sum_ribbonHalfFlow_pairing
    (f : OpenDiamondEdge A → ℚ) (g : FaceVertex N M true → ℚ) :
    (∑ d : DirectedDart (checkerArrows N M),
      g (ribbonFace hN hM d) * ribbonHalfFlow hN hM A f d) =
      -(∑ u, g u * diamondBoundary hN hM A f u) := by
  classical
  rw [diamondBoundary_pairing, ← (ribbonEndEquiv hN hM).sum_comp]
  conv_lhs => rw [Fintype.sum_prod_type]
  change (∑ v, ∑ b : Bool,
    g (ribbonFace hN hM (ribbonEndEquiv hN hM (v, b))) *
      ribbonHalfFlow hN hM A f (ribbonEndEquiv hN hM (v, b))) = _
  have hc : (∑ e, diamondCoboundary hN hM A g e * f e) =
      ∑ e : OpenDiamondEdge A,
        (g (faceEndpoint hN hM true e.val true) - g (faceEndpoint hN hM true e.val false)) *
          extendDiamondChain A f e.val := Finset.sum_congr rfl (fun e _ => by rw [extendDiamondChain_open A f e.val e.property]; rfl)
  rw [hc]
  rw [← Finset.sum_subtype (univ.filter fun v => A v = true)
    (by intro v; simp) (fun v =>
      (g (faceEndpoint hN hM true v true) - g (faceEndpoint hN hM true v false)) *
        extendDiamondChain A f v), Finset.sum_filter, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro v _
  simp only [Fintype.sum_bool, ribbonFace_end, ribbonHalfFlow_end,
    Bool.false_eq_true, ite_true, ite_false]
  cases ha : A v
  · simp [extendDiamondChain_closed A f v ha]
  · simp only [ite_true]
    ring

theorem sum_ribbonHalfFlow_corners_eq_neg_boundary (hN : Even N) (hM : Even M)
    (A : RCConfig N M) (f : OpenDiamondEdge A → ℚ) (v : FaceVertex N M true) :
    (∑ p : Port, ribbonHalfFlow hN hM A f (ribbonCornerEquiv hN hM (v, p))) =
      -diamondBoundary hN hM A f v := by
  classical
  have he := sum_ribbonHalfFlow_pairing hN hM A f (fun w => if v = w then 1 else 0)
  rw [← (ribbonCornerEquiv hN hM).sum_comp, Fintype.sum_prod_type] at he
  have hx : ∀ (w : FaceVertex N M true) (p : Port),
      ribbonFace hN hM (ribbonCornerEquiv hN hM (w, p)) = w :=
    fun w p => Subtype.ext (leftFace_faceCorner w.val p)
  simpa only [hx, ite_mul, one_mul, zero_mul, Finset.sum_ite_irrel,
    Finset.sum_const_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true] using he

/-- Vertex conservation is the four-corner zero-sum identity on every primal disc. -/
theorem sum_ribbonHalfFlow_corners
    (f : diamondCycleSpace hN hM A) (v : FaceVertex N M true) :
    (∑ p : Port, ribbonHalfFlow hN hM A f.val (ribbonCornerEquiv hN hM (v, p))) = 0 := by
  have hf : diamondBoundary hN hM A f = 0 := f.property
  simp [sum_ribbonHalfFlow_corners_eq_neg_boundary, hf]

end

end PottsDiscontinuity.Torus
