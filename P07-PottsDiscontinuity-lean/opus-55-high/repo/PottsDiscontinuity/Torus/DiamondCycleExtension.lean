module

public import PottsDiscontinuity.Torus.DiamondDisplacement

/-!
# Extending subgraph cycles to the full torus

The inclusion extends indexed chains by zero on closed edges. It preserves vertex
conservation, the normalized corner primitives, the cyclic-order intersection form,
and both lifted displacement coordinates.
-/

@[expose] public section

open Finset PottsDiscontinuity.SixVertex

namespace PottsDiscontinuity.Torus

variable {N M : ℕ}

/-- The fully open edge subtype is explicitly the full indexed edge carrier. -/
def fullDiamondEdgeEquiv (N M : ℕ) : OpenDiamondEdge (openRCConfig N M) ≃ Fin N × Fin M where
  toFun e := e.val
  invFun v := ⟨v, rfl⟩
  left_inv _ := rfl
  right_inv _ := rfl

section
variable (A : RCConfig N M) (f : OpenDiamondEdge A → ℚ)
/-- Extend a chain to all primal edges, with coefficient zero on absent edges. -/
def fullDiamondChainExtension  :
    OpenDiamondEdge (openRCConfig N M) → ℚ := fun e => extendDiamondChain A f e.val

end

section
variable (hN : Even N) (hM : Even M) (A : RCConfig N M)
theorem ribbonHalfFlow_fullExtension (f : OpenDiamondEdge A → ℚ) (d : DirectedDart (checkerArrows N M)) :
    ribbonHalfFlow hN hM (openRCConfig N M) (fullDiamondChainExtension A f) d =
      ribbonHalfFlow hN hM A f d := by
  rfl

theorem fullDiamondChainExtension_mem (f : diamondCycleSpace hN hM A) :
    fullDiamondChainExtension A f.val ∈ diamondCycleSpace hN hM (openRCConfig N M) := by
  rw [diamondCycleSpace_mem_iff_corners]
  intro v
  exact sum_ribbonHalfFlow_corners hN hM A f v

/-- The actual inclusion of conserved indexed flows into the full torus cycle space. -/
def fullDiamondCycleExtension (f : diamondCycleSpace hN hM A) : diamondCycleSpace hN hM (openRCConfig N M) :=
  ⟨fullDiamondChainExtension A f.val, fullDiamondChainExtension_mem hN hM A f⟩


theorem ribbonIntersectionCoefficient_fullExtension (f : diamondCycleSpace hN hM A) (e : OpenDiamondEdge A) :
    ribbonIntersectionCoefficient hN hM (openRCConfig N M)
      (fullDiamondCycleExtension hN hM A f) ⟨e.val, rfl⟩ =
        ribbonIntersectionCoefficient hN hM A f e := by
  change _ - _ - extendDiamondChain A f.val e.val = _
  aesop
end

theorem sum_fullDiamondChainExtension (A : RCConfig N M) (f : OpenDiamondEdge A → ℚ)
    (c : Fin N × Fin M → ℚ) :
    (∑ e : OpenDiamondEdge (openRCConfig N M), c e.val * fullDiamondChainExtension A f e) =
      ∑ e : OpenDiamondEdge A, c e.val * f e := by
  rw [← (fullDiamondEdgeEquiv N M).symm.sum_comp]
  change (∑ v : Fin N × Fin M, c v * extendDiamondChain A f v) = _
  have he : (∑ e : OpenDiamondEdge A, c e.val * f e) =
      ∑ e : OpenDiamondEdge A, c e.val * extendDiamondChain A f e.val :=
    Finset.sum_congr rfl (fun e _ => by aesop)
  rw [he, ← Finset.sum_subtype (univ.filter fun v => A v = true)
    (by simp) (fun v => c v * extendDiamondChain A f v), Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro v _
  cases ha : A v
  · simp only [extendDiamondChain_closed A f v ha, mul_zero, Bool.false_eq_true, ite_false]
  · rfl

section
variable (hN : Even N) (hM : Even M) (A : RCConfig N M)
/-- Cellular intersection is preserved by the actual subgraph inclusion. -/
theorem ribbonIntersection_fullExtension (f g : diamondCycleSpace hN hM A) :
    ribbonIntersection hN hM (openRCConfig N M)
      (fullDiamondCycleExtension hN hM A f) (fullDiamondCycleExtension hN hM A g) =
        ribbonIntersection hN hM A f g := by
  change (∑ e : OpenDiamondEdge (openRCConfig N M),
    ribbonIntersectionCoefficient hN hM (openRCConfig N M) (fullDiamondCycleExtension hN hM A f) e *
      fullDiamondChainExtension A g.val e) = _
  have he := sum_fullDiamondChainExtension A g.val
    (fun v => ribbonIntersectionCoefficient hN hM (openRCConfig N M)
      (fullDiamondCycleExtension hN hM A f) ⟨v, rfl⟩)
  rw [he]
  exact Finset.sum_congr rfl (fun e _ => by rw [ribbonIntersectionCoefficient_fullExtension])

theorem diamondHorizontalDisplacement_fullExtension (f : diamondCycleSpace hN hM A) :
    diamondHorizontalDisplacement (openRCConfig N M) (fullDiamondCycleExtension hN hM A f).val =
      diamondHorizontalDisplacement A f.val :=
  sum_fullDiamondChainExtension A f.val (fun v => if checker v then -1 else 1)

theorem diamondVerticalDisplacement_fullExtension (f : diamondCycleSpace hN hM A) :
    diamondVerticalDisplacement (openRCConfig N M) (fullDiamondCycleExtension hN hM A f).val =
      diamondVerticalDisplacement A f.val := by
  have he := sum_fullDiamondChainExtension A f.val (fun _ => 1)
  simp at he
  exact congrArg Neg.neg he
end

end PottsDiscontinuity.Torus
