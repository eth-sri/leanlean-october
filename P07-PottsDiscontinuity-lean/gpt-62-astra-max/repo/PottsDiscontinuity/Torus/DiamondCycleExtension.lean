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

/-- Extend a chain to all primal edges, with coefficient zero on absent edges. -/
def fullDiamondChainExtension {A : RCConfig N M} (f : OpenDiamondEdge A → ℚ) :
    OpenDiamondEdge (openRCConfig N M) → ℚ := fun e => extendDiamondChain f e.val

variable (hN : Even N) (hM : Even M) (A : RCConfig N M) (f : diamondCycleSpace hN hM A)

theorem ribbonHalfFlow_fullExtension
    (f : OpenDiamondEdge A → ℚ) (d : DirectedDart (checkerArrows N M)) :
    ribbonHalfFlow hN hM (fullDiamondChainExtension f) d =
      ribbonHalfFlow hN hM f d := by
  rfl

theorem fullDiamondChainExtension_mem :
    fullDiamondChainExtension f.val ∈ diamondCycleSpace hN hM (openRCConfig N M) := by
  rw [diamondCycleSpace_mem_iff_corners]
  intro v
  exact sum_ribbonHalfFlow_corners f v

/-- The actual inclusion of conserved indexed flows into the full torus cycle space. -/
def fullDiamondCycleExtension {hN : Even N} {hM : Even M} {A : RCConfig N M}
    (f : diamondCycleSpace hN hM A) : diamondCycleSpace hN hM (openRCConfig N M) :=
  ⟨fullDiamondChainExtension f.val, fullDiamondChainExtension_mem hN hM A f⟩

theorem ribbonCornerPrimitive_fullExtension (d : DirectedDart (checkerArrows N M)) :
    ribbonCornerPrimitive (fullDiamondCycleExtension f) d =
      ribbonCornerPrimitive f d := by
  rfl

theorem ribbonIntersectionCoefficient_fullExtension (e : OpenDiamondEdge A) :
    ribbonIntersectionCoefficient
      (fullDiamondCycleExtension f) ⟨e.val, rfl⟩ =
        ribbonIntersectionCoefficient f e := by
  unfold ribbonIntersectionCoefficient
  rw [ribbonCornerPrimitive_fullExtension, ribbonCornerPrimitive_fullExtension]
  change _ - _ - extendDiamondChain f.val e.val = _
  rw [extendDiamondChain_open f.val e.property]

theorem sum_fullDiamondChainExtension {A : RCConfig N M} (f : OpenDiamondEdge A → ℚ)
    (c : Fin N × Fin M → ℚ) :
    (∑ e : OpenDiamondEdge (openRCConfig N M), c e.val * fullDiamondChainExtension f e) =
      ∑ e : OpenDiamondEdge A, c e.val * f e := by
  classical
  rw [← (fullDiamondEdgeEquiv N M).symm.sum_comp]
  change (∑ v : Fin N × Fin M, c v * extendDiamondChain f v) = _
  have he : (∑ e : OpenDiamondEdge A, c e.val * f e) =
      ∑ e : OpenDiamondEdge A, c e.val * extendDiamondChain f e.val :=
    Finset.sum_congr rfl (fun e _ => by rw [extendDiamondChain_open f e.property])
  rw [he, ← Finset.sum_subtype (univ.filter fun v => A v = true)
    (by grind) (fun v => c v * extendDiamondChain f v), Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro v _
  cases ha : A v
  · simp [extendDiamondChain_closed f ha, mul_zero, Bool.false_eq_true, ite_false]
  · rfl

/-- Cellular intersection is preserved by the actual subgraph inclusion. -/
theorem ribbonIntersection_fullExtension
    (f g : diamondCycleSpace hN hM A) :
    ribbonIntersection
      (fullDiamondCycleExtension f) (fullDiamondCycleExtension g) =
        ribbonIntersection f g := by
  unfold ribbonIntersection
  change (∑ e : OpenDiamondEdge (openRCConfig N M),
    ribbonIntersectionCoefficient (fullDiamondCycleExtension f) e *
      fullDiamondChainExtension g.val e) = _
  have he := sum_fullDiamondChainExtension g.val
    (fun v => ribbonIntersectionCoefficient
      (fullDiamondCycleExtension f) ⟨v, rfl⟩)
  simp [he, ribbonIntersectionCoefficient_fullExtension]

theorem diamondHorizontalDisplacement_fullExtension :
    diamondHorizontalDisplacement (fullDiamondCycleExtension f).val =
      diamondHorizontalDisplacement f.val :=
  sum_fullDiamondChainExtension f.val (fun v => if checker v then -1 else 1)

theorem diamondVerticalDisplacement_fullExtension :
    diamondVerticalDisplacement (fullDiamondCycleExtension f).val =
      diamondVerticalDisplacement f.val := by
  have he := sum_fullDiamondChainExtension f.val (fun _ => 1)
  simp only [one_mul] at he
  exact congrArg Neg.neg he

end PottsDiscontinuity.Torus
