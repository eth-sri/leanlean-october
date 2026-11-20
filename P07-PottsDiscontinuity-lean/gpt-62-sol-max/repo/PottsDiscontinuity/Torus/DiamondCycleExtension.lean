module

public import PottsDiscontinuity.Torus.DiamondDisplacement

/-!
# Extending subgraph cycles to the full torus

The inclusion extends indexed chains by zero on closed edges. It preserves vertex
conservation and both lifted displacement coordinates.
-/

@[expose] public section

open Finset PottsDiscontinuity.SixVertex

namespace PottsDiscontinuity.Torus

variable {N M : ℕ}

section

variable (A : RCConfig N M) (f : OpenDiamondEdge A → ℚ)

/-- Extend a chain to all primal edges, with coefficient zero on absent edges. -/
def fullDiamondChainExtension :
    OpenDiamondEdge (openRCConfig N M) → ℚ := fun e => extendDiamondChain A f e.val

end

theorem ribbonHalfFlow_fullExtension (hN : Even N) (hM : Even M) (A : RCConfig N M)
    (f : OpenDiamondEdge A → ℚ) (d : DirectedDart (checkerArrows N M)) :
    ribbonHalfFlow hN hM (openRCConfig N M) (fullDiamondChainExtension A f) d =
      ribbonHalfFlow hN hM A f d := rfl

section

variable
  (hN : Even N) (hM : Even M) (A : RCConfig N M)
    (f : diamondCycleSpace hN hM A)

theorem fullDiamondChainExtension_mem :
    fullDiamondChainExtension A f.val ∈ diamondCycleSpace hN hM (openRCConfig N M) := by
  rw [diamondCycleSpace_mem_iff_corners]
  intro v
  simp_rw [ribbonHalfFlow_fullExtension]
  exact sum_ribbonHalfFlow_corners hN hM A f v

/-- The actual inclusion of conserved indexed flows into the full torus cycle space. -/
def fullDiamondCycleExtension : diamondCycleSpace hN hM (openRCConfig N M) :=
  ⟨fullDiamondChainExtension A f.val, fullDiamondChainExtension_mem hN hM A f⟩


end

theorem sum_fullDiamondChainExtension (A : RCConfig N M) (f : OpenDiamondEdge A → ℚ)
    (c : Fin N × Fin M → ℚ) :
    (∑ e : OpenDiamondEdge (openRCConfig N M), c e.val * fullDiamondChainExtension A f e) =
      ∑ e : OpenDiamondEdge A, c e.val * f e := by
  classical
  rw [← (fullDiamondEdgeEquiv N M).symm.sum_comp]
  change (∑ v : Fin N × Fin M, c v * extendDiamondChain A f v) = _
  have he : (∑ e : OpenDiamondEdge A, c e.val * f e) =
      ∑ e : OpenDiamondEdge A, c e.val * extendDiamondChain A f e.val :=
    Finset.sum_congr rfl (fun e _ => by rw [extendDiamondChain_open A f e.val e.property])
  rw [he, ← Finset.sum_subtype (univ.filter fun v => A v = true)
    (by intro v; simp) (fun v => c v * extendDiamondChain A f v), Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro v _
  cases ha : A v
  · simp [extendDiamondChain_closed A f v ha]
  rfl

section

variable (hN : Even N) (hM : Even M) (A : RCConfig N M)

theorem diamondHorizontalDisplacement_fullExtension (f : diamondCycleSpace hN hM A) :
    diamondHorizontalDisplacement (openRCConfig N M) (fullDiamondCycleExtension hN hM A f).val =
      diamondHorizontalDisplacement A f.val :=
  sum_fullDiamondChainExtension A f.val (fun v => if checker v then -1 else 1)

theorem diamondVerticalDisplacement_fullExtension (f : diamondCycleSpace hN hM A) :
    diamondVerticalDisplacement (openRCConfig N M) (fullDiamondCycleExtension hN hM A f).val =
      diamondVerticalDisplacement A f.val := by
  have he := sum_fullDiamondChainExtension A f.val (fun _ => 1)
  simp only [one_mul] at he
  exact congrArg Neg.neg he

end

end PottsDiscontinuity.Torus
