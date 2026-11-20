module

public import RequestProject.ReceivedTreeFoxCoordinates
public import RequestProject.TreeCoverAcyclic

@[expose] public section

/-! Edge chains are determined by their non-tree coordinates and off-root boundary. -/
set_option backward.isDefEq.respectTransparency false

namespace FiniteChains.Comb.ReceivedTree
open SpanningTree
universe u
variable {K : Complex2.{u}} (T : SpanningTree K) {G : Type u} [Group G]
  (φ : PresGroup (treeRel T) →* G)

theorem cover_tgt_of_isTree {e : K.E} (h : T.isTree e) (g : G) :
    (cover T φ).tgt (g, e) = (g, K.tgt e) := by
  simp [cover, tgt, germValue, germWord, h]

/-- A finite chain supported on the tree cannot have boundary only at the
root in each sheet. The maximal-height argument is independent of the receiver. -/
theorem treeChain_eq_zero_off_root {z : (G × K.E) →₀ ℤ}
    (hsupp : ∀ x ∈ z.support, T.isTree x.2)
    (hz : ∀ g v, v ≠ T.root → bdry1 (cover T φ) z (g, v) = 0) : z = 0 := by
  apply treeChain_eq_zero_of_offRoot _ (fun x h => cover_tgt_of_isTree T φ h x.1) hsupp
  intro g v hv
  exact (bdry1_apply (cover T φ) z _).symm.trans (hz g v hv)

theorem edgeChain_eq_zero_of_nonTree_coordinates (c : (G × K.E) →₀ ℤ)
    (hc : ∀ i : NonTree T, cellCoefficient i.1 c = 0)
    (hb : ∀ g v, v ≠ T.root → bdry1 (cover T φ) c (g, v) = 0) : c = 0 := by
  apply treeChain_eq_zero_off_root T φ _ hb
  intro x hx
  by_contra ht
  have h := congrArg (fun a : MonoidAlgebra ℤ G => a.coeff x.1) (hc ⟨x.2, ht⟩)
  rw [cellCoefficient_apply] at h; exact (Finsupp.mem_support_iff.mp hx) h

/-- In particular, one-chains with boundary supported over the root are
determined by their non-tree Fox coordinates, even if they are not cycles. -/
theorem edgeChains_eq_of_nonTree_coordinates (c d : (G × K.E) →₀ ℤ)
    (hc : ∀ i : NonTree T, cellCoefficient i.1 c = cellCoefficient i.1 d)
    (hb : ∀ g v, v ≠ T.root →
      bdry1 (cover T φ) c (g, v) = bdry1 (cover T φ) d (g, v)) : c = d := by
  apply sub_eq_zero.mp
  apply edgeChain_eq_zero_of_nonTree_coordinates T φ
  · simp [map_sub, hc, sub_self]
  · intro g v hv
    rw [map_sub, Finsupp.sub_apply, hb g v hv, sub_self]

end FiniteChains.Comb.ReceivedTree
