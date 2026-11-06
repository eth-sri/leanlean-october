import RequestProject.ReceivedTreeFoxCoordinates
import RequestProject.TreeCoverAcyclic
import RequestProject.Tac


/-! Edge chains are determined by their non-tree coordinates and off-root boundary. -/
bwd

namespace FiniteChains.Comb.ReceivedTree
open SpanningTree
universe u
variable {K : Complex2.{u}} (T : SpanningTree K) {G : Type u} [Group G]
  (φ : PresGroup (treeRel T) →* G)


theorem cover_tgt_of_isTree (h : T.isTree e) g :
    (cover T φ).tgt (g, e) = (g, K.tgt e) := by
  simp [cover, tgt, germValue, germWord, h]

/-- A finite chain supported on the tree cannot have boundary only at the
root in each sheet. The maximal-height argument is independent of the receiver. -/
theorem treeChain_eq_zero_off_root {z : (G × K.E) →₀ ℤ}
    (hsupp : ∀ x ∈ z.support, T.isTree x.2)
    (hz : ∀ g v, v ≠ T.root → bdry1 (cover T φ) z (g, v) = 0) : z = 0 := by
  classical
  by_contra hzne
  have hne : z.support.Nonempty := Finsupp.support_nonempty_iff.2 hzne
  obtain ⟨x₀, hx₀mem, hx₀max⟩ := z.support.exists_max_image
    (if h : T.isTree ·.2 then T.ht (treeTop h) else 0) hne
  have he₀ : T.isTree x₀.2 := hsupp x₀ hx₀mem
  obtain ⟨a₀, ha₀ne, ha₀up⟩ := (T.isTree_iff x₀.2).1 he₀
  have hg : ∀ x ∈ z.support, ∀ a ha, (T.up a ha).1 = x.2 →
      (if h : T.isTree x.2 then T.ht (treeTop h) else 0) = T.ht a := by
    intro x hx a ha hup
    have hex := hsupp x hx
    rw [dif_pos hex, treeTop_eq hex ha hup]
  have hg₀ : (if h : T.isTree x₀.2 then T.ht (treeTop h) else 0) = T.ht a₀ :=
    by tauto
  -- all terms but the one of `x₀` vanish at the vertex `(x₀.1, a₀)`
  have hterm : ∀ x ∈ z.support, x ≠ x₀ →
      z x * ((Finsupp.single ((cover T φ).tgt x) (1)) (x₀.1, a₀)
        - (Finsupp.single ((cover T φ).src x) (1)) (x₀.1, a₀)) = 0 := by
    intro x hx hxne
    have hex := hsupp x hx
    obtain ⟨a, hane, haup⟩ := (T.isTree_iff x.2).1 hex
    have key : ∀ v, (v = K.src x.2 ∨ v = K.tgt x.2) → (x.1, v) ≠ (x₀.1, a₀) := by
      intro v hv hc
      have hparent : T.parent a hane = a₀ → False := by
        intro hp
        have hht := T.ht_parent hane
        grind
      rcases tree_edge_endpoints hane haup with ⟨hs, ht⟩ | ⟨hs, ht⟩
      · grind
      grind
    have h1 : (cover T φ).tgt x ≠ (x₀.1, a₀) := by
      rw [cover_tgt_of_isTree T φ hex x.1]
      grind
    have h2 : (cover T φ).src x ≠ (x₀.1, a₀) := by
      tauto
    simp_all
  -- evaluate the boundary at the vertex `(x₀.1, a₀)`
  have hzero : (0) = z x₀ *
      ((Finsupp.single ((cover T φ).tgt x₀) (1)) (x₀.1, a₀)
        - (Finsupp.single ((cover T φ).src x₀) (1)) (x₀.1, a₀)) := by
    have h := bdry1_apply (cover T φ) z (x₀.1, a₀)
    rw [hz x₀.1 a₀ ha₀ne] at h
    have h2 := h.trans (Finset.sum_eq_single_of_mem x₀ hx₀mem hterm)
    omega
  have hsrc : (cover T φ).src x₀ = (x₀.1, K.src x₀.2) := rfl
  have htgt : (cover T φ).tgt x₀ = (x₀.1, K.tgt x₀.2) := by
    rw [cover_tgt_of_isTree T φ he₀ x₀.1]
  have hpne := parent_ne_self (T := T) ha₀ne
  rcases tree_edge_endpoints ha₀ne ha₀up with ⟨hs, ht⟩ | ⟨hs, ht⟩
  · grind
  grind

theorem edgeChain_eq_zero_of_nonTree_coordinates c
    (hc : ∀ i : NonTree T, cellCoefficient i.1 c = 0)
    (hb : ∀ g v, v ≠ T.root → bdry1 (cover T φ) c (g, v) = 0) : c = 0 := by
  apply treeChain_eq_zero_off_root T φ _ hb
  intro x hx
  by_contra ht
  have h := congrArg (·.coeff x.1) (hc ⟨x.2, ht⟩)
  rw [cellCoefficient_apply] at h
  simp_all

/-- In particular, one-chains with boundary supported over the root are
determined by their non-tree Fox coordinates, even if they are not cycles. -/
theorem edgeChains_eq_of_nonTree_coordinates c d
    (hc : ∀ i : NonTree T, cellCoefficient i.1 c = cellCoefficient i.1 d)
    (hb : ∀ g v, v ≠ T.root →
      bdry1 (cover T φ) c (g, v) = bdry1 (cover T φ) d (g, v)) : c = d := by
  apply sub_eq_zero.mp
  apply edgeChain_eq_zero_of_nonTree_coordinates T φ
  · simp_all
  simp_all
