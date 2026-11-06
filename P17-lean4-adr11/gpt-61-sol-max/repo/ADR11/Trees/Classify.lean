module

public import ADR11.MSC.Relabel
public import ADR11.Trees.Hierarchy
public import ADR11.Rootings.Defs
/-!
# Unrooted trees on four and five taxa, and their rootings

Every species tree on four or five taxa is, after relabelling, a rooting of one of a few standard
unrooted trees, and the rootings of each standard unrooted tree are listed explicitly.

* Four taxa: `U4 1 = AB|CD` and the star `U4 0`; `rootings4 k` lists the hierarchies on `Fin 4`
  with unrooted tree `U4 k` (7 for `AB|CD`: four caterpillars, the balanced tree, and the two
  trees with one cherry and a trifurcating root; 5 for the star).
* Five taxa: `U5 2 = {AB|CDE, ABC|DE}`, `U5 1 = AB|CDE`, the star `U5 0`; `rootings5 k` lists the
  hierarchies on `Fin 5` with unrooted tree `U5 k` (10, 8 and 6 of them), and
  `binaryRootings5` the 7 binary ones with unrooted tree `U5 2`.

## Main results

* `exists_equiv_unroot_eq_U4`, `exists_equiv_unroot_eq_U5`: normal forms up to relabelling.
* `exists_equiv_unroot_eq_U5_two_of_isBinary`: a binary 5-taxon tree has unrooted shape `U5 2`.
* `mem_rootings4`, `mem_rootings5`, `mem_binaryRootings5`: the lists are complete.
-/

@[expose] public section

namespace ADR11

open Finset

variable {X : Type*} [Fintype X] [DecidableEq X]
variable {n : ℕ}

/-! ### Unrooting and relabelling -/

/-! ### The splits of a species tree on four or five taxa -/

/-- On four or five taxa, the splits of a species tree are the trivial ones and those with a side
of two taxa. -/
theorem mem_unroot_iff (hX : Fintype.card X = 4 ∨ Fintype.card X = 5)
    (σ : SpeciesTree X) (A : Finset X) :
    A ∈ unroot σ.clusters ↔ #A = 1 ∨ #A = Fintype.card X - 1 ∨
      A ∈ (unroot σ.clusters).filter (fun B => #B = 2) ∨
      Aᶜ ∈ (unroot σ.clusters).filter (fun B => #B = 2) := by
  have hs := σ.singleton_mem
  have hn := σ.nonempty_of_mem
  have hu := card_lt_iff_ne_univ A
  have huc := card_lt_iff_ne_univ Aᶜ
  grind [mem_unroot, card_eq_one, card_compl, compl_mem_unroot]

theorem mem_rootings (τ : SpeciesTree X) {U : Family X} (h : unroot τ.clusters = U) :
    τ.clusters ∈ rootingsOf U := by
  have hc : τ.clusters = hierarchyOf (τ.clusters.filter fun A => 2 ≤ #A ∧ A ≠ univ) := by
    ext A
    have := τ.isHierarchy
    grind [IsHierarchy, hierarchyOf, card_eq_one, card_pos]
  subst U
  refine mem_image.2 ⟨_, mem_filter.2 ⟨mem_powerset.2 ?_, ?_⟩,
    hc.symm⟩
  swap
  · rw [← hc]
    exact ⟨τ.isHierarchy, rfl⟩
  grind [mem_unroot]

set_option maxHeartbeats 0
set_option maxRecDepth 10000
namespace Shape
def pairs (n : ℕ) : Finset (Family (Fin n)) :=
  (((univ : Family (Fin n)).filter fun A => #A = 2).powerset).filter fun P =>
    ∀ A ∈ P, ∀ B ∈ P, A ≠ B → Disjoint A B

theorem mem_pairs (hn : 4 ≤ n) (σ : SpeciesTree (Fin n)) :
    (unroot σ.clusters).filter (fun A => #A = 2) ∈ pairs n := by
  unfold pairs
  refine mem_filter.2 ⟨mem_powerset.2 ?_, ?_⟩
  · exact filter_subset_filter _ (subset_univ _)
  · intro A hA B hB hne
    simp at hA hB
    have := Fintype.card_fin n
    grind (splits := 40) [→ σ.laminar, mem_unroot, disjoint_compl_right_iff, eq_of_subset_of_card_le, card_compl, subset_compl_iff_disjoint_left]

theorem topology (hn : n = 4 ∨ n = 5) (σ : SpeciesTree (Fin n)) :
    unroot σ.clusters = treeOfClusters ((unroot σ.clusters).filter fun A => #A = 2) := by
  ext A
  rw [mem_unroot_iff (by simpa) σ A, treeOfClusters, mem_unroot]
  simp only [hierarchyOf, mem_union, mem_insert, mem_image, mem_univ, true_and, mem_filter]
  grind [Fintype.card_fin, card_eq_one, card_compl, card_lt_iff_ne_univ]

theorem normal (hn : n = 4 ∨ n = 5) (hX : Fintype.card X = n)
    (U : ℕ → Family (Fin n)) (m : ℕ)
    (hc : ∀ P : pairs n, ∃ e : Equiv.Perm (Fin n), ∃ k : Fin m,
      relabelFamily e (treeOfClusters P.1) = U k) (σ : SpeciesTree X) :
    ∃ e : Fin n ≃ X, ∃ k : Fin m, unroot (σ.relabel e.symm).clusters = U k := by
  let e := (Fintype.equivFinOfCardEq hX).symm
  let τ := σ.relabel e.symm
  obtain ⟨p, k, hk⟩ := hc ⟨_, mem_pairs (by omega) τ⟩
  refine ⟨p.symm.trans e, k, ?_⟩
  rw [← topology hn τ] at hk
  simp only [τ, SpeciesTree.relabel_clusters, unroot_relabelFamily] at hk ⊢
  simpa only [relabelFamily, image_image, Function.comp_def, map_map,
    Equiv.trans_toEmbedding, Equiv.symm_trans, Equiv.symm_symm] using hk
end Shape

end ADR11
