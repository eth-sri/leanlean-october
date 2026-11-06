module

public import ADR11.Defs
/-!
# Notions used in the statements of the paper's results

* `restrictClusters S H`: the clusters of a rooted tree (or forest) `H` on `X`, restricted to the
  taxa `S` and viewed as clusters on the subtype `S`.
* `restrictSplits S T`: the induced unrooted tree `T(S)` of an unrooted tree `T`, in the
  representation of `ADR11.unroot` (the sides of its splits).
* `SpeciesTree.restrict σ S`: the induced species tree `σ⁺(S)` (the paper's Section 2): its
  clusters are the nonempty traces `A ∩ S` of the clusters of `σ`, and the length of the edge above
  a trace `C` is the sum of the lengths of the edges above the clusters `A` of `σ` with
  `A ∩ S = C` (the edges that merge when nodes of degree 2 are suppressed).
* `coalescenceProb i j t`: the paper's `g_ij(t)`, the probability that `i` lineages coalesce into
  `j` lineages within time `t`, defined from Kingman's coalescent itself.
* `SpeciesTree.rootedTripleProb σ a b c`: the probability that the rooted gene tree displays the
  rooted triple `ab|c`.
-/

@[expose] public section

namespace ADR11

open Finset

variable {X : Type*} [Fintype X] [DecidableEq X]

theorem subtype_nonempty_iff {S A : Finset X} :
    (A.trace S).Nonempty ↔ (A ∩ S).Nonempty := by
  simp [Finset.Nonempty, mem_subtype, mem_inter, and_comm]

/-- The clusters of `H` that meet `S`, restricted to `S`, as clusters on the subtype `S`. -/
def restrictClusters (S : Finset X) (H : Family X) : Family S :=
  (H.filter fun A => (A ∩ S).Nonempty).image fun A => A.trace S

/-- The induced unrooted tree `T(S)` of an unrooted tree `T` (given by the sides of its splits):
the splits of `T` whose two sides both meet `S`, restricted to `S`. -/
def restrictSplits (S : Finset X) (T : Family X) : Family S :=
  (T.filter fun A => (A ∩ S).Nonempty ∧ (Aᶜ ∩ S).Nonempty).image fun A => A.trace S

namespace SpeciesTree

/-- The length of the edge above the cluster `C` of the induced tree `σ(S)`: the sum of the
lengths of the edges above the clusters of `σ` whose trace on `S` is `C`. -/
noncomputable def restrictLength (σ : SpeciesTree X) (S : Finset X) (C : Finset S) : ℝ :=
  ∑ A ∈ σ.clusters with A ≠ univ ∧ A.trace S = C, σ.length A

/-- The induced species tree `σ⁺(S)` on a nonempty set of taxa `S`. -/
noncomputable def restrict (σ : SpeciesTree X) (S : Finset X) (hS : S.Nonempty) :
    SpeciesTree S where
  clusters := restrictClusters S σ.clusters
  univ_mem := mem_image.2 ⟨univ, by simp [σ.univ_mem, hS], subtype_univ _⟩
  singleton_mem := by
    intro x
    refine mem_image.2 ⟨{x.1}, by simp [σ.singleton_mem, x.2], ?_⟩
    ext ⟨y, hy⟩
    simp [mem_subtype, Subtype.ext_iff]
  nonempty_of_mem := by
    grind [restrictClusters, subtype_nonempty_iff]
  laminar := by
    have := σ.laminar
    grind [restrictClusters, Finset.subtype_mono, disjoint_left]
  length := σ.restrictLength S
  length_pos := by
    intro C hC hCu
    unfold restrictLength
    apply Finset.sum_pos
    · intro B hB
      grind [σ.length_pos]
    · aesop (add simp [restrictClusters, filter_nonempty_iff])

end SpeciesTree

end ADR11
