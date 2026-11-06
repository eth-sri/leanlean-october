module

public import ADR11.Basic

/-!
# Small species trees and gene trees used in the paper

Taxa are labelled `a, b, c, d, e = 0, 1, 2, 3, 4` (types `Fin 3`, `Fin 4`, `Fin 5`), and gene
lineages carry the same labels (`A, B, C, D, E` in the paper).

* `treeOfClusters C`: the unrooted tree whose nontrivial splits are `A | Aᶜ` for `A ∈ C`,
  in the representation of `ADR11.unroot`.
* `T5 i` (`1 ≤ i ≤ 15`): the paper's unrooted 5-taxon gene tree `T_i` (Table 5), given by one side
  of each of its two nontrivial splits.
* Cluster sets of the five-taxon species tree shapes: the balanced tree `(((a,b),c),(d,e))`, the
  caterpillar `((((a,b),c),d),e)` and the pseudocaterpillar `(((a,b),(d,e)),c)` (Fig. 2c–e).
* `SpeciesTree.ofLengths`: species trees with given clusters and internal edge lengths; pendant
  edges get length `1`, which does not affect the distributions with one lineage per taxon.
-/

@[expose] public section

namespace ADR11

open Finset

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- The unrooted tree with the nontrivial splits `A | Aᶜ`, `A ∈ C` (and all trivial splits). -/
def treeOfClusters (C : Finset (Finset X)) : Finset (Finset X) :=
  unroot (insert univ (C ∪ univ.image fun x => {x}))

/-- The hierarchy with the given nontrivial clusters `C`, together with `univ` and the
singletons. -/
def hierarchyOf (C : Finset (Finset X)) : Finset (Finset X) :=
  insert univ (C ∪ univ.image fun x => {x})

/-- The balanced species tree `(((a,b),c),(d,e))` (Fig. 2c). -/
def balanced5 : Finset (Finset (Fin 5)) := hierarchyOf {{0, 1}, {0, 1, 2}, {3, 4}}

/-- The rooted caterpillar species tree `((((a,b),c),d),e)` (Fig. 2d). -/
def caterpillar5 : Finset (Finset (Fin 5)) := hierarchyOf {{0, 1}, {0, 1, 2}, {0, 1, 2, 3}}

/-- The pseudocaterpillar species tree `(((a,b),(d,e)),c)` (Fig. 2e). -/
def pseudocaterpillar5 : Finset (Finset (Fin 5)) := hierarchyOf {{0, 1}, {3, 4}, {0, 1, 3, 4}}

/-- The paper's unrooted 5-taxon gene trees `T₁, …, T₁₅` (Table 5), each given by one side of
each of its two nontrivial splits. For instance `T₁` has the splits `AB|CDE` and `ABC|DE`. -/
def T5 : ℕ → Finset (Finset (Fin 5))
  | 1 => treeOfClusters {{0, 1}, {0, 1, 2}}
  | 2 => treeOfClusters {{0, 1}, {0, 1, 3}}
  | 3 => treeOfClusters {{0, 1}, {0, 1, 4}}
  | 4 => treeOfClusters {{0, 2}, {0, 1, 2}}
  | 5 => treeOfClusters {{0, 2}, {0, 2, 3}}
  | 6 => treeOfClusters {{0, 2}, {0, 2, 4}}
  | 7 => treeOfClusters {{0, 3}, {0, 1, 3}}
  | 8 => treeOfClusters {{0, 3}, {0, 2, 3}}
  | 9 => treeOfClusters {{0, 3}, {0, 3, 4}}
  | 10 => treeOfClusters {{0, 4}, {0, 1, 4}}
  | 11 => treeOfClusters {{0, 4}, {0, 2, 4}}
  | 12 => treeOfClusters {{0, 4}, {0, 3, 4}}
  | 13 => treeOfClusters {{1, 2}, {0, 1, 2}}
  | 14 => treeOfClusters {{1, 3}, {0, 1, 3}}
  | 15 => treeOfClusters {{1, 4}, {0, 1, 4}}
  | _ => ∅

/-- `u σ i = ℙ_σ(T_i)`, the probability of the unrooted gene tree `T_i` under the multispecies
coalescent on a 5-taxon species tree `σ`, with one lineage per taxon. -/
noncomputable def u (σ : SpeciesTree (Fin 5)) (i : ℕ) : ℝ :=
  σ.unrootedDist id (T5 i)

/-! ### Species trees with given internal edge lengths -/

/-- A species tree with the clusters `H` and the internal edge lengths `len` (pendant edges get
length `1`). -/
noncomputable def SpeciesTree.ofLengths (H : Finset (Finset X)) (len : Finset X → ℝ)
    (h₁ : univ ∈ H) (h₂ : ∀ x : X, {x} ∈ H) (h₃ : ∀ A ∈ H, A.Nonempty)
    (h₄ : ∀ A ∈ H, ∀ B ∈ H, A ⊆ B ∨ B ⊆ A ∨ Disjoint A B)
    (h₅ : ∀ A ∈ H, A ≠ univ → 2 ≤ #A → 0 < len A) : SpeciesTree X where
  clusters := H
  univ_mem := h₁
  singleton_mem := h₂
  nonempty_of_mem := h₃
  laminar := h₄
  length A := if #A ≤ 1 then 1 else len A
  length_pos A hA hne := by
    split_ifs with h <;> grind

end ADR11
